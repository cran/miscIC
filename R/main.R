#Wrapper to do the NNLSE step
nnlse <- function(a, b, c=rep(1,ncol(a)), d=1, eps=1e-3) nnls::nnls(rbind(c, a * eps), c(d, b * eps))

#Logit and inverse logit
expit <- function(x) exp(x)/(1+exp(x))
logit <- function(x) log(x/(1-x))

#Finding the local maxima
locmax <- function(x) {
  left <- c(-Inf,x[1:(length(x)-1)])
  right <- c(x[2:length(x)],-Inf)
  which(x>left & x>right & x>0)
}

cumsumA <- function(x) c(0,cumsum(x[1:(length(x)-1)]))
bcumsum <- function(x) cumsum(x[length(x):1])[length(x):1]

addi <- function(x,i,d) {
  x[i]<-x[i] + d
  x
}


#main function
miscIC <- function(formula, data, subject, initial, est.e, afn=NULL, bfn=NULL,print.level=2,...) {
  #formula: identifying the state and time variable
  #data: data frame containing the 0/1 state indicator, the observation times, the subject variable
  #subject: term indicating the subject variable
  #initial: vector of initial values (or fixed values).
  #est.e: logical to determine if parameters for the misclassification model are to be estimated (TRUE) or fixed (FALSE)
  #afn: optional function that defines the sensitivity parameter as a function of the parameters and time. If omitted, a time constant sensitivity is assumed
  #bfn: optional function that defines the specificity parameter as a function of the parameters and time. If omitted, a time constant specificity is assumed
  #print.level: amount of detail to print of the optimization of the parametric part.
  #...: optional control parameters

  #Data processing:
  #Rename the variables to be in standard form
  call <- match.call()
  indx <- match(c("subject"), names(call), nomatch = 0)
  if (indx!=0) {
    temp <- call[indx]
    subjectvar <- as.character(temp$subject)
  }else{
    stop("subject variable not specified")
  }
  statevar <- all.vars(formula[[2]])
  timevar <- all.vars(formula[[3]])
  indexes <- match(c(statevar,timevar,subjectvar),names(data), nomatch=0)
  if (any(indexes==0)) {
    k <- c(statevar,timevar,subjectvar)[which(indexes==0)]
    stop(paste("Variable(s) ",k,"not found in the data."))
  }
  standard_data <- data[,indexes]
  #Remove any missing values
  if (anyNA(standard_data)) {
    warning("Dataset contains NAs which have been removed")
    standard_data <- stats::na.omit(standard_data)
  }

  #Then need to triage based on whether afn and bfn are specified
  if (is.null(afn) & is.null(bfn)) {
    if (est.e) {
     afn <- function(x,t) expit(x[1])
     bfn <- function(x,t) expit(x[2])
     #Assume the initial values are on the natural scale - so change them to logit scale
     initial <- logit(initial)
    }else{
      afn <- function(x,t) initial[1]
      bfn <- function(x,t) initial[2]
    }
  }
  fitted <- miscICfitting(standard_data, x=initial,afn=afn,bfn=bfn,est.e=est.e,print.level=print.level,...)
  #Extract the relevant parts from the attributes
  F <- attr(fitted,"F")
  f <- attr(fitted,"f")
  lt <- attr(fitted,"lt")
  ut <- attr(fitted,"ut")
  F <- F[f>0]
  lt <- lt[f>0]
  ut <- ut[f>0]
  f <- f[f>0]
  npar <- length(attr(fitted,"x"))
  output <- list(par=attr(fitted,"x"),npar=npar,deviance=2*sum(fitted),F=F,f=f,lt=lt,ut=ut,covmat=attr(fitted,"H"),DD=attr(fitted,"DD"),afn=afn,bfn=bfn,data=standard_data)
  class(output) <- "miscIC"
  return(output)
}

print.miscIC <- function(x,ci=TRUE,...) {
  model <- x
  par <- c(model$par)
  if (is.null(model$covmat)) {
    cat("\nNo unknown parameters in parametric part\n")
  }else{
  covmat <- model$covmat

  if (ci) {
    std.err <- diag(covmat)^0.5
    mat <- round(cbind(par, par - qnorm(0.975)*std.err,par + qnorm(0.975)*std.err),4)
    dimnames(mat)[[2]] <- c("Est","Low 95%","Up 95%")
  }else{
    mat <- round(cbind(par),4)
    dimnames(mat)[[2]] <- c("Est")
  }
  dimnames(mat)[[1]] <- c(1:length(par))
  print(mat)
  }
  cat(paste("\nDeviance:",round(model$deviance,2)))
}

plot.miscIC <- function(x,...) {
  plot(c(0,x$ut),c(0,x$F),type="s",xlab="Time",ylab=expression(hat(F)),...)
  F1 <- c(0,x$F)
  incr <- which(x$F - F1[1:(length(x$F))]>1e-6)
  for (i in incr) {
    polygon(c(x$lt[i],x$lt[i],x$ut[i],x$ut[i]),c(F1[i],F1[i+1],F1[i+1],F1[i]),col="black")
  }

}


miscICfitting <- function(data,x,afn,bfn,est.e=FALSE,print.level=2,fullplik=FALSE,incrm=1e-5,stops=NULL) {
  #data should have columns called
  #state (0/1 indicator), time, subject.
  if (is.null(stops)) stops<-list(low = rep(-Inf,length(x)), high = rep(Inf,length(x)))
  N <-length(unique(data$subject))
  #Need to recode subject numbers so they are sequential
  data$subject <- match(data$subject,sort(unique(data$subject)))
  data <- data[order(data$time),]
  allsubs <- c(data$subject,0)
  alltimes <- c(data$time,Inf)
  allstates <- c(data$state,1)
  maxsupportu<-c(unique(alltimes))
  maxsupportl<-c(0,maxsupportu[1:(length(maxsupportu)-1)])
  n1s<-tapply(allstates,alltimes,function(x) sum(x==1))
  n0s<-tapply(allstates,alltimes,function(x) sum(x==0))
  pn1s <- c(1,n1s[1:(length(n1s)-1)])
  pn0s <- c(1,n0s[1:(length(n0s)-1)])
  includs0 <- which(n1s>0 & pn0s>0)
  includs<-apply(array(maxsupportu[includs0],c(length(includs0),1)),1,function(x) min(which(x==alltimes)))
  if (est.e==FALSE) {
    out <- computeF_gen(x,N=N,allsubs=allsubs,alltimes=alltimes,allstates=allstates,includs=includs,afn=afn,bfn=bfn,fullplik=fullplik)
    attr(out,"lt")<-maxsupportl[includs0]
    attr(out,"ut")<-maxsupportu[includs0]
  }else{
    #Perform Newton-Raphson algorithm...
    it <- 1
    lik <- computeF_gen(x,ind.out=TRUE,N=N,allsubs=allsubs,alltimes=alltimes,allstates=allstates,includs=includs,afn=afn,bfn=bfn)
    converged<-FALSE
    while (!converged) {
      if (any(x < stops$low)) {
        out <- x
        warning("Algorithm terminated due to a large negative parameter value. Probable boundary solution")
        attr(out,"converge")<-FALSE
        return(out)
      }
      if (any(x > stops$high)) {
        out <- x
        warning("Algorithm terminated due to a large positive parameter value. Probable boundary solution")
        attr(out,"converge")<-FALSE
        return(out)
      }
      g <- array(0,c(N,length(x)))
      for (i in 1:length(x)) g[,i] <- (computeF_gen(addi(x,i,incrm),ind.out=TRUE,N=N,allsubs=allsubs,alltimes=alltimes,allstates=allstates,includs=includs,afn=afn,bfn=bfn) - lik)/incrm
      if (length(x) >1) {
        h <- array(apply(apply(g,1,function(x) x%*%t(x)),1,sum),c(length(x),length(x)))
      }else{
        h <- matrix(sum(g^2),1,1)
      }
      if (det(h) < 1e-5) {
        out <- x
        attr(out,"converge")<-FALSE
        return(out)
      }
      H <- solve(h)
      G <- apply(g,2,sum)
      #print(H)
      if (print.level>=2) {
       cat(paste("\nGradient values:",paste(round(G,4),collapse=" "),sep=" "))
      }
      xnew <- x - G%*%H
      liknew <- computeF_gen(xnew,ind.out=TRUE,N=N,allsubs=allsubs,alltimes=alltimes,allstates=allstates,includs=includs,afn=afn,bfn=bfn)
      if (sum(lik) - sum(liknew) > 1e-5 ) {
        lik <- liknew
        if (print.level>=1) cat(paste("\nIteration",it," Likelihood",round(sum(lik),4)))
        x <- xnew
        if (print.level>=2) cat(paste("\nCurrent parameter values: ",paste(round(x,4),collapse=" ")))
      }else{
        #Check the gradient
        if (max(abs(G))>0.1 | min(eigen(H)$values) < 0) {
          x0 <- x
          dir <- -G%*%H
          if (print.level>=2) cat("\nPerform line search step")
          linesearch <- function(x,dir,x0) sum(computeF_gen(x0 + x*dir,ind.out=TRUE,N=N,allsubs=allsubs,alltimes=alltimes,allstates=allstates,includs=includs,afn=afn,bfn=bfn))
          lse<-optimize(linesearch,c(0,1),dir=dir,x0=x0)
          if (lse$objective < sum(lik)) {
            liknew <- computeF_gen(x0 + dir*lse$minimum,ind.out=TRUE,N=N,allsubs=allsubs,alltimes=alltimes,allstates=allstates,includs=includs,afn=afn,bfn=bfn)
            x <- x0 + dir*lse$minimum
            if (print.level>=2) cat(paste("\nCurrent parameter values: ",paste(round(x,4),collapse=" ")))
            lik <- liknew
          }else{
            stop("Algorithm failed to converge to a stationary point")
          }
        }else{
          out <- lik
          attr(out,"x")<-x
          attr(out,"lt")<-maxsupportl[includs0]
          attr(out,"ut")<-maxsupportu[includs0]
          attr(out,"converge")<-TRUE
          attr(out,"H")<-H
          attr(out,"grad")<-G
          converged<-TRUE
        }
      }
    it <- it+1
    }
  }
  out
}



computeF_gen <- function(x,ind.out=FALSE,N,allsubs,alltimes,allstates,includs,afn,bfn,fullplik=FALSE) {
  M<-length(includs)
  if (fullplik) ind.out<-fullplik
  plik <- array(0,c(M,N))


  mtime <- max(alltimes[alltimes<Inf])
  bvec <- bfn(x,pmin(mtime,alltimes))
  avec <- afn(x,pmin(mtime,alltimes))
  if (any(bvec<=0) | any(avec<=0) | any(avec + bvec >= 1)) stop("Boundary values of error probabilities detected")

  for (i in 1:N) { #NB requires subjects to be labelled 1:N in allsubs!
    plik[,i] <- bcumsum(log(1-bvec) * (allsubs==i & allstates==1))[includs] + bcumsum(log(bvec)*(allsubs==i & allstates==0))[includs]  + cumsumA(log(1-avec)*(allsubs==i & allstates==0))[includs] + cumsumA(log(avec)*(allsubs==i & allstates==1))[includs]
  }
  lc <- apply(plik,1,sum)
  fs<-rep(0,length(includs))
  fs[lc==max(lc)]<-1
  Fs <- cumsum(fs)
  p<-rep(0,length(includs))
  p[lc==max(lc)]<-1
  set <-which(lc==max(lc))
  lG <- log(apply(plik,2,function(x) sum(p*exp(x))))
  old <- sum(lG)
  conv<-FALSE
  while (!conv) {
    DD <- apply(plik,1,function(x) sum(exp(x)/exp(lG))) - N
    if (max(DD)<1e-8) conv<-TRUE
    add <- locmax(DD)
    set <- unique(c(set,add))
    S <- exp(plik[set,])/exp(array(rep(lG,each=length(set)),c(length(set),N)))
    pnew <- nnlse(a=t(S),b=rep(2,N))$x
    pnew <- pnew/sum(pnew)
    p <- rep(0,length(includs))
    p[set] <- pnew
    lG <- log(apply(plik,2,function(x) sum(p*exp(x))))
    curr <- sum(lG)
    old <- curr
    set <- which(p>1e-10)
  }
  if (ind.out) {
    out<--lG
  }else{
    out<--sum(lG)
  }
  if (fullplik) attr(out,"plik")<-plik
  attr(out,"DD")<-DD
  attr(out,"F")<-cumsum(p)
  attr(out,"f")<-p
  out
}

anova.miscIC <- function(object, ...) {
  dotargs <- list(...)
  named <- if (is.null(names(dotargs)))
    rep_len(FALSE, length(dotargs)) else (names(dotargs) != "")
  if(any(named)) {
    warning("the following arguments to 'anova.miscIC' are invalid and dropped: ",
            paste(deparse(dotargs[named]), collapse=", "))
  }
  dotargs <- dotargs[!named]
  is.miscIC <- vapply(dotargs,function(x) inherits(x,"miscIC"), NA)
  dotargs <- dotargs[is.miscIC]
  if (length(dotargs)==0) stop("More than one miscIC fitted object must be supplied.")
  if (length(dotargs)>=1) {
    deviances <- c(object$deviance, sapply(dotargs,function(x) x$deviance))
    dev_difference <- sapply(dotargs,function(x) (x$deviance - object$deviance))
    par_difference <- sapply(dotargs,function(x) (x$npar - object$npar))
    dev_difference <- -dev_difference * sign(par_difference)
    par_difference <- abs(par_difference)
    params <- c(object$npar,sapply(dotargs,function(x) x$npar ))
    output <- data.frame("Dev"=deviances,"npar"=params,"Lik Ratio"=c(NA,dev_difference),"Df"=c(NA,par_difference),"p val"=c(NA,1-pchisq(dev_difference,par_difference)))
    row.names(output)<-paste("Model",1:length(deviances),sep=" ")
    class(output) <- c("anova","data.frame")
    return(output)
  }
}
