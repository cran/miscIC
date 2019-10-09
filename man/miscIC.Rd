\name{miscIC}
\alias{miscIC}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{Nonparametric Maximum Likelihood Estimation of the survivor function for interval censored time-to-event data
}
\description{
Estimate the survivor function for interval censored time-to-event data subject to misclassification using nonparametric maximum likelihood estimation. Misclassification probabilities can either be specified as fixed or estimated. Models with time dependent misclassification may also be fitted through user supplied functions.
}
\usage{
miscIC(formula, data, subject, initial, est.e, afn=NULL, bfn=NULL,print.level=2,...)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
    \item{formula}{
  A formula identifying the status and time variables within \code{data}, for instance \code{status ~ time} would imply the variables are \code{status} and \code{time}, respectively.
  }
  \item{data}{
data frame containing the observed status (0 or 1), observation times (>0), and subject identifiers. All subjects assumed to be event free at time 0.
}
\item{subject}{
Name of the subject identifier variable within the \code{data} data frame.
}
  \item{initial}{Vector of initial parameter values. If \code{est.e=FALSE} these are the fixed values for the misclassification probabilities. If \code{afn} and \code{bfn} are not supplied the parameters should be on the natural scale (i.e. a probability strictly between 0 and 1). If \code{afn} and \code{bfn} are supplied then the parameters should be on an unconstrained scale.}
  \item{est.e}{Logical to indicate whether the misclassification probability parameters are to be estimated or not. If \code{FALSE} then the initial values will be taken as fixed. Note that the misclassification probabilities can only be estimated if observations continue after the first observed failure.}
  \item{afn}{Optional user supplied function for the probability of a false positive observation. The function should have two arguments; the first corresponding to the model parameters and the second to time. }
    \item{bfn}{Optional user supplied function for the probability of a false negative observation. The function should have two arguments; the first corresponding to the model parameters and the second to time. }
    \item{print.level}{Level of detail in optimization algorithm. Either 0, 1 or 2. 0 = No printing, 1 = Print likelihood values at each iterations. 2 = Print parameter, gradient and likelihood values at each iteration. Note that printing only refers to the Newton-Raphson algorithm for the misclassification probabilities.}
    \item{...}{
 Other control parameters for the fitting algorithm.
}
  }

\details{
The function uses the methodology developing in Titman (2017) to find the NPMLE of the survivor function for interval censored survival data that are subject to misclassification. For fixed or known misclassification probabilities, the NPMLE is found using an adaptation of the algorithm of Wang (2007) for finding the NPMLE of a mixing distribution.

   If a subject continues to be observed after the first observed failure (observed value 1) then it is possible to estimate the misclassification probabilities from the observed data itself. In this case the profile likelihood via a Newton-Raphson algorithm where the derivatives are computed using finite differences.
}
\value{
Returns an object of class \code{miscIC} containing model output data such as the estimated parameters, maximized likelihood value, variance-covariance matrix etc. The object can be used with \code{print}, \code{plot} and \code{anova}.
}

\examples{
### Analysis of the example dataset
### Fixed error probabilities
fit_fixed <- miscIC(state~time,data=simulated_data,subject=subject,initial=c(0.05,0.1),est.e=FALSE)
}


\author{Andrew Titman \email{a.titman@lancaster.ac.uk}}


\references{
 Titman AC. Non-parametric maximum likelihood estimation of interval-censored failure time data subject to misclassification \emph{Statistics and Computing}, 2017. 27, 1585-1593.

 Wang Y. On fast computation of the non-parametric maximum likelihood estimate of a mixing distribution. \emph{Journal of the Royal Statistical Society, Series B}. 2007; 69. 185-198.

}

\note{
The current implementation of the function only covers the case in which there are both false negatives and false positives within the data. If no misclassification is present then the estimates can be calculated using other packages such as \code{Interval} or \code{ICens}. If one type of misclassification is possible, but not the other, an approximate solution would be to fix that value arbitrarily close to 0. However, the regions of support will be incorrect (generally too narrow).
}

% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
\keyword{survival}% use one of  RShowDoc("KEYWORDS")
\keyword{nonparametric}
\keyword{models}% __ONLY ONE__ keyword per line
