\name{simulated_data}
\alias{simulated_data}
\docType{data}
\title{
Simulated example dataset of misclassified interval censored time-to-event data
}
\description{
The observed status, observation time and subject identifier for 100 simulated subjects. This is the same dataset as used in Figure 2 of Titman (2017).
}
\usage{data("simulated_data")}
\format{
  A data frame with 908 observations on the following 3 variables.
  \describe{
    \item{\code{state}}{Binary observed status at the observation time}
    \item{\code{time}}{Time of the observation}
      \item{\code{subject}}{Subject identifier corresponding to the observation}
  }
}
\references{
 Titman AC. Non-parametric maximum likelihood estimation of interval-censored failure time data subject to misclassification \emph{Statistics and Computing}, 2017. 27, 1585-1593.
}
\keyword{datasets}
