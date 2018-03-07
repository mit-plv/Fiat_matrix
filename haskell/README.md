The `Kalman` module should be generated by running the Coq file
`KalmanExtractionHaskell.v`.

You will need to manually add the line
```haskell
import KalmanAxioms
```
to the generated `Kalman.hs` file at the appropriate place.

The resulting Haskell Stack project should then build successfully by invoking
the command `stack build`.