# A1 round two

Changing the six aliases to ordinary `def` produced the expected regular definition
hint, but the historical consumer failed before kernel conversion: `IsLeftDerivedFunctor`
instance synthesis failed and Lean then reported `No goals to be solved`. This row has
no valid conversion timing. The failure was measured with a targeted module build.
