# ProjectionFormulaField classification

Case ID: `AlgebraicGeometry.ProEtale.CondensedRing.ProjectionFormulaField`; Lean 4.35.0, built dependencies, revision `1ef1fddac73e`.

The original-name setup replay is successful (150.23 user CPU s). The synchronous profile attributes 124 s to elaboration, 1.94 s to Kernel type checking, and 918 ms to typeclass inference. The main source site is the pair of localizing projection/base-change constructions in `projectionFormula_baseChange_localizingBoundedConstructible_continuousMapRingObj` and its `padicAlgCl` analogue. The earlier missing-instance errors were produced only by a renamed copy.

Phase: **elaboration**. The shared `homotopyCounit_naturality` trace control emits many small instance-oriented `Meta.isDefEq` comparisons and reaches the heartbeat/timeout before identifying a dominant conversion. No A–F Kernel label is assigned. Confidence in phase and declaration is strong; inner Meta mechanism is **unclassified / open**.

