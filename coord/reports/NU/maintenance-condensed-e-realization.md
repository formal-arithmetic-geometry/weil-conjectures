# Maintenance: lem-weil-pbc-condensed-e-realization

2026-10-16, dispatcher group NU, stage 2.

The repeated failures were an incomplete published prerequisite interface, not a
compiler crash or a failure-count stopping rule. Batch 31a287752f introduced the
scheme-universe `Profinite.continuousCoefficientRingObj` and rebound
`def-weil-pbc-condensed-e-module-category` to it, but omitted the commutativity
instance present for the older Type 0 `Profinite.continuousMapRingObj`. The
archived bounded constructible operations and exchange require that instance.
The worker correctly obeyed its bottom-up brief and named this unusable dependency.

The server compiler prefers live published artifacts for every module also
present in live. Consequently an edit to the frozen side copy of
`ContinuousCoefficientUniverse.lean` would not fix an ordinary downstream compile.
The repair is the side-only `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`:
it publicly imports the original coefficient construction and MorphismDefs, and
proves the missing instance by `Sheaf.isCommMonObj_sheafCompose_obj` and pointwise
`mul_comm`, for arbitrary commutative topological rings in `Type u`.
The owning dependency's Lean record now points to that complete interface.
The binding is also promoted to the shared live DAG so periodic sync cannot undo it.
Live Lean and its compiled artifacts are untouched.

Validation used `tools/lean_file.sh`, one file at a time, each under 60 seconds.
The original saved check reproduced the missing instance. The new module compiled
in 1.7 seconds. A separate consumer imported only the new module and checked
MonObj and IsCommMonObj both at the point and after pullback to a scheme,
BoundedConstructible, restricted pullback and pushforward, their adjunction,
pullback composition and the specified boundedConstructibleBaseChange. This
consumer compiled in 2.7 seconds (its imported companion separately in 1.7 seconds).
The new instance's axiom print contains only propext, Classical.choice, Quot.sound.
The saved worker diagnostic also lacked `open scoped CategoryTheory.Obj`; that
scope is needed to synthesize the functor-transported ring-object instances.

Next worker: import `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` and
`open scoped CategoryTheory.Obj`. Use the same original
`Profinite.continuousCoefficientRingObj E` in the realization statement. The
remaining realization mathematics is your existing stage-2 task. The old BLOCKED
note predates this fix; rerun the checks with the repaired import and scope.

Existing node files have timestamped .bak copies; the new module also has a .bak.
No mathematical statement, original definition, dispatcher counter, claim or
unrelated working-tree file was changed, and no foreign process was stopped.
