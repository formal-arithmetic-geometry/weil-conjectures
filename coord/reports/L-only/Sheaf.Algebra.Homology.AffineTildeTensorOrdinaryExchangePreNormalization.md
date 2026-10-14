# AffineTildeTensorOrdinaryExchangePreNormalization

Completed `AlgebraicGeometry.affineTildeTensorOrdinaryExchange_preNormalization` with its original statement, hypotheses, and docstring unchanged. No `sorry` remains in either delivered Lean file.

The ordinary chain calculation is recorded as `affineTildeTensorOrdinaryExchange_preNormalization_chain`, with a matching DAG node. Its proof transposes the ordinary base-change map through the tensor-pullback adjunction along g. The tilde adjunction reduces equality to global unit sections. The existing normalized tensor/tilde and affine pushforward comparisons preserve these sections and reduce the assertion to `hk i 1 q`. Cancellation of the comparison isomorphisms and complex extensionality give the chain equality. This completes the chain route found in the earlier U4 sandbox and the parent route notes.

The remaining proof identifies homotopy exchange with the quotient chain map, localizes the chain equality, and applies naturality of the right-derived pushforward unit to the inverse tensor/tilde comparison. No invertibility of the derived pullback counit is added. Zero rings and zero complexes require no exceptional argument.

`affineTildePushforwardComplexMap` is moved to the chain module and publicly reexported by the original module. Its public signature, body, and docstring are unchanged. The original public pre-normalization theorem statement was compared verbatim with the repository version. Introducing all its let-bound definitions into the proof caused expensive kernel checks; applying the general transport theorem directly keeps the final module within the file limit.

Validation on the server, one file at a time with `tools/lean_file.sh` and the private `elite-prenorm` output mirror:

- Chain module: compiled in 48.9 seconds.
- Final pre-normalization module: compiled in 36.6 seconds.
- Axiom scratch: compiled in 1.8 seconds; `#print axioms` for the pushforward map and both chain/derived theorems lists exactly `propext`, `Classical.choice`, and `Quot.sound`.
- Direct importer `AffineTildeTensorOrdinaryExchange`: compiled in 41.6 seconds.

No target statement or mathematical definition changed. No imports were pruned; the public import surface is preserved. The next global build is monitored after the merge-locked commit.
