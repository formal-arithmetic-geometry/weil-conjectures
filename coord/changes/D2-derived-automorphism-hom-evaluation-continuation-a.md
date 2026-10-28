# D2: ordinary finite restriction and system Hom transport

The item module retains all declaration signatures, public imports, instances,
attributes and definitions. Two theorem proofs replace existing holes; no new
statements or holes are introduced. Unused private proof imports are removed;
private imports for the finite comparison, sequence pullback and categorical
Hom calculation are added.

The shared node `lem-pod-derived-automorphism-hom-evaluation` also describes
companion modules. Its proof steps 1 and 5 and proof dependencies are updated
to record these two proofs. Its statement, statement dependencies and Lean
attachment are unchanged; the remaining companion proofs and their dependencies
are retained. No other existing Lean module is changed, and no consumer
adaptation is required because the public interface is preserved.
