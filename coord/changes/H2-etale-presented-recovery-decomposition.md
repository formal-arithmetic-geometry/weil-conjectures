# Étale presentation recovery decomposition

Status: submitted for independent review and global-build verification.

The full recovery theorem and EtalePresentedRecovery retain their signatures and
all fields. The five coordinate definitions move verbatim to the new module
Sheaf.AlgebraicGeometry.EtalePresentedRecoveryData, publicly imported by the item.
The former public imports remain public through that module. No existing
WeilConjectures file is changed. New partial structures package only the local
cokernel step and the subsequent descent/gluing step; their two existence
statements are separate proof obligations.

The item now constructs the restriction isomorphism by composing the unit with
restriction of the glued isomorphism. The normalized unit is proved invertible
objectwise. The adjunction Hom equivalence proves the counit invertible, and the
right triangle identity proves the exact open-section normalization.

Consumers: a source search of lean/ found zero direct Lean importers of the
item, and no other occurrence of its five coordinate names or structure.
All DAG parents continue to cite the original theorem with its unchanged type;
none is withdrawn. The new module reexports the moved definitions under their
original fully qualified names. There are no forced adaptations.
