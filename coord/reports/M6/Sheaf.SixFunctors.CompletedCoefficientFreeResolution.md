## What changed

Replaced the hole in
`WeilConjectures.CompletedCoefficientFree.completed_coefficient_free_resolution`
by the coefficient short exact sequence, bounded-flat K-flatness, an ordinary
finite-free quotient limit, the epimorphic Roos short exact sequence, and the
normalized derived scalar-extension adjunction.

The existing public definitions and theorem statement are unchanged. New private
helpers track the actual quotient projection and adjunction unit. The new module
`Sheaf.Paper.CompletedFreeCellOrdinaryLimit` constructs an explicit cone, proves
its compatibility, and calculates its ordinary finite-free limit. The DAG records
this route. No source-library declaration or definition is changed.
The proof-local instance additions and the unchanged downstream consumer are
documented in `coord/changes/M6-completed-coefficient-proof-instances.md`.
The sole downstream consumer, `Sheaf.Paper.SupportedLatticeHomReductionTower`,
compiles unchanged against the delivery in 9.4 seconds.

## Proved and sorry left

Closed one existing hole:
`WeilConjectures.CompletedCoefficientFree.completed_coefficient_free_resolution`.
The new statements `WeilConjectures.completedFreeCellCone_compatibility` and
`WeilConjectures.completedFreeCell_ordinaryLimit` are also proved.

Holes closed: 1. Holes added: 0. No `sorry` remains in either delivered module,
and no unproved statement was split off.

The complete sandbox compiles cleanly with no warnings: the ordinary-limit module
in 20.4 seconds and the item module in 50.8 seconds. The proof uses the existing
Mathlib sheafification-counit instance and scopes its coefficient-universe
sheafification witness to the tensor calculation.

## No longer needed

The proof does not use the old generic constant-algebra detour through
`lem-weil-l-adic-extension-integers-dvr`,
`lem-weil-pbc-constant-module-section-properties`, or
`lem-weil-pbc-completed-constant-sheaf-reduction`. Instead it uses the published
independent-universe completed-scalar regularity and projection-divisibility
lemmas directly.

`lem-pc-bounded-above-flat-kflat-site` is replaced by the independent-coefficient
bounded-flat criterion `lem-weil-pbc-independent-bounded-flat-kflat`.

`lem-weil-pbc-total-tensor-homotopy-cone-signs` and
`lem-pc-tensor-mapping-cone-iso` are unnecessary: a flat-term K-flat resolution
allows tensoring the coefficient short exact sequence degreewise, and the derived
short-exact-sequence triangle already has the required scalar and unit maps.
Removed proof imports:
`Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`,
`Sheaf.Paper.CompletedConstantSheafReduction`,
`Sheaf.Paper.ConstantModuleSectionProperties`,
`Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`, and
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`.
All existing public imports remain unchanged.

The obsolete `tool_uses` approvals for the six nodes named above were removed;
all retained approvals stay in their original order. No approval was added or replaced.
No upstream declaration is removed. These are local dependency removals only;
other target routes may still use the named nodes.

## Where the brief, the DAG or earlier work was wrong

The original plan uses several interfaces fixing the coefficient universe in
terms of the scheme universe. The assigned statement has independent universes.
The replacement proof uses the existing independent-coefficient flatness,
resolution, scalar regularity, and derived-adjunction interfaces throughout.

The K-flat resolution interface supplies categorical termwise flatness. The
proof converts it to site flatness through the canonical tensor comparison.

## New nodes

`lem-sf-completed-free-cell-ordinary-limit` records only the ordinary quotient
limit and degreewise epimorphism calculation. It contains no derived completeness
or distinguished-triangle assertion. Scalar extension of the unit is compared
with the quotient unit by the existing adjunction; finite powers and the single
complex functor then preserve the coefficient limit. Rank zero and arbitrary
integer degrees are included. This node is proved in the delivery and introduces
no new hole. The local proof instances have change record
`coord/changes/M6-completed-coefficient-proof-instances.md`; existing definitions
and signatures are unchanged.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
