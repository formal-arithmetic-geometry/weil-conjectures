## What changed

Proved the direct-image coefficient restriction comparison, constructed the direct-image functor on strict systems, and proved the local mate equivalence. `SemilinearOrdinaryDirectRestrictions` contains the proved comparison; `SemilinearOrdinaryDirectSystemCoreData` contains reassembly and is publicly reexported by the item module. `SemilinearOrdinaryDirectSystemMate` contains and reexports the completed mate calculation through the item module. The original `OrdinaryDirectSystem`, `OrdinaryDirectSystemCore`, `OrdinaryDirectSystemHomData`, and their final existence statements are unchanged.

The former mate assertion for arbitrary component data was false. Added `OrdinaryDirectSystemCoreNormalized`, strengthened the component construction to supply it, and used it as an explicit hypothesis of the repaired mate theorem. This repairs the missing invariant rather than assuming that arbitrary levelwise isomorphisms determine horizontal maps. See `coord/changes/M2-ordinary-direct-system-normalization.md`.

The comparison is constructed by transposing the restricted counit along the supplied normalized adjunctions. Its underlying map is invertible, hence it is an isomorphism. This gives linear horizontal maps without assuming any additional module structure or choosing data from an unproved existence theorem. The existing strict-system/sequence-site equivalence reassembles them. Every helper is proved.

## Proved and sorry left

Initial holes: `ordinaryDirectSystem_core_data_exists` and `ordinaryDirectSystem_core_transition_mate_exists`.

Closed the construction hole with the stronger normalization conclusion, and proved the corrected mate theorem. The original unnormalized universal mate assertion is false and is not claimed proved. Added zero holes; split off zero unproved statements. There are no `sorry` declarations in any of the four delivered modules. The new `directRestrictions_exists` theorem is fully proved.

A clean server compile passed for all four proof modules: restriction comparison 19.8 s, component reassembly 52.3 s, local mate 21.2 s, and the item module 51.0 s. The unchanged direct importer `Sheaf.Paper.GeometricOrdinaryRealization` also passed in 21.5 s; its byte-identical temporary sandbox copy was removed. Every compile was within 60 s and printed no warning. The delivery tool performs the final axiom checks.

## No longer needed

No module is withdrawn, and no preexisting public import is removed. The component proof uses the existing inverse-image scalar-restriction comparison, source strict-system functor, and sequence-site equivalence. It does not need a new module-direct-image existence axiom or an additional module structure transported from unspecified data.

Removed `lem-coef-ordinary-inverse-system` and `lem-coef-normalized-module-adjunction` from the component node's proof dependencies: their data and normalization are already hypotheses; the construction does not apply their existence theorems. The inverse-system node remains needed by the mate proof and as a statement dependency. The normalized-module-adjunction node remains a statement dependency describing the supplied normalization, but neither the restriction comparison nor the mate calculation invokes its existence theorem. The core node uses only the proved component existence and mate nodes. No unit-level statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED, repaired: the E1 split discarded the horizontal invariant that E4 had correctly identified as essential. On the one-object site with a constant nonzero ring, take identity inverse-image functors and identity adjunctions. Define D.push to keep every level and every component map, but replace all strict transitions between different levels by zero. Its levelwise components and section identifications are identities, so it satisfies the old CoreData structure. For constant towers with identity transitions and the identity component maps at 0 and 1, the original square commutes, whereas the transposed square for D would assert zero equals identity. Thus the old mate statement cannot follow from component data alone.

The repaired construction explicitly supplies horizontal normalization, and the mate theorem uses exactly that invariant. The existing core and final theorem receive it internally, so their hypotheses and conclusions are preserved. The source-library boundary is respected: no file under WeilConjectures is edited.

The old stage document forbids splitting slow files; the current worker brief explicitly permits splitting after improving slow definitions. Concrete rewrite searches were replaced by abstract categorical calculations, and transition definitions are kept locally irreducible after their API lemmas. The separate modules then keep individual compilation within the required limit.

## New nodes

`lem-coef-ordinary-direct-restriction-comparison`: the fully proved normalized isomorphism between scalar restriction followed by V and V followed by scalar restriction. It is strictly the coefficient-restriction part of reassembly, not a restatement of either initial obligation. Its module is `Sheaf.Paper.SemilinearOrdinaryDirectRestrictions`; the existing component node depends on it. The existing component node now attaches to `SemilinearOrdinaryDirectSystemCoreData`. No new unproved statement is introduced.

Change record: `coord/changes/M2-ordinary-direct-system-normalization.md`.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
