## What changed

Added direct proofs when either open contains the other (including empty-open cases).
Replaced the hole in `AlgebraicGeometry.perfect_hom_continuity_union` by the five-lemma
argument and the complete filtered-colimit element chase. Its signature and public imports
are unchanged. The original proof-dependency imports are replaced by the new comparison
module, Mathlib's five lemma, and Mathlib's filtered set colimit lemmas.

Added `Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisComparison` with one statement:
`AlgebraicGeometry.perfect_hom_mayerVietoris_comparison`. It isolates construction of the
exact five-term diagram and its four local comparison isomorphisms. It pins the central
source presentation to both `perfectStageMap` and `perfectLimitMap`; it does not assert
central invertibility or either eventual-stage clause. The main theorem proves these using
Mathlib and the supplied equations. This is a decomposition, not a net hole reduction.
No definitions, existing interfaces, targets, or modules held by other groups were changed.

The source read was Stacks Tag 09RE and its cited Tag 08BW. The unit record
`sk-thm-picard-semicon` has no realized nodes; no unit statement or step is bypassed.

Validation: the dependency `PerfectHomContinuityOn` is now available in the sandbox and all three modules compile together. The official dry run `deliver3.py H4 Sheaf.AlgebraicGeometry.PerfectHomContinuityUnion --no-push` printed OK.

Earlier retries had failed because the global green build lacked the dependency object.

The proof uses qualified `congr_hom` as
`ConcreteCategory.congr_hom`, fixing the unknown-identifier error introduced when the
incidental `open ConcreteCategory` was removed. The dependency copy is identical to the landed interface module and is present only so the isolated sandbox build can resolve the import. No tool was changed.

## Proved and sorry left

The original hole in `AlgebraicGeometry.perfect_hom_continuity_union`
(node `lem-pc-perfect-hom-continuity-union`) is replaced by a complete proof in the candidate;
its algebraic argument compiles in the sandbox build. The official dry run passed.

One hole added: `AlgebraicGeometry.perfect_hom_mayerVietoris_comparison`
(node `lem-pc-perfect-hom-mayer-vietoris-comparison`). Its proof is exactly `by sorry`.
No other holes were added. Net holes: zero change after this decomposition.

## No longer needed

Removed these direct imports from the main module:
`Sheaf.AlgebraicGeometry.PerfectImpliesQCoh`,
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`,
`Sheaf.AlgebraicGeometry.DerivedAdjoint`,
`Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle`, and
`Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial`.
They remain needed by the new diagram-construction node and its module; no module is
claimed pruned from the target closure. The corresponding original proof dependencies
now belong to the comparison node, rather than being direct dependencies of the parent.
The parent's proof also directly unfolds `def-pc-perfect-hom-continuity-on`.
The complete list of old proof dependencies removed from the parent's direct dependency
list is `def-pc-perfect-complex`, `lem-pc-affine-derived-pullback-tensor-tilde`,
`lem-pc-derived-mayer-vietoris-functorial`, `lem-pc-derived-mayer-vietoris-triangle`,
`lem-pc-perfect-hom-transport`, `lem-pc-ringed-spaces-derived-adjoint`,
`lem-pc-ringed-spaces-derived-pullback-composition`, and `lem-sc-perfect-qcoherent`.
All remain in the new comparison node's construction plan or statement dependencies;
none is claimed removed from the target closure.

## Where the brief, the DAG or earlier work was wrong

The DAG's first two steps do not currently have a declaration exposing the exact Hom
comparison diagram with the prescribed central transport. A distinguished triangle alone
cannot supply its compatibility with transition maps and boundary maps. The new statement
makes this missing geometric construction explicit, with stage and limit pinning equations.
The existing triangle, direct-image functoriality, adjunction, and restriction statements
are retained in that construction's plan; their holes are not an obstacle to using them.

The brief's compiled-library assumption fails for the recently landed split. The local
sync is current, but the server's last green build is 2026-10-13T09:56:06Z, before the
09:59:35 landing introducing PerfectHomContinuityOn. The latest global build log reports
failures in unrelated modules `Sheaf.Algebra.Homology.HomTensorDifferentialSummand` and
`Sheaf.Algebra.Homology.SingleSupportTorAcyclicTensor`. These are maintainer work, not
forced adaptations of this delivery. No tools were changed or circumvented.

## New nodes

`lem-pc-perfect-hom-mayer-vietoris-comparison`, in
`dag/nodes/sec-picard-framework/lem-pc-perfect-hom-mayer-vietoris-comparison.json`, is the
exact comparison-construction step preceding the five lemma in Tag 09RE. Its Lean module
is `Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisComparison`. The five-term diagram and
its colimit presentation are existential proof data, never data of a definition. Universe
`max u w` permits the filtered colimit even when the index universe exceeds the Hom
universe. The proof plan covers empty opens and empty schemes, zero Hom groups, a singleton
index, and non-antisymmetric preorders. The tail is nonempty because it contains i; no
extra nonemptiness hypothesis or cofinality axiom is needed.

LeanSearch returned Internal Server Error; LeanFinder returned derived-category fraction
lemmas and AB5 infrastructure, not this comparison; grep found Mathlib's five lemma and
ordinary sheaf-cohomology Mayer--Vietoris, not the pinned scheme-derived Hom diagram. The
library, the DAG and blueprint search found no existing statement exposing this data.
No change record is needed because every existing signature and visibility is unchanged.


## Second reading by H4

1. Compared every existing delivered module with the repository using diff. The union
   theorem signature is byte-for-byte identical, its public imports are unchanged, and
   PerfectHomContinuityOn is an identical dependency copy. No definition or target changed.
   Restored the original union theorem docstring; the decomposition explanation is here.
2. Reviewed the five lemma and both element chases. Directedness gives representatives
   beyond every requested stage; cocone naturality pins their limit images. Injectivity
   and Mathlib's equality criterion give eventual equality, propagated by the functor law.
   All modules compile. The only new direct sorry is the named comparison theorem, with
   its source, complete proof docstring and matching node. No forbidden declaration or
   hollow definition was found. Explicit `#print axioms` scratch probes for both theorems show only propext,
   Classical.choice, Quot.sound and sorryAx (the comparison is still open).
3. The new statement isolates the construction of the exact geometric diagram, without
   assuming its central isomorphism or either eventual-stage conclusion. It is a genuine
   reduction of the original argument, followed by the actual five-lemma and colimit proof,
   and is recorded as a decomposition (one original hole closed, one new hole added).
   Read Stacks Tags 09RE and 08BW and the existing derived triangle, direct-image comparison
   and canonical transport declarations. Checked empty opens/schemes, zero Hom groups,
   equal or nested opens, singleton indices and non-antisymmetric directed preorders.
   The tail always contains i; universe max u w accommodates both index and Hom sizes.
   Existential diagram data is eliminated only in a Prop proof and never chosen to define
   an object. A second LeanFinder search for additive Hom exact sequences under open covers
   returned ordinary sheaf Mayer--Vietoris lemmas, not this pinned derived comparison;
   Loogle and local grep likewise found no replacement. This substantial geometric hole
   cannot be closed by a short application of the existing declarations.
4. The parent takes the direct nested-open cases first, then Mathlib's five lemma and
   filtered-set colimit results. Removed the new module's redundant direct triangle import
   (provided publicly by DerivedMayerVietorisFunctorial). Replaced its unnecessarily public
   Grp.Abelian import with Grp.Preadditive, which supplies the zero morphisms used by Exact.
   Construction-plan imports remain for the split theorem. Completed the list of removed
   original direct node dependencies above; no module is pruned from the target closure.
   The unit sk-thm-picard-semicon has empty realized statement/step lists; its route is kept.
5. Read both node records against the Lean declarations. The parent proof/dependency union
   matches the five-lemma and colimit chase; the new node records the geometric construction,
   canonical stage/limit pinning, sources, searches, provenance and verbatim signature.
   No changes to unit, target, statement or definition records were needed.

Second reading changed only import cleanup, restoration of the existing docstring, and
report precision. The compiled proof and the split statement were retained.
