## What changed

Proved WeilConjectures.PointDerivedHom.point_derived_hom_evaluation from the named
point-extension K-flatness, normalized Hom-adjunction and evaluation lemmas, without
changing its signature. The proof handles both actual coefficient models.

PointHomComplexAdjunction constructs the product of the additive adjunction
bijections, proves R-linearity from the explicit generator formula, and checks the
Hom differential. The main module proves naturality on generators, preservation of
K-injectivity and the coefficient resolution, and invertibility of the prescribed
derivedModelMap. The derived isomorphism is its inverse followed by Q.mapIso q.
ModuleHomSignedEvaluation constructs ordinary module evaluation and proves its
signed differential identity. PointSheafHomMaps constructs sheaf evaluation through
the tensor/sheafification adjunction and the sections-tensor map using its natural
bilinear components and the existing lax-total chain-map construction.
PointTensorHomEvaluation proves the evaluation square on pure tensors and total
summands.

The unchanged concrete definitions now live in PointDerivedHomModels, publicly
reexported by the original module, so the new lemmas can depend on them without an
import cycle. Compared the relocated implementation after stripping comments: it
is identical; the main theorem signature is also verbatim identical. No upstream
WeilConjectures file changes and no target changes.

Validation: all seven sandbox modules compiled together with lcompile.py --all,
without errors or warnings. PointSheafHomMaps took 50.8 seconds and the main module
took 30.1 seconds, within the existing 60-second per-file limit.

## Proved and sorry left

Closed the original hole:

- WeilConjectures.PointDerivedHom.point_derived_hom_evaluation
  (lem-pod-point-derived-hom-evaluation).

Also proved:

- WeilConjectures.PointDerivedHom.point_hom_complex_adjunction
  (lem-pod-point-hom-complex-adjunction).
- CochainComplex.module_hom_signed_evaluation
  (lem-pod-module-hom-signed-evaluation).
- WeilConjectures.PointDerivedHom.point_sheaf_hom_maps
  (lem-pod-point-sheaf-hom-maps).
- WeilConjectures.PointDerivedHom.point_tensor_hom_evaluation
  (lem-pod-point-tensor-hom-evaluation).

Added and retained named holes:

- WeilConjectures.PointDerivedHom.point_extension_kflat
  (lem-pod-point-extension-kflat), only the geometric constant inverse-image bridge
  and K-flat pullback specialization, without any Hom or evaluation conclusion.

The item has zero remaining holes; this one new hole makes this a decomposition
with net zero holes closed, rather than a net hole reduction. No private theorem
or definition contains sorry.

## No longer needed

Removed the original proof-only imports:

- WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap: replaced by the existing
  independent-universe QuasiIsoHomComplexMapOfUniverses theorem in the main proof.
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses: the main proof does not
  construct the generic derived tensor pullback.
- Mathlib.CategoryTheory.Sites.Sheafification: existing model imports supply what
  the unchanged definitions require; the main proof does not unfold sheafification.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses: needed only in the
  lower tensor constructions, not directly by the main theorem or model interface.
- WeilConjectures.Algebra.Homology.HomComplex: projection/component APIs and the
  model interface supply the Hom constructions used by the proof.
- Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal: direct chain-level
  signed evaluation replaces constructing the generic derived closed structure.
- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom: the existing model
  public imports supply the statement-level Hom interface.

WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp remains a
proof import in the main theorem, not in the model interface.

The main node no longer directly uses lem-pur-rhom-well-defined (its universe
variant is used), lem-sf-ringed-derived-closed-symmetric-monoidal, or the generic
derived tensor-pullback construction. Exactness of sections is a hypothesis here;
the point exactness theorem is not reapplied to establish it. Constant sheafification
and ringed-topos K-flat pullback remain needed by the separate extension lemma's
proof plan, so those mathematics and their modules are not claimed globally pruned.
The old top-level tool approvals are reduced to the actual direct K-injective
adjunction use, in their original order. No module is withdrawn; no unused upstream
declaration is removed, and no blueprint unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was disputed. The planned generic Hom invariance import
has a coefficient/site universe restriction, so the proof uses its existing
independent-universe version. The ordinary module Hom complex is used directly,
without presenting it as an unspecified sheaf Hom on a one-object site.

The point generator is the adjunction unit by the explicit adjunction hypothesis.
Its naturality gives the required differential/naturality formula without using the
object-and-morphism presentation of L again. The latter remains required in the
separate K-flat extension lemma. The generic constant realization theorem fixes
coefficients to the maximum site universe, while this model permits a larger
independent coefficient universe; it cannot be directly specialized to this lemma.
The sections-tensor construction uses maps into
sections of a total coproduct and never assumes sections commute with infinite sums.

## New nodes

- def-pod-point-derived-hom-models: attachment for the unchanged relocated interface.
- lem-pod-point-extension-kflat: constant inverse-image/flat-term K-flat specialization.
- lem-pod-point-hom-complex-adjunction: the normalized R-linear chain isomorphism.
- lem-pod-module-hom-signed-evaluation: signed evaluation for ordinary module complexes.
- lem-pod-point-sheaf-hom-maps: ordinary sheaf evaluation and the sections-tensor map.
- lem-pod-point-tensor-hom-evaluation: the actual evaluation square from normalization.

Each node retains the item's chapter and unit and cites the same blueprint ancestor.
Searched the whole imported blueprint for point Hom and K-flatness, with no duplicate
of these specialized conclusions. Mathlib searches include LeanSearch, LeanFinder,
Loogle and grep; the existing product, tensor and adjunction tools are used in the
proofs, and no exact point model theorem was found.

Change record: coord/changes/A8-point-derived-hom-model-interface.md.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
