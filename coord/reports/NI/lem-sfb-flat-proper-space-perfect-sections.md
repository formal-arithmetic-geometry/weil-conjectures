## Worker report

The module `Sheaf.AlgebraicGeometry.FlatProperSpacePerfectSections` states
`AlgebraicGeometry.AlgebraicSpace.flatProperSpace_perfect_sections` with proof `sorry`.
No definition, dependency repair, new node, or statement correction is needed.
The mathematical statement is unchanged. Four already landed definition nodes are
added to `stmt_deps` to cite the actual small-model, derived-module, morphism-property,
and scalar-sections interfaces. These additions are authorized by brief-stage2 §5
(STMT_DEPS MAY GAIN LANDED NODES).

Hypothesis and clause correspondence:

- The size convention is explicit `universe u w`, `Scheme.{u}`, `A : Type u`, and
  `[HasDerivedCategory.{w} X.SmallModules]`. The localization universe is not forced
  to equal the ring universe. The existing `SmallEtaleModel` is a u-small affine
  basis model equivalent to the original small étale ringed topos; its modules
  retain section universe u. No enlargement of coefficients is imposed.
- A commutative ring is `(A : Type u) [CommRing A]`.
- The affine target is `(Y : Over S) (e : Y.left ≅ Spec (.of A))`. This is a
  presentation of Spec A, allowing the same arbitrary ambient scheme S as the
  algebraic-space framework. Every map to Spec A is included by taking S = Spec A,
  Y = Over.mk (𝟙 S), e = Iso.refl _. No geometric condition on S is required.
- An algebraic space is `(X : AlgebraicSpace S)`; the morphism is
  `(f : X ⟶ schemeSpace Y)`, with the representable affine target.
- Flatness is `_hflat : MapIsFlat f`. This is exactly `MapIsLocally (@Flat) f`,
  universally testing compatible étale chart maps with Mathlib's flatness.
- Properness is `_hproper : MapIsProper f`. Its definition is separatedness,
  finite type and universal closedness. Finite type includes quasi-compactness
  and the chartwise Mathlib locally-finite-type condition. Separatedness uses
  the representable closed-immersion diagonal, and universal closedness tests
  all algebraic-space base changes on the existing point topology.
- Finite presentation is `_hfp : MapIsLocallyOfFinitePresentation f ∧
  MapIsQuasiCompact f.hom.hom ∧ MapIsQuasiCompact (pullback.diagonal f.hom.hom)`.
  These are respectively the chartwise local condition, quasi-compactness, and
  quasi-separatedness. The last two are retained even though properness implies
  relevant finiteness properties.
- The arbitrary unbounded derived object is `(E : X.DerivedModules)`.
- Local perfectness is `_hE :
  SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u,u,u,w}
  X.smallStructureSheaf E`. Unfolding gives a representative K and a covering
  sieve over every object, bounded local complexes of degreewise finite-free
  retracts, and quasi-isomorphisms to the restrictions of K. Bounds and ranks
  may vary with the cover. No quasi-coherence hypothesis on E is added.
- D_QCoh in the prose fixes terminology; the theorem does not quantify a second
  object of that subcategory. The existing `derivedQCohProperty` tests the actual
  cohomology after the inverse module equivalence, using `IsQuasicoherent`.
- RΓ(X,E) in D(A), with the specified scalar action, is exactly
  `(affineDerivedSections A Y e X f).obj E`. Its underlying ordinary functor is
  Hom(O_X,-), made A-linear by `affineGlobalScalar`, whose components are the
  pullbacks along T→X→Y→Spec A. It is the canonical unbounded right derived
  functor computed on K-injectives, not H⁰ or an unspecified chosen functor.
- The conclusion `DerivedCategory.IsPerfectRingComplex ...` is the dependency's
  exact predicate: existence of a cochain complex P, strict lower/upper bounds,
  projectivity and finite generation in every degree, and a nonempty isomorphism
  from the derived sections object to Q(P). Its strict bounds express actual
  zero terms outside a finite interval. The ring-derived localization used by
  `affineDerivedSections` is the published standard localization.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `EtaleSite`, `structurePresheaf`, `structureSheaf`, `Modules`, and the chart
  representability definitions. Morphisms are those of the full subcategory.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib's `SheafOfModules` and its category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its
  slice sheafification instances, using Mathlib `SheafOfModules.IsQuasicoherent`.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`, with its local predicate
  and the existing `StrictPerfectCoefficientPackageOnSite`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`;
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`. These supply the scheme properties in the chart
  tests. The direct import of Proper also retains the original dependency record.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex` (bounded finite projective models).
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses` is read/imported for
  the original dependency; it is H⁰RΓ into abelian groups. The already landed
  affine-sections API supplies its untruncated A-linear version needed here.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`: `SmallEtaleModel`,
  `SmallModules`, `smallStructureSheaf`, `smallModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedQCohProperty`, `chartToScheme` and the existing derived direct image.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsFlat`,
  `MapIsProper`, `MapIsLocallyOfFinitePresentation`, with definitions read in full.
- `Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections`: `affineChartScalar`,
  `affineGlobalScalar`, `affineScalarSections`, `affineDerivedSections`.

The four stated proof dependencies are imported plainly: ProperSupportTensorPerfect,
PerfectAffineBoundedProjective, RingedToposDerivedPushforwardComposition, and
AffineQCohDerivedEquivalence, with the declaration names recorded by those nodes.
The two comparison/perfectness-detection proof nodes have no Lean attachment in
this read checkout and therefore no import is invented for them. Their uses remain
explicit in the theorem's complete four-step proof docstring. No proof prerequisite
is restated or assumed as an extra hypothesis.

Sources read: `literature/stacks-project/spaces-perfect.tex`,
lemma-flat-proper-perfect-direct-image-general (Tag 0CTM(1)), and
lemma-derived-quasi-coherent-small-etale-site (Tag 071Q). The former specializes
0A1P with O_X[0]; the latter identifies scheme étale and Zariski D_QCoh.
The source also states arbitrary base change, which is not a clause of this node;
this delivery states precisely the node's derived-sections perfectness assertion.

Edge cases checked before drafting: E = 0 gives the zero bounded projective model;
X empty gives zero sections; A the zero ring is permitted (no Nontrivial instance);
the identity of Spec A gives the defining bounded-projective characterization.
No Noetherian, separated ambient-base, connectedness, characteristic, nonempty
atlas, fixed rank, or uniform local-bound assumption was introduced. Degree-zero
and shifted perfect complexes are included. There are no disputed statements.

Searches executed:

- msearch leanfinder: "Derived global sections of a perfect complex on a flat
  proper finitely presented algebraic space are perfect". Eight hits on flat
  scheme maps, affine limits, and K-projective/derived homology notions; none
  states this theorem.
- msearch loogle: "AlgebraicGeometry.IsProper,
  DerivedCategory.IsPerfectRingComplex". Zero hits; the service reports the
  latter project-specific name unknown. This is not evidence that its local
  definition is absent; that definition was opened and reused.
- msearch grep: "perfect.*(proper|globalSections)|proper.*perfect" in
  AlgebraicGeometry. Zero Mathlib hits.
- msearch leansearch: "Perfect complex flat proper algebraic space derived global
  sections perfect". Eight ordinary global-sections/Spec-adjunction hits, no
  derived algebraic-space perfectness theorem.
- rg in `lean/WeilConjectures` and `lean/Sheaf`: searched flat/proper/perfect,
  perfect/globalSections, and the item id. The noetherian perfect direct image
  is different; ProperSupportTensorPerfect is the existing general tool in the
  proof. SpaceAffineGlobalSections supplies the exact scalar-sections functor.
  The proposed theorem name has no existing declaration. The upstream name index
  and existing local perfectness consumers were inspected as well.

Validation: the delivered module is compiled by scompile.py; the deliver2.py dry
run and delivery perform their independent server checks. Only the expected
warning for the theorem's `sorry` is allowed.

## Second reading by NI

This is a separate rereading pass by the same dispatched worker, not a claim of
another agent's independent review; the prompt forbids starting other agents and
assigns independent review to the maintainer. I reopened the node and the written
file, then traced its local-perfectness, morphism-property, scalar-sections and
ring-perfectness definitions. The correspondence above includes every geometric
hypothesis and the entire conclusion. In particular, the affine presentation e
preserves the A-action, quasi-separatedness is retained in finite presentation,
RΓ is untruncated, E is arbitrary in the unbounded module derived category subject
only to perfection, and the conclusion gives an actual bounded finite projective
model. The small affine basis is already the published equivalent ringed topos.
No statement mismatch or correction was found. No independent rereader is claimed.
