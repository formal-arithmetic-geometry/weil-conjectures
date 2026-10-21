## Worker report

The delivery states `SheafOfModules.successive_quotient_linear_triangle` in
`Sheaf.Algebra.Homology.SuccessiveQuotientLinearTriangle`. It constructs the missing
quotient ring sheaves in a separate definition node and module. No existing node's
statement, proof or proof dependencies is changed. The item's statement dependencies
gain only that new definition node. The theorem asserts `Nonempty SuccessiveQuotientLinearTriangle`, whose fully
specified fields package exactly the existential witnesses and equations below.
The structure is elaborated over abstract coefficient sheaves before specialization
to the actual quotients, avoiding expensive unfolding of sheafification in types.
No data is extracted by choice. All postponed proofs are named `sorry` theorems;
all definitions have actual data.

The source read is the current blueprint
`main-20261015/blueprint/sec-proetale-coefficients/sk-prop-integral-criterion/`
`sk-prop-integral-criterion-reductions.proof.md`, second paragraph, including the
coefficient sequence and induction using its triangle. The general ring-sheaf
expansion is already the item's statement and five proof steps. Also read Stacks
`sites-cohomology.tex`, `lemma-K-flat-resolution` (06YS) and
`lemma-derived-base-change` (06YY), `sites-modules.tex`, `definition-flat` (03ER),
and `derived.tex`, `lemma-derived-canonical-delta-functor` (0152).

Hypothesis and clause correspondence:

* The site is `{C : Type u} [Category.{v} C]`, `J : GrothendieckTopology C`, with
  `[EssentiallySmall.{r} C]`: small relative to the coefficient universe `r`.
  The sheaf-composition, additive-sheaf sheafification and locally bijective
  equivalence instances expose the standard abelian module-sheaf category.
  `[HasSheafify J CommRingCat.{r}]` exposes ring-sheaf sheafification, also available
  for a site small in this universe. None is an extra geometric hypothesis on B or K.
* `B : Sheaf J CommRingCat.{r}` is the arbitrary commutative ring sheaf.
  `t : (B.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections` is its global section,
  including its restriction compatibility. `ht` is injectivity of multiplication
  by its component on every object, exactly injectivity of that sheaf morphism.
* `principalPowerRingQuotient B t j` is the sheafification of
  `U ↦ B(U) ⧸ Ideal.span {t_U ^ j}`. Its projection is
  `principalPowerRingProjection B t j`. Thus these are the actual quotient ring
  sheaves, including their ring structures, rather than bare module cokernels.
* `n : ℕ`, `hn : 1 < n` gives exactly the range of exponents in the node, with the
  predecessor represented by `n - 1`. There is no restriction to n greater than 2.
* Module sheaves use the recorded transparent `ringedSiteModules` abbreviation for
  Mathlib `SheafOfModules`; `DerivedCategory` is the recorded unbounded category.
  The four localization instances have separate universes `wB`, `wPrev`, `wN`,
  `wOne`; site object, site morphism and coefficient universes are independent.
* `FPrev`, `FN`, `FOne` are arbitrary presentations of the *recorded* derived change
  of rings for those three projections. Their ordinary functors are fixed by
  `obj_eq`, `map_eq`, their derived functors by their universal counits. The
  dependency's existence theorem supplies them; they are not arbitrary maps or
  an extra assumption about K.
* `K` is an arbitrary object of D(B). `G` and `e : Q.obj G ≅ K` range over all its
  representatives. `P`, `f : P ⟶ G`, `hf` and `hflat` range over every K-flat
  resolution with flat terms, exactly the node's final clause. A representative
  exists by essential surjectivity of Q; such resolutions exist by 06YS. The
  statement is therefore not conditional on a boundedness or existence hypothesis
  missing from the node. Neither termwise epimorphism of f nor any bound is assumed.
* The three computation isomorphisms `ePrev`, `eN`, `eOne` identify `Fj.T.obj K`
  with `Q.obj (successiveQuotientTensorModel Fj P)`. Each is fixed by
  `Fj.T.map (Q.map f ≫ e.hom) ≫ ej.hom = Fj.ε.app P`. These identify the displayed
  tensor models with precisely K_(n-1), K_n and K_1, using the canonical resolution
  computation rather than unrelated object isomorphisms.
* The existential quotient ring maps `rPrev`, `rOne` satisfy
  `π_n ≫ rPrev = π_(n-1)` and `π_n ≫ rOne = π_1`. The quotient projections are
  locally surjective, so these equations uniquely fix the canonical quotient maps.
* `successiveQuotientRestrictedModel` applies the *existing*
  `SheafOfModules.restrictScalars` termwise to the tensor complex. The endpoints
  are then localized in D(R_n). This is exactly the termwise representative
  interpretation specified in the node; it does not assert a triangle merely
  after forgetting to D(B). The computation isomorphisms above identify the
  corresponding R_j representatives with K_j. Exactness of restriction transports
  them to Res K_j; no separate construction of a derived tensor or derived
  restriction functor is introduced.
* The first two derived arrows are `Q.map α`, `Q.map β`; the third is `δ`, into
  the first object's `[1]`. `Triangle.mk ... ∈ distTriang (DerivedCategory ... R_n)`
  states distinguishedness in exactly D(R_n).
* The last two clauses quantify over every degree, object, coefficient lift b and
  module section x. They require α to send `[b] tensor x` to `[tb] tensor x`, and
  β to send `[b] tensor x` to `[b] tensor x`. The existing extension uses scalar-first
  tensors. Tensor symmetry gives exactly the node's second-factor convention.
  Quotient sections lift locally and sheafified tensors are locally generated by
  pure tensors, so the formulas specify the full maps without presuming sectionwise
  surjectivity or the existence of points.
* The helper definitions and transparent Q abbreviation merely expose the existing
  localization and termwise functor and their pure
  sections in the dependency's fixed object presentation. There is no boundedness,
  derived completeness, point, Noetherian, or sectionwise-flatness assumption.

Dependency declarations read and used:

* `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`; the ordinary E,
  derived T, object/map equations and universal cochain counit are retained.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, its full signature, same underlying sections
  and restricted scalar action, and additive instance.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`, with Mathlib's abelian instance.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, shifts and distinguished triangles.
* `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and
  `CochainComplex.IsKFlatResolutionIndependentCoefficients` (quasi-isomorphism
  and the same tensor-acyclicity definition of K-flatness).
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, exactness of the existing sheaf tensor functor.
* Proof-only imports retain the recorded flat-term K-flat resolution theorem,
  sheaf tensor interface, and `DerivedCategory.triangleOfSES_distinguished`.

Edge cases checked before writing: n=2 (the two endpoint ring sheaves coincide,
while their positions and their tensor maps remain distinct); K=0; a unit t
(all positive quotients vanish); the zero ring with t=0 (multiplication is
injective on its singleton underlying group); empty sites; unbounded P in both
directions; arbitrary site topologies without enough points. The new definition
also has n=0, where the unit ideal gives the zero ring, but the theorem only uses
positive exponents. Flatness is sheaf tensor exactness, never sectionwise flatness.

Searches actually run:

* `msearch.py leanfinder`: successive powers of a regular section and a derived
  quotient-ring-linear triangle. No exact statement; results concern presheaf
  differentials and identities for structure-sheaf sections.
* `msearch.py loogle`: `"SheafOfModules", "quotient"`, zero hits.
* `msearch.py grep`: `quotient.*[Tt]riangle|[Tt]riangle.*quotient`,
  `Algebra/Homology`, 23 hits about generic homotopy/derived triangles; none gives
  the ring-sheaf quotient and its canonical scalar-linear tensor maps.
* For the new notion, LeanSearch (8 hits: module sheafification and structure-sheaf
  constructions), LeanFinder (8 hits: total quotient presheaves and structure
  sheaves), and grep of `CategoryTheory/Sites` (one unrelated H1 comment) found no
  exact quotient-ring-sheaf definition. Their actual logged records are copied
  into the new node, without claiming a failed service found no match.
* `tools/blueprint_refs.py search 'quotient ring sheaf'`: zero blueprint nodes.
  The DAG grep found the item and specialized constant/Padic coefficient facts.
* Direct rg searches of `lean/WeilConjectures` and `lean/Sheaf` found
  `CategoryTheory.principalQuotient` (a B-module cokernel only), the continuous
  Padic quotients in `DerivedNakayamaResolution`, and
  `RingedSiteIdeal.IsQuotientIso` (a predicate on a target already supplied).
  None constructs the general quotient ring sheaf. The upstream node-id search
  found no declaration for this item. Mathlib `Ideal.quotientMap` and
  `presheafToSheaf` are reused as the actual construction's building blocks.

No statement fault or STATEMENT-DISPUTED remains. The example CompactObject module
specified in the brief is now withdrawn; its node record and the current project's
other stage-2 headers were read for the required record and header conventions.

## New nodes

`def-pe-principal-power-ring-quotients` introduces B/t^nB as the sheafification of
U ↦ B(U)/(t_U^n), together with its projection and restriction maps. Its source is
the coefficient sequence in the blueprint's integral-criterion-reductions proof,
with general sheafification of algebraic structures as in Stacks Sites Section
00YR. The searches above found no existing node or declaration for this general
ring sheaf: module cokernels and specialized constant quotients do not supply
its ring structure. The definition has genuine sectionwise quotient data and
Mathlib sheafification, with no choice from an unconstrained existence theorem.
Its four named postponed obligations are ideal preservation by restriction,
identity and composition on quotient restrictions, and naturality of the projection;
their docstrings give the elementary representative
arguments. These are the construction laws explicitly included in this definition
node's statement and are recorded among its declarations.

Validation: scompile.py compiled each delivered file separately in dependency order
against the live published server library. The quotient file passed in 1.9 seconds
and the triangle file passed in 7.2 seconds under its actual module name; there
were no errors or warnings. All temporary diagnostic options were removed.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
