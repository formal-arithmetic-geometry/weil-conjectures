## Worker report

Repair of return L, immutable head 54ba25b41f0c, H3. Removed the false degreewise
surjectivity assumption `hdeg` and all arbitrary `chart`/`hchart` assumptions.
Restored the chart-map conclusion and uniqueness under the standard-open and chart
formulas. The repository node's statement, dependencies, and proof are unchanged;
only its lean record is updated. The earlier report's claim of a statement correction
was inaccurate and has been removed.

Module: `Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension`.
Declaration: `AlgebraicGeometry.lem_nagata_affine_proj_scalar_extension`.
The only proof is `sorry`; no definition or auxiliary theorem is introduced.

Hypothesis-by-hypothesis correspondence:

- `R`, `S`, `A`, `B` with `CommRing` render the four commutative rings.
  `Algebra R S` renders the specified ring map R → S; `Algebra R A` and
  `Algebra S B` render the scalar actions.
- `𝒜 : ℕ → Submodule R A`, `ℬ : ℕ → Submodule S B` and both `GradedRing`
  instances render the direct-sum nonnegative gradings and their scalar-stable pieces.
- `ρA`, `hρA` render R → A₀ inducing the given R-action on A.
  `ρB`, `hρB` render S → B₀ inducing the given S-action on B.
- `β : TensorProduct R S A ≃ₐ[S] B` renders the S-algebra isomorphism from
  the usual balanced tensor-product algebra (including its usual multiplication).
- `ψ : 𝒜 →+*ᵍ ℬ` renders the induced graded ring map; `hβψ` fixes its value
  as β(1 ⊗ a). This is not an arbitrary additional ring map.
- `hgraded : ∀ n, ℬ n = Submodule.span S (ψ '' (𝒜 n : Set A))` renders that
  β identifies the homogeneous component S ⊗ Aₙ with Bₙ. Indeed the image of
  the component tensor map under β is exactly this S-span, by the pure-tensor
  generators and S-linearity. This equality, together with the algebra equivalence,
  is exactly graded scalar extension. It allows arbitrary finite S-linear sums;
  it does not require any single-element preimage under ψ.

Conclusion clause-by-clause correspondence:

- `∃ r : Proj ℬ ⟶ Proj 𝒜` gives the canonical morphism.
- `CategoryTheory.IsPullback r ...` gives its cartesian square with exactly
  `Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom ρB)`, the analogous A map,
  and `Spec.map (CommRingCat.ofHom (algebraMap R S))`.
- The first universal clause states exactly the inverse-image equality for every
  `f ∈ 𝒜 n` with `0 < n`.
- The next clause is
  `Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hn ≫ r =
   Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f)) ≫
   Proj.awayι 𝒜 f hf hn`.
  The `awayι` maps are the standard chart isomorphism inverses followed by the open
  inclusions. Thus this equality says exactly that the restriction is the spectrum
  morphism of the canonical homogeneous-localization ring map. Its value on
  `Away.mk 𝒜 hf m x hx` is `Away.mk ℬ (ψ.map_mem hf) m (ψ x) (ψ.map_mem hx)`
  by Mathlib's `HomogeneousLocalization.Away.map_mk`: a/fᵐ ↦ ψ(a)/ψ(f)ᵐ.
  This uses an existing real ring-map construction, with no extra chart assumptions.
- The indexed supremum over `{p : ℕ × A // p.2 ∈ 𝒜 p.1 ∧ 0 < p.1}` is top,
  exactly the cover by all positive-degree homogeneous image standard opens.
- The last clause quantifies every competing scheme morphism `r'` with the same
  inverse-image and canonical chart formulas and asserts `r' = r`. It does not
  claim uniqueness among arbitrary cartesian-square morphisms.

Dependency declarations read and used:

- `def-nagata-affine-proj`: `AlgebraicGeometry.Proj` in
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`; standard opens,
  `Proj.toSpecZero`, `Proj.basicOpenIsoSpec`, `Proj.awayι` in
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, its projections and lift
  in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; cartesianness
  expressed by `CategoryTheory.IsPullback` in its recorded pullback API.
- `def-nagata-homogeneous-localization-degree-zero`:
  `HomogeneousLocalization.Away`, `Away.mk`, `Away.map`, `Away.map_mk` in
  `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`.

All these dependency notions are Mathlib notions, used through imports; no dependency
module or new node is needed. Proof dependencies without recorded Lean declarations
are named in the theorem's step-by-step proof docstring for stage 3.

Edge cases checked:

- R = ℤ, S = ℚ, A = ℤ[X], B = ℚ[X] demonstrates the rejected `hdeg` assumption:
  X/2 has no single ψ-preimage. The repaired S-span condition includes it.
- Scalar extension need not be flat, faithful, finite, or injective. The S-span
  characterization needs no flatness: Aₙ → A is split R-linear by the
  grading decomposition, so tensoring preserves this particular injection.
- Zero rings, gradings concentrated in degree zero, nilpotent homogeneous f, and
  empty Proj are permitted. Empty standard opens and zero localization rings cause
  no exception. The cover uses all positive-degree elements, including zero.
- No nonzerodivisor, characteristic, nonemptiness, or degree-one generation condition
  appears. Positive degree is precisely the node's chart condition.

Searches performed during this repair (via msearch.py and direct rg):

- LeanFinder: “Proj of a graded algebra commutes with scalar extension with standard
  open chart maps”: 8 hits, standard-chart and structure-map lemmas only; no matching theorem.
- Loogle: `HomogeneousLocalization.Away.map, Proj.awayι`: 0 hits,
  unknown identifier `Proj.awayι` in the service's naming context.
- msearch grep `Away.map|scalar.extension|baseChange` in
  `AlgebraicGeometry/ProjectiveSpectrum`: 3 hits in Functor.lean, including the
  canonical chart formula; none states the scalar-extension pullback theorem.
- Direct rg in Mathlib located `Away.map`, `Away.map_mk`, `Proj.awayι` and its full
  signature/docstring, and the bundled `GradedRingHom` definition. These APIs are
  reused without duplication.
- Direct rg over `WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry`
  for scalar-extension and tensor-grading statements found no matching theorem;
  search for this blueprint id in both source trees found none.

Source checked locally: constructions.tex, lemma-morphism-proj (Tag 01MY), condition (2)
and uniqueness proof; lemma-base-change-map-proj (Tag 01N2), conditions (1), (2).
No statement dispute or node correction remains.

## Earlier second reading (a previous round; superseded)

The former second-reading text approved the returned assumptions and missing conclusion,
so it has been removed. This repair has been self-checked against every clause as above;
the independent second reader must review the changed delivery before pushing it.


## Second reading by NH

Independent second reading of the repaired file and the unchanged repository node.
I read constructions.tex, lemma-morphism-proj (01MY), including its uniqueness
argument and condition (2), and lemma-base-change-map-proj (01N2), including its
inherited hypotheses. These assume arbitrary commutative graded rings and scalar
extension, with no flatness, finite generation, or degree-one generation hypothesis.
The omission of twist-sheaf assertions is explicit in this node's source record.
There is no statement_change and no correction to audit against citers.

Objects and hypotheses, in the order of the node:

1. Commutative rings R and S and a map R → S: `{R : Type u} [CommRing R]`,
   `{S : Type u} [CommRing S]`, `[Algebra R S]`. An algebra structure here
   is precisely a specified unital ring homomorphism, since the rings are
   commutative. Verdict: exact.
2. A nonnegatively graded commutative ring A and R → A₀:
   `[CommRing A]`, `[Algebra R A]`, `𝒜 : ℕ → Submodule R A`,
   `[GradedRing 𝒜]`, `ρA : R →+* 𝒜 0`, and `hρA`.
   GradedRing extends the graded multiplication and DirectSum.Decomposition;
   it is a genuine direct-sum grading. Scalar stability of each component
   follows from multiplication by the degree-zero image of R, so Submodule
   adds no restriction. hρA identifies the ambient scalar action with ρA.
   Verdict: exact, including the specified degree-zero map.
3. The balanced tensor-product algebra S ⊗_R A with its usual multiplication:
   `TensorProduct R S A` in the S-algebra equivalence `β` uses Mathlib's
   tensor-product commutative ring and left S-algebra instances, not a custom
   tensor product. Verdict: exact.
4. Graded commutative B with its degree-zero S-action and graded isomorphism β:
   `[CommRing B]`, `[Algebra S B]`, `ℬ : ℕ → Submodule S B`,
   `[GradedRing ℬ]`, `ρB`, `hρB`, `β`, and `hgraded`.
   For every n, the image of S ⊗_R Aₙ inside B is exactly the S-span of
   β(1 ⊗ a) for a ∈ Aₙ. This follows by the pure-tensor generators and
   S-linearity of β. Thus hgraded identifies precisely the induced graded
   components, not a stronger single-element lifting property. Conversely
   the stated graded scalar extension gives this span equality. The inclusion
   Aₙ → A is split R-linear: the additive grading projections are R-linear
   because multiplication by degree-zero scalars preserves every component.
   Its tensor is consequently injective even for nonflat S. Together with
   the bijection β, hgraded therefore also identifies the components as the
   modules S ⊗_R Aₙ, not just as unrelated quotients. Verdict: exact.
5. ψ(a) = β(1 ⊗ a): `ψ : 𝒜 →+*ᵍ ℬ` and `hβψ`.
   I opened GradedRingHom in RingTheory/GradedAlgebra/RingHom.lean:
   it is a ring homomorphism with degree-preservation map_mem, exactly the
   induced map. hβψ fixes it on every a, so no arbitrary extra map is
   assumed. Verdict: exact.
6. The structural maps p_A and p_B: the two composites of `Proj.toSpecZero`
   with `Spec.map (CommRingCat.ofHom ρA)` and the corresponding ρB expression.
   These have the correct contravariant direction and use the specified
   degree-zero coefficient maps. Verdict: exact.

Conclusion clauses:

1. Canonical scheme morphism: `∃ r : Proj ℬ ⟶ Proj 𝒜` supplies the map,
   with canonicity expressed by the last uniqueness clause. Verdict: exact.
2. Cartesian square: `CategoryTheory.IsPullback r p_B p_A
   (Spec.map (CommRingCat.ofHom (algebraMap R S)))` asserts commutativity
   and the full universal property, not only an isomorphism of objects.
   Verdict: exact.
3. For each f ∈ A_n, n > 0: the first universal clause is
   `r ⁻¹ᵁ Proj.basicOpen 𝒜 f = Proj.basicOpen ℬ (ψ f)`.
   Its quantifiers and positive-degree condition agree with the node.
   Verdict: exact.
4. The restriction on that chart: the next clause equates `awayι_B ≫ r`
   with `Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f))
   ≫ awayι_A`. I read awayι's definition as basicOpenIsoSpec.inv followed
   by the open inclusion. I also read Away.map and Away.map_mk: this ring
   map sends the fraction a/f^m exactly to ψ(a)/ψ(f)^m. Thus this is the
   specified restriction under the canonical chart identifications, with
   no unspecified chart map hypothesis. Verdict: exact.
5. Cover: the indexed supremum over pairs (n,f) satisfying f ∈ A_n and
   0 < n equals top. These are precisely all positive-degree homogeneous
   image standard opens, including redundant zero elements. Verdict: exact.
6. Uniqueness: every `r'` satisfying the inverse-image and chart formulas
   equals r. No competing map needs a separately supplied pullback proof;
   uniqueness is exactly under the node's characterizing formulas.
   Verdict: exact.

Dependencies: I opened all four stmt_deps node records and checked the actual
Mathlib declarations, not just their names. Proj is the general graded scheme
of ProjectiveSpectrum/Scheme.lean, not projectiveSpaceOverAffine; toSpecZero,
basicOpenIsoSpec and awayι are the general APIs of Basic.lean. Spec and Spec.map
are the scheme constructions in Scheme.lean. pullback, its projections and lift
are in Pullback/HasPullback.lean; IsPullback is the limiting PullbackCone predicate
of IsPullback/Defs.lean, available through the imported Basic module.
HomogeneousLocalization.Away and Away.mk are the degree-zero homogeneous
localization and fraction constructor in HomogeneousLocalization.lean, and
Away.map is the existing induced ring map. All four notions are usable as
recorded. No new node or dependency module is needed. Proof dependencies without
Lean records are named in the proof docstring; existing chart and gluing APIs
are available through the imports.

Edge cases: zero rings, empty Proj, and degree-zero-only gradings are allowed.
There are no Nontrivial, nonempty, Noetherian, flat, finite-type, field, regularity,
or characteristic assumptions. For degree-zero-only gradings all positive-degree
homogeneous elements are zero, their opens are empty, and Proj is empty, so the
cover remains correct. Zero and nilpotent f give legitimate empty charts and
zero localization rings. Degree n = 0 is excluded only from the chart clauses,
as the node requires, while hgraded includes n = 0. The index is not an arbitrary
nonempty family: every positive homogeneous element is indexed. The common
ambient universe u is arbitrary, as in Mathlib's category Scheme.{u}; all rings
can be taken in that ambient universe (using ULift when starting in differing
universes). No independent smaller test-object universe truncates the pullback
universal property. autoImplicit is false, and every variable and universe in
the signature is bound.

Independent searches: msearch LeanFinder query “projective spectrum base extension
cartesian square of graded rings” returned eight standard-chart intersection
results, not this scalar-extension theorem. Loogle query `"Proj", "TensorProduct"`
returned twelve unrelated projective-module and seminorm results. Direct rg in
Mathlib's ProjectiveSpectrum directory for IsPullback, baseChange, base_change,
scalar and tensorProduct found no matching theorem. Direct rg in WeilConjectures
and lean/Sheaf/AlgebraicGeometry for Proj with tensor/scalar/base-change terms and
the exact declaration name found only twists and polynomial projective-space
specializations. I opened WeilConjectures/AlgebraicGeometry/ProjectiveSpace.lean:
its TODO explicitly distinguishes base-changed projective space from raw Proj
and notes the missing general base-change comparison. No existing declaration
replaces this module.

Mismatches and changes: no mismatch between the repaired Lean statement and the
node was found; the Lean file and node record are unchanged. I corrected one
explanatory sentence in the Worker report: tensoring the graded component
inclusion is injective because it is split, even without flatness. Its earlier
wording could suggest this injection need not hold. No statement is weakened,
no object is redefined, and the only proof remains the named theorem's sorry.
Both source docstrings and the five successive proof stages (cover, chart
pullbacks and fraction maps, overlaps and gluing, global universal property,
uniqueness) are present. Lines obey the 100-character convention.

Validation: scompile.py compiled the delivered module on the project server
cleanly in 1.4 seconds, nice 19, two threads, with the 60-second per-file limit.
I checked the node's lean.statement is verbatim the signature before `:= by`.
