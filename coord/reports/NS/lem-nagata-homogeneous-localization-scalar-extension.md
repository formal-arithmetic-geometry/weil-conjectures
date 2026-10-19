## Worker report

The module Sheaf.RingTheory.HomogeneousLocalizationScalarExtension states
HomogeneousLocalization.exists_away_scalarExtension_equiv, with one `sorry` and no
new definitions. The statement and dependency records required no corrections.

Hypothesis and conclusion correspondence:
- Commutative rings R, S, A are the explicitly universe-bound types with `CommRing` instances.
- The map R → S is `[Algebra R S]`. The map R → A₀ is encoded by `[Algebra R A]`
  and the grading `𝒜 : ℕ → Submodule R A` with `[GradedAlgebra 𝒜]`.
  The latter guarantees that scalars land in degree zero. This is equivalent to
  the node's graded ring with a coefficient map into A₀: its graded pieces are
  stable under that scalar action. There is no injectivity or surjectivity assumption.
- C is the existing algebra tensor product `S ⊗[R] A`; its standard multiplication
  is precisely `(s ⊗ a)(t ⊗ b) = st ⊗ ab`.
- Cₙ is `(𝒜 n).baseChange S`, using Mathlib's `GradedAlgebra.baseChange` instance.
  This submodule is the image of S ⊗[R] Aₙ, canonically identified with it by the
  split graded-piece inclusion. It does not require flatness.
- The degree d and homogeneous f are `{d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d)`.
- The image f_S is `1 ⊗ₜ[R] f`; its homogeneity is the actual Mathlib proof
  `Submodule.tmul_mem_baseChange_of_mem 1 hf`.
- The two chart rings use exactly `HomogeneousLocalization.Away`, the dependency's
  declaration. The source is `S ⊗[R] Away 𝒜 f` and the target is
  `Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f)`.
- The isomorphism of S-algebras is `∃ e : ... ≃ₐ[S] ...` with the prescribed
  value on EVERY `s`, denominator exponent `m`, and numerator `a` of degree `m • d`.
  Natural-number scalar multiplication `m • d` is m*d. `Away.mk` is a/f^m.
  The right numerator is `s ⊗ₜ[R] a`, with actual membership proof
  `Submodule.tmul_mem_baseChange_of_mem s ha`. Thus the existential is the
  existence of the isomorphism defined by the specified formula, not an arbitrary
  unspecified isomorphism; fractions and pure tensors generate the source.
- There is no `Flat`, `Nontrivial`, nonzero, nonzerodivisor, finite-generation,
  or invertibility assumption on either coefficients or f.

Dependency declarations read and used:
- def-nagata-homogeneous-localization-degree-zero records
  Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization,
  `HomogeneousLocalization.Away`. Its abbreviation and the full signature and
  docstring of `HomogeneousLocalization.Away.mk` were read.
- Mathlib.RingTheory.GradedAlgebra.TensorProduct: `GradedAlgebra.baseChange`,
  and the base-changed zero-piece instances. Read the full module.
- WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization:
  `HomogeneousLocalization.algebra` supplies the coefficient algebra via
  R → 𝒜 0 → Away 𝒜 f (and S for the base-changed ring). Read the instance's
  complete definition and docstring. The module publicly imports the dependency's
  Mathlib module, so the latter is available without duplicating an import.
- Mathlib's `Submodule.tmul_mem_baseChange_of_mem` provides both membership terms.

Source checked: literature/stacks-project/constructions.tex,
lemma-base-change-map-proj (Tag 01N2), including its standard-open proof,
and lemma-standard-open (Tag 01M4). The docstring carries all four node proof
steps: common denominators, split graded-piece base change and the inverse,
balanced forward map and inverse composites, multiplication/unit/scalars.

Edge cases checked mathematically: m=0 permits all degree-zero numerators;
f=0 and nilpotent f make both chart rings zero, so the equivalence is valid;
zero rings are included; zero-divisors require no cancellation; nonflat scalar
extension that kills f also makes both sides zero. Distinct arbitrary universes
for R, S, A are retained. Positive degrees other than 1 are included. No edge
case or node fault requires STATEMENT-DISPUTED.

Searches (before writing):
- msearch leanfinder: "Tensoring a graded algebra commutes with degree zero
  homogeneous localization" returned eight graded tensor multiplication and
  GradedTensorProduct hits, none the required localization equivalence.
- msearch loogle: "HomogeneousLocalization.Away, Algebra.TensorProduct" returned
  zero hits with unknown identifier Algebra.TensorProduct; inconclusive.
- msearch loogle: "HomogeneousLocalization.Away" returned 12 hits: Away, fraction constructors,
  fraction surjectivity, localization maps, finite type, and eventual degree
  membership; none is a scalar-extension equivalence.
- msearch leansearch: "scalar extension commutes with degree zero homogeneous
  localization" was unavailable (Internal Server Error); no negative verdict
  is inferred from its unavailability.
- msearch grep: "baseChange|tensor|scalar" in
  RingTheory/GradedAlgebra/HomogeneousLocalization.lean returned only scalar
  tower declarations, not the theorem.
- Read Mathlib's complete GradedAlgebra/TensorProduct.lean and the Away API;
  found tensor grading and fraction constructors, no equivalence.
- rg in upstream WeilConjectures for HomogeneousLocalization and scalar/base
  change, including its GradedAlgebra modules, found the existing coefficient
  algebra instance and chart/overlap tools, not this theorem.
- rg for this blueprint item id in upstream WeilConjectures found no declaration.
- rg in lean/Sheaf for HomogeneousLocalization, baseChange/scalarExtension and
  the proposed declaration found chart applications and ordinary localization
  tensor equivalences, not the required homogeneous-localization result.
- Searched dag/lean_names_upstream.json for the proposed name and Away equivalences;
  only chart and overlap equivalences were recorded, not this statement.

Validation: server scompile.py compiled the delivered file cleanly (1.3 seconds),
using the prescribed isolated overlay. No local compiler or global build was run.

## Second reading by NS

I read the node, all four proof steps, its sole statement/proof dependency
(def-nagata-homogeneous-localization-degree-zero), the delivered Lean, Stacks
constructions.tex Tags 01N2 and 01M4, and the inherited hypotheses of
lemma-morphism-proj. The latter assumes graded rings and a graded map, with no
Noetherian, generation, flatness, or nonvanishing condition. Tag 01N2 specializes
that map to arbitrary coefficient extension. The Lean says exactly the node's
standard-open algebra calculation; no statement correction is needed.

Object/hypothesis/conclusion checklist, independently matched:

- Commutative rings R and S and a ring map R → S: `{R : Type u} {S : Type v}`,
  `[CommRing R] [CommRing S] [Algebra R S]`. Verdict: exact; an algebra over a
  commutative ring records precisely such a map, with its induced scalar action.
- Nonnegatively graded commutative ring A with R → A₀: `{A : Type w}`,
  `[CommRing A] [Algebra R A]`, `(𝒜 : ℕ → Submodule R A)` and
  `[GradedAlgebra 𝒜]`. Verdict: exact. I read GradedRing and the GradedAlgebra
  alias in Mathlib.RingTheory.GradedAlgebra.Basic: the structure includes the
  direct-sum decomposition, unit degree zero, and graded multiplication.
  Submodules impose precisely the scalar stability induced by R → A₀;
  conversely scalars lie in 𝒜 0 because it contains 1 and is an R-submodule.
- C = S ⊗[R] A with its tensor algebra multiplication: `S ⊗[R] A`.
  Verdict: exact standard algebra tensor product, with no alternative map chosen.
- Grading Cₙ = S ⊗[R] Aₙ: `fun n ↦ (𝒜 n).baseChange S`.
  Verdict: exact as an internal grading. I read Submodule.baseChange and its
  membership constructor in LinearAlgebra.TensorProduct.Tower, and the
  GradedAlgebra.baseChange instance in GradedAlgebra.TensorProduct.
  This is the range of the tensor of the inclusion Aₙ → A. The graded
  projection splits that inclusion R-linearly, so its tensor is injective
  even for nonflat S. Hence using the range loses no graded-piece data.
- Positive degree d and homogeneous f: `{d : ℕ} (hd : 0 < d) {f : A}` and
  `(hf : f ∈ 𝒜 d)`. Verdict: exact, including positive degrees greater than 1.
- f_S = 1 ⊗ f: `1 ⊗ₜ[R] f`, whose degree-d membership is supplied by
  `Submodule.tmul_mem_baseChange_of_mem 1 hf`. Verdict: the specified element.
- Both degree-zero homogeneous localizations: `Away 𝒜 f` and
  `Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f)`.
  Verdict: the dependency's recorded HomogeneousLocalization.Away, not a
  duplicate or full ungraded localization. I read its abbreviation, Away.mk,
  Away.val_mk and Away.mk_surjective. The last includes nilpotent denominators.
- The formula defines an S-algebra isomorphism: `∃ e : ... ≃ₐ[S] ...` followed
  by `∀ (s : S) (m : ℕ) (a : A) (ha : a ∈ 𝒜 (m • d)), ...`.
  Verdict: exact. Here m • d = md, Away.mk is a/f^m, and the image numerator
  is exactly `s ⊗ₜ[R] a`. The RHS uses denominator (1 ⊗ f)^m and its actual
  homogeneous membership proof. The equivalence is chosen before all fraction
  arguments. Fractions exhaust Away by Away.mk_surjective, and pure tensors
  additively generate the tensor product, so the formula determines the map;
  this existential does not permit an arbitrary unrelated equivalence.
- Coefficient structures on chart rings: I read the full upstream instance
  HomogeneousLocalization.algebra and val_algebraMap. They use exactly
  R → 𝒜 0 → Away (and S → C₀ → Away after base change). Verdict: correct
  S-algebra structures, including the unit and scalar requirements of ≃ₐ[S].
- No flatness or regularity: neither occurs among the binders. No finite type,
  nonzero, Nontrivial, or field assumption occurs either. Verdict: exact.

Edge cases: m = 0 gives every degree-zero numerator over 1; d = 0 is excluded
by the node itself. Zero numerator is included. Zero rings and f = 0 are
allowed. Nilpotent f makes both localizations zero. Nonflat scalar extension
can kill f, in which case tensoring the relations makes the source zero too.
Zero divisors require only power-annihilated fraction equality, never
cancellation. Arbitrary characteristics and independent universes u, v, w
are retained; every type and variable is explicitly bound. There is no
independent index family or scheme in this algebraic statement, so empty
index sets and empty schemes add no excluded cases.

Independent searches: msearch leanfinder for "Degree zero part of localization
of graded ring commutes with arbitrary base ring change" returned eight
HomogeneousLocalization map/awayMap/scalar-structure results, none this
isomorphism. msearch loogle `HomogeneousLocalization.Away` returned twelve
fraction, map, and finiteness declarations, none a tensor comparison.
msearch grep `scalarExtension|tensorEquiv|baseChange` returned general tensor
base-change operations. Direct rg with `scalarExtension|baseChange|TensorProduct|⊗`
in Mathlib and upstream GradedAlgebra directories found the grading instance,
not the desired theorem. Direct rg in lean/Sheaf and dag/lean_names_upstream.json
for Away equivalences and homogeneous scalar extension found overlap/chart
applications and the consumer NagataAffineProjScalarExtension, no duplicate.
The worker's recorded LeanSearch service failure is not treated as evidence
of absence. No new definition nodes or dependency modules were delivered.

H5/H6/H8/H9: no definitions are introduced; the sole theorem has exactly one
whole-proof `sorry`. Module and theorem docstrings contain the source and
blueprint id. The proof docstring covers all four node steps: comparison at
a common later denominator, split graded-piece tensoring and the compatible
inverse maps, the balanced forward map and both inverse identities, and
multiplication/unit/scalars. All lines respect the limit, both imports serve
the statement and dependency, and no file-local definitions or instances
are used. I compared lean.statement with the file signature verbatim.

Mismatches found: none. Changes: appended this independent second-reading
record only; preserved the correct Lean and node. Required server scompile.py
compiled the file cleanly (sandbox 1.3 seconds, library module 1.4 seconds),
with no warnings or errors. No local compiler or library build was run.
