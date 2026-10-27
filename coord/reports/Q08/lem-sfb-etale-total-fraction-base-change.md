## Worker report

The module `Sheaf.RingTheory.EtaleTotalFractionBaseChange` states
`etale_total_fraction_base_change`, with its proof left `sorry`. No definitions,
extra nodes, dependency repairs, or statement corrections are needed.

Hypothesis and clause correspondence:

- The commutative rings are `{A B : Type u} [CommRing A] [CommRing B]`.
  The common universe is arbitrary and accommodates any pair of rings in a common
  universe, as required for Mathlib's category of schemes.
- The ring homomorphism `f : A → B` is encoded by `[Algebra A B]` and is
  `algebraMap A B`. This is the standard equivalent encoding of an arbitrary
  commutative-ring homomorphism; it adds no flatness or injectivity assumption.
- Noetherianity is `[IsNoetherianRing A]`; reducedness is `[IsReduced A]`.
- The precise geometric étaleness hypothesis is
  `[AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map
  (CommRingCat.ofHom (algebraMap A B)))]`.
- `T_A` and `T_B` are Mathlib's `nonZeroDivisors A` and `nonZeroDivisors B`.
  `FractionRing R` is literally `Localization (nonZeroDivisors R)`, the total
  fraction ring for an arbitrary commutative ring, without a domain assumption.
  Mathlib identifies this ring localization with `LocalizedModule S R` at the
  underlying quotient-type level (`example_localization_eq_localizedModule` in
  the recorded localized-module source); this is the ring specialization of the
  dependency's module-localization notion, not another localization definition.
- The first conclusion is `∃ h : ∀ s : nonZeroDivisors A,
  algebraMap A B s ∈ nonZeroDivisors B`. This is exactly `f(T_A) ⊆ T_B`.
  Its proof is bound so that denominators in the subsequent formula are typed.
- The second conclusion quantifies an `AlgEquiv B` from
  `FractionRing A ⊗[A] B` to `FractionRing B`. The source's `B`-algebra structure
  is explicitly `Algebra.TensorProduct.rightAlgebra`, so it is the action through
  `b ↦ 1 ⊗ b`; the target uses its canonical fraction-ring algebra structure.
  This uses no file-local instance, hidden let, or extra structure assumption.
- The last clause quantifies every `a : A`, `s : nonZeroDivisors A`, `b : B` and
  states that the equivalence sends `IsLocalization.mk' (FractionRing A) a s ⊗ b`
  to `IsLocalization.mk' (FractionRing B) (algebraMap A B a * b)
  ⟨algebraMap A B s, h s⟩`, precisely `(a/s) ⊗ b ↦ f(a)b/f(s)`.
  Fractions exhaust `Q(A)` and pure tensors generate the tensor product; this
  formula uniquely determines the map. Thus the existential equivalence is the
  canonical comparison, rather than an arbitrary isomorphism of the two rings.
  No separate construction is chosen from the theorem.

Statement dependencies, with recorded modules and declarations read:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (every ideal finitely generated).
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale` (affine-local étale ring maps).
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`, publicly available
  through the étale module.
- `def-weil-pbc-module-localization`:
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule`, its quotient
  construction and fraction representation. Ring specialization uses the
  existing `Localization`, `FractionRing`, and `IsLocalization.mk'` APIs.
- `def-weil-pbc-module-tensor-product` (Mathlib match):
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, `TensorProduct`, with the ring and
  right-algebra structures from `Mathlib.RingTheory.TensorProduct.Basic`.

Proof dependencies are imported without `public`: the affine flatness criterion
in `Mathlib.AlgebraicGeometry.Morphisms.Flat`; `RingHom.Flat` in
`Mathlib.RingTheory.RingHom.Flat`; `IsLocalization.tensor` in
`Mathlib.RingTheory.Localization.BaseChange`;
`reduced_noetherian_total_ring_fractions` in
`WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions`;
`TensorProduct.piLeft` in `Mathlib.LinearAlgebra.TensorProduct.Pi`;
`AlgebraicGeometry.pullbackSpecIso` in `Mathlib.AlgebraicGeometry.Pullbacks`;
`Algebra.Etale.iff_exists_algEquiv_prod` in `Mathlib.RingTheory.Etale.Field`.
Étale stability under base change is already provided by the public étale import.
The theorem docstring gives all six node proof steps, including their dependencies,
the localization zero criterion, finite-product algebra compatibility, regularity
and invertibility, and the mutually inverse fraction maps.

Source read: `literature/stacks-project/spaces-divisors.tex`,
`lemma-meromorphic-quasi-coherent` (Tag 0EN6), especially the displayed
`Q(A) ⊗_A B → Q(B)` and the parenthetical preservation of nonzerodivisors by
flatness. The node is the stated reduced Noetherian specialization of that source.

Edge cases checked before writing:

- `A = 0`: unitality forces `B = 0`. Both localizations and tensor product are
  zero rings; no `Nontrivial` or `IsDomain` hypothesis appears.
- Any `A → 0`: an étale zero algebra is permitted; `nonZeroDivisors 0` contains
  the sole element, so the denominator subtype and equivalence remain meaningful.
- `A` a field: `B` can be a finite product of separable extensions, including the
  empty product. The statement imposes neither connectedness nor faithful action.
- A disconnected reduced Noetherian ring, or an étale localization killing a
  component, is allowed. In particular injectivity of `A → B` is never assumed.
- Taking `s = 1` recovers the expected formula on `a ⊗ b`; the algebra structure
  already enforces `1 ⊗ b ↦ b/1`.

Searches made on 2026-10-24:

- `msearch.py ... leanfinder`: "For a reduced Noetherian ring A and an etale A
  algebra B the canonical map Q(A) tensor A B to Q(B) is an isomorphism".
  Eight hits, including `Algebra.Etale.baseChange`, formally étale tensor-product
  stability, integral-closure comparisons and the field-algebra decomposition;
  none is the total-fraction comparison.
- `msearch.py ... loogle`: `"IsFractionRing", "Etale"`; zero hits.
- `msearch.py ... grep` in `RingTheory`:
  `(IsFractionRing|FractionRing|nonZeroDivisors).*[Ee]tale|[Ee]tale.*(IsFractionRing|FractionRing|nonZeroDivisors)`;
  zero hits.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for the item ID and
  étale/fraction combinations: existing chart fraction maps and meromorphic
  objects occur, but no statement of this base-change result. The upstream
  `ReducedNoetherianTotalRingFractions` module supplies the proof prerequisite,
  rather than this result.
- `rg` of Mathlib, both project source trees, and `dag/lean_names_upstream.json`
  for `etale_total_fraction_base_change`: no declaration collision.
- Read Mathlib's `FractionRing`, `IsFractionRing`, `IsLocalization.mk'`,
  `Algebra.TensorProduct.rightAlgebra`, `AlgEquiv`, tensor-product quotient/lift,
  and all recorded statement-dependency signatures and docstrings.

No STATEMENT-DISPUTED flag or node fault was found. The sandbox and library forms
both compiled cleanly with the prescribed `scompile.py` wrapper.

## Second reading by Q08

A separate clause-by-clause rereading by the assigned worker checked the node
against the finished source; no additional agent was started, as the dispatcher
explicitly prohibits that. The maintainer supplies the independent review.

The ring, Noetherian, reduced and spectrum-étale hypotheses appear exactly once.
The source of the equivalence has the node's tensor-factor order. Inspecting
`@AlgEquiv` and its explicit `rightAlgebra` argument verifies that this is a
`B`-algebra equivalence, not merely an `A`-linear or ring equivalence. Inspecting
the quantified formula verifies both the numerator `f(a)b` and denominator
`f(s)` and ties them to the same nonzerodivisor-preservation witness. All
fractions and pure tensors are covered. There are no extra assumptions excluding
zero rings, products, or noninjective structure maps. No mismatch or correction
was needed on this rereading. The module contains one theorem and one `sorry`,
no definition or proof helper, and imports every recorded proof prerequisite.
