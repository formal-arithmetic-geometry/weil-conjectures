## Worker report

The module `Sheaf.RingTheory.EppFiniteFamilyTraits` states
`IsDiscreteValuationRing.exists_epp_finite_family_traits`, with `sorry` as its
entire proof. Its two construction helpers have real data:
`eppTraitTensorMap` is Mathlib's heterobasic tensor map on the given embeddings;
`eppNormalizedFactorSpecialFibre` takes its maximal-ideal quotient, integral
closure, and quotient by the canonical image of the uniformizer. These helpers
belong to the statement's specified construction and are listed in
`lean.declarations`; they are not new independent notions. No new nodes, no
dependency repairs, and no statement correction are needed.

Hypothesis and conclusion correspondence:

- Prime p: `(p : ℕ) (hp : p.Prime)`.
- W₀ a complete DVR: `[CommRing W₀] [IsDomain W₀]`
  `[IsDiscreteValuationRing W₀] [IsAdicComplete (maximalIdeal W₀) W₀]`.
- Fraction field K₀: `[Field K₀] [Algebra W₀ K₀] [IsFractionRing W₀ K₀]`.
  Mixed characteristic is `[CharZero K₀] [CharP (ResidueField W₀) p]`.
  The named residue field k₀ is the canonical `ResidueField W₀`;
  `[PerfectField (ResidueField W₀)]` says it is perfect, equivalently its
  p-power Frobenius is surjective in characteristic p.
- Finite index set, including empty sets: `(I : Type w) [Finite I]`.
- Upper traits: `(T F : I → Type v)` with the pointwise commutative-ring,
  domain and DVR instances for T; `hexc : ∀ i, IsExcellent (T i)` supplies
  excellence. No completeness assumption is made on any T i.
- Injective local base maps: `[∀ i, Algebra W₀ (T i)]`, pointwise
  `IsLocalHom (algebraMap W₀ (T i))`, and `hinj` for injectivity.
- Fraction fields Fᵢ: the pointwise Field, Algebra (T i) (F i), and
  IsFractionRing instances. `[∀ i, Algebra K₀ (F i)]` and `hF` specify
  the induced base-field embeddings: the two composites W₀ → Fᵢ agree.
  This compatibility supplies precisely the fraction-field map extending the
  given injective map, rather than an arbitrary additional structure.
- The perfect-core hypothesis is `hcore`: membership is written explicitly as
  `∀ n, ∃ y, y ^ (p ^ n) = x`. The conclusion is `IsAlgebraic` over k₀
  using exactly `(ResidueField.map (algebraMap W₀ (T i))).toAlgebra`.
- The conclusion existentially provides W with the commutative-ring, domain,
  DVR and maximal-ideal-adic completeness instances, together with its
  W₀-algebra and local-map instance. Injectivity is the first conjunct;
  `Module.Finite W₀ W` is finiteness as a module.
- Its residue extension is finite along the canonical induced residue map:
  `(ResidueField.map (algebraMap W₀ W)).Finite`. The subsequent `CharP`
  and `PerfectField` conjuncts give characteristic p and perfection.
- Its fraction field K has Field, Algebra W K and IsFractionRing instances;
  CharZero K completes the mixed-characteristic assertion. Algebra K₀ K
  and the equality `hK` specify the unique induced base-field embedding.
- For every i the tensor product Fᵢ ⊗[K₀] K is explicitly a finite product
  of fields: there exist n, fields E j indexed by Fin n, and a ring
  equivalence to their dependent product. This assertion is separate from
  and conjoined with the special-fibre assertion.
- Every uniformizer is covered by `∀ π, maximalIdeal W = Ideal.span {π} →`.
  Every field factor is covered by `∀ m, m.IsMaximal →`, with field factor
  exactly `(F i ⊗[K₀] K) ⧸ m`.
- `eppTraitTensorMap` is the canonical map Tᵢ ⊗[W₀] W → Fᵢ ⊗[K₀] K,
  given on simple tensors by the two fraction embeddings. Composing with
  `Ideal.Quotient.mk m` specifies the map to that field factor E.
- In `eppNormalizedFactorSpecialFibre`, `integralClosure (T i ⊗[W₀] W) E`
  is the integral closure of the image: monic polynomial equations over
  the tensor product and over its image are equivalent by coefficient lifting.
  Its algebra map carries 1 ⊗ π into this integral closure B. Quotienting by
  the ideal spanned by that element is exactly B/πB. The theorem concludes
  `IsReduced` of this actual quotient ring, not a predicate on arbitrary maps.

Dependency declarations used, with their recorded modules:

- def-sc-discrete-valuation-ring: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`; uniformizers use the
  maximal-ideal-generator characterization in `irreducible_iff_uniformizer`.
- def-weil-pbc-adically-complete-ring: `IsAdicComplete`,
  `Mathlib.RingTheory.AdicCompletion.Basic`.
- def-weil-field: `Field`, `Mathlib.Algebra.Field.Defs` (provided by the
  fraction-field and residue-field imports).
- def-exc-excellent-ring: `IsExcellent`, `Sheaf.RingTheory.ExcellentRing`.
- def-weil-finitely-generated-module: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs` (imported through RingHom.Finite).
- def-pc-field-extension: `Algebra`, `Mathlib.Algebra.Algebra.Defs`.
- def-weil-pbc-module-tensor-product: `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, with its algebra structure and
  canonical `Algebra.TensorProduct.mapRingHom` from
  `Mathlib.RingTheory.TensorProduct.Maps`.
- def-weil-pbc-integral-closure: `integralClosure`,
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`.

All statement dependencies' records and the full signatures/docstrings of
these declarations were read. The two proof dependencies
lem-per-epp-single-trait-base-change and
lem-per-epp-common-finite-trait-extension currently have neither Lean records
nor Mathlib matches. Thus they have no modules to import; their precise uses
are retained in the theorem's three-step proof docstring. They are proof
inputs, not missing statement notions.

Edge cases checked before writing: an empty I is permitted and takes W=W₀;
there is no Nonempty hypothesis. No Tᵢ is assumed complete (ILO IV Remark
3.1.3 explicitly allows this). Ramified and unramified finite base extensions
are permitted. Every generator of the nonzero maximal ideal is quantified,
so no special choice of uniformizer is fixed. The intersection includes n=0
and all positive n. Both residue maps and tensor maps are the specified
canonical maps, with no independent residue inclusion. Field factors use
maximal, rather than arbitrary prime, quotients. The nonzero generic tensor
product cannot be equivalent to an empty field product, although allowing
n=0 in the finite-product encoding creates no extra case. The independent
index universe w permits any finite indexing set; upper traits/fraction
fields use v, base and its finite extension use u, and factors use max u v.
All universes and binders are explicit. Finite algebraic extensions and
fraction fields of a Type u base admit Type u representatives, so the
existential sizes impose no mathematical restriction.

Source read: local ILO PDF, Exposé IV 3.1.2–3.1.3 and 4.2.3 (extracted text
at lines 2779–2794 and 2975–2984). It explicitly states Epp's perfect-core
hypothesis, permits noncomplete T, and uses finiteness of the traits plus
stability under further finite base change. No source discrepancy or
STATEMENT-DISPUTED issue was found.

Searches for existing declarations:

- msearch leanfinder: "A finite family of discrete valuation rings admits a
  finite extension of a complete mixed characteristic base DVR with reduced
  normalized special fibres". Eight hits, including Tilt, PreTilt,
  WittVector.isDiscreteValuationRing and good reduction of Weierstrass curves;
  none gives the simultaneous Epp statement.
- msearch loogle: "IsDiscreteValuationRing, IsReduced". Zero hits.
- msearch leansearch: "Epp elimination of wild ramification simultaneously
  for finitely many discrete valuation rings". Eight hits about ramification
  indices, DVR characterizations and unramified extensions; no match.
- msearch grep: "Epp|elimination.*ramification|normalized.*base.*change".
  Twenty-five hits, mostly incidental substrings such as stepping or ePp;
  no Epp theorem.
- rg of WeilConjectures for Epp/perfect-core names, the item id and the
  three chosen declaration names: no relevant declaration. Case-insensitive
  conceptual search also found only unrelated normalized descent/base change.
- rg of lean/Sheaf for Epp/perfect-core names and this item id found only
  proof-docstring mentions in MixedReducedSpecialFibreCover; no declaration.
- rg of dag/lean_names_upstream.json for the item and chosen declaration
  names found no declaration. The eight dependency records were resolved
  directly from the DAG, including Mathlib-only matches without lean records.

Validation: scompile.py compiled the sandbox and named library module cleanly
(2.2 seconds each) after making the constructed special fibre a reducible
abbreviation so that its inherited ring operations are available. A final
compile and delivery preflight follow the explicit-universe cleanup.

## Second reading by Q125

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
