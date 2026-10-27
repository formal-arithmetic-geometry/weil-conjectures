## Worker report

The module `Sheaf.RingTheory.RaynaudFaltingsNormalizedReduction` states
`Algebra.exists_raynaudFaltings_normalized_reduction`, with its proof postponed.
Its three public abbreviations expand existing Mathlib constructions, and its one
map definition applies `Algebra.TensorProduct.productMap` to the actual inclusion
of the integral closure and the scalar inclusion. None contains postponed data.
These are construction names belonging to this theorem, not independent notions
or copies of normality, completeness, field extension, or integral closure.

Hypothesis and clause correspondence:

- Complete DVR D: `[CommRing D] [IsDomain D] [IsDiscreteValuationRing D]` and
  `[IsAdicComplete (IsLocalRing.maximalIdeal D) D]`. Completeness includes separatedness.
- Fraction field F: `[Field F] [Algebra D F] [IsFractionRing D F]`.
- Finitely generated commutative D-algebra E, flat as a D-module:
  `[CommRing E] [Algebra D E] [FiniteType D E] [Module.Flat D E]`.
- Geometrically normal E_F: `hgeneric` quantifies over every field K over F and
  every prime p of `K ⊗[F] (F ⊗[D] E)`, requiring that its localization be an
  `IsDomain` and `IsIntegrallyClosed`. Swapping the tensor factors identifies
  this ring with `(E ⊗[D] F) ⊗[F] K`. No domain assumption is imposed on E or E_F.
- Finite field extension L/F: the existential `L`, `Field L`, `Algebra F L`,
  and `FiniteDimensional F L`. The existential `Algebra D L` and
  `IsScalarTower D F L` specify the composite D-algebra structure; this is the
  unique compatible structure, not an additional mathematical restriction.
  No separability assumption occurs.
- R is exactly `integralClosure D L`: Mathlib's carrier is `IsIntegral D`,
  namely roots of monic polynomials over D. No arbitrary integral model is chosen.
- E_R is `normalizedReductionBase D E L`, definitionally `R ⊗[D] E`, the
  factor-swapped version of the node's `E ⊗[D] R`.
- The ambient generic ring is `normalizedReductionGeneric D E L`, definitionally
  `E_R ⊗[R] L`. Tensor cancellation identifies this with `E ⊗[D] L`, and then
  with `(E ⊗[D] F) ⊗[F] L`. Mathlib's `Algebra.TensorProduct.comm`, `assoc`
  and `cancelBaseChange` give these canonical identifications. E_R maps to the
  ambient ring by `Algebra.TensorProduct.includeLeft`; under these identifications
  it is precisely the node's inclusion, whose injectivity follows from flatness.
- C is literally `normalizedReductionClosure D E L`, definitionally
  `integralClosure E_R (E_R ⊗[R] L)`. Its canonical module and algebra structures
  come from Mathlib's `Subalgebra` instances and the tensor scalar towers.
- Finite C over E_R: `Module.Finite (normalizedReductionBase D E L)
  (normalizedReductionClosure D E L)`.
- Finitely generated flat R-algebra: `FiniteType R C` and `Module.Flat R C`.
- Normal C: the inline condition at every prime localization, exactly as the
  recorded normal-ring dependency prescribes.
- The natural generic map is an isomorphism: `Function.Bijective
  (normalizedReductionGenericMap D E L)`. This is a specified algebra homomorphism,
  hence bijectivity is exactly invertibility. On a pure tensor it is c tensor l
  mapped to the inclusion of c multiplied by `includeRight l`. After swapping
  factors the source is the node's `C ⊗[R] L` and the target is its generic ring.
- Every maximal n and every extension Omega of R/n: the final universal
  quantifiers use `[n.IsMaximal]`, `[Field Ω]`, `[Algebra (R ⧸ n) Ω]`.
  `IsReduced (Ω ⊗[R ⧸ n] ((R ⧸ n) ⊗[R] C))` is exactly reducedness of the
  node's `(C/nC) ⊗[R/n] Ω`: `quotIdealMapEquivQuotTensor` identifies the inner
  tensor with C/nC, and tensor commutativity gives the displayed outer order.
- The zero algebra is allowed: no `Nontrivial E`, `IsDomain E`, or
  `FaithfulSMul D E` assumption occurs. C may be the zero ring, normality is
  vacuous at its empty prime spectrum, and `IsReduced` admits zero rings.

The independent input universes are `u` for D, `v` for F, `w` for E.
Test fields and the existential finite extension live in `Type (max u v w)`.
Thus the field tests are not restricted to a universe below either coefficient
or algebra universe. As usual, scalar extensions and field lifts transport
these predicates to larger universes; finite type and finite extension allow
representatives in this common universe. No site or coefficient universes are
identified.

Recorded statement-dependency declarations read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`.
- `def-weil-pbc-adically-complete-ring`: `IsAdicComplete`,
  `Mathlib.RingTheory.AdicCompletion.Basic`.
- `def-weil-pbc-flat-ring-map`: `Module.Flat`, in the imported
  `Mathlib.RingTheory.RingHom.Flat` interface. `RingHom.flat_algebraMap_iff`
  identifies this with flatness of the structure ring map.
- `def-weil-pbc-normal-ring`: `IsIntegrallyClosed`,
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, with `IsDomain` and
  `Localization.AtPrime` from `Mathlib.RingTheory.Localization.AtPrime.Basic`.
  The recorded inline normal-ring form is used verbatim.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`.

All currently recorded proof modules are imported privately, including the
finite-normalization, Nagata, total-fraction, normality, height, flatness and
associated-prime ingredients. The following proof dependencies have no recorded
Lean module on this base, so there is no corresponding import yet:
`lem-per-complete-dvr-finite-normalization`,
`lem-per-epp-common-finite-trait-extension`,
`lem-sfb-epp-essentially-finite-type-traits`. They are proof prerequisites,
not missing notions in this statement. Their uses, and all nine proof steps,
are included in the theorem docstring. No proof is supplied in stage 2.

Source reading: opened Prasad--Yu at https://arxiv.org/pdf/math/0405381,
Appendix Theorem A.2 and Remark A.3 (PDF p.27, printed p.27), and the local
`literature/stacks-project/more-morphisms.tex`, setup and proof of
`theorem-normalized-base-change-with-reduced-fibre` (Tag 09IL). The geometric
normality assumption specializes the source so normalization leaves the generic
ring unchanged. No source-based statement correction was needed.

Edge cases checked before and after drafting: E = 0; disconnected normal
algebras and empty component sets; E with the uniformizer invertible (empty
special fibre); inseparable finite L/F; imperfect residue fields; characteristic
zero and positive characteristic. The statement never assumes irreducibility,
separability, a nonempty special fibre, or a nonzero algebra. The residue-field
extension is arbitrary, not just finite, algebraic or algebraically closed.

Searches for existing statements (the msearch wrapper was used with group NO
and this item):

- `leanfinder`: "Flat finite type algebra over a complete discrete valuation ring
  with geometrically normal generic fibre admits finite base extension with
  normalized base change having geometrically reduced fibres". Eight hits,
  including `Algebra.IsGeometricallyReduced`, smooth finite-type descent, and
  flat going down; none is this theorem.
- `leansearch`: "Raynaud Faltings reduced fibres after finite extension of a
  complete discrete valuation field". Eight hits, primarily
  `Algebra.IsGeometricallyReduced` and Weierstrass good reduction; none matches.
- `loogle`: `"integralClosure", "TensorProduct"`. Seven hits, including
  `TensorProduct.toIntegralClosure` and its smooth/localization bijectivity
  theorems. Those compare base change with integral closure and do not assert
  reduced fibres after a finite extension of a DVR fraction field.
- `grep` through msearch: `Raynaud|Faltings|normalized.*reduc|reduc.*normali`,
  under Mathlib `RingTheory`. Only unrelated normalized-factor lemmas and an
  etale descent attribution to Raynaud--Gruson were returned.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `raynaud|Raynaud|Faltings|normalized_reduction|geometrically.*normal`, and
  `rg -n 'lem-sfb-raynaud-faltings-normalized-reduction' lean/WeilConjectures`.
  No statement of the item exists. `DvrNormalGenericReducedSpecial` is the
  converse normality criterion, and the geometrically-normal tensor lemmas
  preserve normality but do not produce reduced special fibres.
- Read the existing `integralClosure`, `Algebra.TensorProduct.productMap`,
  `includeLeft`, `includeRight`, `cancelBaseChange`, and quotient-tensor
  equivalence definitions directly; reused all underlying notions.

No statement dispute, changed node statement, dependency repair, or new DAG node.

## Second reading by NO

Reread the complete node and the delivered Lean file clause by clause. The
completeness ideal is the maximal ideal of D; F is its fraction field; E is
finite type and flat. Geometric normality uses all field extensions and the
recorded prime-localization definition, including non-domains and the zero ring.
The finite L/F is unrestricted by separability and its D-action is forced by the
scalar tower. R and C are actual Mathlib integral closures. E_R and the generic
ring differ from the displayed tensor expressions only by canonical tensor
commutativity, associativity and cancellation, with no alternative model or
arbitrary map substituted. The conclusion separately includes finite C/E_R,
finite type C/R, flat C/R, normal C, bijectivity of the canonical generic map,
and reducedness after every special residue-field extension. The nested residue
tensor is C/nC by the canonical quotient-tensor isomorphism; it includes empty
fibres. No hypothesis or conclusion was added or dropped. All helper data is
explicit; only the theorem proof is postponed. This is the worker's second
reading; the maintainer supplies the independent delivery review as required by
the dispatcher brief, which prohibits starting additional agents.

Validation: `scompile.py NO lem-sfb-raynaud-faltings-normalized-reduction
<module.lean>` passed both the sandbox and library module checks on the server.
There were no compiler errors or non-sorry warnings. The only subsequent source
change before dry run adds the explicit public import of the recorded
`Mathlib.Algebra.Algebra.Defs` dependency; dry run recompiles the final file.
