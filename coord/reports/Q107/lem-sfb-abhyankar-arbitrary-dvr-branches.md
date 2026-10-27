## Worker report

The module `Sheaf.RingTheory.AbhyankarArbitraryDvrBranches` states
`RingTheory.abhyankar_arbitrary_dvr_branches`, with its sole postponed proof `sorry`.
The node statement and its dependencies are unchanged. Its two public helpers belong to
this normalization diagram: `AbhyankarReducedTensor` abbreviates the actual quotient
`(L ⊗[K] N) ⧸ nilradical (L ⊗[K] N)`, and `abhyankarNormalizationMap` constructs
the actual map `integralClosure A N →+* integralClosure B (AbhyankarReducedTensor K L N)`.
It sends an integral element x to the reduction of `1 ⊗ x`. The integrality witness uses
`IsIntegral.map` for the right tensor inclusion and quotient, then `IsIntegral.tower_top`
for A → B. Ring-homomorphism fields are existing map identities. Neither helper
contains postponed proof or chosen unspecified data. They introduce no independent notion.

Hypotheses and conclusion, clause by clause:

- A and B are commutative domains and DVRs: `[CommRing A] [CommRing B]`,
  `[IsDomain A] [IsDomain B]`, and both `[IsDiscreteValuationRing ...]` binders.
- The injective local map A → B is `[Algebra A B]`, `hinj`, and
  `[IsLocalHom (algebraMap A B)]`. This local-hom class says that units are reflected,
  equivalently that the maximal ideal pulls back to the maximal ideal.
- K and L are fraction fields: `[Field K] [Field L]`, their algebra structures,
  `[IsFractionRing A K] [IsFractionRing B L]`. `[Algebra K L]` is the field embedding.
  `[Algebra A L]` and the two scalar towers make precisely the compatibility square
  of this fraction-field extension; they specify representation, not extra finiteness.
- The index is `(e : ℕ)`, `he : 1 ≤ e`, and `hindex`, the stated equality of ideals
  `(maximalIdeal A).map (algebraMap A B) = maximalIdeal B ^ e`.
- The first allowed residue characteristic is `CharZero (IsLocalRing.ResidueField A)`.
  No residue separability is imposed in that branch. The second is the existential
  prime p with `CharP ... p`, `¬ p ∣ e`, and `Algebra.IsSeparableExtension` of the two
  local residue fields. Their algebra structure is Mathlib's induced residue map
  from the specified local A → B. This uses the project's possibly transcendental
  separability definition, not the algebraic-separability class.
- Any finite field extension N/K is `[Field N] [Algebra K N] [FiniteDimensional K N]`.
  `[Algebra A N] [IsScalarTower A K N]` express the restricted A-algebra structure.
  No separability is required of N/K.
- R is literally `integralClosure A N`; C is literally
  `integralClosure B (AbhyankarReducedTensor K L N)`. All subsequent occurrences use
  these very constructions. The reduction quotients all nilpotents, including in the
  inseparable case. The base B-algebra acts through B → L → L tensor_K N → its quotient.
- Every maximal ideal of C is covered by `(q : Ideal C) [q.IsMaximal]`. Its contraction
  n is `q.comap (abhyankarNormalizationMap A B K L N)`. No ideal over the closed point
  is separately assumed. Primality of n is inferred by the standard comap instance.
- The first conjunct is exactly `n.IsMaximal`. The existential domain structures for
  `Localization.AtPrime n` and `Localization.AtPrime q` allow the two ensuing
  `IsDiscreteValuationRing` assertions to be typed; these are returned conclusions,
  not assumptions. Mathlib's DVR class takes the domain structure as a parameter.
- The conditional part quantifies over every d with `1 ≤ d` and `e ∣ d`. Its premise
  maps `maximalIdeal A` along A → R → R_n and equates it to the d-th power of the
  image of n along R → R_n. This is precisely m_A R_n=(nR_n)^d.
- The final equality maps n along R → C → C_q and maps q along C → C_q.
  It therefore says exactly nC_q=qC_q. There is no additional residue-field or
  formal-smoothness conclusion.
- All five object universes are explicit and independent; `autoImplicit` is false.
  No finite-dimensional condition is imposed on L/K, no module-finite condition on
  either normalization, and no completeness or essential finite type assumption occurs.

Dependency declarations read and used:

- `def-sc-discrete-valuation-ring`: Mathlib.RingTheory.DiscreteValuationRing.Basic,
  `IsDiscreteValuationRing`, its explicit domain argument and its local PID definition.
- `def-pc-field-extension`: Mathlib.Algebra.Algebra.Defs, `Algebra`, with fields on both
  sides. The specified fraction-field square is expressed using `IsScalarTower`.
- `def-weil-pbc-integral-closure`: Mathlib.RingTheory.IntegralClosure.Algebra.Basic,
  `integralClosure` and `IsIntegral`, publicly exposed through
  Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic. The carrier is exactly
  integral elements, with actual ring data.
- `def-weil-pbc-module-tensor-product`: Mathlib.LinearAlgebra.TensorProduct.Defs,
  `TensorProduct`; its canonical algebra structure and `Algebra.TensorProduct.includeRight`
  come from Mathlib.RingTheory.TensorProduct.Basic.
- `def-weil-pbc-localization-at-prime`: Mathlib.RingTheory.Localization.AtPrime.Basic,
  `Localization.AtPrime`, the localization at the complement of a prime. Residue fields
  in the hypothesis use Mathlib.RingTheory.LocalRing.ResidueField.Basic,
  `IsLocalRing.ResidueField` and its induced local-hom algebra instance.
- `def-weil-pbc-separable-field-extension`: WeilConjectures.FieldTheory.SeparableExtension,
  `Algebra.IsSeparableExtension`, read in full: every intermediate field F with F.FG is
  `Algebra.IsSeparablyGenerated`. That definition uses a transcendence basis and
  algebraic separability over its generated intermediate field.

Proof imports are the recorded modules of `lem-sbc-dvr-uniformizer-root-algebra`,
`lem-sfb-unit-binomial-finite-etale`, `lem-sfb-finite-etale-normal-generic-components`,
`lem-weil-pbc-etale-fibre-discrete-separable-points`, and the Mathlib matches for
`lem-weil-pbc-char-zero-field-extension-separable` and
`lem-weil-pbc-integral-closure-commutes-localization`. Integral transitivity is available
from the already public IsIntegralClosure.Basic module. The four proof inputs
`lem-sfb-dvr-algebraic-normalization-structure`, `lem-sfb-dvr-unit-root-normalized-lift`,
`lem-sfb-separable-finite-top-extension`, and `lem-sfb-dvr-index-one-separable-base-change`
have no recorded declaration or Mathlib match in the read DAG; no nonexistent module is
imported. They are used in the complete seven-step natural-language proof docstring.
They are proof prerequisites only and are not needed to type this stage-2 statement.

Edge cases checked before writing and rechecked against the signature:

- e=1 is included: any positive d satisfies the divisibility requirement. The residue
  characteristic conditions are retained even in this case, exactly as the node says.
- d=1 is included; the divisibility condition then forces e=1.
- N=K is included, with no degree-greater-than-one condition.
- Purely inseparable finite N/K is included; tensor nilpotents are actually quotiented.
- L/K and the residue extension may be transcendental. There is no algebraic-separability
  assumption substituted for `IsSeparableExtension`.
- Residue characteristic zero is accepted without a separability binder, and equal or
  mixed positive residue characteristic is accepted with the prime-to-e condition.
- Zero rings and fields do not satisfy the DVR hypotheses, as in the node definition.
- No assumption that normalization is finite, complete, or of finite type occurs.
- Maximal q is arbitrary. The conclusion first produces maximality of its contraction,
  then both DVR structures, before the cancellation implication.

Sources read: local Stacks `more-algebra.tex`, Remark 09EM, lemma-abhyankar (0BRM) and
its unit-root proof; the statement is its maximal-ideal consequence via 09E7.
The full existing upstream local Abhyankar signatures were compared: the
`DvrAbhyankarLocalMaximalIdeal` and `DvrAbhyankarNormalizedFactor` statements require
finite module normalizations or finite separable generic extensions, so cannot supply
this node's unrestricted assertion. The current node is auxiliary, not a unit statement.
No statement correction or mathematical dispute was found.

Searches for an existing statement (2026-10-24):

- msearch leanfinder, query “Abhyankar lemma tame ramification of arbitrary local discrete
  valuation rings normalized tensor product branches”: eight hits, chiefly unramified
  base change and ramification-index formulas; no normalized arbitrary-DVR cancellation.
- msearch loogle, query `IsDiscreteValuationRing, Algebra.IsSeparable`: zero hits.
- msearch grep, query `abhyankar|ramificationIdx.*dvd|dvd.*ramificationIdx` in RingTheory:
  five hits, all ramification-index divisibility results, no cancellation statement.
- msearch leansearch, query “Abhyankar lemma tame extension discrete valuation rings
  normalization tensor product ramification index one”: eight hits, unramifiedness
  criteria and index formulas with stronger hypotheses; none matches the assertion.
- rg over both project roots for `abhyankar` found the related upstream declarations
  discussed above and specialized root-divisor applications; none states this node.
- Search for the exact item id in WeilConjectures returned no match. Search for
  `abhyankar_arbitrary_dvr_branches|abhyankarNormalizationMap|AbhyankarReducedTensor`
  in WeilConjectures, Sheaf and dag/lean_names_upstream.json returned no match.
- Searched the integral-closure API for maps/lifts. Existing `AlgHom.mapIntegralClosure`
  keeps the same base ring; it cannot directly express changing A to B. The helper here
  restricts the canonical tensor/quotient map and uses existing integrality lemmas.

Validation: the prescribed scompile.py wrapper accepted the module in both its sandbox
and actual library namespace, without errors or warnings (3.9 s and 3.3 s respectively).
The only theorem proof is `sorry`, and all definitions have real data.

## Second reading by Q107

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
