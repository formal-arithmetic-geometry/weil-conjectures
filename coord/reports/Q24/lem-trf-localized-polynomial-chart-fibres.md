## Worker report

The module `Sheaf.RingTheory.LocalizedPolynomialChartFibres` states
`Algebra.exists_localizedPolynomialChart_fibres`, with its proof consisting only of
`sorry`. The helper `Algebra.localizedPolynomialChartFieldMap` constructs the
induced field-fibre polynomial map using `MvPolynomial.aeval`; its data contain
no postponed proof. It belongs to this node's canonical field-map construction,
not to a second independent notion. Both declarations are listed in
`lean.declarations`. No dependency records, new nodes, or mathematical statements
are changed.

Source read: `literature/stacks-project/algebra.tex`, Tag 00QE,
`lemma-quasi-finite-over-polynomial-algebra`, statement and proof, and Tag 00QK,
`lemma-finite-type-domain-over-valuation-ring-dim-fibres`, statement and proof.
The latter uses precisely this polynomial chart and its two fibre maps. The
local-ring chart assertion is the application of 00QE recorded in the node;
it does not require the valuation-ring hypothesis used later in 00QK's dimension
argument. Also read the current blueprint ancestor and its proof under
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`.
This item is an auxiliary algebra assertion, not the blueprint unit's statement.
The example CompactObject module has been withdrawn and contains no declarations;
its node currently binds the existing compact-object notion. The new module
follows the current module/public-import/public-section instructions.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Commutative local ring A, unique maximal ideal m, residue field k | `(A : Type u) [CommRing A] [IsLocalRing A]`; `IsLocalRing.ResidueField A` is the quotient by `IsLocalRing.maximalIdeal A`, not an independently chosen field. |
| Finite type commutative A-algebra D | `(D : Type v) [CommRing D] [Algebra A D] [Algebra.FiniteType A D]`. |
| E = D tensor k and Q prime | `Q : PrimeSpectrum (IsLocalRing.ResidueField A ⊗[A] D)`. Tensor factors are exchanged by Mathlib's canonical `Algebra.TensorProduct.comm A D k`; Q denotes the corresponding prime. This is a change of representation, not an extra assumption. |
| q is the inverse image in D | `Q.comap (TensorProduct.includeRight ...).toRingHom`, appearing directly in the condition on g. Here includeRight is `d ↦ 1 ⊗ d`. |
| Finite nonnegative local dimension n | `(n : ℕ)` and `hdim : topologicalKrullDimAt Q = (n : WithBot ℕ∞)`. This is dimension at a point, not prime height or dimension of the local ring. |
| g avoids q and B = D_g | Existential g with the displayed nonmembership; B is always `Localization.Away g`. |
| A-algebra polynomial chart | `α : MvPolynomial (Fin n) A →ₐ[A] Localization.Away g`; no injectivity of α is assumed. |
| B finite type over A | First conjunct `Algebra.FiniteType A (Localization.Away g)`. |
| α finite type and quasi-finite at every prime | Existential `hft : α.toRingHom.FiniteType` and the next conjunct, `∀ p, @IsQuasiFiniteAtPrime ... α.toRingHom.toAlgebra hft p`. This uses the dependency's isolated-fibre-point definition. |
| Every A-field c and its induced α_c | `∀ (c : Type w) [Field c] [Algebra A c]`; the helper evaluates each variable at `1 ⊗ α(X i)`. Coefficients use the c-algebra structure. The conclusion is universe-polymorphic in w, with no hypothesis quantifying over a potentially empty class of test fields. |
| α_c finite type and quasi-finite at every prime | `∃ hftc : ...toRingHom.FiniteType`, followed by the universal `@IsQuasiFiniteAtPrime` clause with that exact map and finite-type proof. |
| Fibre target finite type over c | `Algebra.FiniteType c (c ⊗[A] Localization.Away g)`. |
| Canonical c-algebra localization isomorphism | Existential `e : c ⊗[A] Localization.Away g ≃ₐ[c] Localization.Away (1 ⊗ g)` with the complete fraction formula for every d, j, and a. Its formula is `a ⊗ (d/g^j) ↦ (a ⊗ d)/(1 ⊗ g)^j`, with `IsLocalization.mk'` and explicitly specified powers submonoids. Since all b in B have fraction representatives and pure tensors span, this characterizes the canonical map, rather than choosing an unconstrained equivalence. By multiplicativity, this is exactly the product-of-images formula in the node. |
| At c=k, spectrum identifies with the basic open | Existential homeomorphism from `PrimeSpectrum (k ⊗[A] B)` onto `PrimeSpectrum.basicOpen (1 ⊗ g)`. Its underlying map is required to be comap of `TensorProduct.map (AlgHom.id A k) (IsScalarTower.toAlgHom A D B)`, the canonical localization base-change map. Thus it is the stipulated identification, not an arbitrary homeomorphism. |
| Q corresponds to Q_g and local dimension stays n | Existential `Qg`, `(e Qg).val = Q`, and `topologicalKrullDimAt Qg = (n : WithBot ℕ∞)`. The homeomorphism makes the corresponding prime unique. |
| Optional domain inclusion A subset D | Final conditional `∀ [IsDomain A] [IsDomain D], Function.Injective (algebraMap A D) → ...`. These are conditions only on this final clause, not on the local-ring chart. |
| g nonzero; B domain containing A | `g ≠ 0 ∧ IsDomain (Localization.Away g) ∧ Function.Injective (algebraMap A (Localization.Away g))`. |
| K = Frac(A), F = D tensor K, H = B tensor K | `FractionRing A`, `FractionRing A ⊗[A] D`, and `FractionRing A ⊗[A] Localization.Away g`, again using canonical tensor symmetry. |
| H is a nonzero domain and H is isomorphic to F localized at g | `IsDomain` for the generic fibres (in particular H includes nontriviality) and `Nonempty (H ≃ₐ[FractionRing A] Localization.Away (1 ⊗ g))`. The F domain clause makes explicit the domain implicit in the node's field-of-fractions notation. |
| Fraction fields isomorphic over K | `Nonempty (FractionRing H ≃ₐ[FractionRing A] FractionRing F)`, using the structural algebras obtained by localization. |

Dependency declarations read and used:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` (the dependency's recorded
  bare-map interface) and `Algebra.FiniteType` (finite algebra generation).
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, the quotient
  construction; the commutative algebra structures and the inclusions come from
  `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`, exposed by BaseChange.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`;
  the theorem uses their underlying prime spectra, since the clauses concern
  topology and dimension only.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`,
  the infimum over open neighbourhoods, and proof dependency
  `IsOpen.topologicalKrullDimAt_eq`.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`,
  `MvPolynomial.aeval`, `MvPolynomial.algHom_ext`.
- `Mathlib.GroupTheory.MonoidLocalization.Away` and
  `Mathlib.RingTheory.Localization.Away.Basic`: `Localization.Away` and
  `IsLocalization.Away`, with the ring/algebra structures.
- `WeilConjectures.RingTheory.QuasiFiniteAtPrime`:
  `Algebra.IsQuasiFiniteAtPrime`. Its full signature and isolated-point
  docstring were read; Mathlib's differently presented predicate is not
  substituted.
- The two non-Mathlib proof interfaces are imported as plain proof imports:
  `Sheaf.Paper.QuasiFiniteOverPolynomialAlgebra`,
  `Algebra.exists_quasiFinite_over_polynomial_algebra`; and
  `WeilConjectures.RingTheory.QuasiFiniteFourRings`,
  `Algebra.finiteType_and_isQuasiFiniteAtPrime_of_four_rings`.
- Other recorded proof interfaces read: `PrimeSpectrum.preimageOrderIsoFiber`
  and the fibre prime formulas (LocalRing.ResidueField.Fiber);
  `Algebra.TensorProduct.productMap`/`ext` (tensor universal property);
  `MvPolynomial.algebraTensorAlgEquiv` (TensorProduct.MvPolynomial, proof import);
  `IsLocalization.Away.tensorProductEquivTMulRight` and its tmul formula
  (Localization.BaseChange);
  `PrimeSpectrum.localization_comap_isEmbedding`/`localization_comap_range`
  (Spectrum.Prime.Topology);
  `IsLocalization.tensor`/`tensorRight`,
  `IsLocalization.isDomain_of_le_nonZeroDivisors`, and
  `PrimeSpectrum.irreducibleSpace` (generic localization);
  `IsLocalization.lift`/`ringHom_ext` (Localization.Defs).
  These Mathlib modules are exposed by the public dependency imports; no
  duplicate interfaces are declared.

Edge cases checked before and after drafting:

- n=0 uses `Fin 0`; the polynomial algebra has no variables. The helper is
  still evaluation of the empty family. No positive-dimension assumption appears.
- Q itself rules out a zero special-fibre ring. No nontriviality assumption on
  general D, no nonzero assumption on g, and no domain assumption are added to
  the chart clause. The optional domain clause proves g nonzero separately.
- For an arbitrary A-field c, g may vanish on the entire fibre, so its
  localization and the fibre target may be zero. Their spectra are empty and
  the quasi-finiteness clauses are universal over the empty spectrum; no
  nontriviality or injectivity is imposed on that field map.
- Nilpotents and positive characteristic are permitted. The fraction formula
  allows j=0, d=0, a=0 and nilpotent g. It uses the actual localization rather
  than division in a presumed field.
- The special-field case has a separately stated canonical homeomorphism and
  Qg clause and is never discarded by a universe choice. The generic-field
  case is also stated explicitly, including both domain and inclusion
  conclusions. The arbitrary-field clause is polymorphic in its own w, so
  includes identity, residue-field and arbitrary-extension maps.
- In the domain clause, injectivity of A into D is required precisely where
  the node says A is a subring. Being a domain alone would not express that.
- Tensor symmetry exchanges `g ⊗ 1` with `1 ⊗ g`, the coefficient structure
  maps with the displayed c-algebra maps, and contracted primes with the
  includeRight prime used here. It changes none of the clauses.

Searches run (service searches use the prescribed msearch wrapper for Q24 and this item):

1. `leanfinder`: "A finite type algebra over a local ring has a principal
   localization quasi finite over a polynomial algebra in the dimension of its
   special fibre, compatible with all field fibres". Eight hits, including
   `Algebra.QuasiFiniteAt`, `Algebra.quasiFinite_iff` and localization facts.
   No theorem constructs this dimension-prescribed chart and states the fibre
   comparisons.
2. `loogle`: "Algebra.IsQuasiFiniteAtPrime, MvPolynomial". Zero hits; diagnostic
   says the project-specific identifier is unknown to Loogle. This is a
   service index limitation, not evidence against the existing project notion.
3. `loogle`: "Algebra.QuasiFinite, MvPolynomial". Zero hits.
4. `grep`: `quasiFinite.*[Pp]olynomial|[Pp]olynomial.*quasiFinite`. Seven hits
   in Mathlib QuasiFinite/Polynomial, QuasiFinite/Basic and ZariskisMainTheorem.
   They concern individual quasi-finite maps and polynomial arguments, not this
   combined chart-and-fibres statement.
5. `leansearch`: "Finite type algebra over local ring principal localization
   quasi finite polynomial algebra with dimension equal to special fibre local
   dimension". Eight hits: general `RingHom.QuasiFinite` and permanence lemmas,
   no exact statement.
6. `rg` of the project RingTheory modules for polynomial charts and
   quasi-finiteness found the existing QuasiFiniteAtPrime interface and the
   recorded polynomial-chart theorem. `rg` of `lean/WeilConjectures`,
   `lean/Sheaf` and `dag/lean_names_upstream.json` for this node's id and the
   proposed declaration names found no existing attachment or name collision.
   The prescribed `grep -rn` of the node id in `lean/WeilConjectures` also
   returned no matches.
   `rg` of the upstream name table for QuasiFinite confirmed the existing
   dependency interface rather than any complete chart-fibres theorem.

Validation: scompile.py successfully compiled this file in both sandbox module
mode and its final library module mode (2.6 s and 2.4 s respectively). Explicit
powers submonoids fixed the only denominator inference issue. There are no
errors or unexpected warnings. `set_option autoImplicit false` checks that no
variable or universe is silently introduced. Every line is at most 100 columns.
There is no STATEMENT-DISPUTED issue or statement correction.
The prescribed deliver2.py --no-push dry run also returned OK: its preflight
and compilation passed for commit 9d6c07a152d, with only the item node, module
and report staged.

## Second reading by Q24

I reread the unchanged node and the complete final module after compilation.
This is the dispatcher's single-worker final pass; no second agent was started.
The maintainer performs the independent delivery review.

I checked that the local-ring and finite-type assumptions occur before the
existential, whereas the domain/injectivity assumptions occur only inside the
last conditional conjunct. Thus the general local-ring clause is retained.
The q in the node is exactly the contraction through includeRight in the g
condition. The dimension uses the minimum of open-neighbourhood dimensions,
not the dimension of a localization at Q. The number of variables is exactly n,
including zero. Both α and α_c use the recorded quasi-finite predicate with
the finite-type proof belonging to that exact map.

I checked each part of the field clause against the source: evaluation on
variables fixes the induced map; the c-algebra structure fixes coefficients;
the fraction formula fixes the comparison isomorphism on all elements rather
than just constants. In the special clause the underlying homeomorphism is
explicitly the canonical comap, and its image point equals Q before the
local-dimension assertion. In the generic clause all three inclusion/domain
claims, the localized-generic-fibre isomorphism and the equivalence of fraction
fields over K occur explicitly. The last equivalence is an algebra equivalence
over K, not merely a ring equivalence. No hypothesis on α being injective, no
valuation-ring restriction and no nonzero-field-fibre restriction were added.

The final pass retained the canonical symmetry convention for tensor products
and checked its effect on every point and scalar map. No mathematical change
was needed; the only drafting repairs were a reserved identifier and the
explicit localization submonoids required for elaboration.
