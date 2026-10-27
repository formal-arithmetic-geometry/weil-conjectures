## Worker report

Stage 2, Q78, lem-trf-polynomial-monoid-lift-stratum. The module
`Sheaf.RingTheory.PolynomialMonoidLiftStratum` states
`ToricMonoid.polynomialMonoidLiftStratum`, with one postponed theorem and real
helper definitions. The live Q86 review is the stage-1 split, not a Lean landing:
the live node has no lean record. The stage-2 handoff in brief-stage2 §0 explicitly
permits stating this reviewed split. No repair note exists. The accepted statement,
proof, proof dependencies, and stage-1 review are preserved. The sole additional
statement dependency is the already landed `def-trf-complete-toric-model`, whose
published completion and ideal constructions are used without copying them.

Source read: ILO VI 1.6, printed page 70 (PDF page 76), including both the equal
characteristic model and the Cohen quotient with parameter congruent to p. The
polynomial-lift and residue-stratum calculation is the node's explicitly
agent-supplied auxiliary argument, not a claim that ILO states this whole lemma.
I also read the current blueprint/latest locality statement and proof: the source
chain is historical, as blueprint.from.place and the accepted split already say.

Hypotheses and objects, clause by clause:

- L is a commutative local ring with `hL : IsField L ∨ ∃ p : ℕ, IsCohenRing p L`.
  A field has its unique local-ring structure; the explicit local-ring instance
  merely supplies its maximal ideal and also covers the Cohen case. No field
  characteristic is restricted. Cohen rings are the recorded `IsCohenRing`.
- S and T are independent types with `AddCommMonoid` instances. `hS` and `hT`
  use the published `AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative _)`.
  The multiplicative type tag changes notation only. `hsharpS`, `hsharpT` say an
  invertible element must be zero. Zero is always invertible in the type tag.
- K has `AddCommGroup`, `Module.Free ℤ K`, and `Module.Finite ℤ K` instances:
  precisely a finite free abelian group, including rank zero. P is the product
  `K × T`, the finite direct sum. `f : S →+ K × T` is the specified homomorphism;
  its two projections are delta and beta, and `hβ` says `(f s).2 ≠ 0` if `s ≠ 0`.
- `n : ℕ` includes zero and `Fin n` indexes all polynomial variables. The
  existing `PolynomialRing L S n` is R0 = L[S][t], `completionIdeal L S n`
  is I = (m_L,[s] for s ≠ 0,t), and `Complete L S n` is its adic completion H_S.
- E is `PolynomialRing L K n` and U is `PolynomialRing L (K × T) n`.
  Mathlib's finite-support `AddMonoidAlgebra` has multiplication [u][v]=[u+v].
  Thus U also realizes E[T], through the canonical finite-product monoid-ring
  rearrangement; no extra isomorphism datum is assumed.
- `polynomialChartMap L n f` is `MvPolynomial.map` of
  `AddMonoidAlgebra.mapDomainRingHom L f`. It sends [s] to [f(s)], equivalently
  [delta(s)][beta(s)], fixes L, and fixes every variable. `integerChartMap`
  uses integer coefficient inclusion followed by polynomial constants.
- `PolynomialLift L S (K × T) n f` is W = H_S tensor over R0 with U, using
  the algebra induced by this actual chart map, not an arbitrary scalar action.
  `IntegerPolynomialLift` likewise constructs both canonical ℤ[S]-actions.
  `polynomialLiftLeft`, `polynomialLiftRight` and both tensor-element helpers
  are the standard TensorProduct inclusions and pure tensors with these actions.
  `polynomialLiftIdeal` extends I through R0 → U → W, hence is IW.

Conclusions, in the order of the Lean conjunction:

1. `(completionIdeal L S n).FG` is finite generation of I. The following four
   `IsNoetherianRing` terms assert Noetherianity of R0, U, H_S and W, respectively.
2. A ring equivalence W → IntegerPolynomialLift is required with both displayed
   formulas. On `x ⊗ MvPolynomial.monomial d (single p l)` it gives
   `(x * image (MvPolynomial.monomial d (single 0 l))) ⊗ single p 1`, exactly
   x tensor l[p]t^d ↦ xlt^d tensor [p]. Its inverse fixes x tensor [p] in the
   stated sense. Exponents are arbitrary `Fin n →₀ ℕ`, so these cover all terms.
3. The equivalence W/IW → U/IU is required to take the image of every u under
   U → W to its class modulo IU. Its inverse is therefore the specified
   canonical U-algebra map. The commutation condition specifies canonicity.
4. `N : PrimeSpectrum W` supplies primality, and the ideal-inclusion hypothesis
   says N contains the images of `(m_L,t)` and every nonzero T-monomial.
   `polynomialParameterIdeal` is the former ideal; `polynomialStratumIdeal`
   spans exactly `C (single (0,t) 1)` for t ≠ 0. Quantified primes p and r are
   constrained by equalities to contraction along E → U → W and U → W.
   Contractions of prime ideals along these unital ring maps are prime, so this
   formulation introduces no existence hypothesis or restriction on N.
5. `polynomialParameterIdeal L K n ≤ p.asIdeal` says p contains `(m_L,t)`.
   `r.asIdeal = Ideal.map (polynomialChartMap ... inl) p.asIdeal ⊔
   polynomialStratumIdeal ...` is r = pU + ([v]: v ≠ 0).
   The next inclusion is IU ⊆ r. The next gives IW ⊆ N, making explicit that
   N itself lies in the class in which the following uniqueness is asserted.
6. Every prime N' of W with contraction r and containing IW equals N. This is
   uniqueness over r among primes containing IW; it does not assert uniqueness
   among all primes or impose a maximal-ideal hypothesis.
7. The first residue equivalence N.ResidueField → r.ResidueField has inverse
   exactly `Ideal.ResidueField.map r N polynomialLiftRight hr`. The second is
   r.ResidueField → `FractionRing (E ⧸ p.asIdeal)` and agrees on all a in E
   with the canonical E → E/p → FractionRing(E/p) map. Images of E generate
   this field as a field (U/r = E/p in the mathematical proof), so the equation
   specifies the intended residue-field identification, not an abstract isomorphism.
8. For every natural residue prime p0 with `IsCohenRing p0 L`, and every theta
   with `theta - (p0 : Complete ...) ∈ completedChartIdeal ...`, the image of
   theta belongs to N. `HasCompatibleQuotientResidueField W N imageTheta`
   then expands to a prime q of W/(imageTheta) contracting to N and an
   equivalence of their residue fields, commuting with the images of every
   element of W. The prime q is necessarily N/(theta), and its residue field
   is by definition that of the local ring (W/(theta))_q. Hence this is exactly
   the final local-quotient residue clause. The named predicate is only a
   transparent packaging of this clause with real Prop data; it assumes and
   proves nothing. It prevents expensive repeated elaboration of the large W
   expression inside a dependent quotient-residue-map equality.

Dependency declarations read and used:

- `WeilConjectures.RingTheory.CohenRing`: `IsCohenRing`, including Nat.Prime,
  the domain/DVR witnesses, maximalIdeal = span{p}, and p-adic completeness.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: its public log-structure
  interface, importing `Sheaf.AlgebraicGeometry.LogRegularPair` and its
  `AlgebraicGeometry.IsFineSaturatedMonoid`. The latter's definition is finite
  generation, injectivity into the canonical Grothendieck group, and saturation.
  No log-scheme hypothesis is introduced when using just the monoid predicate.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, reached through
  the published complete-model abbreviations, and its canonical algebra map.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and
  `Mathlib.RingTheory.TensorProduct.Basic`: `TensorProduct`, `TensorProduct.tmul`,
  and `Algebra.TensorProduct.includeRight`, `includeLeftRingHom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and ideal finite
  generation; no private notion of Noetherianity.
- `Mathlib.RingTheory.Localization.AtPrime.Basic` and
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Localization.AtPrime`,
  `Ideal.ResidueField` and `Ideal.ResidueField.map`; FractionRing is Mathlib's.
- `Sheaf.RingTheory.CompleteToricModel`: `ToricMonoid.PolynomialRing`,
  `completionIdeal`, `Complete`, `completedChartIdeal`. These reuse
  `AddMonoidAlgebra.localModelCompletionIdeal`, `CompletedLocalModel` and
  `completedLocalModelBoundaryIdeal` from LogRegularSaturationNormality.
- Plain proof imports: `Mathlib.RingTheory.AdicCompletion.Completeness`
  (`AdicCompletion.pow_smul_top_eq_ker_eval`, Tag 05GG),
  `Mathlib.RingTheory.FiniteType` (`Algebra.FiniteType.isNoetherianRing`),
  `Mathlib.RingTheory.Localization.Ideal` (localize-quotient interface, Tag 00CT),
  `WeilConjectures.RingTheory.AdicCompletionNoetherian`
  (`AdicCompletion.isNoetherianRing`, Tag 0316). These are all the stated proof
  tools in the accepted eight-step plan. The theorem docstring carries that plan.

Edge cases checked mathematically before finalizing:

- n = 0: Fin 0 is empty, so variable ideals vanish and the sole exponent is zero.
- S, T and K trivial, separately and jointly: all types remain inhabited by zero;
  no positive monomial is invented and all appropriate spans are bottom.
- T trivial forces S trivial by hβ. When S is trivial hβ is vacuous, as it should be.
- K of rank zero gives an ordinary T-monoid algebra; no positive rank is assumed.
- Field coefficients include positive characteristic and characteristic zero;
  maximalIdeal L = 0, so there is no extra coefficient parameter in I.
- The Cohen branch includes every prime p and every permitted theta, not just p
  itself; theta = p is allowed. The parameter image belongs to N before the
  residue field of the quotient is compared.
- N is arbitrary prime with the stratum inclusion, not necessarily maximal.
  Properness and domain quotients come from PrimeSpectrum, not extra assumptions.
- All four type universes u,v,w,z are explicitly bound and independent; no
  equality of coefficient, source monoid, target monoid, and lattice universes is used.

Searches (recorded by msearch in searches.jsonl, including inherited saved searches):

- LeanSearch, `polynomial monoid algebra adic completion tensor residue field
  Laurent stratum`: eight hits, including AdicCompletion and finite-module
  tensor-completion equivalences, plus unrelated LaurentSeries. No matching lemma.
- LeanFinder, `Polynomial monoid algebra completed at the maximal monomial ideal
  base change and residue field along the Laurent stratum` and
  `Completed monoid algebra polynomial lift tensor product Laurent closed stratum
  residue field`: LaurentSeries and polynomial/Laurent conversion hits; no match.
- Loogle, `"AdicCompletion", "TensorProduct"`: twelve hits, including
  `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`, which requires finite
  modules and identifies a different completion. None states this polynomial
  lift or its prime/residue calculations. The earlier query
  `AddMonoidAlgebra, MvPolynomial, AdicCompletion` returned no hits.
- Mathlib grep, `CompletedLocalModel|polynomialMonoid|PolynomialMonoid|
  baseChange.*[Cc]ompletion` in RingTheory: AsTensorProduct only; no exact statement.
  The follow-up `polynomialMonoidLift|polynomialChartMap|[Mm]onoid.*[Ss]tratum|
  HasCompatibleQuotientResidueField` found one unrelated Hahn-stratum comment.
- rg in the live WeilConjectures and Sheaf trees for the item id and the proposed
  declaration/helper names found no duplicate. Reading the existing toric files
  found exactly the completion model reused above. No new independent definition
  node or dependency repair is needed.

No statement correction or STATEMENT-DISPUTED issue was found. Nothing is proved;
the sole sorry is the full proof of the public theorem matching the item.

## Second reading by Q78

I made a separate clause-by-clause rereading of the live node, its eight proof
steps, the published dependency definitions, and the final module. No additional
agent was started, as required by the dispatch brief; the maintainer performs the
independent delivery review.

The rereading checked both tensor scalar actions rather than just their types:
R0 → U is precisely the extension of f fixing variables, and ℤ[S] → H_S is integer
coefficient inclusion into R0 followed by completion. This ensures the two tensor
formulas describe the same rings as the node. The first equivalence must specify
both directions, and both equations are present. The quotient equivalence is
normalized on U, excluding arbitrary field or ring isomorphisms.

For the stratum clauses, the original hypothesis spans the coefficient parameters
and only the T-positive monomials, not all nonzero K × T monomials. The final
`polynomialStratumIdeal` uses `(0,t)`, so Laurent K monomials are preserved.
The contractions p and r are canonical; the uniqueness quantifier restricts N'
by both contraction and IW containment. Both residue-field identifications are
normalized by their canonical maps. Finally the Cohen congruence uses the chart
ideal without m_L (the distinct completion ideal is not substituted for it).

Found and repaired during this pass: the saved node's lean.statement was stale
at its final quotient-map binders. It is now extracted verbatim from the final
module. The expanded quotient-residue clause hit the default elaboration heartbeat
limit; packaging precisely that clause into `HasCompatibleQuotientResidueField`
restored clean compilation without raising any resource limit or changing its
mathematical content. Its compatibility is stated on images of W, which generate
its residue field as a field. All helper definitions are listed in lean.declarations
and carry the owning item's source and blueprint docstring.

The live node was freshly copied before applying only lean and adding the already
landed definition dependency, so Q86's reviewed stage-1 split is preserved.
