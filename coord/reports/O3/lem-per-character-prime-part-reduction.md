## Worker report

The module Sheaf.RepresentationTheory.CharacterPrimePartReduction states
Representation.character_prime_part_reduction with one postponed proof and no new definitions.
The node statement, statement dependencies, proof and proof dependencies are unchanged.
The previous dispatch's unchanged-stage-1 failure does not apply: this is a stage-2 delivery,
and the current node has no Lean attachment.

The signature renders each hypothesis and clause as follows:

- N ≥ 1 is `(N : ℕ) (hN : 1 ≤ N)`.
- The specified primitive complex Nth root is `(ζ : ℂ) (hζ : IsPrimitiveRoot ζ N)`.
- K is exactly `IntermediateField.adjoin ℚ ({ζ} : Set ℂ)`, not an abstract cyclotomic field.
- A is exactly `integralClosure ℤ (IntermediateField.adjoin ℚ ({ζ} : Set ℂ))`.
  Its elements are the elements of that actual subfield satisfying a monic integer polynomial.
- The finite group is `{G : Type u} [Group G] [Finite G]`; divisibility is
  `(hG : Nat.card G ∣ N)`. No commutativity assumption is imposed on G.
- The finite-dimensional complex vector space is `{V : Type v} [AddCommGroup V]
  [Module ℂ V] [FiniteDimensional ℂ V]`. This includes the zero space.
- Its action is `(ρ : Representation ℂ G V)`. This is a monoid homomorphism into
  complex-linear endomorphisms. Since G is a group, ρ(g⁻¹) is an inverse of ρ(g),
  so this is precisely the action into GL in the node.
- The conclusion `∃ χ : G → A, (∀ g, ((χ g).val : ℂ) = LinearMap.trace ℂ V (ρ g)) ∧ …`
  simultaneously says that every ordinary character value lies in A and identifies the
  A-valued function used in the reduction clause. The embedding A → K → ℂ is injective,
  so the equation uniquely determines χ. This is a theorem about the actual trace;
  no chosen arbitrary character, new trace definition or additional hypothesis is used.
- Every prime is quantified by `∀ (p : ℕ), p.Prime → …`; every residue field is
  `∀ (k : Type w) [Field k] [CharP k p]`, with w independent of the universes of G,V.
- Every unital ring homomorphism is `(r : A →+* k)`; k need not be finite or algebraic.
- Every qualifying triple is `(g s u : G), g = s * u → Commute s u →
  Nat.Coprime (orderOf s) p → (∃ a : ℕ, orderOf u = p ^ a) → …`.
  Prime-to-p is coprimality of the order with p; a=0 explicitly includes order 1.
- The asserted reduction is exactly `r (χ g) = r (χ s)`.
  In particular this clause does not assume that s,u are powers of g.
- Existence for every prime and element is a separate conjunct
  `∀ (p : ℕ), p.Prime → ∀ g : G, ∃ s u : G, …`, independent of a field or ring map.
  It repeats the product, commutativity and two order properties, and asserts
  `(∃ m : ℕ, s = g ^ m) ∧ (∃ n : ℕ, u = g ^ n)`. Finite-order integer powers can
  be reduced modulo |G|, so these natural-power expressions are exactly the node's powers.

Dependency declarations read and used:

- def-weil-simple-field-extension: IntermediateField.adjoin,
  Mathlib.FieldTheory.IntermediateField.Adjoin.Defs; subfield closure of the base and singleton.
- def-weil-pbc-integral-closure: integralClosure and IsIntegral,
  Mathlib.RingTheory.IntegralClosure.Algebra.Basic and IsIntegral.Defs;
  the former's carrier is the latter predicate, with the actual subring operations.
- def-weil-finite-dimensional-subspace: FiniteDimensional,
  Mathlib.LinearAlgebra.FiniteDimensional.Defs; abbreviation for Module.Finite.
- def-weil-endomorphism-trace: LinearMap.trace and trace_eq_matrix_trace,
  Mathlib.LinearAlgebra.Trace; basis-independent trace and its diagonal-sum formula.

All recorded proof interfaces are imported privately, as required by the stage:
Complex.isAlgClosed (Mathlib.Analysis.Complex.Polynomial.Basic);
IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp (Mathlib.RingTheory.SimpleModule.Basic)
and Maschke (Mathlib.RepresentationTheory.Maschke);
Representation.normal_commuting_weight_induction
(Sheaf.RepresentationTheory.NormalCommutingWeightInduction);
Module.Free (Mathlib.LinearAlgebra.FreeModule.Basic);
pow_card_eq_one', the multiplicative form of card_nsmul_eq_zero'
(Mathlib.GroupTheory.OrderOfElement);
rootsOfUnity.isCyclic and card_rootsOfUnity (Mathlib.RingTheory.RootsOfUnity.Basic);
iterateFrobeniusOfPrime and iterateFrobeniusOfPrime_apply
(WeilConjectures.Mathlib.Algebra.CharP.Lemmas);
Submodule.torsionBy_isInternal (Mathlib.Algebra.Module.Torsion.Basic);
DirectSum and its module structure, lof and component (Mathlib.Algebra.DirectSum.Module).
The full node proof is rendered in the theorem docstring, retaining the four steps and
identifying the agent-derived proof rather than attributing it to the contextual citation.

Edge cases checked mathematically before drafting:

- V=0 gives the zero trace and the empty eigenbasis; no Nontrivial V binder excludes it.
- G trivial, N=1, ζ=1 gives K=ℚ and A its integral closure of ℤ, and s=u=1 works.
- The identity has order 1; a=0 is allowed in both reduction and existence clauses.
- If p does not divide |G|, take s=g,u=1. If |G| is a p-power, take s=1,u=g.
- For a cyclic group of order 6 and p=2, a generator g decomposes as g^4 g^3;
  the orders are 3 and 2. A one-dimensional character sends the order-two eigenvalue
  to 1 under reduction in characteristic 2, giving the stated equality.
- Nonabelian G is permitted; only the chosen pair must commute. There is no finite,
  algebraic-closure or surjectivity restriction on the residue field or ring map.

Searches made with the prescribed msearch.py wrapper (full response summaries are in
sandbox searches.jsonl):

- leanfinder: "Finite group complex character values are cyclotomic integers and reduction
  modulo a prime depends only on the prime to p part". Eight hits concern Galois
  cyclotomic characters, finite-field characters or Gauss sums; none is this theorem.
- loogle: `"isIntegral_character"`. FDRep.isIntegral_character and
  Representation.isIntegral_character prove only integrality, not membership in the
  specified field or the reduction/existence clauses; neither is in pinned Character.lean.
- grep in Mathlib/RepresentationTheory:
  `prime.to.p.part|p.regular|isIntegral_character|character.*cyclotomic`: zero hits.
- leansearch: "Ordinary finite group characters take values in cyclotomic integers and
  their reductions modulo p equal their values at the prime to p part". Eight hits on
  Galois cyclotomicCharacter and modularCyclotomicCharacter: no ordinary-character result.
- rg on lean/WeilConjectures and lean/Sheaf using the preceding pattern and the item id:
  unrelated regularity/prime-part prose, no existing theorem.
- rg on both source roots and dag/lean_names_upstream.json for
  `character_prime_part_reduction|lem-per-character-prime-part-reduction`: no hits.

No statement correction, new node, dependency repair or STATEMENT-DISPUTED finding.
The current blueprint ancestor proof Step 3 was read: it is a Verdier-duality argument,
not a proof of this auxiliary ordinary-character lemma. The source is accurately identified
as motivation only; Serre remains unavailable as the node records.

## Second reading by O3

This is the dispatch worker's own clause-by-clause rereading, not an independent review;
the dispatch forbids starting other agents and assigns independent review to the maintainer.
The node and completed signature were reread together. All four statement dependencies use
their recorded Mathlib definitions. The initial module omitted a public import of Complex,
which module-mode compilation identified; Mathlib.Data.Complex.Basic was added publicly.
The next check identified the missing public rational-algebra instance; the canonical
DivisionRing.toRatAlgebra from Mathlib.Algebra.Algebra.Rat was then imported publicly.
The A-valued existential is constrained by the complex trace equation at every element;
there is no weakening to an unconstrained function. The reduction quantifies all commuting
pairs, whereas only the existence conjunct requires powers of g. The prime, field and map
quantifiers and a=0 case are present. No mathematical mismatch or node correction was found.

Validation: scompile.py passed both the sandbox probe and the named library-module compile
with no warnings or errors (1.6 s and 1.7 s respectively).
