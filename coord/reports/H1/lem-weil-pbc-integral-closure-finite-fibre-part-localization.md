## Worker report

The module defines `integralClosure_finiteFibrePart_localization`, formalizing the
finite fibre component result from Stacks Tag 09XH. It binds commutative rings A and
B, an A-algebra structure of finite type, ideal I, product factors C₁ and C₂ with
C₁ finite over A/I, a ring equivalence e of the fibre quotient, and an idempotent
ε mapping to (1,0). The conclusion existentially supplies ε' in the integral
closure quotient, g in the integral closure, and a quotient ring map q. Clauses
assert ε' idempotent, q ε' = ε, the selected component is (1,0), and a nonempty
ring equivalence between localizations away from g and its image g.1 in B.

Each hypothesis is rendered directly by the corresponding Lean binders and typeclass
assumptions. The product decomposition is represented by the ring equivalence `e`;
the idempotent condition is `hε : e ε = (1, 0)`. The four conclusion clauses are
rendered by the conjunction after the existential binders.

Dependencies: no DAG statement dependencies; Mathlib `integralClosure`,
`Algebra.FiniteType`, `Ideal.Quotient`, `Localization.Away`, and `RingEquiv`.

Edge cases checked: I may be ⊥ or ⊤; C₁ or C₂ may be zero rings; ε may be 0 or 1;
the statement imposes no nonemptiness or characteristic assumptions. Universes are
explicit (`u`, `v`).

Searches: `rg` in Mathlib RingTheory for `integralClosure` (found
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic`); `rg` for `Algebra.FiniteType`
(found `Mathlib.RingTheory.FiniteType`); project search for the node id and related
integral-closure declarations (no existing project declaration); LeanFinder/Loogle
searches recorded in the node found only Zariski Main ingredients, not this theorem.

## Earlier second reading (a previous round; superseded)

The statement was compiled remotely with `scompile.py`; all binders are explicit and
the theorem is intentionally left with `sorry` as required for stage 2. The dry-run
preflight checks the recorded signature, blueprint tag, and node metadata.


## Second reading by H1

Read the node's complete statement and five proof steps against Stacks
`more-algebra.tex`, lemma-helper-finite-type (Tag 09XH), lines 2502–2550.
The repository lacks the literature checkout; I read the official Stacks GitHub
.tex source in scratchpad/more-algebra.tex and also checked the official source
through the web reader. A pair here is just a commutative ring and an ideal;
this lemma does not require a henselian, Zariski, Noetherian, or domain assumption.

Object/hypothesis/conclusion checklist (verdicts refer to the repaired module):

- A, B and the ring map: `A : Type u`, `B : Type v`, both `CommRing`,
  `[Algebra A B]`. This is an arbitrary unital commutative ring map. MATCH.
- Finite type: `[Algebra.FiniteType A B]`. This is finite generation as an
  A-algebra, not module finiteness. MATCH.
- Ideal I and fibre quotient: `I : Ideal A` and
  `B ⧸ Ideal.map (algebraMap A B) I`; map is the generated image ideal IB. MATCH.
- Product of A/I-algebras: `C₁ : Type w`, `C₂ : Type z`, their `CommRing`
  and `Algebra (A ⧸ I)` instances, `e` a ring equivalence, and `he` stating
  compatibility with the algebra maps on every a in A. Surjectivity of the
  quotient A → A/I makes this exactly an A/I-algebra product decomposition. MATCH.
- C₁ finite: `[Module.Finite (A ⧸ I) C₁]` with the compatible algebra above.
  No finiteness of C₂ is imposed. MATCH.
- ε=(1,0): `ε` and `hε : e ε = (1, 0)`; ring-equivalence injectivity implies
  idempotence, so no extra hypothesis is needed. MATCH.
- B' integral closure: Mathlib `integralClosure A B`, the subalgebra with
  membership `IsIntegral A`, as verified in IntegralClosure/Algebra/Basic.lean
  at the definition and `mem_integralClosure_iff`. This is integrality over
  the image of A and does not demand injectivity of A → B. MATCH.
- ε', g and induced quotient map: the existential `ε'`, `g`, `q` have exactly
  the required carriers. The equation for every x in B' pins q to the map
  induced by inclusion, since the quotient map is surjective. MATCH.
- (i), idempotence and lifting: `IsIdempotentElem ε' ∧ q ε' = ε`. The two
  following clauses state that x fixed by ε' has second coordinate zero,
  and x fixed by 1−ε' has first coordinate zero. For an idempotent δ,
  `{x | δ*x=x}` is exactly δR. Thus these are the two factor-preservation
  clauses; the standard idempotent decomposition yields their product. MATCH.
- (ii), the induced first-factor isomorphism: `∀ c : C₁, ∃! x,
  ε' * x = x ∧ e (q x) = (c, 0)`. This states bijectivity of the canonical
  first-factor map on ε'R'. That map preserves addition and multiplication
  because q and e are ring maps, and sends the factor unit ε' to 1.
  Thus it is exactly a ring isomorphism, and by compatibility also an
  A/I-algebra isomorphism. It does not merely assert an unrelated abstract
  equivalence. MATCH.
- (iii): `Ideal.Quotient.mk _ g = ε'`. MATCH.
- (iv): `Function.Bijective (Localization.awayMap
  (integralClosure A B).val.toRingHom g)`. Opened Away/Basic.lean:
  `awayMap` is precisely the induced map from B'_g to B_g; bijectivity of
  this ring hom is precisely its being an isomorphism. MATCH.

There are no statement dependencies, new definition nodes, or dependency
modules in this delivery. I also opened the project's proof-ingredient modules
IntegralClosureFiniteFibreImageClopen and IntegralClosureFiniteFibreChooseG:
these assume an isomorphism on a neighbourhood U and are not the present
unconditional finite-type theorem. Their quotient map and awayMap formulations
confirm the intended canonical maps; neither duplicates this item.

Edge cases: I=⊥ and I=⊤ are allowed, as are zero A or B and zero C₁ or C₂.
If C₁=0 the fixed-by-ε' ideal can be zero; the unique-preimage clause still
has exactly its correct meaning. ε=0 or ε=1 is allowed, and localization
away from 0 is the zero ring on both sides. No field, characteristic,
nonempty-spectrum, reducedness, or dimension assumption appears. There is no
index set or integer parameter. A, B, C₁ and C₂ now have independent universes;
none is restricted to the same universe as another. Every binder is explicit,
and there is no local instance, notation, hidden `let`, definition, or proof.

Independent searches (2026-10-11):

- LeanSearch via msearch: “finite component of quotient comes from integral
  closure localization isomorphism”. Service returned Internal Server Error;
  unavailable, with no verdict inferred from that failed search.
- LeanFinder via msearch: “finite component quotient integral closure
  localization” and “idempotent finite quotient algebra integral closure
  preserves product decomposition”. Results were quasi-finite localizations,
  finite integral closures under domain/field hypotheses, and Dedekind ideal
  product quotients. None has this theorem's hypotheses and conclusion.
- rg of Mathlib, WeilConjectures and repository lean/Sheaf for finiteFibre,
  finite_fibre, 09XH, helper-finite-type, and integralClosure with idempotent
  found the two proof ingredients above and Etale/QuasiFinite.lean's
  etale-local splitting. The latter changes the base by an etale extension;
  it is not this result. Standard notions all use their existing Mathlib
  declarations, so no missing notion or new definition is needed.

Mismatches repaired: the previous e was unrelated to the supplied A/I-algebra
structures; added `he`. The existential q was arbitrary; fixed it on quotient
representatives. The first-factor isomorphism and both factor preservation
clauses were missing; restored them using the idempotent ideals. The image of
 g was never constrained; added the exact lift equation. The localization
conclusion asserted only some ring equivalence; replaced it with bijectivity
of the inclusion-induced awayMap. Removed the repeated hypothesis `e ε=(1,0)`
from the conclusion. Independent universes replace the common-universe
restrictions on A/B and C₁/C₂. Expanded the proof docstring to all five node
steps with their dependency ids, added the standard header, and removed unused
Polynomial scope. No node statement was corrected: the node and source agree.
The node's lean.statement is extracted verbatim from the repaired signature.

The worker report above records the original draft; this second reading
supersedes its claims about the four original conclusion clauses.
