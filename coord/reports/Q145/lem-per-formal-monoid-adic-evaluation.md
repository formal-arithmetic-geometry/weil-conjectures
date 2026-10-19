## Worker report

The module `Sheaf.RingTheory.FormalMonoidAdicEvaluation` states
`AddMonoidAlgebra.exists_formalMonoid_adicEvaluation`, with `sorry` as its only
proof. No definitions, additional nodes, dependency repairs, or statement
corrections are needed. The original node is preserved except for `lean`.

Hypothesis-by-hypothesis correspondence:

- A commutative coefficient ring is `(R : Type u) [CommRing R]`.
- The coefficient ideal and its finite generation are `(aI : Ideal R)` and
  `(haI : aI.FG)`.
- The finitely generated commutative additive monoid is `(P : Type v)
  [AddCommMonoid P]`, with `hfg` asserting that some finite subset has additive
  submonoid closure equal to the top submonoid. This imposes neither cancellation,
  saturation, torsion-freeness, nor any fs condition.
- Sharpness is `hsharp : ∀ p, IsUnit (Multiplicative.ofAdd p) → p = 0`.
  Multiplicative is Mathlib's change of notation for the same monoid.
- `AddMonoidAlgebra R P` is the ordinary finite-support monoid algebra. The
  equality `hbI` fixes `bI` to the supremum of the coefficient ideal's extension
  and the ideal spanned by `single p 1` for `p ≠ 0`. Naming this ideal does not
  impose an independent mathematical assumption.
- The ring B is exactly `AdicCompletion bI (AddMonoidAlgebra R P)`.
- `(A : Type w) [CommRing A]`, `(J : Ideal A)` and `[IsAdicComplete J A]`
  express the target ring, ideal, and completeness including separatedness.
- `α : R →+* A` and `hα` give the coefficient map and `α(aI) ⊆ J`.
- `a : Multiplicative P →* A` gives the additive-to-multiplicative monoid map;
  `map_one` is precisely a(0)=1. `ha` puts every nonzero exponent's image in J.

Clause-by-clause correspondence:

- `∃ Ea : AdicCompletion ... →+* A` is existence of the evaluation ring map.
- The first conjunct is continuity from the inverse-limit topology of discrete
  quotient rings, written `⨅ n, TopologicalSpace.induced (AdicCompletion.evalₐ
  bI n) ⊥`, to `J.adicTopology`. These are explicit topology arguments, with
  no file-local instances or notations.
- The formula `Ea (AdicCompletion.of ... (single p c)) = α c * a (ofAdd p)`
  expresses both specified restrictions: p=0 gives the coefficient restriction,
  and c=1 gives the monomial restriction. Conversely those two restrictions
  imply this formula by multiplicativity, since c*z^p is their product.
- The next conjunct quantifies over EVERY continuous ring map E satisfying that
  formula and asserts `E = Ea`. Thus uniqueness does not assume the power bound
  or congruence conclusion.
- The power-bound conjunct quantifies over every `n : ℕ` and every f in the
  ideal `Ideal.map (algebraMap R[P] B) (bI ^ n)`, exactly b^n B, and concludes
  `Ea f ∈ J ^ n`.
- The last conjunct quantifies over a second admissible monoid map b and ANY
  continuous extension Eb with its prescribed coefficient-monomial values.
  Existence of this Eb follows by the same theorem applied to b, and uniqueness
  identifies it with E_b. This avoids making an arbitrary chosen evaluation
  definition or assuming an extension exists as an extra initial hypothesis.
- A generator list is `p : Fin h → P`, including h=0. Its entries are nonzero
  and `AddSubmonoid.closure (Set.range p) = ⊤`. For every r with `1 ≤ r`, the
  displayed generator differences belong to `J ^ r`; the conclusion is
  `∀ f : B, Ea f - Eb f ∈ J ^ r`.

Dependencies and source readings:

- Both recorded dependencies use `Mathlib.RingTheory.AdicCompletion.Basic`:
  `AdicCompletion` (compatible quotient sequences, full signature at Basic.lean
  171), and `IsAdicComplete` (Hausdorff and precomplete, Basic.lean 56).
  Their full definitions and surrounding docstrings were read.
- `Mathlib.RingTheory.AdicCompletion.Algebra` supplies the completion ring and
  algebra structure, the canonical algebra map, and `AdicCompletion.evalₐ`.
  Its declarations were read, including their full signatures.
- `Mathlib.Algebra.MonoidAlgebra.Basic` supplies `AddMonoidAlgebra` and `single`;
  `Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology` supplies
  `Ideal.adicTopology`. The latter's docstring identifies the powers as a zero
  neighbourhood basis.
- The proof-only import `Mathlib.RingTheory.AdicCompletion.RingHom` supplies
  `IsAdicComplete.liftRingHom`, whose compatible-quotient signature and docstring
  were read. The node has no recorded proof dependencies or proof steps. The
  theorem docstring supplies the complete agent-origin finite-level argument.
- Read the actual local source `literature/stacks-project/algebra.tex`, label
  `lemma-hathat-finitely-generated` (Tag 05GG), including its proof. Its
  finite-level kernel description supports the completion interpretation; the
  evaluation/congruence refinement is explicitly agent-supplied in the node.

Edge cases checked before writing:

- Trivial P permits the empty generating family; no `[Nonempty (Fin h)]` or
  positive h is imposed. Here the monomial ideal is zero and the two evaluations
  are equal, so the empty congruence hypothesis is correct.
- The power bound includes n=0 (whole ring maps to J^0=A). The r=1 boundary is
  included in the congruence statement; r=0 is not required by the node.
- J=0 makes A discrete and complete; the nonzero monomials must evaluate to zero.
  The statement continues to give the coefficient/augmentation evaluation.
- J=top forces A to be a subsingleton by separatedness; no Nontrivial assumption
  excludes this case. The zero coefficient ring is likewise permitted.
- Noncancellative sharp finitely generated monoids, including an idempotent
  monoid, are allowed. The finite-level construction uses the actual relations,
  not a free power-series replacement.
- The ring, monoid, and target universes u,v,w are explicitly independent. No
  test-object universe restriction or automatically bound variable occurs.

Searches for existing statements (2026-10-19):

- `msearch.py ... leanfinder "Continuous evaluation from the adic completion of a
  monoid algebra into a complete ring and congruence of evaluations"`: eight
  projection/evaluation hits, including `AdicCompletion.evalₐ_mk` and
  `AdicCompletion.ext_evalₐ`; none states the node.
- `msearch.py ... loogle '"AdicCompletion", "liftRingHom"'`: four hits on the
  inverse-limit universal property (`AdicCompletion.liftRingHom` and its
  projection equations). These give maps INTO a completion, not the node's
  evaluation and congruence theorem.
- `msearch.py ... grep 'AdicCompletion.*MonoidAlgebra|MonoidAlgebra.*AdicCompletion'
  RingTheory`: zero hits.
- `msearch.py ... leansearch "Unique continuous evaluation homomorphism from
  completed monoid algebra into an adically complete ring"`: eight hits including
  `IsAdicComplete.algHom_ext`, `PowerSeries.eval₂Hom`, `MvPowerSeries.aeval_unique`
  and `UniformSpace.Completion.extensionHom`. None states the monoid-algebra
  theorem with the ideal-power and congruence clauses.
- `rg` of the upstream WeilConjectures tree and side-project `lean/Sheaf` for
  formal monoids and evaluation finds related formal-chart modules. The existing
  `FormalMonoidImplicitElimination` only cites this node in its proof plan;
  `FormalMonoidRingDimension` assumes an fs monoid and proves a different result.
  Reading these modules confirmed the same monoid algebra and topology conventions.
- Exact-node-id search upstream found no declaration; side-project hits were
  proof-plan references only. Exact proposed declaration-name searches in those
  trees and `dag/lean_names_upstream.json` found no collision.

There is no STATEMENT-DISPUTED issue or mathematical node fault. The inherited
node status is `unsplit`; the delivery preserves it as required by the field-only
rule. `scompile.py` compiled both sandbox and library-name forms cleanly on the
first check, with no diagnostics. A final compile and delivery preflight follow.

## Second reading by Q145

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
