## Worker report

The module `Sheaf.RingTheory.HigherGradedCokernelPerturbation` states the full
higher-width comparison. Both theorems have `sorry` proofs. All definitions in
the new construction module have real data, and contain no postponed theorems.
The source was read in ILO, Travaux de Gabber, Expose III, printed pp.39--41,
including the definition before Remark 4.1 and Proposition 4.5(iii)--(iv), and
Stacks `more-algebra.tex`, the first proof paragraph of Tag 07VE. The source's
finite adjustment, rather than its later Krull intersection step, supplies the
transferred bound. No statement correction is needed.

Hypotheses and clauses, in order:

- A commutative Noetherian ring is `{B : Type u} [CommRing B]
  [IsNoetherianRing B]`; `I : Ideal B` is arbitrary.
- The three modules have independent universes `v,w,z`, with additive group and
  module structures and both `[Module.Free B _]` and `[Module.Finite B _]`.
  Over a commutative ring these encode precisely finite free modules, including
  rank zero. They do not require a chosen basis or impose a nonzero-ring hypothesis.
- `r r' : L →ₗ[B] M`, `p p' : M →ₗ[B] F` are the four maps.
  `hexact` is `range r = ker p`, and `hcomplex` is `p'.comp r' = 0`.
- `intAdicPower I V q` is `I ^ q.toNat • ⊤`. Thus it is the whole module for
  `q ≤ 0` and is exactly the ideal-power-generated submodule otherwise.
- `c n : ℕ` makes both nonnegative and `hn : c ≤ n` is the remaining inequality.
  `hr` and `hp` quantify over integer `j ≥ c` and render each Artin--Rees
  intersection bound using `⊓`, `≤`, and submodule `map`.
- `hrr'` and `hpp'` are the range inclusions for the differences in the target
  `intAdicPower ... (n+1)`.
- The width is written explicitly as the natural number `n+1-c`. Since `c≤n`,
  this is the same positive integer as the node's width, without truncated
  subtraction changing its meaning.
- The first conjunct of `higherGradedCokernelPerturbation` is exactly the
  displayed submodule equality for every `q : ℤ`: sums are `⊔`, intersections
  are `⊓`, and images are `LinearMap.range`.
- The second conjunct gives a `B`-linear equivalence of the actual direct sums
  `higherAdicGraded I (F ⧸ range p)` and its primed counterpart. Its first
  condition specifies the identity-induced map on the homogeneous class of
  every representative `x ∈ I^q F`, through the two quotient maps `mkQ`.
  These representatives surject onto each graded piece: the quotient map sends
  ideal multiples onto ideal multiples. Consequently the condition also says
  the equivalence preserves grading and uniquely specifies it.
- The second condition preserves `higherAdicAction` for every element of
  `G_a(B)` and of the source direct sum. A `B`-linear equivalence with this
  compatibility is exactly an isomorphism of the graded `G_a(B)`-modules.
  The operations are unbundled functions; no extra arbitrary ring structure
  or module structure is assumed, and no ring-law theorem is silently postponed.
- `higherGradedCokernelPerturbation_algebra` specializes the final module to `B`
  with exactly the same hypotheses, supplies the same homogeneous formula and
  action compatibility, and additionally preserves `higherAdicQuotientMul` and
  `higherAdicQuotientOne`. These are the quotient-ring multiplication and unit.
  The formula determines the same comparison as the preceding theorem, rather
  than an unrelated algebra equivalence. Multiplicativity, preservation of one,
  and the common scalar action express precisely the algebra assertion.
- There is no Jacobson radical binder, perturbed exactness conclusion, or
  nontriviality assumption.

Dependency declarations: `Mathlib.RingTheory.Noetherian.Defs.IsNoetherianRing`
(recorded by `def-weil-pbc-noetherian-ring`) was read with its docstring and
signature. The new node supplies `Ideal.intAdicPower`, `higherAdicPiece`,
`higherAdicGraded`, `higherAdicClass`, `higherAdicAction`,
`higherAdicQuotientMul`, and `higherAdicQuotientOne`, imported publicly from
`Sheaf.RingTheory.HigherAdicGraded`. It uses the quotient-module dependency's
Mathlib match, `Submodule.hasQuotient`, `Submodule.Quotient.module`, and
`Submodule.mkQ`, from `Mathlib.LinearAlgebra.Quotient.Basic` and its public
imports. `Module.Free` and `Module.Finite` use Mathlib's finite-free module API.
There are no proof dependency imports because the node's `proof_deps` is empty.

Edge cases checked mathematically before writing: zero modules/ranks are allowed;
`I=0` forces equal map pairs and gives the identity comparison; `I=B` makes
all pieces zero and the equality automatic; `n=c` gives width one; for
`q≤-a` the numerator and denominator are both the whole module; for `-a<q<0`
the pieces are genuine quotients and are retained; `j=c` is the base case of
the finite transferred-bound argument. The zero ring is included. No exactness
of the perturbed complex follows or is claimed. The sum formulas over quotient
representatives give the usual action and product: representatives lie in their
numerator filtration steps and changing them by denominator elements changes
the result in the denominator of the total degree. Arbitrary lifts from `B/U`
to `B` alter products only by the ideal `U`.

Searches made: msearch leanfinder "Higher width associated graded cokernels of
two ideal-adically close finite free complexes are canonically isomorphic"
returned completion/congruence statements only; loogle `"Ideal.Filtration"`
returned natural-indexed filtrations; grep
`associatedGraded|AssociatedGraded|higherAdic` in Mathlib RingTheory had no hits.
For the new construction, msearch leansearch "Integer indexed higher width
ideal associated graded module direct sum I power q quotient I power q plus a"
returned general graded structures; leanfinder "Integer indexed higher width
ideal associated graded module" returned increasing filtrations and homogeneous
ideals; grep `higherAdic|HigherAdic|associatedGraded|AssociatedGraded` had no hits.
The exact returned search records are attached to the new node.
Direct rg searches in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
`dag/lean_names_upstream.json` found none of the chosen declaration names.
Searching project source for associated graded constructions located
`WeilConjectures.RingTheory.AssociatedGradedRing`; its full source uses
natural degrees and width one, so it cannot express the present negative-degree
higher-width pieces and was not duplicated. Searching for the item ID in
`lean/WeilConjectures` found no declaration. DAG searches for higher-width and
higher-graded notions found only the item and its approximation consumer.
`tools/blueprint_refs.py search higher graded`, `search higher adic`, and
`search graded module` returned unrelated general or sheaf notions, none of this
integer-indexed higher-width construction.

Validation: both files compiled separately in dependency order using scompile.py,
with no errors or warnings. Explicit `autoImplicit false` checks all binders.
The delivery dry run and push are performed after the final records are written.

## New nodes

`def-per-higher-adic-graded` defines the integer filtration, higher-width pieces,
the direct sum, and its representative-induced action and quotient algebra
operations, following ILO Expose III section 4, printed p.39 and 4.5(iv), p.40.
The zero-off-filtration extension only makes the class function total; every
comparison normalization in the theorem explicitly restricts its input to the
filtration step. The real construction uses `Quotient.out` from Lean's proved
quotient API, not choice from an unproved existence theorem. It is independent
of the representatives for the standard ideal-product reason, including integer
degrees because `max(s,0)+max(q,0)≥max(s+q,0)` and the corresponding denominator
inequalities. The searches listed above found no preexisting node or definition.
Its statement dependency is the existing quotient-module node; the owning item
adds this new definition to `stmt_deps`. No other field of the item changes.

## Second reading by Q59

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
