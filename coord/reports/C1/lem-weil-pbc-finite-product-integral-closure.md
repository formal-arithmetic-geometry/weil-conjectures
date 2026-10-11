## Worker report

The module `Sheaf.RingTheory.IntegralClosureFinitePi` states
`integralClosure_finite_pi`, with its entire proof `sorry`. It states both clauses of the
node in one conjunction. No definitions or additional nodes are introduced, and no node
faults or statement corrections were needed.

Hypothesis and clause correspondence:

- A finite family indexed by 1,...,n is represented by `{I : Type w} [Finite I]`.
  An arbitrary finite indexing type merely permits relabeling; `Fin n` is included,
  as is the empty indexing type. Universes `w u v` are explicitly bound.
- The commutative rings are `R : I → Type u`, `S : I → Type v`, with
  `[∀ i, CommRing (R i)]` and `[∀ i, CommRing (S i)]`. No domains or nonzero
  rings are assumed.
- The component homomorphisms are `φ : ∀ i, R i →+* S i`. The local instance
  `letI : ∀ i, Algebra (R i) (S i) := fun i ↦ (φ i).toAlgebra` equips each
  component with exactly this map, without restricting which homomorphisms are allowed.
- The product rings R and S are the dependent function types `∀ i, R i` and
  `∀ i, S i`. Mathlib's `Pi.instAlgebraForall` makes their algebra map
  exactly `fun r i ↦ φ i (r i)`.
- The component subrings S'_i are `(integralClosure (R i) (S i)).toSubring`.
  This uses the dependency's exact integral closure rather than a second definition.
- The subring equality is
  `(integralClosure (∀ i, R i) (∀ i, S i)).toSubring =
  ⨅ i, (integralClosure (R i) (S i)).toSubring.comap (Pi.evalRingHom S i)`.
  The right side is the product subring inside the original ambient product S:
  membership means membership of every coordinate in its component closure.
  Using the infimum of inverse images states equality of subrings, not merely an
  abstract ring isomorphism or a choice of a new carrier.
- The final clause is conditional on `∀ i, Function.Injective (φ i)` and concludes
  `IsIntegrallyClosedIn (∀ i, R i) (∀ i, S i) ↔
  ∀ i, IsIntegrallyClosedIn (R i) (S i)`. Injectivity is confined to this clause;
  it is not assumed for the closure equality.

Dependency: `def-weil-pbc-integral-closure`. Read its statement and full record and opened
its recorded Mathlib declarations and their docstrings:
`integralClosure` in `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`,
`IsIntegral` in `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`, and
`IsIntegrallyClosedIn` in `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`.
The latter is `IsIntegralClosure R R S`, which records both injectivity and exactly
that integral elements are in the image. All are available through the
`IntegrallyClosed` import. The `Pi` import supplies the coordinatewise product algebra.
No dependency module is needed.

Source read online because the local literature checkout has no algebra.tex:
[Stacks Tag 0CY9](https://stacks.math.columbia.edu/tag/0CY9) and
[Stacks Tag 0CY8](https://stacks.math.columbia.edu/tag/0CY8).
The module docstring includes all three node proof steps: projection of a monic
polynomial; padding finitely many monic polynomials to a common degree and assembling
coefficients (including the empty product); and identification of the closures and
of the injective-map integrally-closed condition.

Edge cases checked before writing: empty I gives two zero product rings, top as the
empty infimum, and a vacuous component condition; IsIntegrallyClosedIn holds for the
unique zero-ring map. Singleton I gives the original ring map. Zero component rings
are permitted, and noninjective maps remain permitted for the first clause. Mixed
characteristics impose no issue: coefficients lie in their respective rings.
Finiteness is essential for the common-degree argument; no infinite product is claimed.
There is no `Nonempty I`, `Nontrivial`, domain, or characteristic restriction.

Searches for an existing statement (recorded also in sandbox searches.jsonl):

- `msearch.py ... leansearch "integral closure finite product of rings coordinatewise"`:
  unavailable, Internal Server Error. Other search kinds and local sources were used.
- `msearch.py ... leanfinder "integral closure commutes with finite products of ring
  homomorphisms"`: eight results, including `IsIntegral.pair_iff`, `IsIntegral.pair`,
  and `Algebra.IsIntegral.prod`; these concern binary products over a single fixed
  base ring, not products of varying base ring maps or equality of closure subrings.
- `msearch.py ... loogle "integralClosure, IsIntegrallyClosedIn"`: six results, including
  `IsIntegrallyClosedIn.integralClosure_eq_bot_iff`; none is the finite-product statement.
- `msearch.py ... grep "integralClosure.*(pi|Pi)|[Ii]sIntegral.*[Pp]i|[Pp]i.*[Ii]sIntegral"
  RingTheory`: four unrelated hits, no finite-product closure theorem.
- `rg` over Mathlib's IntegralClosure directory for closure and integrality product
  names located the existing definitions and binary product ingredients only.
- `rg` over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for finite-product closure names and Pi-integrality
  patterns found no exact statement; unrelated hits concerned integral morphisms.
- Search for this node id in the source project's WeilConjectures tree found no hit.
- Read Mathlib `Algebra/Algebra/Pi.lean` to verify the varying-base product algebra
  map, and `IsIntegralClosure/Defs.lean` to verify the integrally-closed predicate.

Validation: server compilation and the delivery dry run are performed for this file;
only the expected `sorry` proof remains. The independent second reading is reserved
for the next worker.


## Second reading by C1

I independently opened the item node, its sandbox copy and module, and the sole
statement dependency `def-weil-pbc-integral-closure`, including its recorded Mathlib
signatures and implementations. No new nodes, dependency modules or statement
correction occur in this delivery.

Source: the local Stacks checkout is absent. I read the upstream algebra.tex around
`lemma-finite-product-integral`, `definition-integral-closure`, and
`lemma-finite-product-integral-closure`, as well as
[0CY8](https://stacks.math.columbia.edu/tag/0CY8) and
[0CY9](https://stacks.math.columbia.edu/tag/0CY9).
The source introduces arbitrary ring maps in a finite family. The preceding definition
uses integral closure for arbitrary maps and integrally closed for an inclusion.
Thus the node's explicit injectivity condition on its second clause is faithful;
there is no ambient domain, Noetherian, characteristic or finiteness-of-algebra assumption.

Object, hypothesis and conclusion inventory, matched independently to Lean:

- Finite index set 1,...,n: `{I : Type w} [Finite I]`. Pass: relabeling a finite family
  gives this formulation, including `Fin 0`; no inhabitedness or decidable equality
  is imposed. The index universe is independent of both ring universes.
- Commutative rings R_i and S_i: `(R : I → Type u) (S : I → Type v)` with
  `[∀ i, CommRing (R i)] [∀ i, CommRing (S i)]`. Pass: no extra instances.
- Arbitrary component homomorphisms: `(φ : ∀ i, R i →+* S i)` and
  `letI : ∀ i, Algebra (R i) (S i) := fun i ↦ (φ i).toAlgebra`. Pass: the local
  algebra structures use precisely these maps, with no independently chosen action.
- Product rings and their product map: `(∀ i, R i)` and `(∀ i, S i)`.
  Pass: I read `Pi.instAlgebraForall` in `Mathlib.Algebra.Algebra.Pi`; its algebraMap
  is `RingHom.pi` of the component algebra maps composed with coordinate evaluation,
  hence sends r to the tuple whose i-th coordinate is φ i (r i).
- Component closure subrings S'_i: `(integralClosure (R i) (S i)).toSubring`.
  Pass: the dependency's `integralClosure` has carrier `{x | IsIntegral (R i) x}`;
  `IsIntegral` unfolds through `RingHom.IsIntegralElem` to a monic polynomial root
  with evaluation via the specified algebraMap. This is the recorded notion.
- First conclusion, equality of the closure in S with the product subring:
  `(integralClosure (∀ i, R i) (∀ i, S i)).toSubring =
  ⨅ i, (integralClosure (R i) (S i)).toSubring.comap (Pi.evalRingHom S i)`.
  Pass: membership in the right side says exactly that every coordinate belongs
  to S'_i. Both sides are subrings of the same S, so this is actual subring equality,
  not merely an abstract isomorphism. This clause assumes no injectivity.
- Extra hypothesis for the second clause: `(∀ i, Function.Injective (φ i)) →`.
  Pass: it appears only on that clause and identifies each base with its image.
- Second conclusion: `IsIntegrallyClosedIn (∀ i, R i) (∀ i, S i) ↔
  ∀ i, IsIntegrallyClosedIn (R i) (S i)`. Pass: I opened the abbreviation
  `IsIntegrallyClosedIn` and the class `IsIntegralClosure`; together they require
  injectivity and that integral elements are exactly the image of the base.
  Under the stated injectivity hypothesis this is precisely the node's conclusion.
  Both conclusions hold for the same arbitrary family and maps, joined by `∧`.

Edge cases: empty I gives singleton/zero product rings and the empty infimum is top,
so the first equality and the vacuous component condition remain meaningful and true.
The unique map of the two empty products is injective and its image is the whole ring.
Singleton families recover the component condition. Zero component rings are allowed;
the monic-polynomial definition also covers the zero ring (its zero polynomial is
monic since 0 = 1), so no positive-degree convention accidentally excludes it.
The first clause permits noninjective maps, while the second is conditional.
No field, characteristic, domain or nontriviality restriction appears. Arbitrary
universes w, u, v are explicitly bound. Scheme and cohomological edge cases do not
apply to this ring statement.

Independent searches, using different wording from the first reader:

- LeanSearch: `Subring of integral elements of finite product equals product of
  integral element subrings`: unavailable with Internal Server Error; no search
  verdict is inferred from this unavailable service.
- LeanFinder: `Integral elements in a dependent finite product of algebras with
  different scalar rings`: eight results. `IsIntegral.pair`, `IsIntegral.pair_iff`
  and `Algebra.IsIntegral.prod` have a single base ring and binary ambient product;
  `IsIntegral.prod` concerns multiplication of elements. None states this node.
- Loogle: `integralClosure, Pi` did not parse (`Pi` unknown); the replacement
  `IsIntegral, (_ → _)` returned twelve entries, including the same fixed-base
  binary product results, with no exact finite varying-base closure theorem.
- Direct rg over Mathlib, the source WeilConjectures tree and repository lean/Sheaf
  for `integral.*(finite.product|finite_product|pi_iff)`, `integralClosure.*prod`,
  `IsIntegrallyClosedIn.*prod`, and Pi/integralClosure combinations found only
  closure membership under multiplication (`multiset_prod_mem`, `prod_mem`),
  not the node's theorem. The exact proposed declaration name and Pi-integrality
  patterns were also searched in `dag/lean_names_upstream.json`; no duplicate.
  These checks support retaining this new statement module and using the existing
  definitions, with no new definition node or private copy.

H5-H9: there are no definitions, so no hollow definition. The sole theorem's proof
is exactly `by sorry`; nothing is proved in this stage. Both imports are used for
product algebra structure and integral-closure predicates. Header, topic path,
namespace-free global name, 100-character lines and explicit universe/variable
bindings conform. The module and declaration docstrings name the source and item.
The declaration docstring carries all three proof steps: projection, common-degree
assembly (with empty product), and identification of subrings followed by the
injective-map equivalence. The node's lean.statement agrees verbatim with the file
signature through the final conclusion, excluding the proof delimiter.

Mismatch and repair verdict: none found. I changed only this report by adding the
independent second reading; the correct Lean module and node record were preserved.
Validation: `scompile.py C1 lem-weil-pbc-finite-product-integral-closure` on the module
returned exit code 0, compiled, with no errors or warnings. Delivery preflight and
server compilation are also rerun by the dry run and final delivery commands.
