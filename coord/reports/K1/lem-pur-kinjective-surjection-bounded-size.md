## Worker report

The module `Sheaf.CategoryTheory.BoundedSubobjectSurjection` states
`CategoryTheory.exists_subobject_surjecting_bounded_size`. It uses the landed
statement `CategoryTheory.bounded_subobject_size_quotient_and_small_iso_classes`
from `Sheaf.CategoryTheory.BoundedSubobjectSize` as the statement dependency's
recorded declaration (the proof remains `sorry`).

The variables `{C : Type u}`, `[Category.{v} C]`, `[Abelian C]`, and
`[IsGrothendieckAbelian.{v} C]` render the Grothendieck abelian category. `U : C`
and `_hU : IsSeparator U` render the generator. `M N : C`, `π : M ⟶ N`, and
`[Epi π]` render the arbitrary surjection. The local `size X` is
`Cardinal.mk (Shrink.{v} (Subobject X))`, the cardinality of the subobject set.
The local `c k` is the size of the coproduct of `k.out` copies of `U`.
The conclusion supplies `M'`, a monomorphism `ι : M' ⟶ M`, the monicity clause,
the epimorphism clause `Epi (ι ≫ π)`, and the bound `size M' ≤ c (size N)`.

I checked the zero-cardinal case (the coproduct is the empty coproduct), the
zero object, and the case where `N` has only its zero subobject. The source
proof's three clauses are recorded in the declaration docstring: generator maps
indexed by proper subobjects, the image/subobject cardinal estimate, and the
surjectivity contradiction.

Searches found no existing declaration for this lemma: LeanFinder query
“surjection from a subobject of bounded size onto an object in a Grothendieck
abelian category” found only general Grothendieck-category declarations;
Loogle query “CategoryTheory.IsGrothendieckAbelian surjective subobject bounded
cardinal” found no hit; grep of Mathlib for
`surjection-bounded-size|subobject.*surject` found none; grep of the project
found no declaration of this node. The existing dependency module was inspected
and compiled together with this module via `scompile.py`.

## Earlier second reading (a previous round; superseded)

I independently read the node and module. Every category, generator, object,
and epimorphism hypothesis appears in the Lean signature. The mono inclusion
renders the subobject, the composite epi renders its surjection onto `N`, and
the local cardinal expressions render exactly `|M'|` and
`c(|N|) = |\bigoplus_{|N|} U|`. No clause or edge case is omitted.

## Second reading by K1

I independently opened the node, its module, both statement dependencies and their
recorded declarations. The local Stacks checkout is absent on this machine, so I read
`injectives.tex` directly from the Stacks project's upstream source at
https://raw.githubusercontent.com/stacks/stacks-project/master/injectives.tex:
`definition-grothendieck-conditions`, `definition-size`,
`lemma-set-iso-classes-bounded-size`, the surrounding introduction to
`section-K-injective`, and `lemma-surjection-bounded-size` with its proof.
The source introduces no ring, characteristic, finiteness or scheme hypotheses here.

The node's objects, hypotheses and conclusion, matched in order:

- Grothendieck abelian category A: `{C : Type u} [Category.{v} C] [Abelian C]
  [IsGrothendieckAbelian.{v} C]`. Exact match to `def-sp-grothendieck-abelian`'s
  Mathlib record. I read `Basic.lean:55–107`: AB5, a separator and locally small
  hom sets are bundled; small colimits and well-poweredness are inferred, not
  additional assumptions. Local smallness at the hom universe is automatic.
- Chosen generator U: `(U : C) (_hU : IsSeparator U)`. Exact match. I read
  `Generator/Basic.lean`'s `IsSeparator`: Hom(U,-) is faithful. In an abelian
  category this is equivalent to the source's condition that a map from U escapes
  every proper subobject (apply faithfulness to the nonzero quotient map).
- Size of an arbitrary object X: local `size X = Cardinal.mk
  (Shrink.{v} (Subobject X))`. Exact match to the subobject-set cardinality,
  and exactly the expression in the dependency declaration
  `bounded_subobject_size_quotient_and_small_iso_classes` in
  `Sheaf.CategoryTheory.BoundedSubobjectSize`. Shrinking is an equivalence of
  types supplied by well-poweredness; it does not count representatives twice.
- Function c(lambda): local `c k = size (∐ fun _ : k.out => U)`. Exact match;
  `k.out` is a set representing cardinal k, so this is k copies of the same U.
- Arbitrary M, N and surjection pi: `(M N : C) (π : M ⟶ N) [Epi π]`.
  Exact match: surjection means categorical epimorphism here, and no lifting
  hypothesis on U is inserted.
- Existence of a subobject M' of M: `∃ (M' : C) (ι : M' ⟶ M), Mono ι ∧ ...`.
  Exact match: a mono with arbitrary domain represents a subobject up to iso;
  the later clauses and size are invariant under this choice of representative.
- M' surjects onto N by restriction of pi: `Epi (ι ≫ π)`. Exact match to the
  same composite, not an unrelated epi onto N.
- Bound: `size M' ≤ c (size N)`. Exact non-strict inequality and quantifier order.

Edge cases: no nonempty assumption on coproduct indices. `c 0` uses the empty
coproduct. Every object has at least its bottom subobject, so its size is never
zero; in particular the zero object's size is one, not zero. When N is zero,
there are no proper subobjects, and the zero subobject of M supplies the required
epi onto zero. M = zero and the zero category are included. Schemes, n and
characteristic are not parameters of this categorical statement; their empty,
zero and positive-characteristic specializations acquire no added restriction.
Universes u and v are independent and declared; subobjects are v-small by the
Grothendieck instance and the required coproduct is v-small. There is no u = v
or small-object-category requirement, nor any unbound binder.

Independent duplicate searches used different wording from the worker:
`msearch.py leansearch` on "Every epimorphism in a Grothendieck category restricts
 to an epimorphism on a subobject with cardinally bounded subobject lattice"
returned Internal Server Error (unavailable, not evidence of absence).
`msearch.py leanfinder` on "An epimorphism admits a smaller domain whose subobject
cardinality is bounded by the coproduct of copies of a separator indexed by
subobjects of its codomain" returned generator/coproduct epi criteria, larger
subobjects in EnoughInjectives, and the strong-generator escape lemma, none of
which states this bounded restriction of an arbitrary epi.
`msearch.py loogle` on `CategoryTheory.Epi, CategoryTheory.Mono, Cardinal.mk`
returned no hits. `msearch.py grep` on
`subobject.*cardinal|cardinal.*subobject|bounded.*epi` in CategoryTheory found
HasCardinalLT and colimit-size results, not this statement. Direct rg on
Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json also found
no existing declaration of the lemma: the nearby BoundedSubobjectSize theorem
classifies objects of bounded size, and KInjectiveCriterion concerns complexes.
No new definition node or dependency module is needed; size and c are local
expressions in existing cardinal, subobject and coproduct notions, not private
copies of categorical definitions.

No mathematical mismatch was found, and the theorem signature is unchanged.
The repair adds the DAG dependency ids to the three-step proof docstring, so
stage 3 sees which nodes justify the generator choice and cardinal estimate.
The node's lean.statement now stores the literal multiline signature from the
file. No item statement correction was made. The only proof is the named
`exists_subobject_surjecting_bounded_size` theorem with `sorry`; there are no
hollow definitions or proved auxiliary facts. Remote single-file compilation
passed with exit code 0 and no warnings before the docstring-only repair; the
final module is compiled again by the delivery checks.
