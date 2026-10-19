## Worker report

The node is already stated by the exact upstream declarations
`CategoryTheory.Rationalization.torsion` and
`CategoryTheory.Rationalization.instIsClosedUnderIsomorphismsTorsion` in
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization`. No Lean module is
added. The recorded definition signature is `def torsion : ObjectProperty C :=` (with the
enclosing variables `{R : Type w} [CommRing R] (M : Submonoid R) (C : Type u) [Category.{v} C]
[Preadditive C] [Linear R C]`). Its body is the object predicate `fun X ↦ ∃ m ∈ M, m • 𝟙 X = 0`.

The node's hypotheses render as follows. `𝒯` is the category `C` with `[Category.{v} C]` and
`[Preadditive C]`; linearity over the commutative ring `R` is `[CommRing R] [Linear R C]`; and the
submonoid `M ⊆ R` is `M : Submonoid R`. For an object `X : C`, the clause “there exists `m ∈ M`
with `m • id_X = 0`” is exactly the body of `torsion M C X`, using categorical identity `𝟙 X` and
the `R`-scalar action on morphisms. The required closure under isomorphisms is supplied by the
upstream instance `(torsion M C).IsClosedUnderIsomorphisms`, named
`CategoryTheory.Rationalization.instIsClosedUnderIsomorphismsTorsion`; its proof conjugates scalar
multiplication by an isomorphism, exactly as in the node's proof clause.

There are no statement dependencies. The source declaration was read in full, including its
docstring and the surrounding namespace and variables. The source module also provides
`torsion_iff`, but the node's definition is directly `Rationalization.torsion`; no private copy is
introduced.

Edge cases checked: a submonoid always contains `1`, so the empty set is not an admissible `M`. If
`0 ∈ M`, every object is torsion. For the trivial submonoid `{1}`, the predicate is `𝟙 X = 0`,
equivalently `IsZero X`. The category may be empty or have zero objects; no triangulated, nonzero,
or characteristic assumption beyond the node is imposed. Arbitrary isomorphisms are covered by the
upstream closure instance. Universes `w`, `u`, and `v` remain independently polymorphic.

Searches made:

- `msearch.py Q50 def-sfb-torsion-objects leanfinder "M torsion objects preadditive category
linear over commutative ring submonoid scalar identity zero"`: returned only module-torsion
declarations, with no exact categorical match.

- `msearch.py Q50 def-sfb-torsion-objects loogle
"CategoryTheory.Rationalization.torsion, IsClosedUnderIsomorphisms"`: zero hits; Loogle reported
the project identifier as unknown.

- `msearch.py Q50 def-sfb-torsion-objects grep "torsion"
Mathlib`: no exact categorical declaration.

- `msearch.py Q50 def-sfb-torsion-objects grep
"Rationalization\\.torsion|IsClosedUnderIsomorphismsTorsion" WeilConjectures/CategoryTheory`: no
hits from that wrapper search (inconclusive for upstream names); direct `rg` over
`WeilConjectures` located it in `CategoryTheory/DerivedCategory/Complete/Rationalization.lean`.

- Direct `rg` over `WeilConjectures` and `lean/Sheaf` found the upstream declaration and no project
duplicate. The complete source was also read through `scompile.py --source`.

- `msearch.py ... leansearch "Objects of an R-linear preadditive category killed by some scalar in
a submonoid of R"`: returned generic `Linear`, module annihilator, and torsion submodule
declarations; no exact categorical torsion property.

- `msearch.py ... loogle
"CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms"`: found the general
closure-under-isomorphisms class and its constructors, not a second torsion definition.

- `msearch.py ... grep "torsion|IsClosedUnderIsomorphisms" CategoryTheory/ObjectProperty`: found
generic closure machinery, not this torsion predicate.

- `scompile.py --source
WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization` confirmed the current
source and all enclosing binders. The older audit module path without `Complete` is stale; only
the authorized `lean` field is updated, preserving the audit and other fields verbatim.

No new node, dependency module, statement correction, or `STATEMENT-DISPUTED` issue applies.

## Second reading by Q50

I independently opened the sandbox node, the upstream module at lines 63–94, and the
node's actual source: the main-20261015 blueprint file
`sec-proetale-coefficients/sk-def-sfb-rationalization/def-sfb-torsion-objects.md`.
This source is a blueprint definition, not a Stacks tag. I also read its parent
`sk-def-sfb-rationalization/_section.md`. The child explicitly requires only a
preadditive linear category; its parent uses the same predicate in a triangulated
setting. The upstream definition and closure instance are before
`section Pretriangulated`, so they introduce no parent-only assumptions.
The current source returned by `scompile.py --source
WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization` agrees.
There is no repair note for this item and no statement correction.

Objects, hypotheses, and conclusion, matched individually:

1. The commutative coefficient ring is `{R : Type w} [CommRing R]`.
   Verdict: exact; neither a field nor a nonzero-ring assumption is imposed.
2. The category `𝒯` is `(C : Type u) [Category.{v} C] [Preadditive C]`.
   Verdict: exact; it need not be abelian, triangulated, nonempty, or have a zero object.
3. Linearity over this same ring is `[Linear R C]`.
   Verdict: exact; this gives the scalar action on morphisms and bilinear composition.
4. The multiplicative submonoid of `R` is `(M : Submonoid R)`.
   Verdict: exact; no nonzero-elements or localization restriction is imposed.
5. For each object `X : C`, the property is `torsion M C X`, with real body
   `fun X ↦ ∃ m ∈ M, m • 𝟙 X = 0` and signature
   `def torsion : ObjectProperty C :=`.
   Verdict: exact; the existential scalar may depend on the object, and the equation
   is on its identity endomorphism, not on chosen elements or cohomology groups.
6. Closure under every isomorphism is
   `CategoryTheory.Rationalization.instIsClosedUnderIsomorphismsTorsion`, whose type
   is `(torsion M C).IsClosedUnderIsomorphisms` under precisely the same binders.
   Verdict: exact. Its `of_iso` retains the witness `m` and `hm : m ∈ M` and uses
   `smul_id_eq_conj e` to rewrite the identity scalar on the target as
   `e.inv ≫ (m • 𝟙 X) ≫ e.hom`; substituting zero makes the composite zero.
   This is the node's sole proof step, with no missing dependency.

There are no statement dependencies, new nodes, or dependency modules to review.
The upstream instance is an existing proved declaration; this delivery adds no proof,
no definition, and no module. The node's `lean.statement` is verbatim the existing
source signature, and both declarations are recorded in `lean.declarations`.
The independent universe binders `w`, `u`, and `v` are all bound in the upstream file.
The new-module docstring and sorry requirements do not require rewriting upstream.

Edge cases: an empty category is permitted; no index set or scheme is involved.
A submonoid cannot be empty since it contains `1`. The bottom submonoid `{1}`
selects precisely objects with zero identity. Any zero object satisfies the predicate
using `1`. When `0 ∈ M`, every object satisfies it; in particular the zero ring is
allowed. Arbitrary characteristic is allowed, with no positive-integer or `n ≠ 0`
condition. Ring, object, and morphism universes stay independent.

Independent searches used different wording from the first worker:

- `msearch.py Q50 def-sfb-torsion-objects leanfinder "A scalar from a multiplicative
  subset annihilates the identity endomorphism of an object in a linear category"`
  returned linear-category center and endomorphism facts, not a second predicate.
- `msearch.py ... loogle "CategoryTheory.Linear.smul_comp"` confirmed the general
  scalar/composition compatibility, not another definition of torsion objects.
- `msearch.py ... grep "annihilat|smul_id" CategoryTheory` returned Schur lemmas.
- Direct `rg -n -i` with `annihilat.*(object|identity)`, `identity.*annihilat`,
  `killed.*scalar`, `torsion.*ObjectProperty`, and `def torsion : ObjectProperty`
  over Mathlib's CategoryTheory, the upstream `WeilConjectures`, and project
  `lean/Sheaf` found the exact upstream definition at
  `CategoryTheory/DerivedCategory/Complete/Rationalization.lean:75` and no second
  categorical torsion definition. I read its full enclosing variables and closure
  proof rather than relying on its name or the search result.

No mathematical mismatch was found. I preserved the existing Lean binding and all
node fields, and added this independent clause-by-clause review. No delivered Lean
file exists to compile; the delivery dry run checks the existing-declaration record.
