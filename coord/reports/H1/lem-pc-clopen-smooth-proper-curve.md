## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ClopenSmoothProper.lean` states
`AlgebraicGeometry.smooth_and_isProper_of_clopen_immersion`, with only `sorry` as its proof.
No definitions, new nodes, dependency modules, or statement corrections were needed.
The node's title and id mention curves, but its actual statement imposes no dimension
hypothesis: the delivery follows the statement exactly.

Hypotheses and clauses:

- A field K: `{K : Type u} [Field K]`.
- Schemes Y and Z: `{Y Z : Scheme.{u}}`.
- The structure morphism Y → Spec K: `(f : Y ⟶ Spec (.of K))`.
  This explicit morphism is the named structure morphism; the composite supplies Z's
  structure morphism without introducing independent structure data or an extra equation.
- Smoothness of Y over K: `[Smooth f]`.
- Properness of Y over K: `[IsProper f]`.
- Nonemptiness of Z: `[Nonempty Z]`, meaning the underlying space has a point.
- A morphism i : Z → Y: `(i : Z ⟶ Y)`.
- i is an open immersion: `[IsOpenImmersion i]`.
- i is a closed immersion: `[IsClosedImmersion i]`.
- Z → Spec K is smooth: the first conjunct `Smooth (i ≫ f)`.
- Z → Spec K is proper: the second conjunct `IsProper (i ≫ f)`.

Dependency declarations, read with their full signatures and docstrings in the local source:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, the dependency's recorded declaration.
  Its affine-local smooth ring-map definition is the same notion as the dependency's
  lifting-property formulation by Stacks 02H6, already documented in its lean record.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`,
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`; universally closed implies quasi-compact,
  so locally finite type in the class supplies the node's finite type condition.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion` (available through Smooth), the recorded
  mathlib_match: an open immersion of underlying locally ringed spaces.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` (available through Proper), the
  recorded mathlib_match: closed embedding and surjective stalk maps.

Edge cases checked before writing: i the identity gives the original smooth/proper
structure morphism; a nonempty component in a disjoint union satisfies both immersion
hypotheses. Empty Z is deliberately excluded by the node's Nonempty assumption, although
both permanence arguments would also hold for it. Empty Y cannot contain a nonempty Z.
No connectedness, dimension, perfectness, algebraic closedness, or characteristic
restriction is imposed. The universe u is explicit and arbitrary; schemes, their rings
of sections, and K can all be placed in a common universe. Every binder is explicit.
There is no mathematical dispute or node fault.

Searches (2026-10-11; msearch.py H1 lem-pc-clopen-smooth-proper-curve):

- LeanFinder query: "An open and closed immersion into a smooth proper scheme over a
  field has smooth proper composite structure morphism". Eight hits, including smooth
  composition and relative-dimension-zero composition; no combined statement. Some
  remote results use deprecated IsSmooth names; actual local Smooth source was read.
- Loogle query: "AlgebraicGeometry.Smooth, AlgebraicGeometry.IsProper". Zero hits.
- LeanSearch query: "An open and closed subscheme of a smooth proper scheme over a field
  is smooth and proper". Service unavailable: Internal Server Error; no verdict inferred.
- Mathlib grep query: "smooth_comp|IsProper.*comp|IsOpenImmersion.*Smooth", restricted
  to AlgebraicGeometry. Eleven hits: separate smooth/open-immersion and proper-composition
  facts, no combined declaration with the node's hypotheses.
- rg over WeilConjectures and lean/Sheaf for
  "clopen|smooth.*proper|Smooth.*IsProper|lem-pc-clopen-smooth-proper-curve": many
  applications and different curve results, no exact statement. A narrower search for
  "smooth.*proper.*(immersion|comp)|smooth_and.*proper|proper_and.*smooth" in both
  trees and dag/lean_names_upstream.json found only smooth proper curve compactifications.
- grep -rn of the item id in WeilConjectures returned no match.
  The chosen full declaration name was also covered by the narrower name search.

The local literature/stacks-project/morphisms.tex is absent on this machine. Read the
four primary source pages directly instead: [01VC](https://stacks.math.columbia.edu/tag/01VC)
(open immersions are smooth), [01VA](https://stacks.math.columbia.edu/tag/01VA)
(smooth composition), [01W5](https://stacks.math.columbia.edu/tag/01W5)
(closed immersions are proper), and [01W3](https://stacks.math.columbia.edu/tag/01W3)
(proper composition). The theorem docstring carries the node's two proof steps and names
both proof-dependency nodes. These sources confirm the precise permanence argument.

Validation: scompile.py compiled the module cleanly on the server in 1.6 seconds, exit
code 0, with no warnings. deliver2.py --no-push printed OK: compilation and preflight
passed except for the independent second reading, which the designated reader writes.
Nothing was pushed. The independent second reading is left to that reader.

## Second reading by H1

Independently read the node, all five statement-dependency nodes, their recorded
Mathlib declarations, and the delivered Lean file. Verdict: exact statement;
no mismatch and no change to the Lean module or node record were needed.

Object, hypothesis, and conclusion checklist (each item passes):

- Field K: `{K : Type u} [Field K]`. Read `Field` in Algebra/Field/Defs.lean:
  commutative ring plus division ring, including nontriviality and inverses.
- Scheme Y: `{Y : Scheme.{u}}`; no curve or dimension assumption in the node.
- Structure morphism of Y over K: `(f : Y ⟶ Spec (.of K))`. It is the given
  structure morphism, permitted by the project convention for explicitly named f.
- Y smooth over K: `[Smooth f]`. Read Smooth.lean:59ff: affine-locally smooth
  ring maps, precisely the dependency's notion (its record invokes Stacks 02H6).
- Y proper over K: `[IsProper f]`. Read Proper.lean:42ff: separated, universally
  closed, locally finite type. UniversallyClosed.lean:167 supplies quasi-compactness,
  hence finite type as required by the dependency; no added finiteness assumption.
- Nonempty scheme Z: `{Z : Scheme.{u}} [Nonempty Z]`. This is nonemptiness of
  its underlying point space, not nontriviality of a ring or existence of a K-point.
- Morphism i from Z to Y: `(i : Z ⟶ Y)` with the correct source and target.
- Open immersion: `[IsOpenImmersion i]`. Read OpenImmersion.lean:38: the recorded
  locally ringed space open-immersion notion, not merely an open topological map.
- Closed immersion: `[IsClosedImmersion i]`. Read ClosedImmersion.lean:45:
  closed embedding and surjective stalk maps, the dependency's sheaf-surjection
  notion. Neither an immersion alone nor a closed image suffices; both are retained.
- Smooth structure morphism of Z: `Smooth (i ≫ f)`, first conjunct.
- Proper structure morphism of Z: `IsProper (i ≫ f)`, second conjunct.
  The composite is exactly the structure morphism induced by the given inclusion.
  There is no separately chosen incompatible map Z to Spec K. All objects and
  hypotheses are universally quantified before this conjunction.

Source check: local morphisms.tex is absent. Independently retrieved and read the
actual Stacks TeX from
https://raw.githubusercontent.com/stacks/stacks-project/master/morphisms.tex,
including the starts of sections `section-smooth` and `section-proper` and the
full statements and proofs with labels `lemma-open-immersion-smooth` (01VC),
`lemma-composition-smooth` (01VA), `lemma-closed-immersion-proper` (01W5), and
`lemma-composition-proper` (01W3). These are about arbitrary schemes and have
no standing Noetherian, characteristic, dimension, or field-perfection assumptions.
Also checked the four tagged primary-source pages. The two docstring steps follow
these sources and name the node's two proof dependencies exactly.

Edge cases: identity i recovers the original properties. A nonempty summand in a
finite disjoint union is covered. Empty Z is excluded by the node itself and by
`Nonempty Z`; empty Y admits no such i. The zero ring cannot be K, matching Field.
There is no index set or integer n in this statement; zero-dimensional schemes
are included. All characteristics are included. Universe u is explicitly bound
and arbitrary, with schemes and field in a common universe as Mathlib Scheme
requires; enlarging the common universe accommodates objects initially of different
sizes. No implicit variable is left unbound and no hidden instance strengthens the
node. No connectedness, integrality, algebraic closedness, or relative dimension
is introduced.

Independent duplicate searches (msearch.py, 2026-10-11): LeanFinder query
"A subscheme inclusion that is both open and closed preserves smoothness and
properness over the base" returned eight hits, only individual open-immersion
smoothness and other immersion notions, no combined statement. Some remote names
are old; the actual installed Smooth declaration was read directly. Loogle query
`AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.Smooth` returned zero hits
(an earlier incorrectly quoted query gave a parser error and was not evidence).
LeanSearch query "A clopen immersion into a proper smooth scheme gives a proper
smooth scheme" returned Internal Server Error: unavailable, no negative verdict
inferred. Independent rg searches across Mathlib algebraic geometry,
WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json used
`proper.*smooth`, `isProper.*smooth`, `IsProper.*Smooth`,
`closed.*open.*immersion`, `clopen`, the exact declaration name and blueprint id,
and both conjunction orders. Results were separate permanence instances, general
immersion factorizations, and unrelated smooth proper curve/descended Jacobian
results; none states this node. No duplicate definition or exact existing statement
was found.

There are no new nodes, dependency modules, hollow definitions, or corrected
statements to review. Both imports supply notions actually used. The sole theorem
has only `by sorry`; header, namespace, source docstrings, blueprint tag, proof
steps, and line lengths satisfy the contract. Checked the node's lean.statement
against the file verbatim: equal from theorem keyword through conclusion, excluding
`:=`. Changes: appended this independent reading only; retained correct Lean and
node. Independent scompile.py run: exit 0, compiled in 1.7 seconds, no warnings.
