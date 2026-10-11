## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteThickeningCartesian` states
`AlgebraicGeometry.isFinite_iff_of_finiteOrderThickening`, with proof `sorry`.
It introduces no definitions and proves nothing. The node is unchanged apart from `lean`.

Source read: Stacks Project, More on Morphisms, Lemma 37.3.3, Tag 09ZW,
https://stacks.math.columbia.edu/tag/09ZW, especially part (8), the first proof paragraph,
and the proof of (8). The local literature checkout contains no `more-morphisms.tex`,
so the source was read on the Stacks website. Its cartesian finite-order-thickening
hypotheses and finite equivalence agree with this node. The docstring records all six
steps of the node's proof, including their dependency IDs.

Hypothesis and clause correspondence:

- Schemes `S`, `S'`, `X'`: `{S S' X' : Scheme.{u}}`, with arbitrary explicit universe `u`.
- The inclusion of the closed subscheme: `(i : S ⟶ S')`, with closed immersion contained
  in `(hi : IsFiniteOrderThickening i)`. This is the recorded definition, not a copy.
- Finite order: the same `hi` unfolds to `∃ n : ℕ, IsNthOrderThickening n i`, namely
  `IsClosedImmersion i ∧ i.ker ^ (n + 1) = ⊥`. Thus it encodes exactly the node's
  nilpotent quasi-coherent defining ideal, allowing every order including zero.
- Arbitrary morphism to `S'`: `(f' : X' ⟶ S')`, with no finiteness or other assumption.
- `X = S ×_{S'} X'` and its map `f : X → S`: the canonical pullback
  `pullback f' i` and projection `pullback.snd f' i`. The factor order is the canonical
  `X' ×_{S'} S` order of def-pc-base-change, the same fibre product with factors swapped;
  its projection to `S` is exactly the base change of `f'`.
- `f` finite: `IsFinite (pullback.snd f' i)`.
- If and only if `f'` finite: `↔ IsFinite f'`, preserving both directions.

Dependencies read and used:

- `Sheaf.AlgebraicGeometry.Thickening`: `AlgebraicGeometry.IsFiniteOrderThickening`,
  `IsNthOrderThickening`, and their full defining bodies and source docstrings.
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`: its module's explicit conventions
  for `Limits.pullback f T.hom` and `pullback.snd` as the scheme base change and map to
  the new base. The recorded primary `Scheme.Modules.moduleBaseChange` concerns modules;
  the node's own `lean.note` directs scheme citers to these existing pullback objects.
  Its declaration and the module's comparison declarations and docstrings were read.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`, the affine
  morphism with finite section ring homomorphisms on every affine open. Its definition
  and docstring were read, as was `IsIntegralHom` in Morphisms.Integral. No private
  versions of finiteness, thickenings or base change are introduced.

Edge cases checked before writing: empty source and empty base are allowed, without
`Nonempty` or nontriviality hypotheses; a thickening of an empty scheme has empty
underlying space. Order zero is allowed, forcing the defining ideal to be zero,
so this includes the identity/base-change-by-isomorphism case. Nonzero nilpotent
ideals (e.g. dual numbers) satisfy the hypothesis, whereas an arbitrary reduced
closed subscheme with nonnilpotent defining ideal does not. No characteristic,
Noetherian, separated, affine, finite-type, or chosen-order restrictions are imposed.
All schemes share the arbitrary scheme universe used by the existing dependency.
There are no test-object quantifiers or index sets with vacuous universe restrictions.
No statement fault or STATEMENT-DISPUTED issue was found.

Searches made (2026-10-11):

- `msearch.py ... leansearch "A morphism of schemes is finite if and only if its base
  change along a finite order thickening is finite"`: unavailable, Internal Server
  Error; recorded as unavailable, no verdict assigned to this service.
- `msearch.py ... leanfinder "finite morphism iff base change along a finite order
  nilpotent thickening is finite"`: eight hits, including stable-under-base-change,
  SpecMap_iff, of_comp and comp_iff; none gives nilpotent-thickening descent.
- `msearch.py ... loogle "AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsClosedImmersion"`:
  three hits on closed immersions being finite and finite-plus-mono characterizations;
  none states this equivalence.
- `msearch.py ... grep "thickening|nilpotent" AlgebraicGeometry/Morphisms`: seven hits
  on nilpotent sections and formally unramified lift uniqueness; no matching theorem.
- `rg -n "thickening.*finite|finite.*thickening|isFinite.*[Tt]hicken"` on project
  `lean/Sheaf` and upstream `WeilConjectures`: existing thickening definitions, lifting
  consumers and algebraization statements; no equivalent declaration.
- `rg -n "lem-weil-pbc-thickening-finite-cartesian"` on `dag/lean_names_upstream.json`
  and upstream `WeilConjectures`: no recorded upstream statement.
- `rg -n "isFinite_iff_of_finiteOrderThickening"` on Mathlib, upstream
  `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

Validation: server single-file compile and the required deliver2 dry run are performed;
only the expected sorry warning is acceptable. The independent second reading and
actual delivery are left to the second reader as instructed.

## Second reading by C1

I independently compared the node statement, the source (Stacks Project, More on Morphisms,
Lemma 37.3.3, Tag 09ZW, especially item (8) and its proof), and
`Sheaf.AlgebraicGeometry.FiniteThickeningCartesian`.

- Objects: the node's schemes `S`, `S'`, and `X'` are rendered by
  `{S S' X' : Scheme.{u}}`; the closed-subscheme map is `i : S ⟶ S'`; the
  finite-order-thickening hypothesis is `hi : IsFiniteOrderThickening i`; and the
  arbitrary morphism is `f' : X' ⟶ S'`. These are the same objects and hypotheses
  used by Tag 09ZW(8), with no finiteness, affine, Noetherian, separated,
  characteristic, or nonemptiness assumptions added.
- Base change: the node's `X = S ×_{S'} X'` and its map to `S` are rendered by
  `pullback f' i` and `pullback.snd f' i`, using the project's recorded pullback
  convention. This is the canonical base-change object/map, including empty
  schemes and the zero/order-zero thickening cases.
- Conclusion: the node's two clauses are rendered exactly as
  `IsFinite (pullback.snd f' i) ↔ IsFinite f'`; the iff direction and quantifier
  order are unchanged. No clause is missing or strengthened.

I read the dependency declarations `IsFiniteOrderThickening` and
`IsNthOrderThickening` in `Sheaf.AlgebraicGeometry.Thickening`, the pullback
convention in `Sheaf.AlgebraicGeometry.BaseChangeConventions`, and Mathlib's
`AlgebraicGeometry.IsFinite`. They match the notions named by the node; no
private replacement or dependency module is needed. The searches recorded by the
worker (LeanSearch, LeanFinder/Loogle, and grep over Mathlib, the project, and
upstream) found no existing declaration of this equivalence.

Edge cases checked: empty schemes and empty fibres are admitted; order zero is
allowed; nonzero nilpotent defining ideals are admitted; arbitrary characteristic
and the full scheme universe are admitted; there are no index-set or test-object
quantifiers. No mismatch was found, so no Lean or node statement change was needed.

The module compiles cleanly with the expected `sorry` proof warning under
`scompile.py`.
