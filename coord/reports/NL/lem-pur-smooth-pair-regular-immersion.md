## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothPairRegularEquations` states
`AlgebraicGeometry.exists_regular_equations_of_smooth_closedImmersion` with proof `sorry`.
It introduces no definition and no additional theorem. Its declaration docstring carries
all seven proof steps from the reviewed Q65 split, including the fibre-only Noetherian
argument and the induction lifting successive regularity via Tag 062Y(3).

Source read: Stacks `divisors.tex`, Tag 067U,
`lemma-immersion-smooth-into-smooth-regular-immersion` (lines 5719–5740), and Tag 063J,
`definition-regular-immersion` (lines 4909–4938); `more-morphisms.tex`, Tag 0FUE,
`lemma-etale-local-structure`, first proof paragraph (lines 4880–4889).
The latter explicitly supplies an affine neighbourhood with regular equations for the
closed immersion between schemes smooth over an arbitrary base.

Hypothesis and clause correspondence:

- Schemes `S`, `X`, `Y`: `{S X Y : Scheme.{u}}`, with arbitrary explicitly bound universe `u`.
- Structure morphisms `X → S` and `Y → S`: `(p : X ⟶ S)` and `(q : Y ⟶ S)`.
- Smoothness of both: `[Smooth p] [Smooth q]`.
- The morphism `i : Y → X`: `(i : Y ⟶ X)`; closed immersion: `[IsClosedImmersion i]`.
- The phrase “over S”: `(hi : i ≫ p = q)` is the required commutative triangle.
- Every point `y ∈ Y`: `(y : Y)` is an arbitrary theorem argument.
- An open neighbourhood of `i(y)`: `∃ U : X.Opens, i y ∈ U ∧ ...`.
- This neighbourhood is affine, `U = Spec A`: the existential commutative ring
  `(A : CommRingCat.{u})` and isomorphism `(a : U.toScheme ≅ Spec A)` witness exactly this.
  No arbitrary identification of rings of functions is assumed; the affine chart is chosen.
- A nonnegative integer `b` and an ordered tuple of `b` elements of `A`: `(f : List A)`.
  Here `b = f.length`; all nonnegative lengths, including zero, occur, so no length or case
  is lost by this equivalent encoding of finite sequences.
- `Y ×_X U`: `pullback i U.ι`, using the actual open inclusion `U.ι` and the chosen pullback.
- The quotient by precisely these equations: `A ⧸ Ideal.ofList f`.
- The asserted identification with its spectrum:
  `∃ e : pullback i U.ι ≅ Spec (CommRingCat.of (A ⧸ Ideal.ofList f)), ...`.
- “As a closed subscheme of U”: the equation
  `e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList f))) =
    pullback.snd i U.ι ≫ a.hom`.
  This is the compatibility of the isomorphism with the two embeddings into `Spec A`.
  An abstract scheme isomorphism without this equation would not suffice.
- Multiplication by each equation is injective on the preceding quotient:
  the `IsWeaklyRegular` part of `RingTheory.Sequence.IsRegular A f`. The recorded definition
  has `regular_mod_prev : ∀ i (h : i < f.length), IsSMulRegular
  (A ⧸ (Ideal.ofList (f.take i) • ⊤ : Submodule A A)) f[i]`.
- The final quotient is nonzero: `IsRegular.top_ne_smul` asserts
  `(⊤ : Submodule A A) ≠ Ideal.ofList f • ⊤`, exactly this condition for the regular module.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its category of morphisms,
  `AlgebraicGeometry.Spec`, and `AlgebraicGeometry.Spec.map` (source signatures/docstrings read).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`; its affine-local
  smooth-ring-map definition agrees with the node's formally smooth plus locally finitely
  presented definition by the recorded Stacks 02H6 comparison. No relative dimension is assumed.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, a closed embedding surjective on stalks.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `U.ι` is the canonical inclusion of the actual open subscheme, so no additional open
  immersion hypothesis is necessary.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded scheme-base-change
  interface is `Limits.pullback` with projections `pullback.fst` and `pullback.snd`.
  This module's current source was read using `scompile.py --source` because the older
  local slopmaster2 checkout lacks it. The module sheaf functor `moduleBaseChange` is not
  used for scheme base change, in accordance with the dependency record's note.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`, using its
  actual structure and `IsWeaklyRegular` signature, without a private regularity predicate.

All six statement-dependency modules are public imports. All already recorded proof-dependency
modules are ordinary imports, deduplicated by module. Their statements are left unchanged.
No missing notion or unusable dependency requires a new or repaired node in this delivery.

Edge cases checked before writing:

- `Y` empty: there is no `y`, so the statement requires no nonzero quotient in this case.
- `X` or `S` empty: a supplied point of `Y` cannot occur; no nonemptiness hypothesis is added.
- `i` the identity: choose the empty sequence; its ideal is zero, and the chosen neighbourhood
  has a point, hence nonzero coordinate ring and nonzero final quotient.
- An open-and-closed component: shrink into the component, again obtaining the empty sequence.
- The zero section of affine space, including over nonreduced/non-Noetherian bases: polynomial
  coordinates give the successive injections. No regularity or Noetherian hypothesis on the
  base or its local rings occurs in the theorem.
- Codimension may vary between components: the sequence is chosen separately for each `y`;
  no globally fixed length or pure-codimension predicate is imposed.
- A nonempty list that generates the unit ideal is excluded by `IsRegular.top_ne_smul`, exactly
  as the retained source point requires; this does not discard the empty-list case.

Searches for an existing statement:

- `msearch.py` LeanFinder, query “A closed immersion between smooth schemes over a common
  arbitrary base is locally defined by a regular sequence”: 8 hits, including
  `IsClosedImmersion.Spec_iff` and smoothness/chart constituents; none supplies regular
  equations under the two smoothness hypotheses. `Spec_iff` supplies an arbitrary ideal only.
- `msearch.py` Loogle, query `"IsRegularImmersion"`: 0 hits in Mathlib.
- `msearch.py` Mathlib grep, query
  `IsRegularImmersion|smooth.*regular.*immersion|regular.*immersion.*smooth` in
  `AlgebraicGeometry`: 0 hits.
- `msearch.py` LeanSearch, query “A closed immersion between schemes smooth over the same
  base is locally defined by a regular sequence”: 8 hits, all constituent closed-immersion
  or immersion definitions/facts; no matching theorem.
- `rg` in upstream `WeilConjectures` and the project's `lean/Sheaf`, query
  `IsRegularImmersion|smooth_pair_regular|lem-pur-smooth-pair-regular-immersion`:
  upstream `AlgebraicGeometry/Morphisms/RegularImmersion.lean` defines a pure-codimension
  predicate and proves the opposite implication over a perfect field. The full definition
  and `IsRegularImmersion.smooth_comp` were read. They do not state this arbitrary-base
  implication, and a global pure codimension would add a hypothesis. Project matches include
  smooth-diagonal regular generators and pure-codimension definitions, not the given pair.
- `rg` in `dag/lean_names_upstream.json` for regular immersions found the same upstream
  `smooth_comp` and dimension-count declarations, not the requested theorem.
- The item id has no source declaration in upstream or in `lean/Sheaf`.

No statement correction, disputed assertion, or new node is needed. The current shared DAG's
Q65 `reviewed` record and the complete reviewed proof are preserved byte-for-byte as JSON
values: only `lean` is added. This avoids treating the already reviewed stage-1 split as a
field to reset or redo. The initially kept sandbox contained only dispatcher marker files,
so this delivery's module, node and report were written afresh from the current shared record.

Validation: prescribed `scompile.py NL lem-pur-smooth-pair-regular-immersion` compiled the
single module successfully in both its sandbox and library-path checks, with no errors or
warnings (approximately 1.6 s and 1.8 s respectively). No local/global library build was run.

## Second reading by NL

I opened the node, its source place, the complete Lean file, and every recorded statement
dependency. The item-by-item correspondence is:

- The node's scheme S is Lean `{S : Scheme.{u}}`; the ambient and source schemes X,Y are
  `{X Y : Scheme.{u}}`. This is the ordinary Mathlib scheme universe used by the cited
  `def-pc-scheme` declaration.
- The two structure maps X to S and Y to S are `(p : X ⟶ S)` and `(q : Y ⟶ S)`, and the
  closed immersion is `(i : Y ⟶ X)` with `[IsClosedImmersion i]`. The over-S triangle is
  exactly `(hi : i ≫ p = q)`. The smooth hypotheses are exactly `[Smooth p] [Smooth q]`;
  no relative dimension, separatedness, Noetherian, finite-type, or characteristic
  hypothesis is added.
- For the arbitrary point y in Y, Lean has `(y : Y)`. The affine open neighbourhood is
  `U : X.Opens` with `i y ∈ U`. Its affine chart is the existential `A : CommRingCat.{u}`
  and `a : U.toScheme ≅ Spec A`, so the chart is an actual spectrum and no
  ring-of-functions identification is silently assumed.
- The finite list `(f : List A)` is the node's integer b >= 0 together with the ordered
  elements f_1,...,f_b; the empty list is included. `Ideal.ofList f` is exactly the
  generated ideal.
- The base change Y times_X U is `pullback i U.ι`. The isomorphism
  `e : pullback i U.ι ≅ Spec (CommRingCat.of (A ⧸ Ideal.ofList f))` gives the stated
  quotient spectrum, and the following equality
  `e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList f))) =
  pullback.snd i U.ι ≫ a.hom` is the required compatibility with the closed subscheme
  embedding into U.
- `RingTheory.Sequence.IsRegular A f` supplies multiplication injectivity on each prefix
  quotient and `top_ne_smul` supplies the nonzero final quotient, exactly the two clauses in
  the node. No stronger pure-codimension or fixed-length conclusion is asserted.

The source check was against Divisors Tag 067U (the displayed commutative diagram and the
smooth/immersion hypotheses), Tag 063J (regular immersion), and More on Morphisms Tag 0FUE
(the affine regular-equation consequence). The Lean hypotheses are a closed-immersion
specialization of the source's immersion hypothesis, exactly as the node states. I also read
the declarations recorded for `def-pc-scheme`, `def-sbc-smooth-morphisms`,
`def-weil-closed-immersion`, `def-weil-affine-spectrum`, `def-weil-open-immersion`,
`def-pc-base-change`, and `def-weil-pbc-regular-sequence`; the imports and symbols use those
interfaces (with `Limits.pullback` for the base-change object) rather than private copies.

Edge cases remain covered: Y empty is vacuous; empty X or S cannot supply a point; the
identity or an open-and-closed component uses the empty list; b = 0 is admitted; and the
final nonzero condition is retained whenever a point y is present. No field or characteristic
assumption is introduced, and the shared scheme universe is the dependency's standard
`Scheme.{u}` universe.

Independent searches found no exact existing statement: LeanFinder for “closed immersion
smooth schemes regular sequence” returned only smoothness and immersion constituents;
Loogle for `RingTheory.Sequence.IsRegular` returned the Mathlib regular-sequence definition
and elementary lemmas; and `rg` over Mathlib, upstream `WeilConjectures`, and `lean/Sheaf`
found only the unrelated pure-codimension `IsRegularImmersion` and the parent coordinate
lemma. The source's `IsRegularImmersion` declaration is a different pure-codimension class,
so this theorem is not a duplicate.

No mismatch was found and no Lean or node statement was changed. The only delivery edit is
the item's `lean` record, whose `statement` is copied verbatim from the theorem signature.
The sole citer, `lem-pur-smooth-pair-local-coordinates`, uses this item in its proof exactly
as an affine regular-equation input, so its use still holds. Recompilation with the prescribed
`scompile.py` wrapper completed successfully with no errors or warnings.
