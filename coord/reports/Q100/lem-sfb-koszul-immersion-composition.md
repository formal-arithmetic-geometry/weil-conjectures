## Worker report

The module `Sheaf.AlgebraicGeometry.KoszulImmersionComposition` states
`AlgebraicGeometry.isKoszulRegularImmersionNear_comp`, with proof `sorry`.
It uses existing notions throughout. The node's statement and proof are unchanged;
its `stmt_deps` additionally cites the landed definition node
`def-sfb-koszul-regular-immersion-near`, as authorized by brief-stage2 §5.
No new nodes or dependency repairs are needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes Z, Y, X: `{Z Y X : Scheme.{u}}`, using Mathlib's schemes and morphisms.
- Morphisms i:Z→Y and j:Y→X: `(i : Z ⟶ Y) (j : Y ⟶ X)`.
- Both are immersions: `[IsImmersion i] [IsImmersion j]`. Mathlib's
  `IsImmersion.isImmersion_iff_exists` identifies this with the node's
  closed-then-open factorization.
- i is Koszul-regular locally at every point: `hi : ∀ z : Z,
  IsKoszulRegularImmersionNear i z`; similarly `hj` for j.
  The predicate explicitly chooses an open source neighbourhood V, an open
  target neighbourhood U, and a closed immersion of V into U whose composite
  is the restriction of i. Its `CotangentPresentation.IsKoszulImmersion`
  clause requires, at every point of V, an affine target open W and a finite
  tuple a in Γ(W,O) with `RingTheory.Sequence.IsKoszulRegular a` and
  `Ideal.span (Set.range a) = j.ker.ideal W`. For a closed immersion this
  `ker` agrees with the actual kernel ideal on affine opens.
- The conclusion `∀ z : Z, IsKoszulRegularImmersionNear (i ≫ j) z` is the
  same local condition for j∘i. Its ordinary immersion property is already
  supplied by Mathlib's instance `IsImmersion.comp i j`. This automatic
  property is not repeated as a tautological conjunct.
- Empty sequences are permitted by the predicate's existential `r : ℕ` and
  `Fin r → Γ(W,O)`, without any positivity requirement. Lengths can vary
  between points and charts; no codimension is fixed.
- There are no Noetherian, flatness, separatedness or codimension binders.
  Flatness in the proof plan concerns localizations only.

The local predicate is exactly the node's pointwise condition. Its explicit
source open is how “locally at every point of A” is expressed. For an immersion,
a chosen global closed-into-open factorization can be refined to these local
charts and conversely the ideal condition is local. Stacks Divisors Tag 063J
and the preceding paragraph show independence of the target open; Tag 063G
identifies the affine-generator and sheaf conditions. No statement correction
is being made.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom` (recorded by `def-pc-scheme`).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, and
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`:
  `AlgebraicGeometry.IsImmersion`, `IsImmersion.isImmersion_iff_exists`,
  `IsImmersion.comp` (the immersion clause of `def-weil-closed-immersion`
  and clause (e) of `lem-weil-pbc-proper-fp-permanence`).
- `WeilConjectures.RingTheory.KoszulRegularSequence`:
  `RingTheory.Sequence.IsKoszulRegular`, the recorded finite-sequence
  predicate from `def-weil-pbc-koszul-regular-sequence`.
- `Sheaf.AlgebraicGeometry.KoszulRegularImmersionNear`:
  `AlgebraicGeometry.IsKoszulRegularImmersionNear`, from its existing node.
  Its closed-chart notion is the existing
  `AlgebraicGeometry.CotangentPresentation.IsKoszulImmersion` in
  `Sheaf.AlgebraicGeometry.LciCotangentPresentation`, owned by
  `def-sfb-koszul-closed-immersion-chart`.
- Proof imports: `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`
  (`Scheme.Hom.ker`); `Mathlib.RingTheory.Localization.Ideal`
  (quotient-localization instance), `Mathlib.RingTheory.Flat.Localization`
  (`IsLocalization.flat`), `WeilConjectures.AlgebraicGeometry.KoszulComplex`
  (`ExteriorAlgebra.koszulComplex`), and
  `WeilConjectures.RingTheory.KoszulRegularFlatBaseChange`
  (`RingTheory.Sequence.isKoszulRegular_of_flat`).
  The affine-criterion and evaluation-pasting proof nodes currently have no
  recorded Lean declaration, so there is no import for either. They are named
  explicitly in the proof docstring for stage 3. Neither is needed to type
  this statement.

Edge cases checked against the definitions and source:

- Empty Z: the conclusion and hi have no points; no nonemptiness is imposed.
- Empty Y: an immersion from Z forces Z empty; hj remains vacuous.
- Identity and open immersions: use zero kernel and an empty tuple, whose
  Koszul complex is the ring in degree zero. The composite has the same
  interpretation. No proper-ideal or positive-length condition is imposed.
- Zero ring/empty affine chart: no points require generators; no nontrivial
  ring condition is present.
- Non-Noetherian rings and mixed local lengths are included: the predicate
  asks only for finite Koszul-regular generators on each chart.
- The three schemes use the existing category `Scheme.{u}`, with arbitrary
  explicit universe u; no unrelated smaller test-object universe is introduced.

Sources opened: `literature/stacks-project/divisors.tex`,
`definition-regular-immersion` (063J), `lemma-composition-regular-immersion`
(067Q), and `more-algebra.tex`, `lemma-join-koszul-regular-sequences` (0669).
No mathematical fault or disputed statement was found.

Searches performed through msearch.py (Q100, this item):

- LeanFinder: “Composition of Koszul regular scheme immersions”: 8 hits,
  including `IsImmersion.comp` and its multiplicativity instance, but no
  Koszul-regular composition theorem.
- Loogle: `"IsKoszulRegular", "comp"`: 0 hits.
- Mathlib grep in AlgebraicGeometry:
  `KoszulRegular|koszul.regular|regularImmersion`: 0 hits.
- LeanSearch: “Koszul regular immersions are stable under composition”:
  8 hits, consisting of ordinary immersion composition and general morphism
  property/ring-map composition results; no match.
- rg in `lean/WeilConjectures` and `lean/Sheaf`: local immersion/regularity
  searches found the existing `IsKoszulRegularImmersionNear` and the affine
  closed-chart predicate; composition searches found no corresponding theorem.
  Exact proposed name `isKoszulRegularImmersionNear_comp` is absent in both
  trees and Mathlib. The node id has no upstream Lean occurrence.

Validation uses the prescribed scompile.py and deliver2.py wrappers only.

## Second reading by Q100

The dispatcher forbids starting other agents and assigns the maintainer's
independent delivery review. This section records a separate self-rereading,
not an independent worker review.

With the node, source and final module open, rechecked: the order of arrows
is i:Z→Y, j:Y→X, and Lean's `i ≫ j` means j∘i; hi and hj quantify over
all points of the correct domains; the conclusion quantifies over all of Z.
The immersion assumptions are present separately from the near-point
predicate, which itself does not require a global immersion. The composite's
immersion is the existing Mathlib instance. Unfolded both reused predicates:
the finite tuple generates the actual closed-chart kernel ideal, not an
arbitrary ideal or a chosen regular model; the length is unrestricted and
may be zero. Local source restrictions are allowed by the node's explicit
“locally at every point” wording. No additional hypothesis or weaker/stronger
conclusion was found. No changes arose from this rereading.
