## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiAffineFpqcDescent` states
`CategoryTheory.Over.DescentDatum.isEffective_of_isQuasiAffineHom_fpqc`, with `sorry`.
It defines no new notion. The source is Stacks Project, Descent, Tag 0247,
`lemma-quasi-affine`, read in `literature/stacks-project/descent.tex` at lines 9225–9322.
The node is its one-member-cover specialization; no statement correction is needed.
The declaration docstring includes all ten proof steps from the node, including the
finite-coproduct check, affine-envelope construction, tensor-formula compatibility
on double and triple overlaps, affine descent, and descent of the invariant open.

Each hypothesis and clause is rendered as follows:

- Schemes A and B: `{A B : Scheme.{u}}`; the specified morphism is `(p : A ⟶ B)`.
- The one-member family is an fpqc covering:
  `(hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage B)`. This uses the precoverage,
  not merely its generated topology, and imposes no global quasi-compactness on p
  beyond what the node's covering condition entails.
- A scheme V over A: `{V : Over A}`, whose underlying scheme is `V.left` and whose
  structure map is `V.hom`.
- The structure map is quasi-affine: `[IsQuasiAffineHom V.hom]`. Its recorded upstream
  class requires `(V.hom ⁻¹ᵁ U).toScheme.IsQuasiAffine` for every affine open U of A.
  Mathlib's `Scheme.IsQuasiAffine` includes `CompactSpace` and immersion into Spec of
  global sections, and the immediately following instance makes that canonical map
  an open immersion. Thus this is precisely a quasi-compact open in an affine scheme,
  rather than a possibly non-quasi-compact usage of the word quasi-affine.
- The specified isomorphism over A ×_B A and its cocycle:
  `(D : Over.DescentDatum p V)`. The dependency uses its recorded Yoneda transport
  encoding. Naturality is `transport_homMk_comp`; invertibility follows from
  `transport_self` and `transport_transport` by reversing the two maps to A. For the
  universal pair of projections its transport is the stated isomorphism; the
  `transport_transport` field is exactly phi_02 = phi_12 composed with phi_01.
  The self-identity law is implied by invertibility and the cocycle, so this encoding
  adds no hypothesis to the classical datum. The comparison between the iterated
  pullbacks V ×_B A and A ×_B V and the two pullbacks over A ×_B A is canonical.
- Effectivity: `D.IsEffective`. Expanding the recorded predicate gives
  `∃ (V₀ : Over B) (q : V.left ⟶ V₀.left),
  IsPullback q V.hom V₀.hom p ∧ ...` followed by transport invariance under q.
  The Cartesian square gives precisely V₀ ×_B A ≅ V over A (or its inverse),
  and transport invariance says that this isomorphism induces the specified phi.
  It does not merely assert that V happens to have some descended model.
- No local-finite-presentation hypothesis: no `LocallyOfFinitePresentation`, finite
  type, Noetherian, affineness of A or B, or other extra instance appears in the
  theorem. Affineness appears only in the documented proof's reduction.
- The size convention: explicit `universe u`, and all schemes, including the model
  quantified by `IsEffective`, lie in `Scheme.{u}`. The transport predicate tests all
  schemes in this same universe, including the double and triple fibre products.
  No auxiliary test universe that could make the condition vacuous is introduced.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`:
  `AlgebraicGeometry.Scheme.fpqcPrecoverage` (with `Presieve.singleton`). The
  dependency record explicitly identifies its quasi-compact-open cover condition
  with the node's finite affine-open refinement condition.
- `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`:
  `AlgebraicGeometry.IsQuasiAffineHom`, read with its full field and docstring.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`; these underlie the
  classical interpretation of the recorded descent and effectivity predicates.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`:
  `CategoryTheory.Over.DescentDatum` and `.IsEffective`, read in full including the
  explanation of their equivalence with the fibre-product isomorphism formulation.
- `def-weil-size-convention` is explicitly recorded as a metatheoretic convention
  with no declaration; the theorem is universe-polymorphic as just described.

The two stated project proof dependencies are ordinary imports:
`Sheaf.AlgebraicGeometry.AffineFpqcDescent` and
`Sheaf.AlgebraicGeometry.FpqcDescendingTypesMorphisms`. Their signatures agree with
the singleton-cover setup. The other proof imports supply the recorded Mathlib
lemmas for affine spectra and maps to them, finite scheme coproducts, clopen
idempotents, flat base change, qcqs permanence, quotient maps, and pullback points.
`lem-trf-quasi-affine-base-change` has no recorded declaration, so it is mentioned
in the proof docstring and no invented module is imported for it. The proof-only
Mathlib canonical affine embedding is supplied by the public quasi-affine import.

Edge cases checked before writing:

- Empty V is allowed: there is no nonemptiness or inhabitedness assumption, and the
  empty scheme descends to the empty B-scheme with its unique datum.
- Empty B forces A and V empty but is allowed by the covering condition and the
  same effectivity predicate. The fpqc definition allows zero affine refinements
  when the target affine open is empty.
- Identity p is included. The transport identity and cocycle give the usual
  trivial datum and V itself is a descended model.
- Non-affine A and B and non-quasi-compact covers are not excluded by replacing the
  singleton fpqc condition with an extra `[QuasiCompact p]` assumption.
- No base field, characteristic, reducedness, finiteness, or local presentation
  condition is used. The proof's empty finite coproduct is documented via Spec(0).

Searches performed with the prescribed msearch wrapper:

- LeanFinder: `A descent datum on a quasi-affine scheme morphism along an fpqc
  covering is effective` — 8 hits, on affine transition limits and descent of
  properties; no effective descent of quasi-affine objects.
- Loogle: `IsQuasiAffineHom, DescentDatum.IsEffective` — 0 hits, with unknown
  `IsQuasiAffineHom` (it is an upstream class rather than a Mathlib declaration).
- LeanSearch: `A descent datum on a quasi-affine scheme along an fpqc covering is
  effective` — 8 hits, including `HasAffineProperty.descendsAlong_of_affineAnd` and
  descent of isomorphisms; none is the sought effective-descent theorem.
- Mathlib grep: `quasi.affine|QuasiAffine|DescentDatum` in `AlgebraicGeometry` —
  quasi-affine scheme definitions and affine transition limits; no matching theorem.
- `rg` of `IsQuasiAffineHom|DescentDatum.IsEffective|fpqc` in the source project and
  `lean/Sheaf` found the recorded relative predicate and datum interface, affine
  effective descent, and descent of morphism properties, but no quasi-affine
  effective-descent theorem.
- Exact item-id and candidate declaration-name searches in source, `lean/Sheaf`,
  and `dag/lean_names_upstream.json` found no existing theorem. There is no
  `coord/repair-notes/lem-trf-quasi-affine-fpqc-effective-descent.json`.

No new nodes, dependency repairs, disputed statements, or node faults.

## Second reading by N2

This is a separate self-check with the node and final module reopened; the dispatch
brief prohibits starting another agent and assigns independent review to the
maintainer, so this section does not claim an independent worker review.

The node's morphism p, singleton fpqc condition, V over A, and relative
quasi-affineness match respectively `(p : A ⟶ B)`, `hp`, `{V : Over A}`, and
`[IsQuasiAffineHom V.hom]`. Reading the dependency's definition again confirms
that `D` carries the full isomorphism and cocycle, not just an equivalence of the
underlying sets of points. Its test schemes range over all of `Scheme.{u}`, so
Yoneda applies to the actual double and triple pullbacks. Reading `IsEffective`
again confirms that its invariant Cartesian-square conclusion supplies both the
model V₀ and compatibility with the given phi. There is no finite-presentation
assumption or assertion that the descended model itself must be affine. The
empty and identity cases remain included. The ten-step proof docstring follows
the node's proof and the Stacks source; no new definition or unsupported helper
has been introduced. No mismatch was found and no mathematical change was made.
