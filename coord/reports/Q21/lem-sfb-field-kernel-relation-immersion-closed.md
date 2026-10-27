## Worker report

The module `Sheaf.AlgebraicGeometry.FieldGroupoidLocallyClosedImage` states
`AlgebraicGeometry.fieldGroupoid_locallyClosed_image`, with its entire proof `sorry`.
It introduces no definition. The original node is unchanged apart from `lean`.

Hypothesis and clause correspondence:

- A field k is `(k : Type u) [Field k]`; V is written explicitly as
  `Spec (CommRingCat.of k)` throughout. The nontriviality of k is part of `Field`.
- The two arrow schemes are `{R₁ R₂ : Scheme.{u}}`. The binders `s₁ t₁ e₁ i₁ c₁`
  and `s₂ t₂ e₂ i₂ c₂` have exactly the source and target schemes specified by the
  node. In particular `cⱼ : pullback sⱼ tⱼ ⟶ Rⱼ` has the required composable-pair domain.
- `_h₁ : IsGroupoidScheme s₁ t₁ e₁ i₁ c₁` and the analogous `_h₂` are exactly the
  recorded dependency's absolute groupoid laws, including all unit, inverse and
  associative laws on points of every test scheme. There is no relative base
  structure and no equation imposing s=t.
- `a : R₁ ⟶ R₂` is the supplied scheme morphism. With the object map equal to the
  identity, source and target compatibility are `hs : a ≫ s₂ = s₁` and
  `ht : a ≫ t₂ = t₁`; unit and inverse compatibility are `_he : e₁ ≫ a = e₂`
  and `_hi : i₁ ≫ a = a ≫ i₂`.
- Composition compatibility `_hc` is `c₁ ≫ a = pullback.map ... ≫ c₂`.
  The pullback map has `a` in both arrow coordinates and the identity in the V
  coordinate. Its two commutativity proofs are obtained from hs and ht by
  composing their reverses with the right identity laws. These are proof terms,
  not extra assumptions, chosen maps or postponed lemmas.
- The image a(|R₁|) is `Set.range a`, using the underlying map of the scheme
  morphism. The first conclusion is
  `IsLocallyClosed (Set.range a) → IsClosed (Set.range a)`.
  Mathlib's `IsLocallyClosed` is literally existence of U,Z with U open, Z closed,
  and this set equal to U ∩ Z (Topology/Defs/Basic.lean:119).
- The final clause is `IsImmersion a → IsClosedImmersion a`. It is the second
  conjunct, so does not require a separate local-closedness hypothesis. The
  node's two conditional assertions are preserved individually and together.

Dependencies used and inspected:

- `Mathlib.Algebra.Field.Defs`: `Field` (lines 170–180); extends `CommRing` and
  `DivisionRing`, hence excludes the zero ring and supplies all inverses.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`
  (lines 469–480); Spec is the actual affine scheme, not a singleton replacement.
- `Sheaf.AlgebraicGeometry.GroupoidScheme`: `AlgebraicGeometry.IsGroupoidScheme`;
  read its full signature, docstring and all eleven operation-law fields.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, `IsClosedImmersion.iff_isPreimmersion`
  and `IsClosedImmersion.of_isPreimmersion` (lines 42–67).
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `AlgebraicGeometry.IsImmersion`
  and `IsImmersion.isImmersion_iff_exists` (lines 40–46 and 155–159). The latter
  identifies the node's closed-then-open factorization with the class used here.
- `CategoryTheory.Limits.pullback.map` (Mathlib's HasPullback.lean:270–275) is the
  canonical map on composable pairs; it is available through the groupoid import.

Proof dependencies that already have declarations are imported without `public`:
`Sheaf.AlgebraicGeometry.PerfectFieldGroupoidImageClosure` for
`exists_reduced_image_groupoid_of_perfectField`,
`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` for the nilradical subscheme, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` for
`IsClosedImmersion.existsUnique_fac_of_range_subset_range`.
The final immersion criterion's Mathlib module is already a public dependency.
`lem-sfb-field-groupoid-perfect-restriction` and
`lem-sfb-field-groupoid-open-image-closed` have no Lean records at inspection;
no module is imported for these not-yet-stated proof-only dependencies. Their
full uses remain in the theorem's proof docstring for stage 3.

Source check: read `literature/stacks-project/more-groupoids.tex`, Situation 04Q5
and Tag 04Q9 (lines 1459–1485 and 1598–1629), and the immersion criterion in the
recorded Mathlib interface for Tag 01IQ. The node already corrects the printed
R₂-red/R₁-red typo in the source proof; the module follows the node's correction.
The source's arbitrary S does not restrict the absolute specialization: absolute
groupoids are its case over Spec Z, as the dependency docstring explains.

Edge cases checked before writing:

- k has arbitrary characteristic and need not be perfect or algebraically closed.
  Perfectness is only an intermediate proof reduction, never a binder.
- Source and target need not be the same k-structure on either arrow scheme.
  The canonical composition pullback respects both different structures.
- The identity map gives the whole target space and a closed immersion. Unit-only
  subgroupoids and genuine group schemes are included, without requiring a to be
  injective for the image assertion.
- An empty arrow scheme cannot satisfy these groupoid hypotheses on Spec k:
  a unit map from the nonempty field spectrum is required. No extra Nonempty
  binder is added and no possible empty case is excluded separately.
- No finite-type, quasi-compactness, separatedness, reducedness, or perfectness
  assumption is introduced. One explicit universe u contains k and both schemes,
  as in the recorded groupoid definition; arbitrary mathematical data may be
  placed in a common universe. There is no independent too-small test universe.
- The local-closedness and immersion antecedents remain separate implications;
  neither implication incorrectly assumes the other antecedent.

Searches for an existing statement:

1. `msearch.py ... leanfinder`: "The locally closed image of a morphism of absolute
   groupoid schemes on the spectrum of a field is closed, and an immersion is a
   closed immersion". Eight hits: immersion factorization, closed immersion
   definitions, the preimmersion/closed-range criterion and affine spectrum
   examples. None has the field-groupoid image assertion.
2. `msearch.py ... leansearch`: "The locally closed image of a morphism of groupoid
   schemes over a field is closed". Eight hits: locally closed ranges of
   immersions, scheme image, universally closed maps and closed immersion
   criteria. No exact statement or one-line specialization of the groupoid result.
3. `msearch.py ... loogle`: "IsGroupoidScheme, IsClosed, IsImmersion". Service
   unavailable (curl failure); recorded as unavailable, with no mathematical verdict.
4. `msearch.py ... grep`: "groupoid|locallyClosed|LocallyClosed" in
   `AlgebraicGeometry`. Twelve hits about locally closed sets/ranges and group
   schemes, none expressing this field-groupoid image theorem.
5. `rg` in the exact read-only `lean/WeilConjectures` and `lean/Sheaf` trees for
   `IsGroupoidScheme|fieldGroupoid|field_groupoid|groupoid.*[Cc]losed`, plus the item
   id in WeilConjectures: the dependency's groupoid predicate and related groupoid
   theorems, including the perfect-field image-closure theorem; no statement of
   this item. The item id has no source-library match. Exact declaration-name
   search for `fieldGroupoid_locallyClosed_image` in both roots and Mathlib is empty.
6. Read all four stmt_deps records and full recorded declarations. No missing
   notion and no unusable dependency interface was found; no extra node is needed.

Validation: prescribed scompile.py compiled the sandbox and library forms cleanly
(3.6 seconds and 3.0 seconds respectively), with no compiler warning or error.
The normal dry run and final delivery will also compile the final import list.
No statement dispute or node fault was found.

## Second reading by Q21

This is the author's separate clause-by-clause self-check, not an independent
review; the maintainer performs the independent delivery review. Reopened the
node and final module. Matched the field and its actual spectrum, both complete
septuples and IsGroupoidScheme predicates, all five morphism compatibility
conditions, the exact canonical pullback comparison and the two conditional
conclusions. In particular the second conjunct has no locally-closedness binder,
and the first has no immersion binder. The source and target maps remain
independent, and hs/ht are in the direction required by pullback.map after
reversal and identity composition. Mathlib's locally-closed predicate is exactly
the open/closed intersection in the node; IsImmersion has precisely the stated
factorization characterization. All names and universes are explicitly bound.
The full node proof, including its R₁-red correction and each cited proof node,
is in the docstring. No definitions or proofs were added; the one theorem is
sorry-only. No mismatch or statement change was needed. Added the direct public
Scheme import to make the spectrum dependency explicit before final preflight.
