## Worker report

The module `Sheaf.AlgebraicGeometry.RegularPointBlowupGeometry` states
`AlgebraicGeometry.Scheme.regular_point_blowup_geometry`, with its sole proof `sorry`.
No definitions, dependency modules, or new nodes are needed. The node's statement,
dependencies and proof are unchanged. Its eight-step proof is recorded in the theorem
docstring. Source read: `literature/stacks-project/resolve.tex`, lemmas `lemma-blowup`
and `lemma-blowup-regular`, Tags 0AGQ and 0AGR, lines 449–530. The latter's Cartier
local equation gives the dimension calculation for closed exceptional points.

The preserved previous-worker diagnosis confused the reviewed stage-1 split with a
completed Lean statement. The current node is split and reviewed but has no Lean
record; Q13's report explicitly says no Lean file was written. This stage-2 delivery
only attaches the Lean statement and leaves that split intact.

Every hypothesis and clause is rendered as follows:

- The scheme is `X : Scheme.{u}`; its integral condition is `[IsIntegral X]`.
- Noetherian, explicitly locally Noetherian and quasi-compact in the node, is
  `[IsNoetherian X]`. This Mathlib class extends `IsLocallyNoetherian X` and
  `CompactSpace X`.
- Regularity is the recorded `hX : IsRegularScheme X`, which is
  `IsLocallyNoetherian X ∧ IsRegular X`. Its upstream `IsRegular` asserts regularity
  of every stalk. This includes exactly the node's local Noetherian regularity.
- The point and its closedness are `p : X` and `hp : IsClosed ({p} : Set X)`.
- The local dimension hypothesis is `hdim : ringKrullDim (X.presheaf.stalk p) = 2`.
- The reduced closed point is the existing Mathlib construction
  `IdealSheafData.vanishingIdeal ⟨{p}, hp⟩`. Its docstring explicitly identifies its
  quotient with the reduced induced closed subscheme. Thus this is the maximal
  ideal at p, rather than an arbitrary ideal supported at p or a thickening.
- The canonical scheme and structure morphism are that ideal's `.blowup` and
  `.blowupMap` from the dependency's recorded module, repeated explicitly in the
  signature to avoid local aliases or non-unfoldable `let` binders.
- Integrality of X' is the first conjunct, `IsIntegral ...blowup`.
- Regularity of X' is the second conjunct, `IsRegularScheme ...blowup`.
- Noetherianity of X' is the third conjunct, `IsNoetherian ...blowup`.
- Properness is `IsProper ...blowupMap`, the fourth conjunct.
- Being an isomorphism over the complement of p is
  `IsIso (...blowupMap ∣_ (⟨({p} : Set X)ᶜ, hp.isOpen_compl⟩ : X.Opens))`.
  This is the canonical restriction to the inverse image of the actual open complement.
- The final clause quantifies every `q : ...blowup`, assumes that its singleton
  is closed and that `...blowupMap q = p`, and concludes
  `ringKrullDim (...blowup.presheaf.stalk q) = 2`.

Recorded statement-dependency declarations read and used:

- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`; its nonempty and domain-of-sections fields agree
  with the node's equivalent reduced/irreducible condition.
- `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`,
  `AlgebraicGeometry.IsRegularScheme`; its full definition and the underlying
  `AlgebraicGeometry.IsRegular` class in `WeilConjectures.AlgebraicGeometry.Regular`
  were read.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`. `IsNoetherian` in the same module adds
  precisely compactness, matching the item's explicit convention.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`, valued in `WithBot ℕ∞` as the supremum of lengths of prime chains.
- `def-nagata-global-blowup`: `WeilConjectures.Blowup.Gluing`,
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup`, defined by the actual gluing
  construction; `blowupMap` is its canonical map to the base.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`; universally closed implies quasi-compact, so its
  locally finite type field gives exactly the node's finite type convention.

The recorded proof-dependency modules that already have statements are imported
without `public`; statement dependencies are public imports. These include
`WeilConjectures.Blowup.FlatBaseChange`, `.Proper`, `.Complement`, the canonical
local spectrum module, the scheme-theoretic density module,
`Sheaf.AlgebraicGeometry.NagataBoundaryDivisorCartier`, `.CoherentFiniteType`, and
Mathlib's function-field, affine-stalk, pullback, localization, Noetherian and
prime-spectrum modules. The local-surface-blowup theorem has no recorded Lean
statement and is not invented here: it belongs to the proof plan only.

Edge cases checked against the source and signature:

- Empty X is excluded by integrality and by the supplied p, as in the node.
- Dimension zero and one centers are excluded exactly by hdim; no global
  dimension-two hypothesis is imposed on X, and no excellence or field hypothesis
  has been introduced.
- Nonrational closed points and every residue characteristic are allowed. Neither
  a rationality hypothesis nor an algebraic closure is used in the signature.
- The generic point of the exceptional divisor has local dimension one. It is
  correctly excluded from the last clause by its closedness hypothesis.
- Every closed exceptional point is included; points outside that fibre have no
  extra dimension assertion. The complement is the actual singleton complement,
  not an arbitrary smaller dense open.
- All objects live in the explicitly bound arbitrary universe u. All variables
  are explicit; there are no auto-bound implicits or local notation definitions.

Searches for an existing statement:

- `msearch.py leanfinder`, query: “Blowing up a closed regular point of local
  dimension two on an integral regular Noetherian scheme preserves regularity and
  dimension two at exceptional closed points”: eight hits, smoothness and
  normalization results only; none states this theorem.
- `msearch.py loogle`, query:
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup, AlgebraicGeometry.IsRegularScheme`:
  zero hits, unknown blowup identifier in the Mathlib search index.
- `msearch.py grep`, query `blowup|Blowup`, Mathlib `AlgebraicGeometry`: zero hits.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for regular/blowup combinations,
  point ideals and the item id: no exact existing statement. Hits include
  regular-principal-center complement isomorphisms and different log/normal-crossing
  or permissible-center results. The nodal domination consumer only cites the item
  in its proof plan; it does not state this geometry lemma.
- Direct reads of `Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean`, lines 560–567,
  found the existing canonical `vanishingIdeal` of a closed subset, with its
  reduced-closed-subscheme specification. It is used directly, without a duplicate.

Validation: the first server `scompile.py` run compiled both the sandbox form and
library module form cleanly (2.9 s and 2.7 s); only the theorem has a postponed proof.
The final import inventory is checked again by the prescribed delivery dry run.
There are no statement disputes or corrections.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
