## Worker report

The module `Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion` states
`AlgebraicGeometry.isIso_structureSheafMap_of_proper_flat_fiberwise`, with `sorry` as its
only proof. No definitions, new nodes, dependency replacements or statement corrections
are needed. The source was read at https://stacks.math.columbia.edu/tag/0E62 and in
`/home/ubuntu/c1-stacks-review/perfect.tex:8047–8095`, label `lemma-proper-flat-h0`.
The node asks precisely for clause (a), not the source's additional derived splitting (b).

The correspondence with every hypothesis and conclusion is:

- Schemes `X` and `S` and the morphism `f : X → S` are `{X S : Scheme.{u}} (f : X ⟶ S)`.
  The explicit morphism equips `X` with its structure morphism over `S`; no unrelated
  preselected `X.Over S` is imposed.
- Properness is `[IsProper f]`, flatness `[Flat f]`, and finite presentation
  `[LocallyOfFinitePresentation f]`. This last binder is equivalent to finite presentation
  here: properness supplies quasi-compactness by UniversallyClosed.lean:167 and
  quasi-separatedness by Separated.lean:68. Thus neither compactness condition is dropped.
- Every point and its canonical fibre map are represented by
  `hfiber : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop`.
  `f.fiber s` is the pullback along `S.fromSpecResidueField s`; its projection to
  `Spec κ(s)` is `fiberToSpecResidueField`. Its `appTop` maps
  `Γ(Spec κ(s), O)` to `Γ(X_s, O)`. Composing with the inverse of `Scheme.ΓSpecIso`
  gives exactly the canonical map from `κ(s)` in the node; composing with an isomorphism
  does not change whether a map is an isomorphism. No geometric-fibre condition is added.
- `f_* O_X ≅ O_S` via the canonical map is `IsIso f.c`. The inherited `c` is the natural
  transformation from `S.presheaf` to the direct-image ring presheaf of `X`.
  Its components are `f.app U` on every open `U`. Both presheaves are sheaves and the
  category of sheaves is full in presheaves, so an isomorphism here is the same sheaf
  isomorphism. A ring-sheaf isomorphism along this canonical map is also an
  `O_S`-module isomorphism, with its canonical scalar action.
- After every base change is
  `∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (pullback.snd f g).c`.
  The recorded base-change conventions identify `pullback f g` with `X_T` and
  `pullback.snd f g` with its structure map to `T`. There is no condition on `g`.
  The resulting canonical isomorphism is compatible with the original one by the
  naturality of the scheme maps; the statement does not substitute an arbitrary
  isomorphism for the canonical structure-sheaf map.

Dependency declarations read and used:

- `def-weil-scheme-over-base`: `AlgebraicGeometry.Scheme.Over` in
  `Mathlib.AlgebraicGeometry.Over` (lines 33–55); the explicit `f` supplies exactly its
  structure morphism data, without needing an extra typeclass binder.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` (lines 40–42).
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat` and its stalk equivalence
  `Flat.iff_flat_stalkMap` in `Mathlib.AlgebraicGeometry.Morphisms.Flat` (42–46, 106–107).
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`
  in `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` (43–48).
- `def-pc-base-change`: imported `Sheaf.AlgebraicGeometry.BaseChangeConventions`, read
  in full. Its recorded declaration `Scheme.Modules.moduleBaseChange` is module
  pullback, which this statement does not need. Its explicit recorded note and module
  docstring give the scheme base-change convention using `Limits.pullback` and its
  projections, which this statement uses directly. No substitute definition is made.

Other existing notions used are `Scheme.Hom.fiberToSpecResidueField` and `Scheme.Hom.fiber`
from `Mathlib.AlgebraicGeometry.Fiber` (34–47), `Scheme.Hom.appTop` from
`Mathlib.AlgebraicGeometry.Scheme` (184–185), and the inherited presheaf map `c`.
The docstring records both DAG proof steps and their cited theorem nodes, without trying
to formalize their proofs or importing proof dependencies just to state this theorem.

Edge cases checked: an empty base has no fibre assumptions and only empty schemes mapping
to it, so the conclusion is correct. Over a nonempty base, an empty fibre cannot satisfy
`hfiber`: the map from a nonzero field to the zero global-sections ring is not an
isomorphism. The identity morphism satisfies the statement. No reducedness, connectedness,
Noetherianity, characteristic, affineness or chosen base field is imposed. Nonreduced bases
and arbitrary nonflat base changes are included. The explicit arbitrary universe `u`
places no cardinality bound fixed by this module; `T` is any scheme in the chosen universe,
as in the dependency's fibre-product construction. There is no statement dispute.

Searches actually run for this item:

- `msearch.py leansearch`, query “proper flat finitely presented morphism fibre global
  sections residue field pushforward structure sheaf isomorphism”: unavailable, HTTP
  Internal Server Error. This is not recorded as a negative match.
- `msearch.py leanfinder`, same query: eight results about residue fields and fibres,
  including `Scheme.Hom.fiberToSpecResidueField`; no criterion theorem.
- `msearch.py loogle`, query `AlgebraicGeometry.IsProper, AlgebraicGeometry.Flat`:
  zero hits.
- `msearch.py grep`, query `proper.*flat|flat.*proper|structureSheaf.*[Ii]so`, subdirectory
  `AlgebraicGeometry`: 23 hits on flat descent and unrelated structure-sheaf isomorphisms,
  no fibrewise criterion.
- `rg` in `WeilConjectures/AlgebraicGeometry`, queries `proper.*flat`, `global.sections`,
  `GlobalSectionsBijective`, `0E62`, `proper_flat`, `properFlat`, and the item's id:
  the closest `GlobalSectionsBijective` results concern a fixed scheme over a field,
  including base change of that fixed field-scheme, not this general morphism criterion.
  Read its definition and theorem signatures and the usages in `TheoremOfCube.lean`.
  No exact statement found. Item id and tag `0E62` have no match in the source tree.
- `rg` in `lean/Sheaf/AlgebraicGeometry` for proper/flat and global-sections keywords:
  related global-sections results for varieties and finite fibres, no general criterion.
- `rg` for the item id in `dag/lean_names_upstream.json`: no match.
- `rg` for the new full declaration's final component in Mathlib, `WeilConjectures`
  and `lean/Sheaf`: no preexisting name.

Validation: `scompile.py C1 lem-sc-proper-flat-global-sections-criterion` compiled the
54-line module on the server in 1.9 seconds, with no errors or warnings.

## Second reading by C1

I reread Tag 0E62, label `perfect-lemma-proper-flat-h0`, and matched its clause (a)
against the declaration. The objects are schemes `X` and `S` in universe `u` and a
morphism `f : X ⟶ S`, rendered by `{X S : Scheme.{u}} (f : X ⟶ S)`. Properness,
flatness, and finite presentation are rendered by `[IsProper f]`, `[Flat f]`, and
`[LocallyOfFinitePresentation f]`, respectively; these are exactly the source
hypotheses and add no Noetherian, separated, characteristic, or field assumption.
The fibre hypothesis, for each `s : S`, is rendered as
`IsIso (f.fiberToSpecResidueField s).appTop`; via `Γ(Spec κ(s), O) ≅ κ(s)` this is
the source's canonical map `κ(s) → H⁰(X_s,O)`. The conclusion's first clause,
`f_* O_X ≅ O_S`, is rendered by `IsIso f.c`, the canonical structure-sheaf map.
Its universal-base-change clause is rendered, with the quantifiers in the same order,
by `∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (pullback.snd f g).c`, using the recorded
pullback convention. Every object, hypothesis, and conclusion clause therefore matches;
no mismatch was found and no code or node correction was needed.

Edge cases checked independently: an empty base imposes vacuous fibre hypotheses and
the conclusion is vacuous; an empty fibre cannot satisfy the stated isomorphism over a
nonempty base; the identity morphism satisfies the criterion; `T` and `g` are arbitrary,
including nonflat base changes; no characteristic, reducedness, connectedness,
Noetherianity, or cardinality restriction is introduced.

Searches were checked in Mathlib, `WeilConjectures`, and `lean/Sheaf` with grep/rg for
proper-flat global-sections criteria and the declaration name, and with LeanFinder,
Loogle, and LeanSearch queries recorded above. They found only the fibre primitives and
unrelated results; no existing declaration states this criterion. The dependency
declarations (`IsProper`, `Flat`, `LocallyOfFinitePresentation`, and the pullback
convention) were opened and agree with their node statements. The module was compiled
with `scompile.py`; it produced no errors or warnings.
