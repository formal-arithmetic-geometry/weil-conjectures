## Worker report

The module `Sheaf.AlgebraicGeometry.SubmersiveDenseOpenClosedSurjectivity` states
`AlgebraicGeometry.image_closed_eq_univ_of_universally_submersive`. Its only proof
is `sorry`. No definitions, new nodes, dependency repairs, or statement corrections
are needed. The original node is changed only in `lean`.

Source read: `literature/stacks-project/flat.tex`, Tag 0ETT,
`lemma-Noetherian-h-covering`, last paragraph (lines 10237–10277), and
`literature/stacks-project/limits.tex`, Tag 0CM2,
`lemma-reach-point-closure-Noetherian` (lines 3740–3790). The former is exactly the
trait and universal-submersivity argument for a closed subset containing the
horizontal part. The latter is used only at points outside the dense open, as
in the recorded boundary-DVR dependency. The declaration docstring carries all
five steps of the node's proof and names their dependencies.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Schemes X, Y and morphism f | `{X Y : Scheme.{u}} (f : X ⟶ Y)` |
| f of finite type | `[LocallyOfFiniteType f] [QuasiCompact f]`, the recorded conjunction |
| Y integral | `[IsIntegral Y]`, including nonemptiness |
| Y locally Noetherian | `[IsLocallyNoetherian Y]` |
| Y quasi-compact | `[CompactSpace Y]`, with no Hausdorff condition |
| Every scheme morphism T → Y | `∀ (T : Scheme.{u}) (g : T ⟶ Y)` in `hsub` |
| Base-change map X ×_Y T → T | `pullback.snd f g` |
| That map is surjective | `Function.Surjective (pullback.snd f g)` |
| A subset is open iff its inverse image is open | `∀ V : Set T, IsOpen V ↔ IsOpen ((pullback.snd f g) ⁻¹' V)` |
| Open subscheme U ⊆ Y | `(U : Y.Opens)`, with its canonical scheme structure |
| Density means closure is all Y | `(hU : closure (U : Set Y) = Set.univ)` |
| Arbitrary closed subset Z of X | `(Z : Set X) (hZ : IsClosed Z)` |
| Z contains f⁻¹(U) | `(hUZ : f ⁻¹' (U : Set Y) ⊆ Z)` |
| f(Z) is all Y | `f '' Z = Set.univ` |

Universal submersivity is written out as the node writes it, rather than introducing
another named predicate. Scheme morphisms already supply continuity. All universes
and variables are explicit; `set_option autoImplicit false` is also set. The test
schemes run over the full ambient category `Scheme.{u}`, including the identity
base change, affine traits, and empty schemes; no affine-test restriction is added.

Recorded statement dependencies used, with their source signatures and docstrings
read:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom` and `Scheme.Opens`.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  `AlgebraicGeometry.QuasiCompact`. Finite type is their conjunction, as the
  dependency record expressly prescribes.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`, `CompactSpace`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` and `CategoryTheory.Limits.pullback.snd`;
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies `HasPullbacks Scheme`.

Statement imports are public. Proof dependencies already stated are imported:
`Sheaf.AlgebraicGeometry.NoetherianImageBoundaryDvr` gives
`AlgebraicGeometry.exists_dvr_of_mem_closure_range_not_mem_range`, whose full
signature and proof docstring were read;
`Mathlib.RingTheory.DiscreteValuationRing.TFAE` gives
`IsDiscreteValuationRing.ringKrullDim_eq_one`;
`Mathlib.RingTheory.KrullDimension.Basic` gives `ringKrullDim`;
`Mathlib.RingTheory.DiscreteValuationRing.Basic` gives `IsDiscreteValuationRing`.
The other proof dependencies are supplied by the statement imports: the Noetherian
open/closed finite-presentation node is a Mathlib leaf using the Noetherian,
immersion and finite-presentation instances described in its `mathlib_match`;
the quasi-compact open-immersion node uses
`AlgebraicGeometry.locallyOfFiniteType_of_isOpenImmersion`; the spectrum and
fibre-product nodes use `AlgebraicGeometry.Spec`, `Spec.map`, and the pullback API.

Edge cases checked before drafting:

- Empty Y is already excluded by integrality; no additional nonemptiness is added.
- Empty X cannot satisfy `hsub`: its identity base change would not surject onto
  nonempty Y.
- Empty U cannot be dense in integral Y. U = Y is allowed and forces Z = X,
  reducing the conclusion to the surjectivity supplied by `hsub`.
- Z = X is allowed. Z = ∅ is impossible under the containment and density
  hypotheses, since f is surjective and U is nonempty.
- Empty test schemes T are included: both the surjectivity and open-set criteria
  hold there. No field, characteristic, reducedness of X, or separatedness
  restriction occurs.
- For Y a field spectrum, the only dense open is Y, giving the preceding
  surjectivity case. For a DVR base with U its generic point, the closed-point
  contradiction is precisely the proof in the docstring.

Searches on 2026-10-24 (the wrapper saved the exact results in `searches.jsonl`):

- `msearch.py … leanfinder` with query “For a finite type universally submersive
  morphism to a Noetherian integral scheme every closed subset containing the
  preimage of a dense open maps onto the base”: 8 hits, concerning dominance,
  universal closedness, integrality or finite morphisms; no match.
- `msearch.py … leansearch` with query “Closed subsets containing the preimage of
  a dense open under a universally submersive scheme morphism surject onto an
  integral Noetherian base”: 8 hits, including
  `AlgebraicGeometry.surjective_of_isDominant_of_isClosed_range` and
  `Surjective.of_universallyClosed_of_isDominant`; neither has the hypotheses
  or conclusion of this node.
- `msearch.py … loogle` with query `"IsQuotientMap", "closure"`: 0 hits.
- `msearch.py … grep` with query
  `universally.?submersive|UniversallySubmersive|submersive.*closure` in
  `AlgebraicGeometry`: 0 hits.
- `rg` in `lean/WeilConjectures` for universal submersivity and submersivity with
  density: no scheme statement or predicate; the broader “submersive” query
  found only Jacobian presentations. Searching the item id there found no hit.
- `rg` in `lean/Sheaf` found
  `AlgebraicGeometry.AlgebraicSpace.MapIsUniversallySubmersive` in
  `SpaceSubtrusive.lean` and its consumers. Its full definition was read: it is
  a predicate on presheaf maps, quantifying over algebraic-space base changes
  and using the algebraic-space point construction. It is not the scheme
  base-change signature of this node. No theorem states the item.
- Exact declaration-name searches in Mathlib, `lean/WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no existing declaration.

The prescribed example `CompactObject.lean` now contains only a withdrawal notice;
its node points to `WeilConjectures.CategoryTheory.CompactObject`. The new file
follows the required module/public-import/exposed-section convention.

No statement dispute or node fault was found.

## Second reading by Q77

On a second pass I compared the unchanged node statement with the complete file.
Finite type has both conjuncts; Noetherian has both local Noetherianity and compact
underlying space; integrality is on Y alone. The quantified projection is the
second projection to T, not the first to X. The openness equivalence has exactly
both directions for all subsets, together with surjectivity. U is an arbitrary
open and density is the literal closure equality; Z is an arbitrary closed set,
not the closure of f⁻¹(U). Containment is in the specified direction and the
conclusion is equality of the set-theoretic image with the whole target.
No hypothesis or conclusion changed during this second pass. No independent
sub-agent was started, in accordance with the dispatcher brief; the maintainer
performs the independent delivery review.
