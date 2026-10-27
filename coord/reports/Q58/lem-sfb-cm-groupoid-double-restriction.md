## Worker report

The module `Sheaf.AlgebraicGeometry.CohenMacaulayGroupoidDoubleRestriction` states
`AlgebraicGeometry.cm_groupoid_double_restriction`, with its proof entirely `sorry`.
Four supporting definitions give the canonical saturation and restricted projections
appearing in this very node. Their data are explicit composites of Mathlib pullback
projections, with no choice, extra assumptions, or postponed construction. They are
listed in `lean.declarations` and each has this node's source and blueprint docstring.
No new independent notion or dependency repair is needed. The node is unchanged
outside `lean`; there is no statement correction or disputed statement.

Hypothesis-by-hypothesis and clause-by-clause reading:

| Node text | Lean rendering |
| --- | --- |
| Schemes S, U, R, B, C in the size convention | Explicit `universe u` and `{S U R B C : Scheme.{u}}`; `autoImplicit false`. There are no sites or derived categories requiring another size bound here. |
| The relative base and all structure morphisms over S | `p : U ⟶ S`, `q : R ⟶ S`, `hs : s ≫ p = q`, `ht : t ≫ p = q`. Together with `hG`, these imply that e, i, c are over S: use the identity-source, inverse-source and composition-source laws. On composable arrows the two maps to S agree because the middle endpoints agree. Thus the absolute recorded groupoid definition supplies exactly the required relative groupoid when these two equations are included. |
| Groupoid structure s, t, e, i, c | The five explicit morphism binders, `c : pullback s t ⟶ R`, and `hG : IsGroupoidScheme s t e i c`, using the recorded definition, with its composition convention c(a,b) = a after b. |
| g : B → U and j : C → B as S-morphisms | `(g : B ⟶ U) (j : C ⟶ B)`. The respective structure maps to S are `g ≫ p` and `j ≫ g ≫ p`. Giving independent structure maps and the two equality witnesses is equivalent to these determined maps; it would add only redundant presentation data. |
| W = B ×_{g,U,t} R and h_B = s after pr_R | `pullback g t` and `groupoidSaturationMap s t g := pullback.snd g t ≫ s`. |
| R_B = B ×_{g,U,t} R ×_{s,U,g} B | `pullback (groupoidSaturationMap s t g) g`, the indicated parenthesization of the same iterated fibre product. |
| s_B is the last projection | `groupoidRestrictionSource s t g := pullback.snd (groupoidSaturationMap s t g) g`. |
| t_B is the first projection | `groupoidRestrictionTarget s t g := pullback.fst (groupoidSaturationMap s t g) g ≫ pullback.fst g t`. |
| D = C ×_{j,B,t_B} R_B and h_{C/B} = s_B after pr_{R_B} | `groupoidSecondSaturationMap s t g j` has domain `pullback j (groupoidRestrictionTarget s t g)` and is `pullback.snd j (groupoidRestrictionTarget s t g) ≫ groupoidRestrictionSource s t g`. |
| Flatness of h_B at every point | `[Flat (groupoidSaturationMap s t g)]`, equivalent to the stated local-ring flatness by `Flat.iff_flat_stalkMap`. |
| Local finite presentation of h_B | `[LocallyOfFinitePresentation (groupoidSaturationMap s t g)]`. |
| Noetherian local ring at every point of every h_B fibre | `hcmB` quantifies `y : U` and `x : (groupoidSaturationMap s t g).fiber y`; its first conjunct is `IsNoetherianRing` of that fibre stalk. |
| Depth equals Krull dimension in that local ring | The second conjunct of `hcmB` is the equality between `IsLocalRing.depth` of that ring as its self-module, coerced to `WithBot ℕ∞`, and `ringKrullDim` of the same ring. |
| h_{C/B} is Cohen--Macaulay and locally finitely presented | The analogous `Flat` and `LocallyOfFinitePresentation` instances for `groupoidSecondSaturationMap s t g j`, and `hcmCB`, which quantifies `y : B` and every point of its fibre and gives the identical two local-ring clauses. |
| h_C = s after pr_R on C ×_{g∘j,U,t} R | `groupoidSaturationMap s t (j ≫ g)`. Lean's composition is left-to-right, so `j ≫ g` is the node's g∘j. Its domain is literally `pullback (j ≫ g) t`. |
| h_C is Cohen--Macaulay | The first conclusion is `Flat (groupoidSaturationMap s t (j ≫ g))`; the final universally quantified clause gives Noetherian fibre stalks and equality of their depth and dimension. |
| h_C is locally of finite presentation | The second conclusion is `LocallyOfFinitePresentation (groupoidSaturationMap s t (j ≫ g))`. |
| No surjectivity onto U assumed | There is no surjectivity hypothesis, covering hypothesis, chosen image, or extra property of g or j in the signature. The open-image cover belongs only to the natural-language proof. |

The fibre quantifiers are equivalent to the pointwise formulation in the node:
`Scheme.Hom.fiberHomeo` identifies the whole fibre with the subspace of source
points over y, and `asFiber` identifies a source point with its unique point in
the corresponding fibre. Thus no extra geometric points or extra field extensions
are quantified over in the statement. The ring being tested is the scheme fibre's
own stalk, not the total-space stalk. No finite-dimensionality condition is added;
the depth comparison is in `WithBot ℕ∞` including infinity.

Recorded statement-dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.GroupoidScheme`: `AlgebraicGeometry.IsGroupoidScheme`;
  its full signature and all pointwise groupoid laws were read before writing.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` and its
  stalkwise equivalence `Flat.iff_flat_stalkMap`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, and the homeomorphism/point identification above.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `WeilConjectures.RingTheory.Depth`: `Ideal.depth`, `IsLocalRing.depth`;
  only the latter is needed in the signature.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; schemes have the required pullbacks through
  the recorded groupoid module's public import of Mathlib scheme pullbacks.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-size-convention` is the recorded metatheoretic convention without
  a declaration; the explicit universe gives its relevant content.

Every recorded proof dependency has its supplying module imported (plain imports
when used only by the proof): `UniversallyOpen.of_flat` in
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`;
`LocallyOfFinitePresentation.finitePresentation_appLE` and the lfp base-change
instance in the already public finite-presentation module; fppf/fpqc definitions
and comparison in `Mathlib.AlgebraicGeometry.Sites.Fpqc`; flat base change in the
already public flat module; qc/qs/lpf permanence in the corresponding finite-
presentation and `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` modules;
affine fibre products in `Mathlib.AlgebraicGeometry.Pullbacks`; finite type in
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; arbitrary field-extension CM
invariance in `Sheaf.AlgebraicGeometry.CohenMacaulayFieldExtension`; fpqc flat
and lfp descent in `WeilConjectures.AlgebraicGeometry.FlatOfFpqcCover` and
`WeilConjectures.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent`;
surjective base change in `Mathlib.AlgebraicGeometry.PullbackCarrier`.
The six proof steps are reproduced with the two inverse formulas, the open-image
corestriction, the fibre field-extension calculation, descent, and return to U.

Source checks: read `more-groupoids.tex`, the complete lemmas 04MW and 04MX,
and the explicit application in the final paragraph of 04MZ; also read 045V in
`more-morphisms.tex`. Read the current blueprint's unit statement in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`.
This is a supporting node, not a change of that unit or its route.

Edge cases checked before writing:

- Empty B makes W, R_B, D, C and Z empty (C maps to B), so the conclusion is
  pointwise vacuous and flat/lfp conditions are the standard empty-source ones.
- Empty C gives the same conclusion even if B and W are nonempty.
- Empty S forces all schemes over it empty; no nonemptiness assumption is present.
- For the identity groupoid the result reduces to composition of two CM lfp maps.
- For a proper open slice B of U, h_B need not be surjective onto U. The signature
  admits it, and the proof uses its open image V instead of assuming V = U.
- Neither S nor U is assumed Noetherian, and there is no restriction on field
  characteristic, separability or generation of the residue field extensions.
- Dimension zero fibre stalks are allowed. A fibre point has a nonzero local
  ring; empty fibres introduce no stalk test, so the bottom dimension of a zero
  ring is never erroneously compared to a depth at a nonexistent point.
- There are no flat/lfp assumptions on s, t, g or j beyond the two specified
  saturation maps. The relative base equations impose only the specified S-structure.

Searches made with `msearch.py` using group Q58 and this item:

- LeanFinder, `Successive restriction of a groupoid scheme preserves a Cohen
  Macaulay locally finitely presented saturation map`: 8 results, ordinary
  restriction/permanence and affine-local lemmas, no groupoid or CM statement.
- Loogle, `"CohenMacaulay"`: 0 hits.
- Mathlib grep in `AlgebraicGeometry`, `CohenMacaulay|doubleRestrict|IsGroupoidScheme`:
  0 hits.
- LeanSearch, `Cohen Macaulay double restriction groupoid schemes saturation morphism`:
  8 hits, ordinary morphism restriction, iterated open restriction and unrelated
  subalgebra saturation; no exact statement.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  double restriction, saturation maps and CM predicates: no copy of the theorem
  or these four maps. Existing CM modules express depth/dimension inline, as
  reused here. Read the neighbouring groupoid hypersurface-slice statement.
- Exact-name collision search in Mathlib, both project roots and
  `dag/lean_names_upstream.json` for `groupoidSaturationMap`,
  `groupoidRestrictionSource`, `groupoidRestrictionTarget`, and
  `cm_groupoid_double_restriction`: no matches.

Validation: `scompile.py Q58 lem-sfb-cm-groupoid-double-restriction` compiled the
delivered module in module mode against the live published build, without errors
or unexpected warnings. All variables and universes are explicitly bound, all
Lean lines have at most 100 characters, and the only postponed proof is the named
theorem corresponding to this DAG node. Dry-run preflight is run before delivery.

## Second reading by Q58

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
