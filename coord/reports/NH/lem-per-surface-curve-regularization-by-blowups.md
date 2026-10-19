## Worker report

Stage 2, NH, 2026-10-19. The delivery states
`AlgebraicGeometry.exists_surface_curve_regularization_by_blowups` in
`Sheaf.AlgebraicGeometry.SurfaceCurveRegularizationByBlowups`. Its only theorem has
proof `sorry`, with the complete seven-step DAG proof plan in its docstring.
There are no new definitions, auxiliary axioms, new nodes, or dependency repairs.
The node's mathematical statement and proof are unchanged.

The previous worker's stale-dispatch diagnosis confused the two stages. The Q08
landing at `coord/ledger.md:42010` completed the stage-1 split, adding the two
normalization/point-blowup proof inputs. Its node has `reviewed`, but neither
`lean` nor `reviewed_lean`. The present delivery supplies its first Lean statement.

Read the complete source arguments at `literature/stacks-project/resolve.tex`,
labels `lemma-resolve-curve` and `lemma-blowup-curve` (Stacks Tags 0BI4 and 0BI5).
The finite-normalization hypothesis is condition (4) of 0BI4. The proof of
(4) implies (3) explicitly chooses singular closed points. Tag 0BI5 lifts that
intrinsic tower to the ambient scheme using the strict-transform comparison.
No ambient dimension, integrality, regularity, excellence, separation or field
hypothesis occurs in this result, and none was added.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A Noetherian scheme X | `(X : Scheme.{u}) [IsNoetherian X]`; Mathlib's class extends `IsLocallyNoetherian X` and `CompactSpace X`. |
| An integral closed subscheme Y of X | `(Y : Scheme.{u}) [IsIntegral Y] (j : Y ⟶ X) [IsClosedImmersion j]`. The latter is a closed embedding with surjective stalk maps, giving the actual closed subscheme, not only its support. |
| Y has dimension 1 | `(hDim : topologicalKrullDim Y = 1)`. This is the supremum of lengths of chains of irreducible closed subsets and agrees with ring Krull dimension on affine spectra. |
| Normalization of Y in its function field is finite | `[IsFinite Y.fromNormalization]`, where `Y.normalization` and `Y.fromNormalization` are the recorded upstream integral-scheme normalization and its canonical map. No arbitrary finite birational replacement is substituted. |
| A finite sequence of ambient blowups, starting at X | `∃ A : OrdinaryBlowupTower X`; `A.length`, `A.level`, `A.initial`, `A.transition`, `A.center`, `A.blowupIso` and `A.blowup_fac` retain the finite sequence and its actual maps over each center. |
| Start with the given embedded curve Y | The family `C`, embeddings `ι` and `e₀ : C 0 ≅ Y`, with `ι 0 ≫ A.initial.hom = e₀.hom ≫ j`, identify the initial closed immersion with j over the initial ambient identification. |
| The successive curves are closed subschemes | `(∀ i, IsClosedImmersion (ι i))`. These are the actual subscheme embeddings used in the strict-transform condition. |
| Each blowup is at a reduced closed point | At stage i, choose `p : C i.castSucc` with `IsClosed {p}`; the radical equality `(A.center i).radical = A.center i` and support equality `((A.center i).support : Set _) = {ι i.castSucc p}` specify exactly the reduced closed point in the ambient scheme. A closed immersion takes the closed singleton to a closed singleton. Radical ideals are uniquely determined by their vanishing sets on affines, so this does not allow a thickening. |
| Each center is singular on the current strict transform | `¬ IsRegularLocalRing ((C i.castSucc).presheaf.stalk p)`. The singularity is measured on the curve, not on the ambient scheme. |
| Take successive strict transforms, with scheme structure | `∃ e : C i.succ ≅ (A.center i).strictTransform (ι i.castSucc)` together with the equality between `e.hom ≫ strictTransformMap ...` and `ι i.succ ≫ (A.blowupIso i).hom`. This identifies the next embedded curve over the actual ambient blowup. The recorded definition uses the scheme-theoretic image of the complementary open locus in the fiber product. |
| The final strict transform is regular | `IsRegularScheme (C (Fin.last A.length))`, exactly local Noetherianity and regular local rings at all points. |

The data and compatibility equations merely specify the finite sequence and its
successive embedded strict transforms; they impose no additional geometric
hypothesis or conclusion. In particular the statement does not require the
ambient schemes to become regular. The embeddings and isomorphisms prevent
replacing strict transforms by unrelated regular schemes.

Dependency declarations read and used (including their source docstrings and
full signatures):

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`, as used by `IsLocallyNoetherian`.
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `Mathlib.AlgebraicGeometry.Noetherian`; this module also supplies
  `AlgebraicGeometry.IsNoetherian` with precisely local Noetherianity and compactness.
- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace`,
  `Mathlib.Topology.Defs.Filter`, the compactness field of `IsNoetherian`.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim`,
  `Mathlib.RingTheory.KrullDimension.Basic`; scheme dimension uses its topological
  counterpart `TopologicalSpace.topologicalKrullDim` from
  `Mathlib.Topology.KrullDimension`, with the same chain-length convention.
- `def-sc-normalization`: `AlgebraicGeometry.Scheme.normalization` and
  `AlgebraicGeometry.Scheme.fromNormalization`,
  `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `def-nagata-global-blowup`: `AlgebraicGeometry.Scheme.IdealSheafData.blowup`
  and `blowupMap`, `WeilConjectures.Blowup.Gluing`, used by the existing tower.
- `def-nagata-strict-transform`: `AlgebraicGeometry.strictTransform`, its
  blowup specialization `AlgebraicGeometry.Scheme.IdealSheafData.strictTransform`
  and `AlgebraicGeometry.strictTransformMap`,
  `WeilConjectures.Compactification.StrictTransform`.
- `def-weil-regular-scheme`: `AlgebraicGeometry.IsRegularScheme`,
  `Sheaf.AlgebraicGeometry.IsRegularScheme`. Read its underlying
  `AlgebraicGeometry.IsRegular` in `WeilConjectures.AlgebraicGeometry.Regular`
  and Mathlib's `IsRegularLocalRing`.
- Added the already landed `def-trf-ordinary-resolution-rule` to `stmt_deps`:
  `AlgebraicGeometry.OrdinaryBlowupTower`,
  `Sheaf.AlgebraicGeometry.OrdinaryResolutionRule`. Its standalone tower is
  defined for **any** scheme. The separate rational-resolution input and
  smooth-functorial rule in that module are not used, so no rational-base or
  finite-type-over-a-field restriction is imported into the statement.

Statement modules import the corresponding APIs; the definitions underlying
Noetherianness, dimension and the tower are also supplied transitively by them.
Stated proof inputs are imported non-publicly:
`WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent`,
`Sheaf.AlgebraicGeometry.NoetherianQuasicoherentSubmodules`,
`WeilConjectures.Compactification.StrictTransformBlowup`,
`WeilConjectures.Blowup.Proper`, and
`Mathlib.AlgebraicGeometry.Morphisms.Proper`. The closed-immersion and Noetherian
Mathlib modules also supply the composition/base-change and finite-type
permanence proof inputs. The two stage-1 children
`lem-per-finite-curve-normalization-regular` and
`lem-per-singular-curve-point-blowup-step` have no Lean records yet; they are
proof dependencies only, require no additional notion in this statement,
and have no modules to import. No import cycle is introduced.

Edge cases checked before writing:

- If Y is already regular, take a tower of length zero, C(0)=Y and the
  identity initial identifications. `Fin A.length` is empty, so there is no
  demand for a singular point and the final clause is the original regularity.
- An empty Y cannot satisfy `IsIntegral Y`, and a zero-dimensional integral
  scheme fails `hDim`; these are the source's explicit restrictions.
- The ambient X may be reducible or nonreduced and may have any dimension.
  Radical singleton centers still specify reduced points of that ambient X.
- Nonseparated Noetherian schemes and all residue characteristics are included.
  There is no field base, characteristic, projectivity or excellence assumption.
- The cusp illustrates the genuinely nonzero tower case: its singular closed
  point has a nonregular local ring, and blowing up that point regularizes it.
- Curves with infinite normalization are intentionally outside the hypothesis;
  finiteness is not silently derived from Noetherianness alone.
- All schemes and the recorded canonical normalization use the same arbitrary
  universe `u`; no independent small test universe or forced equality occurs.
- All variables/universes are explicit, and no file-local notation or instance
  is used. There is no hollow definition or tautological added hypothesis.

Searches for an existing statement (2026-10-19):

- `msearch.py NH <item> leanfinder`: "An integral curve in a Noetherian scheme
  with finite normalization becomes regular after finitely many blowups at
  singular closed points". Eight hits: `IsIntegral` and Mathlib's morphism
  normalization construction/instances; no regularization theorem.
- `msearch.py NH <item> loogle`: `AlgebraicGeometry.Scheme, IsRegularLocalRing`.
  Zero hits.
- `msearch.py NH <item> leansearch`: "An integral curve whose normalization
  is finite has regular strict transform after finitely many blowups at
  singular closed points of the curve in an ambient Noetherian scheme".
  Eight normalization map/instance hits, none stating this theorem.
- `msearch.py NH <item> grep`: `regularization|strictTransform|pointBlowup|resolve.?curve`
  in Mathlib's `AlgebraicGeometry`: zero hits.
- `rg` of `regularization|Regularization|PointBlowup|pointBlowup|singular.*blowup|point.*tower|BlowupTower|blowup.*sequence|blowup.*tower`
  in the upstream `WeilConjectures` and side `lean/Sheaf`: found the landed
  unrestricted `OrdinaryBlowupTower`, rational surface resolution theorems and
  the parent embedded-surface-resolution theorem; none gives regularization of
  a curve in an arbitrary Noetherian ambient scheme. Reused the tower interface.
- `rg` of `lem-per-surface-curve-regularization-by-blowups` in upstream
  `WeilConjectures`: no hits. Side search finds only its citation in the
  proof plan of `EmbeddedSurfaceCurveResolution.lean`.
- Read the upstream strict-transform scheme/image definition and blowup
  specialization, the actual radical/support ideal-sheaf definitions in
  Mathlib, and the general tower declaration. These give every needed notion
  without a new definition node.

Validation: `scompile.py NH lem-per-surface-curve-regularization-by-blowups
<module>` succeeded on both sandbox and library-name compilations (2.8 s and
2.5 s respectively), without errors or warnings. All module lines have length
at most 100. Delivery preflight and final delivery results are recorded below.

No `STATEMENT-DISPUTED` issue or statement correction was needed.

The prescribed `deliver2.py NH lem-per-surface-curve-regularization-by-blowups
--no-push` succeeded: `OK (dry run): commit bf500f27bc passes the preflight
and compiles; nothing pushed`. The final packet consists of exactly the module,
the item's node JSON, and this report. Independent review is the maintainer's.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
