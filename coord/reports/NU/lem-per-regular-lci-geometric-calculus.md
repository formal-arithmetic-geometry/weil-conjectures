## Worker report

Restores the unavailable module `Sheaf.AlgebraicGeometry.RegularLCIGeometricCalculus`
for `lem-per-regular-lci-geometric-calculus`. The node already named that module, but
its note says it was deleted as unreachable; local and live-server source lookup both
confirm it is absent. The existing codimension definition remains usable. This delivery
changes only the item's `lean` field and provides ten theorem statements, each with
`sorry` and a source-based proof docstring. There are no new definitions, dependency
repairs, or changes to the statement, statement dependencies, proof, or proof dependencies.

Hypotheses and clauses, with all theorem names in `AlgebraicGeometry`:

| Node text | Lean rendering |
| --- | --- |
| Schemes and morphisms | Explicit `Scheme.{u}` and `⟶` binders, arbitrary universe `u`; `autoImplicit false` |
| Noetherian schemes throughout | `IsNoetherian` instances on the schemes in each assertion |
| Regular schemes | Existing `IsRegularScheme`, which includes local Noetherianity and regular local stalks |
| Regular closed immersion with equation length c | Existing `IsRegularClosedImmersionWithCodimension i c`, using regular lists generating the section-map kernel near each source point |
| An immersion between regular schemes is regular | `exists_regularClosedImmersion_factor_of_regular`: `IsImmersion i`, `hY`, `hX`, and an open `U`, closed regular factor `j`, codimension function `c`, with `j ≫ U.ι = i` |
| Locally constant length | First conjunct of `regularClosedImmersion_codimension_rank_unique`: `IsLocallyConstant c` |
| Length equals conormal rank | Its second conjunct: `Module.finrank` of the cotangent module of the stalk-map kernel, over the ambient local ring modulo that kernel, equals `c y` |
| Length is intrinsic | Its final conjunct: every other equation-length function `d` equals `c` |
| Flat base change | `regularClosedImmersion_flat_baseChange`, with `Flat g`; the map is `pullback.snd i g` and its codimension is `c` evaluated on `pullback.fst i g` |
| Composition and addition | `regularClosedImmersion_comp_codimension`, with regular `i : Z ⟶ Y`, `j : Y ⟶ X`; codimension `c z + d (i z)` |
| Smooth section of relative dimension r | `regularClosedImmersion_smooth_section`, with `IsSeparated p`, `SmoothOfRelativeDimension r p`, and section equation `s ≫ p = 𝟙 S`; codimension constantly `r` |
| Smooth over regular is regular | `isRegularScheme_of_smooth_over_regular`, with `Smooth f`, regular target, and regular source as conclusion |
| Finite-type map of regular affines | `regular_affine_finiteType_closed_presentation`: `IsAffine Y`, `IsAffine X`, `LocallyOfFiniteType f`, `QuasiCompact f`, and both regularity hypotheses |
| Closed affine-space presentation exists | First conjunct: `∃ r i`, into `AffineSpace (ULift.{u} (Fin r)) X`, composite with the canonical projection equal to `f`, and `IsClosedImmersion i` |
| Every such closed presentation is regular | Second conjunct quantifies every `r,i` satisfying that projection equation and closedness, and produces `c` with the existing regular-closed predicate |
| Arbitrary regular-closed/smooth factorization | `regular_lci_virtual_dimension_formula`: intermediate Noetherian scheme `P`, maps `i,p`, `Smooth p`, equation `i ≫ p = f`, and regular equations of length `c` |
| r may vary on components | `r : P → ℕ` and `hr : ∀ z, topologicalKrullDimAt (p.asFiber z) = (r z : WithBot ℕ∞)` express the smooth fibre dimension without imposing a global constant |
| r-c locally constant | Formula's first conjunct: `IsLocallyConstant (fun y ↦ (r (i y) : ℤ) - (c y : ℤ))` |
| Intrinsic dimension equality | At each `y`, natural witnesses `dx,dy,t` identify the two `ringKrullDim`s and `Algebra.trdeg` with their finite values; `(r (i y) : ℤ) - c y = (dy : ℤ) - dx + t` |
| Residue extension κ(f(y)) → κ(y) | Explicit canonical algebra `(f.residueFieldMap y).hom.toAlgebra` in every `Algebra.trdeg`; its `toModule` in `FiniteDimensional` |
| Independence of factorization | `regular_lci_virtual_dimension_independent` uses two intermediates `P,Q`, maps `i,p,j,q`, both triangle equations, both regular length functions `c,d`, both fibre-dimension functions `r,s`; equates their integer differences at every source point |
| Quasi-finite as finite type with finite fibres | Left alternative of `hf` in `finite_residue_extension_trdeg_zero_of_quasiFinite`: `LocallyOfFiniteType f ∧ QuasiCompact f ∧ f.HasFiniteFibres` |
| Standard quasi-finite formulation | Right alternative: the recorded upstream `f.IsQuasiFinite` |
| Finite residue extension and trdeg zero | For every `y`, `FiniteDimensional` over the canonical residue-field map, and `Algebra.trdeg = 0` |
| Codimension zero, relative dimension zero, empty schemes | No positivity or nonemptiness hypotheses; all pointwise claims quantify source points, and lengths lie in `ℕ` including zero |

As in the node's preceding sentence and the earlier reviewed interface, the formula and
factorization-independence assertions keep `f` a finite-type morphism of regular affine
schemes; the intermediate schemes are arbitrary Noetherian schemes. The conormal stalk
is encoded by the cotangent module of the stalk-map kernel over the quotient ambient
local ring, canonically isomorphic to the source stalk for a closed immersion. This is
the usual conormal rank, not the fibre dimension of the ideal itself. The dimension
formula retains actual finite witnesses, avoiding any convention sending infinity to
zero. Integer subtraction includes negative virtual dimensions.

Statement dependency declarations read and reused:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and morphisms.
- `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`; finite type also uses `QuasiCompact`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth` and `SmoothOfRelativeDimension`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`; `IsImmersion` comes from `Morphisms.Immersion`.
- `def-weil-pbc-regular-sequence`: `Mathlib.RingTheory.Regular.RegularSequence`, `RingTheory.Sequence.IsRegular`, through the existing codimension predicate.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `AlgebraicGeometry.Flat`.
- `def-sbc-affine-space`: `Mathlib.AlgebraicGeometry.AffineSpace`, `AlgebraicGeometry.AffineSpace`, specialized to `ULift.{u} (Fin r)`, with canonical projection.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsLocallyNoetherian`; `IsNoetherian` includes this and compactness.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, the recorded separatedness notion `AlgebraicGeometry.IsSeparated` used for the section assertion. Properness itself is not assumed.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim`.
- `def-kun-transcendence-degree`: `Mathlib.RingTheory.AlgebraicIndependent.Basic`, `Algebra.trdeg`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`, `Scheme.residueField` and `Scheme.Hom.residueFieldMap`.
- `pqf-def-quasifinite`: `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`, `Scheme.Hom.IsQuasiFinite` and `HasFiniteFibres`. The retired Sheaf twin is not imported.
- `def-per-regular-closed-immersion-codimension`: `Sheaf.AlgebraicGeometry.RegularClosedImmersionCodimension`, `AlgebraicGeometry.IsRegularClosedImmersionWithCodimension`.

Every stated proof dependency's module is imported, using upstream twins where recorded;
Mathlib-only matches contribute their Mathlib modules. Proof-only imports are ordinary
imports, while the statement interfaces are public imports. Docstrings reproduce the
node's proof by its numbered steps: parameters and principal neighbourhoods (1–2), flat
tensor and quotient base change (3), concatenation (4), sections and conormal rank (5),
smooth ascent (6), polynomial presentation (7), flat height and fibre dimension (8),
regular-sequence dimension drop and intrinsic formula (9), finite-fibre residue extensions
(10), and the empty/zero cases (11).

Sources read: the local Stacks divisors.tex lemmas for Tags 0E9J, 067P, 067Q and 067R,
and the node's complete eleven-step proof. The old Q63 report was consulted to understand
the removed interface, then checked against the current definitions and source signatures.
The example CompactObject module is now withdrawn; its DAG record points upstream, so
current exposed-module headers in the codimension and regular-scheme modules were used.

Searches made during this assignment:

- `msearch.py leanfinder`, query “Regular closed immersions of Noetherian schemes are stable under flat base change and composition and virtual dimension equals local dimension difference plus residue field transcendence degree”: eight hits for ordinary immersion, flatness, and smoothness stability; no regular-immersion calculus.
- `msearch.py loogle`, query `IsRegularClosedImmersionWithCodimension, SmoothOfRelativeDimension`: zero hits, unknown first identifier in Mathlib.
- `msearch.py grep`, query `regularClosedImmersion|regular_lci|regular.*immersion` in Mathlib AlgebraicGeometry: zero hits.
- `msearch.py leansearch`, query “Regular immersion of regular schemes flat base change codimension dimension formula”: eight hits including flatness, ordinary immersions, closed-immersion base change, and flat regular-sequence transport; no matching whole statement.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for `regularClosedImmersion|regular_lci|lem-per-regular-lci-geometric-calculus`: no matching theorem or item tag. The existing capitalized codimension definition was found and read separately.
- Live `scompile.py --source Sheaf.AlgebraicGeometry.RegularLCIGeometricCalculus`: module source unavailable, confirming the stale attachment rather than a usable existing declaration.

Edge cases checked before writing:

1. Identity: empty regular equations, zero conormal, r=c=0, virtual dimension zero.
2. Proper clopen inclusion: zero equations are required only near points of its image;
   the existing definition correctly includes codimension zero.
3. Empty source: all equation, rank, and pointwise formula claims are vacuous; no
   nonzero-ring condition is imposed on the empty affine scheme's global sections.
4. Flat base change missing the immersed subscheme: the pulled-back length function is
   empty; no faithful-flatness or nonempty-fibre hypothesis was added.
5. Section of affine r-space: conormal rank r, giving r-c=0, including r=0.
6. Affine line over a field: at its generic point stalk dimension 0 and residue trdeg 1;
   at a closed point stalk dimension 1 and trdeg 0; both give r-c=1.
7. Spec F_p → Spec Z: c=1, r=0, intrinsic integer value -1.
8. Disconnected sources permit distinct codimensions and relative dimensions on different
   components through the functions c and r; local constancy is concluded.

No mathematical statement correction or STATEMENT-DISPUTED issue was found. The restored
module compiled cleanly against the live server build in 2.7 seconds, under the prescribed
60-second limit. All ten proofs are postponed; no theorem was proved in this delivery.
The independent review is performed by the maintainer, as the dispatcher specifies;
no other agents were started.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
