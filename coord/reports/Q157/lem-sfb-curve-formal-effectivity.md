## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.CurveFormalEffectivity`.
Main declaration: `AlgebraicGeometry.ProperCurveFamily.formal_effectivity`.
This is a stage-2 statement with one `sorry`, and no postponed definition data.
The three data-complete helpers instantiate quotient spectra, quotient transition
maps, and the quotient inclusion into Spec A. They belong to this node's canonical
formal-system coordinates, rather than introducing another curve-family definition.

Source read: Stacks `quot.tex`, situation-curves and Tag 0D58
(lemma-curves-existence), including its proof; `artin.tex`, definition-formal-objects;
`spaces-more-morphisms.tex`, Tag 0E7R and proof. The current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`
was also read. This is a supporting node, not a blueprint unit statement.
The node explicitly permits arbitrary residue fields. Although Artin's definition
of a formal object imposes finite type of the residue field, the actual 0D58 proof
and its 0E7R construction apply to every complete Noetherian local ring. No such
extra restriction is introduced here.

Hypothesis and clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Complete Noetherian local commutative ring A, maximal ideal m | `(A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]` |
| Positive orders n >= 1 | `n : ℕ` represents the source order `n + 1`, including order one at `n = 0`. |
| Base Spec(A/m^n) | `effectivityBase A n` is `Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)))))`. |
| Actual algebraic-space sources | `(X : ∀ n : ℕ, ProperCurveFamily (effectivityBase A n))`; `X n` retains its `space : AlgebraicSpace (Spec (.of A))`, not a representing scheme or isomorphism class. |
| Flat | First conjunct of `(X n).isCurve`: `AlgebraicSpace.MapToSchemeIsLocally (@Flat)`, tested on representable etale scheme charts. |
| Proper: separated | `MapToSchemeIsSeparated`, the representable closed-immersion diagonal. |
| Proper: finite type | `MapIsQuasiCompact` and `MapToSchemeIsLocally (@LocallyOfFiniteType)`. |
| Proper: universally closed | `MapToSchemeIsUniversallyClosed`, closedness on point spaces after every scheme base change. For a morphism to a scheme this is the standard universally closed property; testing on schemes also detects it after algebraic-space base change, etale locally on that base. |
| Finitely presented | Quasi-compactness, `MapIsQuasiCompact (pullback.diagonal projection)`, and `MapToSchemeIsLocally (@LocallyOfFinitePresentation)`. |
| Every geometric fibre has dimension <= 1 | Last conjunct of `IsProperCurveFamily`: every algebraically closed field Ω and every `Spec Ω → T.left` has `topologicalKrullDim (AlgebraicSpace.Point (pullback ...)) ≤ 1`. This is the existing atlas topology and the Mathlib topological Krull dimension, not dimension of the set of lifts. |
| Objects and arrows over Spec Z | The existing families and natural transformations are viewed on `Over (Spec A)`. Every family over Spec(A/m^n) already has its forced composite map to Spec A. This is just the slice description of the same algebraic space over that quotient scheme; it does not impose an additional A-structure. Every such scheme has its canonical Spec Z structure. |
| Arrows are base-linear isomorphisms after cartesian base change | `i n` is the map `X_n → X_(n+1)` and `hcart n` is its cartesian square over `yoneda.map (effectivityBaseStep A n)`. |
| The specified adjacent isomorphisms, not merely their existence | Given the source's τ_n : X_(n+1) × S_n ≅ X_n, set `i n = τ_n.inv ≫ pullback.fst`. Conversely the unique map from a cartesian square to the canonical pullback is an isomorphism; its inverse is τ_n. Thus `(i, hcart)` retains exactly the supplied transition data. Iterated transitions are their composites and impose no additional independent cocycle data. |
| An effective object of C(A) | `∃ Y : ProperCurveFamily (Over.mk (𝟙 (Spec (.of A))))`. All of the preceding family conditions are part of `Y.isCurve`. |
| Specified reduction isomorphisms | `∃ e : ∀ n, pullback Y.projection (yoneda.map (effectivityBaseι A n)) ≅ (X n).space.obj.obj`. |
| The isomorphisms are over each quotient base | First concluding conjunct: `(e n).hom ≫ (X n).projection = pullback.snd ...`. |
| Compatibility with all given transitions | Second concluding conjunct: `(e n).inv ≫ pullback.fst ... = i n ≫ (e (n + 1)).inv ≫ pullback.fst ...`. These are the induced maps X_n → Y. Together with base linearity and the canonical quotient maps, equality of the two pullback projections gives exactly compatibility with τ_n. Adjacent compatibilities compose to give every higher-order compatibility. |

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` and
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `IsPullback`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicSpace.IsEtale`, `IsRepresentableWith`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, used in the existing
  family predicate, with empty-space value bottom.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`,
  `IsSeparated`, `UniversallyClosed`, with their etale-chart/point-space counterparts
  already supplied by the family dependency.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and
  `QuasiCompact`, used in those family conditions.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` (the complete and
  separated adic condition of the completion dependency).
- `Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs`: `IsLocalRing.maximalIdeal`.
- `Mathlib.RingTheory.Ideal.Quotient.Operations` (and its Defs import):
  `Ideal.Quotient.mk`, `Ideal.Quotient.factor`.
- `Mathlib.CategoryTheory.Comma.Over.Basic`: `Over.mk`, `Over.homMk`,
  `Over.mkIdTerminal.from`.
- The size dependency is a convention, not a declaration: explicit `universe u`,
  `A : Type u`, and `Scheme.{u}`-based family sites implement it.
- Reused landed node `def-sfb-proper-curve-moduli`, whose module
  `Sheaf.AlgebraicGeometry.ProperCurveModuli` defines `ProperCurveFamily` and
  `AlgebraicSpace.IsProperCurveFamily`. Its full definition and component docstrings
  were read. It is added to the item's `stmt_deps`, as permitted for landed notions.
  No dependency module or new node is required.

All recorded and available proof-dependency modules are imported privately, including
low-dimensional schematicity, quotient base change, projectivity and ampleness,
Picard lifting, Noetherian permanence, flat-module powers, flat localization,
and proper fibre-dimension semicontinuity. Three proof dependencies have no recorded
Lean interface in the read repository and therefore no module to import:
`lem-sfb-space-field-extension-dimension`, `lem-sfb-thickening-of-scheme-space`, and
`lem-sfb-polarized-formal-algebraization`. None is needed to state this theorem.
Their uses are retained in the eight-step theorem docstring, following the node's proof.

Edge cases checked before drafting and again against the resulting signature:
empty families/fibres (no Nonempty premise and dimension bottom <= 1), dimension-zero
fibres, disconnected/nonreduced curves, the first order n = 0 (A/m), m = 0 (constant
quotient system over a field), Artinian A with eventually stationary powers, mixed
and equal characteristic, and arbitrary residue fields. The zero ring is excluded
only by the standard meaning of local ring (`IsLocalRing` includes Nontrivial).
No independent smaller test-field universe makes the geometric-fibre condition vacuous.
The compatibility clauses do not silently replace the specified transitions by chosen
unrelated identifications. No extra polarization, projectivity, connectedness,
smoothness, reducedness or nonempty-fibre premise or conclusion was inserted.

Searches (2026-10-24, via the prescribed `msearch.py` wrapper):

- LeanFinder: `Compatible systems of proper flat algebraic space curves over powers of the maximal ideal of a complete Noetherian local ring are effective`.
  Eight results, including `IsAdicComplete.henselianRing`, flatness and affine
  transition-limit lemmas; no formal-curve effectivity theorem.
- LeanSearch: `Every compatible formal system of proper flat curves over a complete Noetherian local ring is effective`.
  Eight results about flat modules and adic completion; no match.
- Loogle: `IsAdicComplete, AlgebraicGeometry.ProperCurveFamily`.
  Zero results; the remote Mathlib-only index does not know the project declaration
  `AlgebraicGeometry.ProperCurveFamily`. The source inspection above located it.
- Mathlib grep: `formal.*[Cc]urve|[Cc]urve.*[Ee]ffectiv|ProperCurveFamily`.
  Zero results.
- `rg` in `lean/WeilConjectures`: `formal.*effectiv|curve.*algebraiz|curve.*formal|formalCurve`,
  plus the exact node id. No matching theorem or definition was found.
- `rg` in `lean/Sheaf`: `ProperCurveFamily|CurveFamily`, followed by full inspection
  of `ProperCurveModuli.lean`, `CurveInfinitesimalPushout.lean`,
  `CurveModuliGroupoids.lean` and `ProperFormalCurveAlgebraization.lean`.
  The existing family notion is reused. `proper_formal_curve_algebraization` only
  concerns scheme systems over k[[t]], so cannot be the present arbitrary complete
  local-ring algebraic-space theorem.
- Exact proposed-name grep in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no existing `effectivityBase` or `formal_effectivity`.

Validation: `scompile.py Q157 lem-sfb-curve-formal-effectivity` compiled the delivered
file in sandbox and library modes, both clean (2.6 s and 2.8 s). Earlier probes
removed an unnecessary tactic after an equality was already solved; no mathematical
statement changed. There are no statement disputes or node corrections.

## Second reading by Q157

I reopened the DAG statement and the full generated module after the clean compile
and checked them again, separately from drafting. This is a worker self-check;
the maintainer's independent review follows delivery. The complete-local-ring
hypotheses match exactly; in particular the residue field is not restricted.
Expanding `ProperCurveFamily.isCurve` verifies flat, proper, finite presentation
and geometric dimension <= 1, including empty fibres. The index shift covers
precisely all positive orders. `effectivityBaseStep` is induced by the actual
quotient factor map and is over Spec A, not an arbitrary transition on bases.
The cartesian square is exactly the specified transition isomorphism expressed
by its inverse followed by the first projection. The first concluding equation
fixes each quotient base; the second preserves each of those supplied transition
maps. Their compositions give all higher compatibilities. The actual output
is an algebraic-space family and is not forced to carry any extra structure.
The three helpers have actual data, and the sole theorem proof is `sorry`.
No mismatch was found and no mathematical changes were needed on this reading.
