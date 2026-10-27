## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceCompleteDevissageFibreNeighbourhood` states
`AlgebraicGeometry.AlgebraicSpace.exists_completeDevissage_fibre_neighbourhood`.
Its sole theorem has proof `sorry`; no definitions or proofs are added. The node is
unchanged except for `lean`.

Read the node and all nine statement-dependency statements and records, and the actual
source declarations and docstrings. Read Stacks `spaces-flat.tex`, lemma-existence-complete
(Tag 0CWJ, lines 423ff), and `flat.tex`, lemma-existence-complete (Tag 05HU, lines 1576ff),
together with the recorded complete algebra devissage definition (Tag 05HX).

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Schemes and spaces over Spec Z | `X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))` and `Y : Over (Spec (.of (ULift.{u} ℤ)))`. The lift places Z in the scheme universe; it imposes no characteristic restriction. |
| Y is a scheme and f maps X to Y | `Y` is a scheme over Spec Z and `f : X ⟶ schemeSpace Y`; `schemeSpace` is its representable fppf sheaf, with its actual Yoneda presheaf. |
| f is of finite presentation | `hfp` is exactly `MapIsLocallyOfFinitePresentation f ∧ MapIsQuasiCompact f.hom.hom ∧ MapIsQuasiCompact (Limits.pullback.diagonal f.hom.hom)`. Local finite presentation is the recorded chart test. |
| M is a finitely presented quasi-coherent module | `M : X.QCoh` uses the recorded full subcategory, and `hM : M.obj.IsFinitePresentation` uses Mathlib's local finite-free presentation predicate. No flatness or local freeness is assumed. |
| y is any point of Y | `y : Y.left`. |
| Affine pointed etale neighbourhood Y' of y | `R : CommRingCat.{u}`, `g : affineDevissageScheme R ⟶ Y`, `p : PrimeSpectrum R`, `Etale g.left ∧ g.left p = y`. Thus Y' is literally Spec R and p is y'. No residue-field isomorphism is required by the node's conclusion. |
| Actual base change X over Y' | `enlargedFibreProduct f (dimensionFlatBaseMap g)`, the existing sheaf pullback bundled as an algebraic space; its first projection is `enlargedFibreProductFst`. |
| Finitely many affine schemes W_j | `n : ℕ`, `A : Fin n → CommAlgCat.{u} R`, and the sources `schemeSpace (affineDevissageScheme (A j))`. Each W_j is literally Spec A_j. Bundling R-algebras retains the structural maps. |
| Representable etale h_j into X over Y' | `h j` has the stated source and actual base-change target; `IsEtale (h j).hom.hom` is exactly representable etaleness, not just a chartwise substitute. |
| W_j is an R-scheme by its specified structure map | `(h j).hom ≫ Limits.pullback.snd f.hom (dimensionFlatBaseMap g).hom = (dimensionFlatBaseMap (affineDevissageArrow R (A j))).hom`. This binds the algebra structure to the geometric projection. |
| Each W_j to Y' is of finite presentation | `∃ hAfp : Algebra.FinitePresentation R (A j), ...`. For morphisms of affine schemes this is equivalent to local finite presentation, quasi-compactness and quasi-compact diagonal: the affine criterion gives local finite presentation, and an affine-to-affine morphism is affine, hence quasi-compact and separated. Conversely local finite presentation on these affine opens gives a finite polynomial presentation. Thus no extra hypothesis or weaker morphism property is substituted. |
| M_j = h_j^* M over Y' | `(moduleTensorPullback (h j ≫ enlargedFibreProductFst f (dimensionFlatBaseMap g))).obj M.obj`. Pullback along this actual composite is canonically the iterated tensor pullback in the node, by the recorded chart-adjunction/tensor realization. |
| N_j is the actual global sections on W_j | `affineDevissageSections (A j) (...)`. This existing construction restricts to the identity chart, takes Zariski global sections, and restricts scalars through the canonical `Scheme.ΓSpecIso` inverse, giving the A_j-action. It chooses no module or unrelated isomorphism. |
| N_j / A_j / R admits complete algebra devissage over p | `∃ hfinite : Module.Finite (A j) (...), Nonempty (@CompleteAlgebraDevissage R (A j) ... p.asIdeal ... hfinite)`. The finite-type algebra argument is the canonical consequence `Algebra.FiniteType.of_finitePresentation hAfp`. The finite-module witness is required by the recorded devissage structure itself, not an added assumption on the input. All its data and conditions remain those of Tag 05HX. |
| Union of chart images contains the entire distinguished fibre | For every `x : Point (...)`, equality of its projected point with `schemePointMap (𝟙 ...) p` implies `∃ j : Fin n, x ∈ pointImage (h j).hom.hom`. The inverse image of that base point is exactly the point set of the fibre in the node. Coverage concerns all point classes, not just selected points or a neighbourhood of one point. |
| Empty family allowed for an empty fibre | `n = 0` is permitted. There is no `Nonempty (Fin n)` assumption. The coverage condition then requires precisely that there be no point over p. |

Dependency declarations used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and its morphisms.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`, `AlgebraicGeometry.AlgebraicSpace`, `AlgebraicSpace.IsEtale`, and `AlgebraicSpace.Modules`.
- `def-weil-size-convention`: metatheoretic convention; explicit `universe u`, `Scheme.{u}` through the base, `CommRingCat.{u}`, and `CommAlgCat.{u}`. No additional universe equality is imposed.
- `lem-trf-space-fibre-products-etale-covers`: `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`, `AlgebraicSpace.fibreProduct_isAlgebraicSpace`, used in the existing bundled sheaf pullback.
- `def-trf-space-quasi-coherent-module`: `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`, `AlgebraicSpace.QCoh`; Mathlib `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFinitePresentation` from `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
- `def-trf-space-etale-module-functors`: `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`, `AlgebraicSpace.moduleTensorPullback`, canonically adjoint to the specified chart-limit direct image.
- `def-sfb-space-morphism-properties`: `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`, `AlgebraicSpace.MapIsLocallyOfFinitePresentation`. Its quasi-compactness predicate is `MapIsQuasiCompact` from `ProperCurveModuli` and its point topology.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec` and `Spec.map`.
- `def-trf-complete-algebra-devissage`: `Sheaf.TraceFormula.CompleteAlgebraDevissage`, `AlgebraicGeometry.CompleteAlgebraDevissage`, including its permitted zero-length case.

Additional existing canonical constructions, reused without copies:

- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`, `enlargedFibreProduct`, `enlargedFibreProductFst`.
- `Sheaf.AlgebraicGeometry.SpaceDimensionFlatCondition`: `dimensionFlatBaseMap`, which is simply the scheme morphism's Yoneda map, not any dimension-flatness assumption.
- `Sheaf.AlgebraicGeometry.AffineCompleteDevissageDimensionFlattening`: `affineDevissageScheme`, `affineDevissageArrow`, `affineDevissageSections`. These three helpers have real data; the flattening theorem in their owning module is not used. Importing their module avoids duplicating the canonical affine and section constructions. Its proof does not import or rely on this item's theorem.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`, `AlgebraicSpacePointTopology`, and `ProperCurveModuli`: `Point`, `schemePointMap`, `pointImage`, `mapPoint`.

All already stated proof-dependency modules, including Mathlib matches, are imported
without `public` unless they also supply the statement. Two proof dependencies have no
recorded Lean declaration: `lem-sfb-qc-space-affine-etale-atlas` and
`lem-trf-complete-algebra-devissage-etale-existence`; they are not required to type this
statement, and their future modules can be imported during proof work. No source files
outside the delivery are changed.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Finite affine etale charts covering a fibre with complete algebra devissage after affine etale base change"`: eight hits, concerning standard smooth coordinates, etale loci, and finite presentation of etale algebras; none states this theorem.
- `msearch.py ... leansearch "finite affine etale charts covering a fibre with complete algebra devissage"`: eight hits, including ordinary affine open covers and individual etale properties; no match.
- `msearch.py ... loogle '"devissage"'`: zero hits.
- `msearch.py ... grep 'devissage|dévissage'`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `CompleteAlgebraDevissage`, finite-presentation predicates and fibre/chart constructions: found the recorded structure, base-change theorem, pointed henselian chart material, and the affine flattening helpers reused above. None states simultaneous finite fibre coverage with complete devissages. The exact item-id search in `WeilConjectures` returned no hits.

Edge cases checked before and after writing: empty fibre (`n = 0`); zero module with a
nonempty fibre (charts still cover, while each internal devissage may have length zero);
non-affine and disconnected Y; non-flat M; zero algebra charts; arbitrary characteristic
and arbitrary scheme universe u. The chosen prime ensures the base neighbourhood has a
point, as required by the input y. No auxiliary assumptions exclude any of these cases.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED flag is needed.
The first compile exposed an incorrect name for Mathlib's finite-presentation-to-finite-type
instance; it was replaced by `Algebra.FiniteType.of_finitePresentation`. The final server
compile passed both the sandbox and library module checks (2.2 seconds each), with no
errors or unexpected warnings.

## Second reading by Q84

Second pass by the dispatcher-started Q84 worker. No other worker was started, as directed;
the maintainer's independent delivery review remains the independent mathematical reading.
I reopened the node and the finished file and checked every row above against their text.
The base is Spec Z, Y is a scheme, hfp has all three stipulated clauses, M is both
quasi-coherent and finitely presented, and y is arbitrary. The output has one common
affine etale base neighbourhood and finitely many affine R-scheme charts, whose structure
maps are constrained by the displayed projection equation. In particular the algebra
actions in the devissages cannot be unrelated to the maps of schemes. The actual section
modules are used, with tensor pullback along the actual composite map. The final universal
point condition covers the whole fibre and permits an empty family. The affine algebra
finite-presentation condition is equivalent to all three geometric finite-presentation
clauses; it is not just finite type. There is no elementary-neighbourhood residue-field
condition, flatness, properness, or nonemptiness added to the statement. The only Lean
revision was the instance name reported above; no mathematical mismatch was found.
