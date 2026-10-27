## Worker report

Q150 states `AlgebraicGeometry.ProEtale.ScalarCubeFlatModel.simultaneous_flat_model`
in `lean/Sheaf/Paper/EtaleProEtaleSimultaneousFlatModel.lean`. Its proof is `sorry`;
all 16 supporting structures/definitions contain actual data. The node changes only
in `lean`. There are no new nodes, dependency repairs, statement corrections, or
statement disputes. The old `EtaleProEtaleCubeFlatModel` module is withdrawn and has
no declarations; the new filename avoids overwriting that historical placeholder.

Source checked: local Stacks `sites-cohomology.tex`, especially 06YS
(`lemma-K-flat-resolution`), 0G7E (`lemma-pullback-K-flat`) and 0D6D
(`lemma-derived-pullback-composition`); also the node's eight-step proof and its
recorded dependency signatures/docstrings. The theorem docstring carries all eight
steps, including the normalized composition/2-isomorphism argument and the etale
scalar unit calculation. This is a statement delivery, not a proof delivery.

### Hypotheses and objects

| Node text | Lean rendering |
| --- | --- |
| Any commutative rings and homomorphism | `{A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)` |
| Any schemes and morphism | `{X Y : Scheme.{u}} (f : X ⟶ Y)` |
| Fixed small etale/pro-etale sites and constant coefficients | `Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R)` and `Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R)` |
| Ordinary unbounded complexes and derived categories | `CochainComplex … ℤ`, `_root_.DerivedCategory …`, `DerivedCategory.Q` |
| Ordinary/derived etale pullback | `etale R f`, using `Etale.upperStar`, its complex functor and `L(Etale.upperStar …)` |
| Ordinary/derived pro-etale pullback | `proetale R f`, using `ProEtale.upperStar`, its complex functor and `L(upperStar …)` |
| Exact comparison inverse image | `comparison R Z`, using `comparisonUpperStar` and its `mapDerivedCategory` |
| Ordinary/derived scalar extension | `etaleScalar a Z`, `proetaleScalar a Z`; ordinary `etaleSheafExtendScalars`/`sheafExtendScalars`, derived `pbcFixedScalarExtension` |
| Canonical representative counits | Each letter's `representative`; the pro-etale scalar representative is the adjunction transpose of the actual ordinary scalar unit after the exact restriction localization comparison |

No finiteness, boundedness, nonemptiness, flatness of `a`, or extra scheme property
is a binder. All universes and variables are bound explicitly, with `autoImplicit
false`. The pro-etale site retains object universe `u+1` and morphism universe `u`.
The explicit `essentiallySmallSelf.{0}` argument resolves instance elaboration; it
adds no hypothesis, category replacement, or choice of a comparison map.

`Good P` uses the already existing fixed-coefficient monoidal predicates:
`(HomologicalComplex.quasiIso C (.up ℤ)).kFlat P` and
`∀ n : ℤ, ObjectProperty.flat (P.X n)`. These are the predicates used by the
published etale scalar representative interface. In the constant-ring sheaf
presentation they are the recorded ring-sheaf notions: symmetry interchanges the
two tensor sides, acyclic complexes are precisely those with quasi-isomorphic
zero map, and the bridges `CochainComplex.isKFlatTensor_iff_kFlat` and
`SheafOfModules.isFlat_iff_flat` in
`WeilConjectures.Algebra.Homology.KFlatComparison` identify the existing
presentations. No second definition of K-flatness or flat sheaf is introduced.

### Every conclusion clause

The first conjunct is exactly
`∀ K, ∃ (P) (p : P ⟶ K), Good P ∧ QuasiIso p`.
The second conjunct quantifies over **every** good `P`, independently of a choice
of resolution, target complex, or resolution morphism.

`Word.comp F G` uses ordinary and derived functor composition and fixes
`j_(GF)(P) = G.derived.map (F.representative P) ≫
G.representative (F.ordinary.obj P)`. Thus it is the specified successive-counit
identification, not an existential or arbitrary isomorphism.

Composition below is written in the mathematical (rightmost-first) order:

| `vertex a f i` | Ordinary word (and same word in derived letters) |
| --- | --- |
| 0 | `p_B E_Y^p C_Y^A` |
| 1 | `E_X^p p_A C_Y^A` |
| 2 | `E_X^p C_X^A l_A` |
| 3 | `C_X^B E_X^e l_A` |
| 4 | `p_B C_Y^B E_Y^e` |
| 5 | `C_X^B l_B E_Y^e` |

The nine proper nonempty input suffixes are `C_Y^A`, `l_A`, `E_Y^e`,
`E_Y^p C_Y^A`, `p_A C_Y^A`, `C_X^A l_A`, `E_X^e l_A`,
`C_Y^B E_Y^e`, `l_B E_Y^e`. All nine are explicitly `Good`, followed by
`∀ i : Fin 6, Good ((vertex a f i).ordinary.obj P)`. The empty suffix is `P`
itself, already good by the antecedent. This covers every intermediate complex
on both routes. Fifteen explicit `IsIso` conjuncts cover every distinct
letter-at-input occurrence (3 first letters, 6 second letters, 6 third letters).
`∀ i, IsIso ((vertex a f i).representative P)` states invertibility of the fixed
successive identifications themselves.

| Face index / endpoints | `derivedFace` | `ordinaryFace` |
| --- | --- | --- |
| 0: 0→1 | `scalarPullbackProEtaleIso` at `C_Y^A M` | `sheafExtendScalarsCompUpperStarIso` at `C_Y^A P` |
| 1: 1→2 | `T_X^p.map (directImageComparisonAmbientPullbackIso A f)` | `E_X^p.map` of `comparisonUpperStarCompUpperStarIso A f` |
| 2: 2→3 | `pbcComparisonReduction X a` at `l_A M` | inverse of `etaleSheafExtendScalarsCompComparisonUpperStarIso a X` at `l_A P` |
| 3: 0→4 | `p_B.map (pbcComparisonReduction Y a)` | `p_B^0.map` of the inverse ordinary comparison at `P` |
| 4: 4→5 | `directImageComparisonAmbientPullbackIso B f` at `T_Y^e M` | ordinary site square at `E_Y^e P` |
| 5: 5→3 | `C_X^B.map (Etale.scalarPullbackIso a f)` | `C_X^{B,0}.map (Etale.scalarSheafPullbackComplexIso a f)` |

`twoComplexIso` inserts only the canonical termwise functor-composition
comparisons. All ordinary faces are the existing adjunction conjugates with their
pure-tensor unit normalization; the inverse in faces 2 and 3 is required by the
node's direction for delta. The etale derived face is the specified recorded
`Etale.scalarPullbackIso`, not a replacement chosen to force commutativity.

For **all six** faces the same equation is asserted:
`derivedFace … (Q.obj P) ≫ (vertex … target).representative P =
(vertex … source).representative P ≫ Q.map (ordinaryFace … P)`.
The vertex function is fixed once, so the two incident faces cannot choose
different identifications. The final conjunct quantifies over every chain map
`v : P ⟶ P'` with `Good P` and `Good P'`, and asserts `Word.NaturalAt v` for
all nine suffixes and all six vertices. `NaturalAt` is exactly the naturality
square for the already fixed representative arrow. No compatibility with an
extra chosen resolution map is imposed.

### Dependency declarations

All recorded statement-dependency modules are public imports; proof-only modules
are plain imports. The table lists the recorded dependency interfaces read.

| Node | Module and declaration |
| --- | --- |
| `def-kun-projection-formula-map` | `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`: `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap` |
| `def-pc-cochain-complex-modules` | `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex` |
| `def-pc-flat-sheaf-modules` | `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite` |
| `def-pc-kflat-complex` | `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: `CochainComplex.IsKFlatIndependentCoefficients` |
| `def-pc-quasi-iso-modules` | Mathlib: `{'declaration': 'QuasiIso', 'file': 'Mathlib/Algebra/Homology/QuasiIso.lean', 'how': 'specializes in one line: `QuasiIso f` for `f : K ⟶ L` in `CochainComplex (SheafOfModules R) ℤ` (homology exists by `categoryWithHomology_of_abelian`)'}` |
| `def-pc-scheme` | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` |
| `def-pur-etale-scalar-pullback-iso` | `Sheaf.Paper.PurEtaleScalarMateProjection`: `AlgebraicGeometry.Etale.scalarPullbackIso` |
| `def-weil-pbc-canonical-ringed-tensor-comparison` | `Sheaf.Paper.RingedTopoiTensorComparisonData`: `SheafOfModules.CanonicalRingedTensorComparison` |
| `def-weil-pbc-constant-sheaf` | `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf` |
| `def-weil-pbc-derived-categories` | `WeilConjectures.AlgebraicGeometry.DerivedCategories`: `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology` |
| `def-weil-pbc-proetale-operations` | `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: `AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback` |
| `def-weil-pbc-site-comparison-morphism` | `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `AlgebraicGeometry.Scheme.proEtaleSiteComparison` |
| `lem-pur-derived-change-of-rings` | `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`: `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel` |
| `lem-sfb-ringed-derived-monoidal-comparisons` | `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`: `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons` |
| `lem-weil-pbc-canonical-ringed-tensor-comparison-construction` | `Sheaf.Paper.RingedTopoiTensorComparisonConstruction`: `SheafOfModules.canonicalRingedTensorComparison_nonempty` |
| `lem-weil-pbc-ringed-topoi-derived-pullback` | `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`: `SheafOfModules.ringedTopoiDerivedPullbackIndependent` |
| `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` | `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`: `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback` |
| `sk-thm-pe-direct-image-comparison` | `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`: `AlgebraicGeometry.ProEtale.directImageComparison` |
| `def-sfb-ringed-derived-comparison-data` | `Sheaf.SixFunctors.RingedDerivedComparisonData`: `CategoryTheory.RingedDerivedComparisons.System` |
| `lem-pc-kflat-resolution` | `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`: `CochainComplex.exists_isKFlatResolutionIndependentCoefficients` |
| `lem-sfb-ringed-derived-composition-comparison` | `Sheaf.SixFunctors.RingedDerivedCompositionComparison`: `CategoryTheory.RingedDerivedComparisons.compositionCore_exists` |
| `lem-sfb-ringed-derived-two-iso-comparison` | `Sheaf.SixFunctors.RingedDerivedTwoIsoComparison`: `CategoryTheory.RingedDerivedComparisons.twoIsoComparison_exists` |
| `lem-weil-pbc-exact-functor-derived-functor` | `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`: `CategoryTheory.Functor.exactFunctor_derivedFunctor` |

Additional canonical published interfaces used to express those notions:
`WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal` exposes the ordinary
scalar functors, their adjunctions, and their comparison isomorphisms;
`Sheaf.Paper.EtaleProEtaleScalarMate` exposes
`AlgebraicGeometry.ProEtale.scalarPullbackProEtaleIso` and
`AlgebraicGeometry.ProEtale.directImageComparisonAmbientPullbackIso`;
`Sheaf.Paper.WitnessCompatibility` exposes `pbcFixedScalarExtension` and
`pbcComparisonReduction`; `Sheaf.Paper.ScalarPullbackRepresentativeData` exposes
`Etale.scalarGeometricRepresentative`, `Etale.scalarExtensionRepresentative`, and
`Etale.scalarSheafPullbackComplexIso`.
The derived-categories node records an ancillary torsion-cohomology declaration;
the same imported module already defines the required unbounded categories, so
no dependency repair or torsion hypothesis is needed. The projection-formula map
is not invoked as an unrelated map: its module supplies the recorded etale
pullback interface. Only the exact inverse-image square of the direct-image
comparison node is used, not its later qcqs direct-image clause.

The import of the scalar-mate module uses its existing canonical face
constructions. The postponed proof does not use the downstream scalar-mate or
cube theorem. Its proof plan uses the recorded normalized ringed comparison
system and its composition/two-isomorphism interfaces, avoiding a circular appeal
to the statement being modeled.

### Searches and edge cases

The sandbox `searches.jsonl` records msearch results. Searches included:

- `leanfinder`: “All six etale proetale pullback scalar comparison faces are represented simultaneously on one flat term K flat complex”; eight etale ring-algebra results, no common-model theorem.
- `loogle`: `CategoryTheory.Functor.mapDerivedCategoryFactors`; exact-localization infrastructure, no simultaneous face normalization.
- `grep` in Mathlib `CategoryTheory`: `KFlat|K.flat|representative.*counit`; zero matches.
- `leansearch`: “Canonical derived pullback scalar comparison on a common K flat cochain resolution”; unrelated/projective/presheaf results, no exact match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, including the item id and flat-model/cube/pullback predicates; existing resolution and canonical comparison interfaces were reused. The former flat-model module has been withdrawn; no extant declaration states the item.

The prior node's search history also contains ordinary `pullbackComp`,
`leftDerived`, and multiple common-K-flat/derived-scalar queries; these are
infrastructure, not the assertion of all six faces on a shared representative.
Helpers in this module only package the node's own words, arrows and equations;
none introduces an independent mathematical notion requiring a new DAG node.

Edge cases checked against the signature and canonical constructions: `P=0` and
zero complexes; empty schemes (no points or nonemptiness selected); zero rings;
identity `a` and identity `f`; nonflat `ℤ → ℤ/pℤ` (scalar extension of flat/K-flat
inputs is computed over the target ring, so no flat-map hypothesis is needed);
complexes unbounded on both sides; arbitrary chain maps between good complexes.
The routes share endpoints 0 and 3 and reuse the same representative arrows.
The two comparison faces have the inverse direction required by delta. There
are no dropped identity/arbitrary-coefficient-map cases.

### Validation

The prescribed `scompile.py` compiled the delivered module in both sandbox and
library module modes, cleanly. The final delivery dry run will also compile the
file after the documentation-only main-definition list addition. No direct git
command, global build, shared-repository edit, or launcher edit was performed.

## Second reading by Q150

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
