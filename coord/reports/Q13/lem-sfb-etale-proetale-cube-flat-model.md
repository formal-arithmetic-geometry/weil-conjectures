## Worker report

The module `Sheaf.Paper.EtaleProEtaleCubeFlatModel` states
`AlgebraicGeometry.ProEtale.ScalarCubeFlatModel.simultaneous_flat_model`.
Its proof is `sorry`; all helper definitions have actual data. No statement change,
new DAG node, or dependency-node change is needed.

The helper `Word` packages an ordinary complex functor, its specified derived functor,
and its actual representative map. `Word.comp` constructs the representative of a composite
as the derived outer functor applied to the inner representative, followed by the outer
representative counit. The package imposes no flatness or normalization assumptions.
`Good` is just the conjunction of existing K-flatness and termwise flatness predicates.
The enums name exactly the six vertices and six directed faces. These are item-local
bookkeeping helpers, not new pullback, scalar, tensor, or K-flat constructions.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Any morphism of schemes f:X→Y | `{X Y : Scheme.{u}} (f : X ⟶ Y)`, with no geometric instance hypothesis |
| Any homomorphism of discrete commutative rings | `{A B : Type (u+1)} [CommRing A] [CommRing B] (a : A →+* B)`; no topology or flatness hypothesis |
| Constant ring coefficients on the fixed small sites | `Sheaf Z.smallEtaleTopology (ModuleCat.{u+1} R)` and `Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u+1} R)`; exactly the existing parent-cube presentation |
| Ordinary unbounded derived categories and localization | `_root_.DerivedCategory` of those abelian categories, and `_root_.DerivedCategory.Q`; all complexes are indexed by `ℤ` |
| Ordinary/derived etale pullback l | `etale R f`, ordinary `Etale.upperStar ... f` applied degreewise, derived `L(Etale.upperStar ... f)`, representative the published `Etale.scalarGeometricRepresentative` |
| Ordinary/derived pro-etale pullback p | `proetale R f`, ordinary `ProEtale.upperStar ... f`, derived `L(...)`, representative its left-derived counit followed by the homotopy/cochain factor map |
| Comparison C_Z | `comparison R Z`, ordinary `comparisonUpperStar ... Z`, derived `.mapDerivedCategory`, representative `.mapDerivedCategoryFactors.hom.app` |
| Ordinary/derived scalar extension E,T | `etaleScalar a Z` and `proetaleScalar a Z`: the existing sheafified sectionwise extension and `pbcFixedScalarExtension` |
| Scalar representative counit, including identity geometry | Etale uses `scalarExtensionRepresentative`; pro-etale uses the transpose of the localized ordinary scalar-adjunction unit under the fixed derived scalar adjunction. This is the same counit formula on that site, with no assumption that a is flat |
| Every complex K has a quasi-isomorphism P→K, P K-flat with flat terms | First conjunct: `∀ K, ∃ P p, Good ... P ∧ QuasiIso p` |
| Every such P, not merely one chosen resolution | Second conjunct quantifies over every `P` satisfying `Good`. Every such P is itself a resolving complex, by its identity quasi-isomorphism; there is no restriction to a chosen replacement functor |
| All intermediate ordinary complexes are K-flat with flat terms | Nine explicit `Good` conjuncts for all proper nonempty suffixes, followed by `∀ i : Vertex, Good ... ((vertex a f i).ordinary.obj P)` |
| Successive counits identify each vertex | Fifteen `IsIso` assertions, one for each distinct letter-at-suffix occurrence, followed by invertibility of all six recursively constructed `vertex ... .representative P` |
| Six faces are their ordinary localizations under the same identifications | `∀ e : Face, derivedFace ... e (Q.obj P) ≫ j_target = j_source ≫ Q.map (ordinaryFace ... e P)`; no face-dependent choices of j |
| Natural for chain maps between resolving complexes | Last conjunct: for any good `P,P'` and chain map `v`, `Word.NaturalAt v` for all nine proper suffixes and all six vertices |
| No boundedness, geometric finiteness, or flatness of a | No such binder or restriction occurs anywhere in the theorem |

The vertex words, listed in application order (Lean functor composition):

| Vertex | Word |
| --- | --- |
| v0 | C_Y^A ; E_Y^p ; p_B |
| v1 | C_Y^A ; p_A ; E_X^p |
| v2 | l_A ; C_X^A ; E_X^p |
| v3 | l_A ; E_X^e ; C_X^B |
| v4 | E_Y^e ; C_Y^B ; p_B |
| v5 | E_Y^e ; l_B ; C_X^B |

These give the routes v0→v1→v2→v3 and v0→v4→v5→v3.
The nine proper nonempty suffixes are C_Y^A, l_A, E_Y^e, E_Y^p C_Y^A,
p_A C_Y^A, C_X^A l_A, E_X^e l_A, C_Y^B E_Y^e, and l_B E_Y^e.
Together with the good input and all six vertices these exhaust the intermediate complexes.

| Face | Derived map reused | Ordinary representative |
| --- | --- | --- |
| proScalar, v0→v1 | `scalarPullbackProEtaleIso a f` at C_Y^A | `sheafExtendScalarsCompUpperStarIso a f` at C_Y^{A,0} |
| squareA, v1→v2 | `pbcFixedScalarExtension ... a` applied to `directImageComparisonAmbientPullbackIso A f` | E_X^p applied to `comparisonUpperStarCompUpperStarIso ... f` |
| comparisonX, v2→v3 | `pbcComparisonReduction X a` at l_A | Inverse of `etaleSheafExtendScalarsCompComparisonUpperStarIso a X` at l_A^0 |
| comparisonY, v0→v4 | p_B applied to `pbcComparisonReduction Y a` | p_B^0 applied to the inverse of `etaleSheafExtendScalarsCompComparisonUpperStarIso a Y` |
| squareB, v4→v5 | `directImageComparisonAmbientPullbackIso B f` at T_Y^e | `comparisonUpperStarCompUpperStarIso ... f` at E_Y^e |
| etaleScalar, v5→v3 | C_X^B applied to `Etale.scalarPullbackIso a f` | C_X^{B,0} applied to `Etale.scalarSheafPullbackComplexIso a f` |

The ordinary scalar isomorphisms are the existing adjunction conjugates of the
identity-on-sections restriction/direct-image comparisons. Their unit equations send
pulled-back `1 ⊗ m` to `1 ⊗` pulled-back `m`, and linearity extends to generalized pure
tensors. Comparison faces use their inverses, as the node requires. `twoComplexIso`
only inserts the library's termwise functor-composition isomorphisms.

Dependency interfaces read and used (all recorded modules are imported directly):

| Dependency | Module and declarations |
| --- | --- |
| def-kun-projection-formula-map | `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`; its imported `Etale.upperStar` and `Functor.leftDerivedFunctor` interface; `Etale.rightDerivedLowerStarProjectionMap` itself is not a face of this node |
| def-pc-cochain-complex-modules | `Mathlib.Algebra.Homology.HomologicalComplex`, `CochainComplex` |
| def-pc-flat-sheaf-modules | `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, `SheafOfModules.IsFlatOnSite`; in fixed-module coordinates the existing predicate is `CategoryTheory.ObjectProperty.flat` |
| def-pc-kflat-complex | `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`, `CochainComplex.IsKFlatIndependentCoefficients`; in fixed-module coordinates use the existing `(HomologicalComplex.quasiIso _ (.up ℤ)).kFlat` |
| def-pc-quasi-iso-modules | `Mathlib.Algebra.Homology.QuasiIso`, `QuasiIso` |
| def-pc-scheme | `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and its morphisms |
| def-pur-etale-scalar-pullback-iso | `Sheaf.Paper.PurEtaleScalarMateProjection`, `Etale.scalarPullbackIso`; reexported `scalarSheafPullbackComplexIso`, `scalarGeometricRepresentative`, `scalarExtensionRepresentative` |
| def-weil-pbc-canonical-ringed-tensor-comparison | `Sheaf.Paper.RingedTopoiTensorComparisonData`, `SheafOfModules.CanonicalRingedTensorComparison`; its pure-tensor normalization is specialized by the existing ordinary scalar maps |
| def-weil-pbc-constant-sheaf | `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `CategoryTheory.constantSheaf`; fixed-ring module sheaves are the parent cube's presentation of modules over these constant ring sheaves |
| def-weil-pbc-derived-categories | `WeilConjectures.AlgebraicGeometry.DerivedCategories`, reexported `Etale.DerivedCategoryModule` and ordinary `DerivedCategory` |
| def-weil-pbc-proetale-operations | `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`, `Scheme.proEtaleConstantRingDerivedPullback`; in the parent's fixed-coefficient coordinates use the existing `ProEtale.upperStar` and its canonical left-derived functor |
| def-weil-pbc-site-comparison-morphism | `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, `Scheme.proEtaleSiteComparison`; its coefficient functor is the existing `ProEtale.comparisonUpperStar` |
| lem-pur-derived-change-of-rings | `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`, `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`; fixed-module specializations `Etale.scalarExtension`, `scalarExtensionRepresentative` and `ProEtale.pbcFixedScalarExtension` are reused |
| lem-sfb-ringed-derived-monoidal-comparisons | `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`, `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons` and its `System` |
| lem-weil-pbc-canonical-ringed-tensor-comparison-construction | `Sheaf.Paper.RingedTopoiTensorComparisonConstruction`, `SheafOfModules.canonicalRingedTensorComparison_nonempty` |
| lem-weil-pbc-ringed-topoi-derived-pullback | `Sheaf.Paper.RingedTopoiDerivedPullback`, `SheafOfModules.ringedTopoiDerivedPullback` and its representative-counit formula |
| lem-weil-pbc-ringed-topoi-derived-tensor-pullback | `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback` |
| sk-thm-pe-direct-image-comparison | `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`, `ProEtale.directImageComparison`; its exact inverse-image square is `comparisonUpperStarCompUpperStarIso`, and the already published unbounded specialization is `directImageComparisonAmbientPullbackIso` |

The fixed-module predicates above are existing general definitions, not replacement notions.
`MorphismProperty.kFlat` with W=quasi-isomorphisms tests preservation of quasi-isomorphisms
by total tensor on both sides. The cone/zero-complex criterion and symmetry identify this
with acyclicity of F tensor P for every acyclic F (see `CochainComplex.isKFlatTensor_iff_kFlat`
in `WeilConjectures.Algebra.Homology.KFlatComparison` for the ring-sheaf presentation).
Similarly `ObjectProperty.flat` asks exactness on both sides; symmetry identifies the two
conditions (the same module's `SheafOfModules.isFlat_iff_flat`). Fixed-module tensor is the
sheafification of sectionwise tensor. Thus `Good` uses exactly the recorded notions in the
same presentation as the given six face maps, without constructing a duplicate tensor or
imposing a different coefficient/site universe. Site objects remain at u+1, site Homs at u,
and coefficients and module carriers at u+1.

The face helpers `scalarPullbackProEtaleIso` and
`directImageComparisonAmbientPullbackIso` are already housed in
`Sheaf.Paper.EtaleProEtaleScalarMate`; importing that module reuses those constants.
Its future proof-only import of this module must be omitted, exactly as the parent cube's
lean.note already requires. This delivery does not add a DAG dependency on that downstream
node, import the parent cube theorem, or use either downstream theorem as a proof hypothesis.
The resolution, exact-functor derivation, and normalized composition/2-isomorphism proof
modules are imported without `public` when used only by the postponed proof.

Edge cases checked before writing and again on the signature: P=0, empty X or Y, f=id,
a=id, A=B, zero rings, nonflat Z→F_p, and unbounded complexes. Flatness after scalar extension
is measured over the new ring B, so nonflat a does not invalidate preservation. No `Finite`,
`QuasiCompact`, `QuasiSeparated`, boundedness, or coefficient-map flatness is assumed.
The statement does not assert that any composite face route is the identity or already equal
to the other route: its assertion is simultaneous representative normalization.

Searches (the prescribed msearch tool also records the raw results in searches.jsonl):

- LeanFinder: "All six etale proetale scalar pullback faces computed on one common flat term
  K flat representative": eight unrelated etale-ring results; no common-model theorem.
- Loogle: `CategoryTheory.Functor.mapDerivedCategory`: twelve exact-localization interface
  results, including `mapDerivedCategoryFactors`, `mapDerivedCategoryCompIso`, and
  `NatTrans.mapDerivedCategory`; none supplies six-face normalization.
- Mathlib grep: `KFlat|K.flat|representative.*counit` in CategoryTheory: zero hits.
- LeanSearch: "Canonical derived pullback scalar comparison on a common K flat cochain
  resolution": eight unrelated manifold/K-projective/presheaf-pullback results; no match.
- rg of `lean/Sheaf` and `lean/WeilConjectures` for the node id and cube/flat/representative
  names: found the parent cube and the existing scalar helpers, not this normalization theorem.
- Additional source searches located generic kFlat/flat, their ring-sheaf comparison theorem,
  the actual scalar counits and the ordinary scalar/site isomorphisms. All are reused.

No STATEMENT-DISPUTED issue was found. The node's statement, dependencies and proof remain
unchanged. Every declaration is public, explicitly binds universes/variables, and has a
source/blueprint docstring. There is one postponed theorem, with all eight proof steps in
its docstring.

## Second reading by Q13

A separate pass reread the node and the completed file. No independent worker was spawned,
as the dispatch brief forbids sub-agents; the maintainer's delivery review is independent.

Checked all six vertex words and all six source/target pairs against the node's displayed
W0,...,W5. In particular comparisonX and comparisonY use the inverse of the ordinary
etale-scalar/comparison iso, matching delta's direction. Checked that squareB is evaluated
after etale scalar extension, and etaleScalar uses the specified `Etale.scalarPullbackIso`,
not the reverse mate chosen afresh. The ordinary scalar-X face is whiskered by C_X^B,
comparison-Y by p_B, and square-A by T_X^p. Each face equation uses the same previously
defined vertex representative at a shared endpoint.

Enumerated the three one-letter suffixes, six two-letter suffixes, and six full words.
The Good and IsIso clauses include each occurrence. The naturality conclusion includes
all nine proper suffixes and all full vertices, for arbitrary chain maps of good complexes.
The zero/identity/nonflat/unbounded cases remain present. The existence clause is separate
from the universal assertion about every good P, so it does not secretly select a special
resolution. All map-valued helpers contain actual constructions; there is no Nonempty
choice of an unspecified isomorphism. The first compile of the full theorem found only one
line over 100 characters; it was wrapped. No mathematical mismatch or node correction arose.
