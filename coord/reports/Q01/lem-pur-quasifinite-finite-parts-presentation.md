## Worker report

The delivery states `AlgebraicGeometry.Etale.quasiFinite_finiteParts_presentation` in
`Sheaf.AlgebraicGeometry.QuasiFiniteFinitePartsPresentation`. Its only postponed proof is
that theorem, whose docstring carries all ten proof steps from the node. All 21 supporting
structures and definitions have real data and belong to this node's presentation interface.
Nothing is proved. No other DAG node is stated, no dependency module is changed, and there
are no new nodes or statement corrections.

The previous worker's stale-assignment rejection concerned stage 1. The current node is
split and reviewed by ND, but has no Lean binding, so this is a fresh stage-2 statement.
There is no repair note for this item. I read the full brief, stage-2 rules, worker role,
error list H, example CompactObject module/node and the node's dependencies and interfaces.
I checked the actual SGA PDF: XVII 6.2.1 and Proposition 6.2.2, printed pp. 420–422
(PDF pp. 99–100). The generator is (the project server), the refinement matrix is (the project server), and
localization is explicitly stated immediately after that diagram.

Clause-by-clause correspondence:

| Node clause or hypothesis | Lean rendering |
| --- | --- |
| Schemes X and S | `{X S : Scheme.{u}}` |
| Both schemes Noetherian, meaning finite affine covers by Noetherian rings | `[IsNoetherian X] [IsNoetherian S]`; Mathlib `isNoetherian_iff_of_finite_affine_openCover` gives exactly the node's convention. |
| f separated | `[IsSeparated f]` |
| f quasi-finite | `hf : f.IsQuasiFinite`, the recorded Stacks-sense predicate, including local finite type and quasi-compactness. |
| f of finite presentation | `[LocallyOfFinitePresentation f]` together with quasi-compactness from `hf` and quasi-separatedness from separatedness. |
| B any commutative ring | `(B : Type (u + 1)) [CommRing B]`; no finiteness, torsion, characteristic or invertibility condition. |
| F and G module sheaves on the small etale site | `F` in the theorem and every `G` in `FinitePartsUniversal`, both `Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B)`, using the recorded module-sheaf encoding. |
| f-star is inverse image | The recorded `upperStar (ModuleCat.{u + 1} B) f` and its `upperStarLowerStarAdjunction`. |
| f-shriek-supp is the subsheaf of sections with support proper over the test object | `H`, `ι`, `[Mono ι]` and `FinitePartsSupportCondition f F H ι`. That condition uses the recorded `SectionHasProperSupport` on every actual section of `f.Etale.obj U`, with base map `pullback.fst U.hom f`. |
| U etale and of finite presentation | `U : S.Etale`, `QuasiCompact U.hom` and `QuasiSeparated U.hom` in `FinitePartsMaps`; etaleness already supplies local finite presentation. No arbitrary etale object is assumed quasi-compact. |
| Finite pointed index (I,0) | `FinitePartsDecomposition.Index`, `.finite : Finite Index`, `.zero : Index`. Finite indices may be taken in `Type u` without losing any finite pointed set up to relabelling; all index equivalences are allowed in restrictions. |
| Clopen disjoint decomposition of X times S U | `.piece : Index → (f.Etale.obj U).left.Opens`, `.closed`, `.disjoint`, `.cover`. The ambient object is the recorded scheme pullback U times S X, with the canonical projection to U. |
| v_i finite for i nonzero, V_0 unrestricted | `.finite_piece : ∀ i, i ≠ zero → IsFinite ((piece i).ι ≫ pullback.fst U.hom f)`. There is no finiteness assertion for the remainder. |
| Source finite direct sum of copies of F restricted to U | Finite products `((j : {j // j ≠ D.zero}) → F(U))`; the product of finitely many module copies is their direct sum. Sections on all basis restrictions are included. |
| Canonical eta is unit on a finite piece and extension by zero elsewhere | `IsFinitePartsGenerator` characterizes the image of `η` under `ι` by restricting to every piece. `finitePartsCoordinate` is the chosen coordinate for a nonzero label and zero for the remainder; the right-hand side is the actual inverse-image adjunction unit restricted to that piece. The clopen cover and monic inclusion make this a unique map. |
| A refinement uses a pointed sigma and V_i equals the union of V'_j over sigma(j)=i | `FinitePartsRefinement.label`, `.pointed`, `.pieces`. |
| t_sigma has coordinate a_sigma(j) or zero when sigma(j)=0 | `finitePartsTransition`, made from `LinearMap.pi`, the actual restriction map of F, and `finitePartsCoordinate`. Identity restriction gives exactly t_sigma. |
| eta_phi equals eta_phi-prime t_sigma | The second conjunct of `FinitePartsCompatible η`. |
| Families compatible with every etale restriction | The first conjunct of `FinitePartsCompatible`, with every arrow `q : T ⟶ U` and every `FinitePartsRestriction`. The latter relates actual inverse-image opens and a pointed index equivalence. |
| Bijection from sheaf maps H to G to compatible families | `FinitePartsUniversal`: each compatible family has a unique sheaf map whose composites with all generators are the family. The already asserted compatibility of η ensures every sheaf map gives a compatible family, so this is exactly the requested bijection. |
| Etale-local colimit, with a small finite-presentation basis | The same universal property over the finite-presentation etale basis. It does not claim that global sections commute with this colimit or that every etale object is quasi-compact. Restricting a decomposition to all basis objects over U gives a morphism of sheaves on U; conversely such sheaf morphisms give exactly these section maps. Small representatives can be used because finite-presentation etale objects are essentially small, as explained in proof Step 1. |
| Generators commute with arbitrary base change under the proper-support comparison | `FinitePartsBaseChangeCompatible`: every `b : S' ⟶ S`, with no Noetherian or flatness assumption on S', has a normalized support comparison `e`. Its composite into ordinary direct image is the recorded `baseChangeMap`, followed by the inverse-image square compositor. `FinitePartsBaseChange` relates every pulled-back clopen piece, `finitePartsBaseChangeTuple` uses the actual pullback unit, and the displayed equality is generator compatibility on all tuples. It includes existence of the pulled-back decomposition and works for every relabelling of it. The standard pullback square suffices for every Cartesian square by its unique projection-preserving isomorphism. |
| Generators commute with coefficient-ring homomorphisms | `FinitePartsCoefficientCompatible`: every ring homomorphism and semilinear coefficient map induces a map of support sheaves, specified by `FinitePartsCoefficientMapCondition` inside direct image and on each generator tuple. The ordinary scalar-extension comparison is its adjoint and is an isomorphism when the input coefficient map is the scalar-extension unit, including after an isomorphic identification of the scalar extension. No flatness or exactness of scalar extension is asserted. Restriction of scalars is the recorded sectionwise functor. |
| Every geometric point has a pointed FP etale neighbourhood with empty remainder fibre and singleton nonzero fibres | The final quantified existential in the theorem and `FinitePartsSpecial`. Over the specified algebraically closed field, the latter says no lift through V_0 and exactly one lift through each V_i for i nonzero. These are exactly the geometric fibre points. |
| The stalk of eta is the isomorphism with one F-stalk copy per fibre point | `FinitePartsStalkIso η` gives the actual module isomorphism from the finite tuple of F-stalks to H-stalk. Its equation on every representative in every pointed basis restriction identifies it with the stalk of η, rather than an unspecified isomorphism. The special partition identifies the nonzero labels with the geometric fibre points. |

The parameters `H`, `ι` and their membership condition are a presentation of the existing
proper-support subsheaf, not an extra hypothesis about f or F. The recorded theorem
`properSupportSheafComposition` supplies such a sheaf with sectionwise injective inclusion
and exactly this image; `SectionHasProperSupport` is the same closed nonzero-germ locus
with proper reduced induced subscheme. Quantifying over any such inclusion avoids an
arbitrary functor choice. All constructions and conclusions are normalized inside the
same ordinary direct image. No second support functor or inverse image is introduced.

The supporting declarations package this node's own finite-parts data, generators and
relations. `FinitePartsSupportCondition` is only the quantified defining property of its
support inclusion, using the existing support predicate. The canonical base-change map,
coefficient direct-image map and tuple maps have explicit formulas, with no choice or
postponed proof of data. Every theorem proof remains `sorry`.

Dependency declarations used (read from the recorded modules and their source signatures):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme` — `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`.
- `pqf-def-quasifinite`: `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism` — `AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint`, `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`, `AlgebraicGeometry.Scheme.Hom.IsQuasiFinite`, `AlgebraicGeometry.Scheme.Hom.HasFiniteFibres`.
- `def-sbc-locally-finite-presentation`: `Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean` — `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper` — `AlgebraicGeometry.IsProper`, `AlgebraicGeometry.IsSeparated`, `AlgebraicGeometry.UniversallyClosed`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs` — `isNoetherianRing_iff`.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale` — `AlgebraicGeometry.Scheme.Etale`.
- `def-weil-pbc-etale-sheaves`: `WeilConjectures.AlgebraicGeometry.EtaleSheaves` — `AlgebraicGeometry.Scheme.IsLocallyConstantEtaleSheafOfSets`, `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantEtaleSheafOfSets`, `AlgebraicGeometry.Scheme.IsLisseEtaleSheafOfSets`, `AlgebraicGeometry.Scheme.etaleSetPullback`, `AlgebraicGeometry.Scheme.IsConstructibleEtaleSheafOfSets`, `AlgebraicGeometry.Scheme.HasTorsionEtaleCohomology`, `CategoryTheory.Sheaf.IsTorsion`, `CategoryTheory.Sheaf`, `CategoryTheory.constantSheaf`, `SheafOfModules`.
- `def-weil-pbc-inverse-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` — `AlgebraicGeometry.Etale.upperStar`, `AlgebraicGeometry.Etale.upperStarLowerStarAdjunction`.
- `lem-cbc-proper-support-sheaf-composition`: `Sheaf.AlgebraicGeometry.ProperSupportSheafComposition` — `AlgebraicGeometry.Etale.properSupportSheafComposition`.
- `def-weil-pbc-direct-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` — `AlgebraicGeometry.Etale.lowerStar`, `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` — `CategoryTheory.Limits.pullback`, `CategoryTheory.Limits.pullback.fst`, `CategoryTheory.Limits.pullback.snd`.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite` — `AlgebraicGeometry.IsFinite`, `AlgebraicGeometry.IsIntegralHom`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion` — `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-geometric-point`: `Mathlib.FieldTheory.IsAlgClosed.Basic` — `IsAlgClosed`, `AlgebraicGeometry.Scheme.SpecToEquivOfField`.
- `def-weil-pbc-geometric-stalks`: `Mathlib.CategoryTheory.Sites.Point.Basic` — `CategoryTheory.GrothendieckTopology.Point.sheafFiber`, `AlgebraicGeometry.Scheme.pointSmallEtale`.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits` — `CategoryTheory.Limits.Cocone`, `CategoryTheory.Limits.IsColimit`, `CategoryTheory.Limits.colimit.desc`, `CategoryTheory.IsFiltered`.
- `def-cbc-etale-section-proper-support`: `Sheaf.AlgebraicGeometry.EtaleSectionProperSupport` — `AlgebraicGeometry.Etale.SectionHasProperSupport`.
- `lem-sbc-canonical-restrict-scalars-functor-comparisons`: `Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons` — `AlgebraicGeometry.Etale.lowerStarRestrictScalarsIso`, `AlgebraicGeometry.Etale.upperStarRestrictScalarsIsoSheaf`, `AlgebraicGeometry.Etale.derivedUpperStarRestrictScalarsIso`, `AlgebraicGeometry.Etale.derivedLowerStarRestrictScalarsMap`, `AlgebraicGeometry.Etale.isIso_derivedLowerStarRestrictScalarsMap`, `AlgebraicGeometry.Etale.derivedLowerStarRestrictScalarsIso`, `AlgebraicGeometry.Etale.derivedBaseChangeSourceRestrictScalarsIso`, `AlgebraicGeometry.Etale.derivedBaseChangeTargetRestrictScalarsIso`.
- `def-pod-ring-scalar-extension`: `Sheaf.Algebra.Category.ModuleCat.RingScalarExtension` — `ModuleCat.restrictScalars_has_leftAdjoint`, `ModuleCat.ringExtendScalars`, `ModuleCat.ringExtendScalarsAdj`, `ModuleCat.ringExtensionTmul`, `ModuleCat.ringExtensionComp`, `CategoryTheory.Sheaf.ringExtendScalars`.
- `def-weil-pbc-underived-exchange`: `WeilConjectures.SixFunctors.BaseChange.Square` — `AlgebraicGeometry.Etale.baseChangeMap`.

The four additional statement dependencies were already landed: the proper-support
section predicate, the scalar-restriction comparisons, ordinary ring scalar extension,
and the underived exchange. Only the item's `lean` and these `stmt_deps` additions change.
The public imports expose all statement-dependency modules; ordinary imports include
every stated proof-dependency module, including the geometric finite-parts existence,
proper-support stalk formula, stalk colimits, inverse-image germs, coefficient tensors,
geometric-germ extensionality, zero-dimensional sections and stalk conservativity.

Edge cases checked against the written types and source:

- Empty X or an empty fibre: a singleton index containing only the remainder is allowed;
  the tuple module is the zero module and `FinitePartsSpecial` requires the empty fibre.
- Empty labelled finite pieces: allowed in an arbitrary decomposition. They impose their
  zero relation after refinement; the special condition excludes them only at its marked
  nonempty labels, exactly as the node requires.
- A new piece carved from the old remainder receives coordinate zero since
  `finitePartsCoordinate` tests the old label, not the new label.
- Identity and finite disjoint unions recover the unit and the finite diagonal tuple;
  a nonreduced radicial finite piece still has one geometric point, not its scheme length.
- The zero coefficient ring and zero module sheaves are allowed. The finite tuple product
  and all linear maps still make sense, and the empty sum remains zero.
- Nonproper open morphisms retain their genuine remainder; the source is never required
  proper, finite, flat or etale.
- Arbitrary non-Noetherian base changes remain in the base-change clause. Pullback of a
  fixed finite-presentation etale object remains such, so the clause does not need a new
  Noetherian-basis argument on the new base.
- Nonflat coefficient quotients are included: only the scalar-extension comparison is
  asserted invertible, not exactness of tensoring.
- All universes and variables are explicitly bound (`set_option autoImplicit false`).
  Scheme and geometric-point fields use the same universe; coefficients and stalk module
  values use `u+1`, following the recorded module-sheaf interfaces.

Searches performed before stating the interface:

| Tool | Exact query / searched locations | Result |
| --- | --- | --- |
| `msearch.py leanfinder` | `A separated quasi-finite morphism has a finite-parts presentation of the sheaf of sections with proper support by generators on clopen finite pieces and refinement relations` | Eight hits, all ordinary module-sheaf finite-presentation/generator predicates; none is this proper-support presentation. |
| `msearch.py loogle` | `"Sheaf", "extensionByZero"` | Zero hits. |
| `msearch.py grep` | `FiniteParts|finiteParts|properSupportSheaf` | Zero Mathlib hits. |
| `msearch.py leansearch` | `The proper support direct image of a sheaf pulled back along a separated quasi-finite morphism is presented by finite clopen pieces and refinement relations` | Eight hits, including ideal-sheaf supports, finite-to-proper and discrete clopens; no finite-parts presentation or duplicate helper. |
| `rg` | `finiteParts|FiniteParts|finite.parts|properSupport|supportSheaf` in project `lean/Sheaf/AlgebraicGeometry` and upstream `WeilConjectures` | Existing proper-support composition/stalk theorems and downstream weighted-trace references; no presentation declaration. |
| `rg` | `FiniteParts|finiteParts|quasiFinite_finiteParts_presentation` in `lean/Sheaf`, upstream `WeilConjectures`, and `dag/lean_names_upstream.json` | No declaration name overlap. |
| `rg` | `lem-pur-quasifinite-finite-parts-presentation` in upstream `WeilConjectures` | No upstream declaration for the item. |
| `tools/blueprint_refs.py search` | `finite parts` | Zero blueprint nodes; the existing DAG item is the intended owning node, not a new definition node. |

No STATEMENT-DISPUTED flag or node fault was found. The mathematical statement and proof
are unchanged. The module compiles without warnings through the prescribed `scompile.py`
wrapper (both sandbox and module-path compilation, each below 8 seconds). The prescribed
`deliver2.py Q01 lem-pur-quasifinite-finite-parts-presentation --no-push` returned
`OK (dry run)` and confirmed compilation and preflight, with only the independent
second-reading section outstanding. Nothing was pushed. No second-reading section is
written by this worker.

## Second reading by Q01

I independently read the sandbox node, all 22 declarations of the module, and the
statement-dependency nodes and the actual declarations used from their modules. I also
read the original SGA 4 XVII PDF directly with pdftotext: 6.1.1–6.1.4 (printed pp.
415–418), 6.2.1–6.2.2 (pp. 420–422), and the first two paragraphs on p. 425.
The source is SGA, not a Stacks tag: there is no missing Stacks source for the main
presentation. Section 6.1 assumes separatedness and local finite type for proper
support; 6.2.1 assumes quasi-finite and separated. Flatness enters the later trace
construction 6.2.3 and is correctly absent here. The node explicitly specializes to
Noetherian schemes and finite presentation; the Lean retains exactly that specialization.
There is no repair note, statement_change, new node, or dependency module in this delivery.

My object/hypothesis/conclusion checklist, made from the node before assessing the Lean:

| Node item | Actual Lean rendering and second-reader verdict |
| --- | --- |
| Schemes X and S, both Noetherian | `{X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]`. Matches. I opened Mathlib Noetherian.lean: `IsNoetherian` is locally Noetherian plus compact, and `isNoetherian_iff_of_finite_affine_openCover` identifies it with the node's finite affine cover convention. |
| A separated quasi-finite morphism f of finite presentation | `(f : X ⟶ S) [IsSeparated f] [LocallyOfFinitePresentation f] (hf : f.IsQuasiFinite)`. Matches: the actual recorded `Scheme.Hom.IsQuasiFinite` is local finite type AND quasi-compact AND isolation in the scheme fibre. Thus quasi-compactness is available from hf, and separatedness supplies quasi-separatedness. No flatness or finiteness of f is assumed. |
| An arbitrary commutative coefficient ring B | `(B : Type (u + 1)) [CommRing B]`. Matches the recorded module-sheaf universe convention, with no characteristic, torsion, invertibility, Noetherian-ring, or nonzero hypothesis. |
| Module sheaves F and arbitrary target G on S_et | `F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B)` and the same type for every `G` in `FinitePartsUniversal`. Matches the existing six-functor encoding recorded in def-weil-pbc-etale-sheaves, not a private replacement by sheaves of sets or O-modules. |
| The inverse image f* and its unit | Existing `upperStar`, `lowerStar`, and `upperStarLowerStarAdjunction` from UpperLowerStar.Defs. Matches: I read the Kan-extension/sheafification inverse image and objectwise fibre-product direct image. |
| The proper-support subsheaf H of f_* f*F | `H`, `ι`, `[Mono ι]`, and `hH : FinitePartsSupportCondition f F H ι`. Matches: hH characterizes the image on EVERY etale object by the existing `SectionHasProperSupport`. Monicity fixes the subsheaf up to its unique inclusion-preserving isomorphism. These are parameters describing the node's specified object; they add no hypothesis on f or F. |
| Support really means nonzero geometric germs, closed and proper | `FinitePartsSupportCondition` passes `f.Etale.obj U`, its actual projection `pullback.fst U.hom f`, and the section to `SectionHasProperSupport`. Matches the opened dependency's closed nonzero-germ locus and proper reduced induced subscheme; no arbitrary support map or hollow predicate. The opened `properSupportSheafComposition` supplies such support inclusions and normalizes their comparisons inside ordinary direct image. |
| U etale of finite presentation | `U : S.Etale`, with `QuasiCompact U.hom` and `QuasiSeparated U.hom` in `FinitePartsMaps`. Matches, because etaleness already gives local finite presentation. The statement does not require every object of the small etale site to be quasi-compact. |
| A finite pointed set (I,0) | `FinitePartsDecomposition.Index : Type u`, `.finite : Finite Index`, and `.zero : Index`. Matches. The pointed set cannot be empty; its complement of zero may be empty. All finite pointed sets have representatives in this universe, and relabellings are explicitly allowed. |
| Disjoint clopen pieces covering the actual base change | `.piece`, `.closed`, `.disjoint`, and `.cover : iSup piece = ⊤` in `FinitePartsDecomposition`. Matches. `f.Etale.obj U` is the ordinary fibre product U ×_S X, with its projection to X; `pullback.fst U.hom f` is the projection to U. This is canonically the node's X ×_S U, with both projections respected. |
| Every nonzero-labelled piece finite over U; no condition on V_0 | `.finite_piece : ∀ i, i ≠ zero → IsFinite ((piece i).ι ≫ pullback.fst U.hom f)`. Matches the opened Mathlib finite-morphism definition. Neither nonemptiness nor finiteness is imposed on the remainder. |
| A canonical generator from the finite direct sum of F restricted to U | `η : FinitePartsMaps f F H` together with `IsFinitePartsGenerator f F H ι η`. Matches. Finite tuple products of modules are the finite direct sums, and compatibility over every basis restriction specifies the local sheaf map rather than merely its global sections. |
| On each finite piece the generator is the adjunction unit; on the remainder it is zero | `IsFinitePartsGenerator` compares the restriction of `ι(η(a))` along `finitePartsPieceInclusion D i` with the actual unit applied to `finitePartsCoordinate ... i a`. Matches. That coordinate is the appropriate projection for i ≠ zero and the zero linear map otherwise. The disjoint cover and monic ι determine the map uniquely. |
| A refinement is a pointed map sigma:I'→I with V_i the union of the indicated V'_j | `FinitePartsRefinement.label`, `.pointed`, and `.pieces`. Matches, including empty pieces and non-surjective label maps. No bijectivity or nonemptiness was accidentally imposed on refinements. |
| The refinement matrix has coordinate a_sigma(j), or zero for sigma(j)=0 | `finitePartsTransition` is `LinearMap.pi` of restriction composed with `finitePartsCoordinate` at the OLD label. Matches the direction and zero convention of (the project server), including pieces split off from the old remainder. |
| eta_phi = eta_phi' t_sigma | Second conjunct of `FinitePartsCompatible η`, using the identity restriction on U. Matches, with composition in the correct order. |
| Compatibility with all etale restrictions | First conjunct of `FinitePartsCompatible`, quantifying all arrows between finite-presentation basis objects and every `FinitePartsRestriction`. Matches: the latter identifies actual inverse-image opens via a pointed index equivalence. |
| Bijection from sheaf morphisms H→G to compatible families g_phi | `FinitePartsUniversal η` quantifies every module sheaf G and every family g, and asserts unique `k : H ⟶ G` with all the required composites. Matches exactly: the separately asserted compatibility of η ensures composition with any k is a compatible family; existence and uniqueness give its inverse. |
| Etale-local colimit over a small basis | The same `FinitePartsUniversal`, with maps on the finite-presentation etale basis and all its restrictions. Matches the local universal property rather than an unjustified colimit statement on global sections. The proof docstring's Step 1 supplies the small representatives; there is no arbitrary-universe index category assumption. |
| Generators commute with arbitrary base change under the proper-support comparison | `FinitePartsBaseChangeCompatible ι η`. Matches: all schemes S' and all b:S'→S are quantified; no Noetherian or flatness condition is added. The comparison e is normalized by its composite with ι' to the actual `baseChangeMap`, followed by the inverse square compositor on F. Actual inverse images of pieces are encoded by `FinitePartsBaseChange` and exist by an explicit conjunct; generator equality uses the actual inverse-image unit in `finitePartsBaseChangeTuple`. Arbitrary relabellings are covered. Standard pullback squares represent all Cartesian squares by the unique projection-preserving isomorphism. |
| Generators commute with coefficient-ring homomorphisms | `FinitePartsCoefficientCompatible ι η`. Matches: it quantifies all B', all ring maps φ, and all semilinear maps α. `finitePartsCoefficientDirectImage` uses the opened, existing restriction-of-scalars comparisons; `FinitePartsCoefficientMapCondition` normalizes the support map inside direct image and checks every generator tuple. Its scalar-extension formulation uses an actual left adjunction to restriction; the induced comparison is its adjoint, not an arbitrary isomorphism. This is the ordinary scalar-extension compatibility of the colimit presentation and does not assert flatness or tensor exactness. |
| Every geometric point has a pointed FP etale neighbourhood with special decomposition | Final existential, for every `(Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)`, supplies U, both FP conditions, t, D, `t ≫ U.hom = s`, and `FinitePartsSpecial D t`. Matches, with no surjectivity requirement on U beyond containing the specified lift. |
| The remainder fibre is empty and every other fibre has exactly one geometric point | `FinitePartsSpecial` says no Ω-valued lift through V_0, and a unique Ω-valued lift through each V_i for i ≠ zero. Matches: these are finite Ω-schemes, whose geometric points over algebraically closed Ω correspond exactly to their underlying points. No reducedness, degree-one, or etaleness condition is imposed on a finite piece. |
| The stalk of the actual generator is the one-copy-per-fibre-point isomorphism | `FinitePartsStalkIso η` gives a B-module isomorphism and fixes its formula on every section representative over pointed basis restrictions. Matches: labels of a special decomposition biject with fibre points, the source is the finite tuple of the actual F-stalk, and the target is the actual H-stalk. It does not assert that an arbitrary decomposition gives an isomorphism. |

Additional edge-case checks: X may be empty, S may be empty, and a specified fibre may
be empty. In the empty-fibre case the singleton index containing only the remainder
has no nonzero coordinates, so its tuple module is the zero module; the asserted stalk
isomorphism has the correct zero source. Empty labelled finite pieces are permitted
for general decompositions and the refinement relations kill their redundant
coordinates; a special decomposition excludes those labels only at its marked fibre.
Repeated empty pieces and pointed maps with fibres of cardinality zero are permitted.
The zero ring, zero F, and zero G are admitted. Purely inseparable nonreduced finite
pieces contribute one geometric point, independently of their scheme length. There is
no rank, n > 0, torsion, or characteristic restriction. Identity base change, identity
coefficient change, arbitrary non-Noetherian S', and nonflat coefficient quotients all
occur in the quantified clauses. Pullback preserves the FP conditions, so hU' and kU'
do not hide an additional restriction on b. All universes and variables are bound;
`Scheme.{u}`, geometric fields in `Type u`, and modules/coefficients in `u+1` agree
with the opened dependency declarations. There is no forced equality of distinct site
universes and no independent small test universe that could make a hypothesis vacuous.

Independent H4 searches (different wording from the worker):

- `msearch.py ... leanfinder "etale sheaf compact support inverse image finite clopen partition generators relations colimit"`: eight hits about condensed locally constant presheaf colimits; none is this etale proper-support presentation.
- `msearch.py ... loogle '"Sheaf", "support"'`: twelve hits about ideal-sheaf supports; none gives this statement or its finite-parts interface.
- `msearch.py ... leansearch "A quasi finite separated scheme morphism gives a presentation of compactly supported pullback sheaves by finite open and closed components"`: eight hits about quasi-finite or quasi-separated scheme morphisms; no presentation.
- Independent `rg -n -i 'finite.?parts|clopen.*(support|sheaf)|(support|sheaf).*clopen|properSupport|quasiFinite_finiteParts_presentation'` across Mathlib, upstream WeilConjectures, project lean/Sheaf, and dag/lean_names_upstream.json found the existing support interfaces and clopen cohomology decompositions, and downstream references to this item, but no duplicate presentation or helper definition. I opened upstream `AlgebraicGeometry/Sites/CohomologyClopen.lean`: its statements concern cohomology vanishing on clopen covers and finite-morphism edge maps, so they do not replace this item.
- `python3 tools/blueprint_refs.py search 'finite parts'` returned zero imported blueprint nodes. The existing DAG item owns these particular presentation data, so no independent missing definition node is needed.

The only mismatch I found was bibliographic: the docstrings of
`finitePartsBaseChangeMap`, `finitePartsBaseChangeTuple`, and
`FinitePartsBaseChangeCompatible` cited SGA XVII 6.1.5(iii). Direct inspection of the
reedition PDF shows the stated proper-support base-change result is Proposition
6.1.4(iii), printed pp. 417–418. I corrected all three citations to 6.1.4(iii).
No mathematical statement, declaration signature, construction, dependency, or node
field needed alteration. In particular, there is no silent statement correction and
no unit statement affected.

H5/H6/H8/H9 check: all 21 supporting definitions/structures have real data; none selects
an object from a bare unproved existence assertion. The sole postponed proof is the
named theorem `quasiFinite_finiteParts_presentation`, with its blueprint/source
and all ten node proof steps in its docstring. No proof has been filled. Every helper
has its source/blueprint docstring. There are no private definitions, local instances,
or local notations. I checked that every line has at most 100 characters and that the
node's `lean.statement` is byte-for-byte the theorem signature before `:= by`.

Validation after the citation repairs: the prescribed `scompile.py Q01
lem-pur-quasifinite-finite-parts-presentation <file>` compiled both its sandbox and
library module-path forms cleanly (4.7 s and 5.3 s), with no diagnostics. The prescribed
`deliver2.py Q01 lem-pur-quasifinite-finite-parts-presentation --no-push` returned
`OK (dry run)` with preflight and compilation passing. Only the three citation edits
and this independent reading/validation record were added by the second reader.
