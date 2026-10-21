## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.PointSheafInsertionCalculus`.
Main declaration: `AlgebraicGeometry.Scheme.pointSheafInsertionCalculus`.
The only postponed proof is that theorem. All other declarations are real-data
constructions or transparent specializations, listed in `lean.declarations`.
The node's statement and dependency lists are unchanged. There are no new nodes,
dependency repairs, or statement disputes.

### Hypotheses and notation

- An algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
  The scheme is literally `Spec (CommRingCat.of k)`; it is not an arbitrary point
  with an extra comparison assumption.
- The automorphism is `h : Aut (Spec (CommRingCat.of k))`.
- The finite commutative ring is `(A : Type u) [CommRing A] [Finite A]`.
  No nontriviality, characteristic, topology, or invertibility assumption is added.
- The original small site is `s.ProEt` with `ProEt.topology s`. Its object universe
  is `u+1` and Hom universe `u`. The already published `AsSmall` transport inside
  module inverse image is retained; no site objects are removed and those universes
  are not equated.
- The ring sheaf is the existing `proEtaleConstantRing s A`: the sheafification of
  the constant presheaf valued in `CommRingCat.of (ULift A)`. The category of modules
  is the existing `proEtaleRingModules s (proEtaleConstantRing s A)`, definitionally
  `ringedSiteModules` / `SheafOfModules` over that ring after forgetting commutativity.
  `ULift.{u+1,u} A` is the coefficient presentation used by the dependencies; its
  canonical ring equivalence with A means linearity here is exactly A-linearity.
- Each natural number n encodes the original positive exponent r=n+1; each m encodes
  the original m+1. Thus index 0 means exponent 1, and compositor index m has target
  index m+1, namely exponent m+2. There is no omitted positive exponent.

### Every construction and conclusion clause

1. The node's ordinary pullback H_r is `pointSheafPullback h A n`, an abbreviation
   of `proEtaleConstantRingPullback A (h^(n+1)).hom`. Its coefficient is exactly
   `proEtaleConstantRingComparison`, whose forward map is the canonical adjunct
   `proEtaleCoefficientInverseImageMap`; it uses `proEtaleModuleInverseImage` and
   the existing sheafified tensor extension of scalars. No alternative left adjoint
   is substituted.
2. R_r is `pointSheafRestriction h A n`. Its existing
   `proEtaleObjectModuleRestriction` is sectionwise postcomposition: its value at
   `(U,u)` is F at `(U,u ≫ (h^(n+1)).hom)`, with F's restriction maps. Its scalar
   action is transported through `pointSheafRestrictionCoefficients`. That iso is
   the actual continuous/cocontinuous sheafification comparison on the constant
   presheaf, with the constant-preserving forward direction. This is the same
   restriction comparison used in the recorded object inverse-image theorem.
3. `pointSheafGraph` is the actual distinguished comma arrow provided by
   `proEtaleObjectInverseImageIndexPoint`. In Mathlib's chosen fibre product
   `U ×_s s` its coordinates are `(id_U,u)`; interchanging the factors gives exactly
   `(u,id_U)` of the node. At the final object these coordinates are `(id_s,id_s)`.
4. `pointSheafGraphInsertion` applies the published tensor-normalized
   `proEtalePullbackTensorGenerator` at that graph and scalar 1. This is inverse-image
   colimit insertion followed by sheafification and tensor-unit insertion. The
   generator's module adjunction is the one constructed by the tensor Hom
   equivalence in `ProEtaleOperationsCanonicalAdjunction`, not an unspecified
   adjunction. `pointSheafInsertion` first applies F's restriction along
   `pointSheafRestrictionArrow` (underlying arrow h^(n+1)) and then graph insertion.
   Thus its underlying function is the j prescribed by the node, before any
   isomorphisms are asserted.
5. `pointSheafCompositor h A m` is the ordinary successive-to-direct module
   compositor. It is the inverse of the existing normalized comparison, then the
   equality transport induced by the power identity. The existential presentation
   from `proEtaleConstantRingModulePullbackComposition` determines this map: d is
   fixed on every section by the canonical fibre-product comparison, and the
   adjunction conjugation bijection fixes a from d. Consequently the `.choose`
   here takes uniquely determined data, not an arbitrary isomorphism from a bare
   Nonempty assertion. `pointSheafReindexCompositor` is the canonical `Over.mapComp`
   in the same power convention, with identity on underlying schemes.
6. The existential `e : ∀ n, pointSheafPullback h A n ≅ pointSheafRestriction h A n`
   consists of isomorphisms of functors to module sheaves. Its type includes
   A_s-linearity, naturality in F, and naturality in site objects. The first
   conjunct says that every graph/tensor-unit insertion of x maps to x, for every
   original site object and every section x. It does not test only constant or
   global sections.
7. The second conjunct states e_(m+1) after T equals e_1 followed by R_1(e_m), on
   every section of every site object. The final `F.val.map` along
   `pointSheafReindexCompositor.hom.app U` is exactly the identification
   R_1 R_m=R_(m+1) induced by the power identity. Thus this is an equality of sheaf
   maps expressed sectionwise, with no unmentioned equality of chosen site objects.
8. The existential `j n` is a natural transformation
   `pointSheafSections s A ⟶ pointSheafPullback h A n ⋙ pointSheafSections s A`.
   It is linear because its target category is ModuleCat. The third conjunct
   identifies its value on every section with the already constructed insertion.
   The natural-transformation naturality equation is exactly
   `(H_r v)(s) ∘ j_(r,F) = j_(r,G) ∘ v(s)` for every module-sheaf morphism v.
9. The fourth conjunct is e_(r,F)(s) after j_(r,F) equals F's actual restriction
   along h^r. The fifth conjunct is equality of linear maps
   `j_(m+1) = j_m ≫ j_1 ≫ Gamma(T_m)` in categorical composition order, precisely
   the node's displayed section composition identity.
10. `pointSheafSectionComplex` and `pointSheafPullbackComplex` are the existing
    `Functor.mapHomologicalComplex (ComplexShape.up ℤ)` specializations. Their
    objects and differentials are respectively the actual sectionwise and pulled
    back ones; no derived localization is introduced.
11. The existential J consists of genuine cochain maps for every integer-indexed
    complex and every positive exponent. The sixth conjunct identifies every
    component `(J n K).f i` with `(j n).app (K.X i)`. The seventh conjunct states
    naturality for every chain map v:K→L as an equality of chain maps. All component
    maps and chain maps have ModuleCat coefficients, so they are A-linear.
12. The existential t consists of cochain isomorphisms; the eighth conjunct specifies
    that their components are the actual ordinary T_m evaluated on K^i and then
    on sections. The ninth conjunct is the required composition equality of chain
    maps `J_(m+1)=J_m ≫ J_1 ≫ t_m.hom`, not merely equality on cohomology.

### Dependency declarations read and used

- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`:
  `CategoryTheory.constantSheaf` (through `proEtaleConstantRing`).
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, definitionally `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory` / `HasDerivedCategory`; the node's cochain-complex and chain-map
  notions are the underlying `CochainComplex` / `HomologicalComplex.Hom`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleBaseChange`, `proEtaleSheafInverseImage`,
  `proEtaleModuleInverseImage`, `proEtaleConstantRing`,
  `proEtaleCoefficientInverseImageMap`, and the existing module scalar extension.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  the recorded independent-universe sheaf tensor interface. Ordinary scalar extension
  remains the dependency's tensor/sheafification construction.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  `ProEtale.finiteCoefficientInverseImageMap_isIso` and its canonical
  constant-preserving identification; proof import retained. The commutative
  coefficient presentation uses the existing `proEtaleConstantRingComparison`.
- `Mathlib.CategoryTheory.Sites.Sheafification`:
  `CategoryTheory.presheafToSheaf`, `toSheafify`, `sheafificationAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`:
  `Scheme.proEtaleObjectInverseImageIndexPoint`,
  `ProEtaleObjectRestrictionComparison`, `proEtaleObjectModuleRestriction`,
  `proEtaleObjectInverseImageRestriction`.
- `Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit`:
  `Scheme.proEtalePullbackTensorGenerator`, `proEtale_tensor_composition_unit`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`:
  `Scheme.proEtaleCoefficientInverseImageMap_comp`.
- `Sheaf.CategoryTheory.SiteInverseImageCompositionGenerators`:
  `CategoryTheory.site_inverse_image_composition_generators` and its actual
  coprojection/sheafification formulas.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`:
  `SheafOfModules.exists_scalarExtensionRingIso` and its tensor-unit normalization.
- `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`: isomorphisms are weakly etale
  by the recorded Etale/WeaklyEtale instances.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`.
- Existing supporting module `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `Scheme.proEtaleConstantRingPullback`, `proEtaleConstantRingComparison` and the
  tensor-normalized adjunction. Existing supporting module
  `Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition`:
  `Scheme.proEtaleConstantRingModulePullbackComposition` with its full section and
  conjugation characterization, used by the helper T.

### Source and edge-case checks

Read Stacks `sites.tex` at `lemma-localize-given-products` (03CE),
`lemma-composition-morphisms-sites` (03CB), and `section-pullback` (06UM), as well as
this node's seven proof steps and the current blueprint proof of
`lem-trf-frobenius-operator-compact-description`. The theorem docstring retains all
seven proof steps and the stated proof dependencies.

Index n=0 is exponent 1, including m=0 in the composition law (two first powers
compose to exponent 2). Every larger positive power occurs. For h=id the actual
pullback, graph and adjunction compositor are retained rather than replacing them
by judgmental identities. The zero coefficient ring and zero module sheaf are not
excluded. Empty site objects and their zero section modules remain among the
quantified U. Complexes may be zero or unbounded in either direction, and all
integer degrees, arbitrary differentials and arbitrary chain maps are quantified.
No constructibility, evaluation-exactness, or boundedness hypothesis is present.

### Searches

- `msearch.py leanfinder`: query "Pullback module sheaves along an automorphism
  reindexes the site and normalized section insertions are natural and compose on
  cochain complexes". Eight hits, including
  `SheafOfModules.conjugateEquiv_pullbackComp_inv`, `pullbackObjFreeIso`, and free-sheaf
  naturality lemmas. None gives all graph normalizations, section cocycles and
  chain-map conclusions at an automorphic pro-etale point.
- `msearch.py loogle`: `SheafOfModules.pullbackComp`. Five hits: `pullbackComp`,
  `pullback_comp_id`, `pullback_id_comp`, `pullback_assoc`, and
  `conjugateEquiv_pullbackComp_inv`. These are generic comparison results, not this
  normalized insertion calculus.
- `msearch.py grep`: `pullbackComp|pullbackObjFreeIso|conjugateEquiv_pullbackComp`
  in `Algebra/Category/ModuleCat/Sheaf`. Ten hits in PullbackContinuous.lean and
  PullbackFree.lean, again generic comparison/free-sheaf results.
- `rg` of the actual project `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  `pointInsertion`, `automorphicPoint`, point/insertion calculus phrases: no matching
  declaration. Broader searches of pro-etale pullback, reindexing, tensor generators,
  sections, scalar transport and composition found the existing interfaces listed
  above, which this module imports and specializes. The only earlier loose
  point-transport wording in WeilConjectures was an unrelated affine-spectrum
  comparison docstring.

### Validation

`scompile.py Q118 lem-trf-point-sheaf-insertion-calculus` compiled the module under
both its sandbox and actual library module names, with no errors or warnings.
The successful checks took 24.4 s and 24.2 s, within the unchanged 60 s per-file limit.
The initial elaboration required specifying the coefficient universes in the
section functor and exposing its composition of the existing forget, evaluation
and restriction-of-scalars functors; this preserved all site/module universes.
Only `pointSheafInsertionCalculus` has `sorry`; no definition contains one.

## Second reading by Q118

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
