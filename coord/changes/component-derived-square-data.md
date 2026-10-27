# AlgebraicGeometry.ProEtale.ComponentDerivedSquare

## Reason

Separate the shared data from the existence theorem so the ordinary construction,
derived tensor descent and coherence can be stated and proved in independent modules.
The original module publicly re-exports the new data module. Every existing declaration
name, signature, field, instance attribute and definition body is preserved verbatim.
The only new data declarations are OrdinarySystem and TensorSystem, which record
strict parts of the existing System argument. No target definition changes meaning.

## Old

The original module owned all declarations from componentDirect through System and
publicly imported:

```lean
public import Sheaf.Paper.ComponentLiftBaseChange
public import Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel
public import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
```

The complete old declaration block (verbatim) is:

```lean
/-- The direct image of the relative component site is restriction along the recorded tests.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def componentDirect (X : Scheme.{u}) [IsAffine X]
    (hc : (CondensedRing.componentTests X).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      (Scheme.ProEt.topology X)) :=
  letI := hc
  (CondensedRing.componentTests X).sheafPushforwardContinuous Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
    (Scheme.ProEt.topology X)

/-- Restriction carries the canonical pointwise lax tensor maps.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance componentDirectMonoidal (X : Scheme.{u}) [IsAffine X]
    (hc : (CondensedRing.componentTests X).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      (Scheme.ProEt.topology X)) : (componentDirect X hc).LaxMonoidal := by
  dsimp only [componentDirect]
  infer_instance

/-- The actual component-site adjunction, including its specified unit.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def componentAdjunction (X : Scheme.{u}) [IsAffine X]
    (hc : (CondensedRing.componentTests X).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      (Scheme.ProEt.topology X)) :=
  letI := hc
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (CondensedRing.componentTests X) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
    (Scheme.ProEt.topology X)

/-- The slice projection adjunction; its inverse image is restriction to the slice.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def slicePointAdjunction (P : Profinite.{u}) :=
  (Over.forgetAdjStar P).sheafPushforwardContinuous
    ((coherentTopology Profinite.{u}).over P) (coherentTopology Profinite.{u})
    (E := Ab.{u + 1})

/-- The structural adjunction with absolute profinite tests as its direct image.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def absoluteAdjunction (X : Scheme.{u}) :=
  (pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp profiniteToProEt
        (Scheme.proEtaleBaseChange (toSpecZ X)) Ab.{u + 1}
        (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)
        (Scheme.ProEt.topology X))

/-- Simultaneous site and coefficient witnesses, with canonical adjunctions and
absolute-test normalization. These fields add no hypothesis to the theorem.
Source: HRS construction (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
structure Corner (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X] where
  [continuous : (CondensedRing.componentTests X).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
    (Scheme.ProEt.topology X)
    ]
  inverse : Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      Ab.{u + 1} ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  inverse_eq : inverse = @CondensedRing.componentInverse X _ continuous
  [braided : inverse.Braided]
  [finiteLimits : PreservesFiniteLimits inverse]
  [finiteColimits : PreservesFiniteColimits inverse]
  adjunction : inverse ⊣ componentDirect X continuous
  adjunction_eq : HEq adjunction (componentAdjunction X continuous)
  tensor_canonical : ∀ A B,
    Functor.OplaxMonoidal.δ inverse A B =
      (adjunction.homEquiv _ _).symm
        ((adjunction.unit.app A ⊗ₘ adjunction.unit.app B) ≫
          Functor.LaxMonoidal.μ (componentDirect X continuous)
            (inverse.obj A) (inverse.obj B))
  unit_canonical : Functor.OplaxMonoidal.η inverse =
    (adjunction.homEquiv _ _).symm (Functor.LaxMonoidal.ε (componentDirect X continuous))
  absoluteTests : Over.star (affineComponentSpace X) ⋙ CondensedRing.componentTests X ≅
    profiniteToProEtOf X
  absolute_coordinate : ∀ (S : Profinite.{u})
      (z : ((relativeComponentLift X).obj
        ((Over.star (affineComponentSpace X)).obj S)).left),
    (prod.snd : affineComponentSpace X ⨯ S ⟶ S) (relativeComponentCoordinate X
        ((Over.star (affineComponentSpace X)).obj S) z) =
      profiniteTestProjection X S ((absoluteTests.hom.app S).left z)
  beta : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
      (affineComponentSpace X) ⋙ inverse ≅ upperStarFromPoint X
  [beta_monoidal : NatTrans.IsMonoidal beta.hom]
  beta_mate : ∀ (G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (S : Profinite.{u}),
    (((conjugateIsoEquiv
      ((slicePointAdjunction (affineComponentSpace X)).comp adjunction)
      (absoluteAdjunction X) beta.symm).hom.app G).hom.app (op S)) =
      G.obj.map (absoluteTests.inv.app S).op
  coefficient : inverse.mapMon.obj
      (Mon.mk (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))) ≅
    Mon.mk (condensedRingObj Λ.X X)
  coefficient_eq : coefficient.hom.hom = beta.hom.app Λ.X

attribute [instance] Corner.braided Corner.finiteLimits Corner.finiteColimits
  Corner.beta_monoidal

/-- The actual module inverse image, transporting along the prescribed coefficient iso.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def Corner.modules (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X]
    (s : Corner Λ X) :=
  s.inverse.mapMod (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X)) ⋙
    Mod.comap s.coefficient.inv.hom

/-- Additivity comes from finite-product preservation of the actual inverse image.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance Corner.modulesAdditive (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X]
    (s : Corner Λ X) : (s.modules Λ X).Additive :=
  letI : PreservesFiniteLimits (s.modules Λ X) := by
    dsimp only [Corner.modules]
    infer_instance
  Functor.additive_of_preserves_binary_products _

/-- The actual direct image for a map of component spaces is restriction along base change.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def sliceDirect {P Q : Profinite.{u}} (h : Q ⟶ P) :=
  (Over.pullback h).sheafPushforwardContinuous Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over P) ((coherentTopology Profinite.{u}).over Q)

/-- Slice restriction carries its canonical pointwise lax tensor maps.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance sliceDirectMonoidal {P Q : Profinite.{u}} (h : Q ⟶ P) :
    (sliceDirect h).LaxMonoidal := by
  dsimp only [sliceDirect]
  infer_instance

/-- The inverse image left adjoint to restriction along the profinite base-change functor.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def sliceInverse {P Q : Profinite.{u}} (h : Q ⟶ P) :=
  Functor.sheafPullbackConstruction.sheafPullback (Over.pullback h) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over P) ((coherentTopology Profinite.{u}).over Q)

/-- Its canonical adjunction, used to specify all mate normalizations.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def sliceAdjunction {P Q : Profinite.{u}} (h : Q ⟶ P) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Over.pullback h) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over P) ((coherentTopology Profinite.{u}).over Q)

/-- The coefficient comparison on a profinite slice is fixed by the canonical product map.
Source: HRS construction (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
structure Slice (Λ : Profinite.CondensedRing.{u}) {P Q : Profinite.{u}} (h : Q ⟶ P) where
  inverse : Sheaf ((coherentTopology Profinite.{u}).over P) Ab.{u + 1} ⥤
    Sheaf ((coherentTopology Profinite.{u}).over Q) Ab.{u + 1}
  inverse_eq : inverse = sliceInverse h
  [braided : inverse.Braided]
  [finiteLimits : PreservesFiniteLimits inverse]
  [finiteColimits : PreservesFiniteColimits inverse]
  adjunction : inverse ⊣ sliceDirect h
  adjunction_eq : HEq adjunction (sliceAdjunction h)
  tensor_canonical : ∀ A B,
    Functor.OplaxMonoidal.δ inverse A B =
      (adjunction.homEquiv _ _).symm
        ((adjunction.unit.app A ⊗ₘ adjunction.unit.app B) ≫
          Functor.LaxMonoidal.μ (sliceDirect h) (inverse.obj A) (inverse.obj B))
  unit_canonical : Functor.OplaxMonoidal.η inverse =
    (adjunction.homEquiv _ _).symm (Functor.LaxMonoidal.ε (sliceDirect h))
  beta : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} P ⋙ inverse ≅
    (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} Q
  [beta_monoidal : NatTrans.IsMonoidal beta.hom]
  beta_mate : ∀ (G : Sheaf ((coherentTopology Profinite.{u}).over Q) Ab.{u + 1})
      (S : Profinite.{u}),
    (((conjugateIsoEquiv
      ((slicePointAdjunction P).comp adjunction)
      (slicePointAdjunction Q) beta.symm).hom.app G).hom.app (op S)) =
      G.obj.map ((Over.starPullbackIsoStar h).inv.app S).op
  coefficient : inverse.mapMon.obj (Mon.mk (CondensedRing.profiniteCoefficient Λ.X P)) ≅
    Mon.mk (CondensedRing.profiniteCoefficient Λ.X Q)
  coefficient_eq : coefficient.hom.hom = beta.hom.app Λ.X

attribute [instance] Slice.braided Slice.finiteLimits Slice.finiteColimits Slice.beta_monoidal

/-- The actual slice module inverse image with the canonical coefficient transport.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def Slice.modules (Λ : Profinite.CondensedRing.{u}) {P Q : Profinite.{u}} {h : Q ⟶ P}
    (s : Slice Λ h) :=
  s.inverse.mapMod (CondensedRing.profiniteCoefficient Λ.X P) ⋙
    Mod.comap s.coefficient.inv.hom

/-- Finite limits of the component module pullback are computed on underlying sheaves.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance Corner.modulesFiniteLimits (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u})
    [IsAffine X] (s : Corner Λ X) : PreservesFiniteLimits (s.modules Λ X) := by
  dsimp only [Corner.modules]
  infer_instance

/-- Finite colimits of the component module pullback are computed on underlying sheaves.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance Corner.modulesFiniteColimits (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u})
    [IsAffine X] (s : Corner Λ X) : PreservesFiniteColimits (s.modules Λ X) := by
  dsimp only [Corner.modules]
  infer_instance

/-- Finite limits of the slice module pullback are computed on underlying sheaves.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance Slice.modulesFiniteLimits (Λ : Profinite.CondensedRing.{u})
    {P Q : Profinite.{u}} {h : Q ⟶ P} (s : Slice Λ h) :
    PreservesFiniteLimits (s.modules Λ) := by
  dsimp only [Slice.modules]
  infer_instance

/-- Finite colimits of the slice module pullback are computed on underlying sheaves.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance Slice.modulesFiniteColimits (Λ : Profinite.CondensedRing.{u})
    {P Q : Profinite.{u}} {h : Q ⟶ P} (s : Slice Λ h) :
    PreservesFiniteColimits (s.modules Λ) := by
  dsimp only [Slice.modules]
  infer_instance

/-- Additivity of the slice module inverse image.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance Slice.modulesAdditive (Λ : Profinite.CondensedRing.{u})
    {P Q : Profinite.{u}} {h : Q ⟶ P} (s : Slice Λ h) : (s.modules Λ).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Exact module inverse image on the ordinary unbounded derived category.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def Corner.derived (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X]
    (s : Corner Λ X) := (s.modules Λ X).mapDerivedCategory

/-- The slice pullback on the ordinary unbounded derived category is termwise localization.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def Slice.derived (Λ : Profinite.CondensedRing.{u})
    {P Q : Profinite.{u}} {h : Q ⟶ P} (s : Slice Λ h) :=
  (s.modules Λ).mapDerivedCategory


/-- Identify extension along the scheme coefficient isomorphism with transported scalars.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def schemeUnderlying (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    CondensedRing.upperStar Λ.X f ⋙ Mod.forget (condensedRingObj Λ.X Y) ≅
      Mod.forget (condensedRingObj Λ.X X) ⋙ upperStar Ab.{u + 1} f :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ.X X))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ.X f)))
    (Mod.forget (condensedRingObj Λ.X Y))

/-- The two actual module inverse-image paths for one affine scheme morphism.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
structure Square (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    (sX : Corner Λ X) (sY : Corner Λ Y) (sh : Slice Λ (affineComponentMap f)) where
  tests : CondensedRing.componentTests X ⋙ Scheme.proEtaleBaseChange f ≅
    Over.pullback (affineComponentMap f) ⋙ CondensedRing.componentTests Y
  tests_eq : ∀ E : Over (affineComponentSpace X),
    (tests.hom.app E).left = ((component_lift_base_change.choose f).hom.app E).left
  abelian : sX.inverse ⋙ upperStar Ab.{u + 1} f ≅ sh.inverse ⋙ sY.inverse
  abelian_mate : ∀ (G : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (E : Over (affineComponentSpace X)),
    (((conjugateIsoEquiv
      (sh.adjunction.comp sY.adjunction)
      (sX.adjunction.comp (upperStarLowerStarAdjunction Ab.{u + 1} f))
      abelian).hom.app G).hom.app (op E)) = G.obj.map (tests.hom.app E).op
  coefficient :
    (upperStar Ab.{u + 1} f).map sX.coefficient.hom.hom ≫ condensedPullbackHom Λ.X f =
      abelian.hom.app (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X)) ≫
        sY.inverse.map sh.coefficient.hom.hom ≫ sY.coefficient.hom.hom
  ordinary : sX.modules Λ X ⋙ CondensedRing.upperStar Λ.X f ≅
    sh.modules Λ ⋙ sY.modules Λ Y
  ordinary_underlying : ∀ M :
      Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        Ab.{u + 1}) (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X)),
    (ordinary.hom.app M).hom =
      (schemeUnderlying Λ f).hom.app ((sX.modules Λ X).obj M) ≫ abelian.hom.app M.X

/-- The left derived path is the localization of the actual scheme/module inverse images.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
abbrev leftPath (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] (sX : Corner Λ X) (f : Y ⟶ X) :=
  sX.derived Λ X ⋙ (CondensedRing.upperStar Λ.X f).mapDerivedCategory

/-- The right derived path is the localization of the actual slice/module inverse images.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
abbrev rightPath (Λ : Profinite.CondensedRing.{u})
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (sY : Corner Λ Y) (f : Y ⟶ X) (sh : Slice Λ (affineComponentMap f)) :=
  sh.derived Λ ⋙ sY.derived Λ Y

/-- The derived square is the specified termwise module comparison, localized, with
both canonical derived composition comparisons inserted.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def Square.theta (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] {f : Y ⟶ X}
    {sX : Corner Λ X} {sY : Corner Λ Y} {sh : Slice Λ (affineComponentMap f)}
    (sq : Square Λ f sX sY sh) : leftPath Λ sX f ≅ rightPath Λ sY f sh :=
  letI : (CondensedRing.upperStar Λ.X f).Additive :=
    CondensedRing.upperStar_additive Λ.X f
  letI : PreservesFiniteLimits (CondensedRing.upperStar Λ.X f) :=
    CondensedRing.preservesFiniteLimits_upperStar Λ.X f
  letI : PreservesFiniteColimits (CondensedRing.upperStar Λ.X f) :=
    CondensedRing.preservesFiniteColimits_upperStar Λ.X f
  letI := comp_preservesFiniteLimits (sX.modules Λ X) (CondensedRing.upperStar Λ.X f)
  letI := comp_preservesFiniteColimits (sX.modules Λ X) (CondensedRing.upperStar Λ.X f)
  letI := comp_preservesFiniteLimits (sh.modules Λ) (sY.modules Λ Y)
  letI := comp_preservesFiniteColimits (sh.modules Λ) (sY.modules Λ Y)
  letI : (sX.modules Λ X ⋙ CondensedRing.upperStar Λ.X f).Additive :=
    inferInstance
  letI : (sh.modules Λ ⋙ sY.modules Λ Y).Additive := inferInstance
  (Functor.mapDerivedCategoryCompIso (sX.modules Λ X)
      (CondensedRing.upperStar Λ.X f)).symm ≪≫
    Functor.mapDerivedCategoryNatIso sq.ordinary ≪≫
      Functor.mapDerivedCategoryCompIso (sh.modules Λ) (sY.modules Λ Y)


/-- The ordinary component module tensor is the existing transported relative tensor.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance Corner.modulesMonoidal (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (X : Scheme.{u}) [IsAffine X] (s : Corner Λ X) : (s.modules Λ X).Monoidal := by
  dsimp only [Corner.modules]
  infer_instance

/-- The ordinary slice module tensor is the existing transported relative tensor.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
instance Slice.modulesMonoidal (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {P Q : Profinite.{u}} {h : Q ⟶ P} (s : Slice Λ h) : (s.modules Λ).Monoidal := by
  dsimp only [Slice.modules]
  infer_instance

section Tensor
universe v w
variable {C D : Type w} [Category.{v} C] [Category.{v} D] [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v} D]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v} D]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [BraidedCategory C] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Monoidal]

/-- The ordinary derived monoidal structure is normalized by termwise tensor and Q.
The braidings are the existing Koszul braidings, rather than unspecified structures.
Source: HRS Section 3 and (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
structure TensorLift where
  [colimits : PreservesColimitsOfSize.{0, 0} F]
  [monoidal : F.mapDerivedCategory.Monoidal]
  localization : NatTrans.IsMonoidal F.mapDerivedCategoryFactors.hom
  triangulated : F.mapDerivedCategory.IsTriangulated
  symmetric : ∀ K L : DerivedCategory C,
    Functor.LaxMonoidal.μ F.mapDerivedCategory K L ≫
        F.mapDerivedCategory.map ((DerivedCategory.braidedCategory' C).braiding K L).hom =
      ((DerivedCategory.braidedCategory' D).braiding
        (F.mapDerivedCategory.obj K) (F.mapDerivedCategory.obj L)).hom ≫
          Functor.LaxMonoidal.μ F.mapDerivedCategory L K

end Tensor


/-- Identity on the actual slice pullback, normalized by the projection of the test object.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
structure SliceIdentity (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X]
    (s : Slice Λ (affineComponentMap (𝟙 X))) where
  tests : Over.pullback (affineComponentMap (𝟙 X)) ≅ 𝟭 (Over (affineComponentSpace X))
  tests_projection : ∀ E, (tests.hom.app E).left =
    pullback.fst E.hom (affineComponentMap (𝟙 X))
  abelian : s.inverse ≅ 𝟭 _
  abelian_mate : ∀ (G : Sheaf
      ((coherentTopology Profinite.{u}).over (affineComponentSpace X)) Ab.{u + 1}) E,
    (((conjugateIsoEquiv s.adjunction (Adjunction.id) abelian.symm).hom.app G).hom.app
      (op E)) = G.obj.map (tests.inv.app E).op
  ordinary : s.modules Λ ≅ 𝟭 _
  ordinary_underlying : ∀ M, (ordinary.hom.app M).hom = abelian.hom.app M.X

/-- Composition of slice inverse images, with both test-object projections prescribed.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
structure SliceComposition (Λ : Profinite.CondensedRing.{u})
    {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (f : Y ⟶ X) (g : Z ⟶ Y)
    (sf : Slice Λ (affineComponentMap f)) (sg : Slice Λ (affineComponentMap g))
    (sfg : Slice Λ (affineComponentMap (g ≫ f))) where
  tests : Over.pullback (affineComponentMap (g ≫ f)) ≅
    Over.pullback (affineComponentMap f) ⋙ Over.pullback (affineComponentMap g)
  tests_fst : ∀ E,
    (tests.hom.app E).left ≫
        pullback.fst ((Over.pullback (affineComponentMap f)).obj E).hom
          (affineComponentMap g) ≫ pullback.fst E.hom (affineComponentMap f) =
      pullback.fst E.hom (affineComponentMap (g ≫ f))
  tests_snd : ∀ E,
    (tests.hom.app E).left ≫
        pullback.snd ((Over.pullback (affineComponentMap f)).obj E).hom
          (affineComponentMap g) = pullback.snd E.hom (affineComponentMap (g ≫ f))
  abelian : sfg.inverse ≅ sf.inverse ⋙ sg.inverse
  abelian_mate : ∀ (G : Sheaf
      ((coherentTopology Profinite.{u}).over (affineComponentSpace Z)) Ab.{u + 1}) E,
    (((conjugateIsoEquiv sfg.adjunction (sf.adjunction.comp sg.adjunction)
      abelian.symm).hom.app G).hom.app (op E)) = G.obj.map (tests.inv.app E).op
  ordinary : sfg.modules Λ ≅ sf.modules Λ ⋙ sg.modules Λ
  ordinary_underlying : ∀ M, (ordinary.hom.app M).hom = abelian.hom.app M.X

/-- Derived identity of a slice pullback, obtained by the existing localization operation.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def SliceIdentity.derived (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X]
    {s : Slice Λ (affineComponentMap (𝟙 X))} (i : SliceIdentity Λ X s) :=
  Functor.mapDerivedCategoryNatIso i.ordinary ≪≫ Functor.mapDerivedCategoryIdIso _

/-- Derived slice composition, with the existing canonical localization comparisons.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def SliceComposition.derived (Λ : Profinite.CondensedRing.{u})
    {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    {f : Y ⟶ X} {g : Z ⟶ Y}
    {sf : Slice Λ (affineComponentMap f)} {sg : Slice Λ (affineComponentMap g)}
    {sfg : Slice Λ (affineComponentMap (g ≫ f))}
    (c : SliceComposition Λ f g sf sg sfg) :=
  letI := comp_preservesFiniteLimits (sf.modules Λ) (sg.modules Λ)
  letI := comp_preservesFiniteColimits (sf.modules Λ) (sg.modules Λ)
  Functor.mapDerivedCategoryNatIso c.ordinary ≪≫
    Functor.mapDerivedCategoryCompIso (sf.modules Λ) (sg.modules Λ)

/-- Derived scheme identity, with the published ordinary identity and localization maps.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def schemeIdentity (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :=
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ.X X) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Derived scheme composition, with the published ordinary adjunction comparison.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def schemeComposition (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :=
  letI := comp_preservesFiniteLimits (CondensedRing.upperStar Λ.X f)
    (CondensedRing.upperStar Λ.X g)
  letI := comp_preservesFiniteColimits (CondensedRing.upperStar Λ.X f)
    (CondensedRing.upperStar Λ.X g)
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ.X g f) ≪≫
    Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ.X f)
      (CondensedRing.upperStar Λ.X g)


/-- Monoidality of the specified comparison, with canonical termwise-localized structures.
This includes the coefficient-unit equation and both tensor comparisons.
Source: HRS (4.1) (blueprint: lem-zl-component-derived-pullback-square). -/
def Square.monoidal (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] {f : Y ⟶ X}
    {sX : Corner Λ X} {sY : Corner Λ Y} {sh : Slice Λ (affineComponentMap f)}
    (sq : Square Λ f sX sY sh)
    (tX : TensorLift (sX.modules Λ X)) (tY : TensorLift (sY.modules Λ Y))
    (tf : TensorLift (CondensedRing.upperStar Λ.X f)) (th : TensorLift (sh.modules Λ)) : Prop :=
  letI := tX.monoidal
  letI := tY.monoidal
  letI := tf.monoidal
  letI := th.monoidal
  (∀ K L,
    Functor.LaxMonoidal.μ (CondensedRing.upperStar Λ.X f).mapDerivedCategory
        (((sX.modules Λ X).mapDerivedCategory).obj K)
        (((sX.modules Λ X).mapDerivedCategory).obj L) ≫
      (CondensedRing.upperStar Λ.X f).mapDerivedCategory.map
        (Functor.LaxMonoidal.μ (sX.modules Λ X).mapDerivedCategory K L) ≫
      (sq.theta Λ).hom.app (K ⊗ L) =
    ((sq.theta Λ).hom.app K ⊗ₘ (sq.theta Λ).hom.app L) ≫
      Functor.LaxMonoidal.μ (sY.modules Λ Y).mapDerivedCategory
        ((sh.modules Λ).mapDerivedCategory.obj K)
        ((sh.modules Λ).mapDerivedCategory.obj L) ≫
      (sY.modules Λ Y).mapDerivedCategory.map
        (Functor.LaxMonoidal.μ (sh.modules Λ).mapDerivedCategory K L)) ∧
  (Functor.LaxMonoidal.ε (CondensedRing.upperStar Λ.X f).mapDerivedCategory ≫
      (CondensedRing.upperStar Λ.X f).mapDerivedCategory.map
        (Functor.LaxMonoidal.ε (sX.modules Λ X).mapDerivedCategory) ≫
      (sq.theta Λ).hom.app (𝟙_ _) =
    Functor.LaxMonoidal.ε (sY.modules Λ Y).mapDerivedCategory ≫
      (sY.modules Λ Y).mapDerivedCategory.map
        (Functor.LaxMonoidal.ε (sh.modules Λ).mapDerivedCategory))

/-- A single coherent family of the square, its exact symmetric tensor structures and
its termwise descent. Identity/composition maps are normalized by test-object projections.
Source: HRS (4.1), Corollary 4.4(2)
(blueprint: lem-zl-component-derived-pullback-square). -/
structure System (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] where
  corner : ∀ (X : Scheme.{u}) [IsAffine X], Corner Λ X
  slice : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    Slice Λ (affineComponentMap f)
  square : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    Square Λ f (corner X) (corner Y) (slice f)
  cornerTensor : ∀ (X : Scheme.{u}) [IsAffine X], TensorLift ((corner X).modules Λ X)
  sliceTensor : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    TensorLift ((slice f).modules Λ)
  schemeTensor : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    TensorLift (CondensedRing.upperStar Λ.X f)
  monoidal : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    (square f).monoidal Λ (cornerTensor X) (cornerTensor Y) (schemeTensor f) (sliceTensor f)
  sliceIdentity : ∀ (X : Scheme.{u}) [IsAffine X], SliceIdentity Λ X (slice (𝟙 X))
  sliceComposition : ∀ {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (f : Y ⟶ X) (g : Z ⟶ Y),
    SliceComposition Λ f g (slice f) (slice g) (slice (g ≫ f))
  identity : ∀ (X : Scheme.{u}) [IsAffine X]
      (K : CondensedRing.Evaluation.D
        ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    ((square (𝟙 X)).theta Λ).hom.app K ≫
        ((corner X).derived Λ X).map (((sliceIdentity X).derived Λ X).hom.app K) =
      (schemeIdentity Λ X).hom.app (((corner X).derived Λ X).obj K)
  composition : ∀ (X Y Z : Scheme.{u}) [IsAffine X] [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y)
      (K : CondensedRing.Evaluation.D
        ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    (schemeComposition Λ f g).hom.app (((corner X).derived Λ X).obj K) ≫
        (CondensedRing.upperStar Λ.X g).mapDerivedCategory.map
          (((square f).theta Λ).hom.app K) ≫
        ((square g).theta Λ).hom.app (((slice f).derived Λ).obj K) =
      ((square (g ≫ f)).theta Λ).hom.app K ≫
        ((corner Z).derived Λ Z).map (((sliceComposition f g).derived Λ).hom.app K)
  cornerDuals : ∀ (X : Scheme.{u}) [IsAffine X]
      (K : CondensedRing.Evaluation.D
        ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    IsDualizable K → IsDualizable (((corner X).derived Λ X).obj K)
  sliceDuals : ∀ (X Y : Scheme.{u}) [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
      (K : CondensedRing.Evaluation.D
        ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    IsDualizable K → IsDualizable (((slice f).derived Λ).obj K)
  schemeDuals : ∀ (X Y : Scheme.{u}) [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
      (K : CondensedRing.Evaluation.D (Scheme.ProEt.topology X) (condensedRingObj Λ.X X)),
    IsDualizable K → IsDualizable ((CondensedRing.upperStar Λ.X f).mapDerivedCategory.obj K)


```

## New

The declaration block above moves unchanged to
Sheaf.Paper.ComponentDerivedSquareData, which has the same public imports.
The original module instead re-exports it:

```lean
public import Sheaf.Paper.ComponentDerivedSquareData
```

OrdinarySystem adds the ordinary identity and composition equations, and TensorSystem
adds just the three normalized tensor lifts and monoidality of the comparison. These
are data structures, with no choices and no proof holes in their bodies. Their new
DAG owner is def-zl-component-derived-square-data. The original theorem retains
exactly its name, universes and statement.

## Users

The direct-consumer scan is tools/downstream.py with --direct and --uses for Corner,
Slice, Square, TensorLift, System and component_derived_pullback_square. The two
external direct importers are listed below. All transitive consumers retain the same
public API because the original module publicly re-exports the unchanged declarations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ComponentDerivedPullbackSquare | D9 | Re-exports the data and assembles the unchanged theorem. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | unclaimed | Same Corner/Slice instances and theorem signature; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedIrreducibleGenericScalarModel | unclaimed | Same Corner/Slice/Square and scheme comparison definitions; no adaptation. |

Additional textual users returned by the full moved-declaration scan (including
namespace-unrelated suffix matches):

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedForgetTensorTransposition | U1 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Algebra.Homology.RingedForgetTwoInjectiveHom | U2 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.AdicRealizationFamilyData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.AffineLineCompositeTranspose | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.AlgClTopologyMateHomBijection | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | F7 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.BrownTowerBoundedTransport | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.BrownTowerGeometricTransport | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.BrownTowerRealization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.BrownTowerSite | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ClassicalTwoFibreScalarData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ClopenCanonicalFiniteEvaluation | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ClopenCounitAdjointComparison | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ClopenStrictSystemSupport | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ClopenSystemRealizationData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ClosedSectionCompactOrigin | B9 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.CoefFiniteHomSiteDescent | C5 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.CoefFiniteSiteHomTransport | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | R5 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.CoefficientEvaluationNaturality | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.CommonStageRestrictionTensorDescent | U6 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.CompactSupportCompositeTransposeDomains | M2 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | Y5 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.CompactSupportLimitEquationRealization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.CompleteProjectionMateDescent | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.CompositionTensorMate | G8 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ConcreteProjectionReductionSquare | D7 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCompositor | D8 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ConstructibleTensorComposition | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.DerivedWeilOperations | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.DiagonalCompletedDiagramRealization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.DiagonalCompletedFrame | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.DiagonalCompletedPushSquare | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.DiagonalOrientationRefinement | T8 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.DualBaseChange | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.EtaleBrownCoefficientCoherence | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.EtaleBrownGeometricComparisons | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.EtaleBrownProjectionRealization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.EtaleBrownSupportTransition | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.EtaleCoefficientProperCoproducts | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | E1 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.EtaleCofinalSupportComposition | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.EtaleKFlatTensorPresentation | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.EtaleProEtaleScalarCounitTransposes | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.EtaleSystemBrownConstruction | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.EtaleSystemCofinalData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.EtaleSystemCofinalMate | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.EtaleSystemEvaluationBound | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.EtaleSystemProjectionData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.EtaleSystemScalarMateCoherence | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.EtaleTowerBrownAdjunction | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ExceptionalOriginAdjunctionEvaluation | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ExceptionalProOriginExactLinear | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ExceptionalSystemInterfaces | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ExchangeFunctoriality | F6 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | P8 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportCoefficientSquare | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.FiniteExceptionalSiteNormalization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.FinitePointReconstructedEvaluationSquare | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.FiniteSpanModuleDerivedComparison | X8 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.FrameworkPbcComparisonSystem | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.FrameworkPbcPullbackScalarBridge | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.FreeInsertionCompactSupportCoherence | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | M3 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | H6 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | T2 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | F8 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | V6 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.IntegralSemilinearGermSquare | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.KummerStratumScalarMaps | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedStrictSystems | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.NativeWeilClosedForgetful | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.OrientedDoubleHomCancellation | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.OrientedPerfectDuality | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.PairingData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.PerfectDualPairAndTateStability | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.PointEquivariantDiagramLift | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.PointSystemNormalizedComparisonData | H3 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | W8 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ProjectionReductionPresentation | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ProjectiveDiagonalPullback | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ProperCoefficientDescent | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.PurIntegralReductionUniformTor | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | B9 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | Q4 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.PurStrictIntegralExchangeNormalization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SfPackageBaseChangeDomainRealization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | B4 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluing | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.StrictDirectImageMixedUnit | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.StrictReductionCompactSupportNormalization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SupportedCommonFieldScalarData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SupportedRootScalarSiteComparison | A7 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SystemClopenMateIdentification | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SystemCompactSupportRestrictionData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SystemCompactSupportRestrictionEvaluation | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SystemCompactSupportTransitions | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SystemEnrichedProjectionAdjunction | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SystemInternalHomRepresentability | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SystemRefinementConstructibleDomain | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.SystemTensorPresentationIdentification | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | S1 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.TowerAdjointCompositorRealization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.TowerP1GeometricCoordinates | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.TowerP1LevelWords | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.TowerP1PushCoordinates | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.TowerP1TensorCoordinates | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionTower | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.Paper.ZlOpenCompactSupportRestriction | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.AmbientExactClopenComparison | R4 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.CoefFinitePairingEvaluationData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.CoefPairingFiniteNormalization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.CoefPairingSystemDinaturality | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.CoefSystemProjectionEvaluation | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.CoefficientProjectionPointData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.CompactifiedProperTowerExchange | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeRealization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | U7 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | S2 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicRealization | T1 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | G2 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionRecursion | T2 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.OpenBaseChangeSquare | P2 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | A5 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | J1 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | Y8 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | C4 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.ProductSystemUniformRealizationDomain | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization | D2 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.ProjectionRefinementDescent | E2 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | J3 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | D2 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.RefinementProjectionCounit | T3 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.ScalarDirectImageMateCoherence | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.ScalarSixDirectImage | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.SemilinearOpenExternalCoherence | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.TensorHomTranspositionData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.ThreeCellCompositor | J2 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.TriangleProjectionNormalForm | T4 | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.VerdierExchangeData | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.TraceFormula.FrobeniusProperPowerExchange | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| WeilConjectures | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeOpenImmersionSheaf | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompletedExchange | unclaimed | Textual suffix match; original declarations re-exported verbatim; no adaptation. |

Consumer check: `tools/downstream.py Sheaf.Paper.ComponentDerivedPullbackSquare --uses
ComponentDerivedSquare` lists precisely the two external consumers above and the item
itself. Generic last-segment matches such as `System` and `Square` in other namespaces
are unrelated declarations. The original data block was compared byte-for-byte with
the new data module and is identical.

## Status

landed 20261025T100935-L-3640985 2026-10-25 (merge of deliver/D9/Sheaf.Paper.ComponentDerivedPullbackSquare)
