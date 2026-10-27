module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Sheaf.CategoryTheory.ConstantScalarRestrictionTensor
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.CategoryTheory.ConstantModuleGeometricComparisonData
public import Sheaf.Paper.RingedTensorSquarePresentation

public import Sheaf.CategoryTheory.ConstantModuleDerivedComparisonData
public import Sheaf.Paper.RingedProjectionTensorAssociativity
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Étale and ringed-site projection identifications

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 07A6 and 0B56
(blueprint: def-pur-etale-ringed-projection-presentation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w a h

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open CategoryTheory.ConstantScalarRestriction CategoryTheory.ConstantModuleDerivedProjection

namespace AlgebraicGeometry.Etale.RingedProjectionIdentification

/-- A coefficient-small presentation of the étale site, lifting only its Hom universe.
Source: the size convention and Stacks 07A4
(blueprint: def-pur-etale-ringed-projection-presentation). -/
abbrev Site (T : Scheme.{u}) := ULiftHom.{u + 1} T.Etale

/-- Transport the actual étale topology along the canonical equivalence.
Source: the size convention and Stacks 07A4
(blueprint: def-pur-etale-ringed-projection-presentation). -/
abbrev topology (T : Scheme.{u}) : GrothendieckTopology (Site T) :=
  (ULiftHom.equiv : T.Etale ≌ Site T).inverse.inducedTopology T.smallEtaleTopology

/-- Site transport for arbitrary sheaf values, including the underlying set sheaves.
Source: the size convention and Stacks 07A4
(blueprint: def-pur-etale-ringed-projection-presentation). -/
def presentationEquivalence (T : Scheme.{u}) (A : Type a) [Category.{h} A] :
    Sheaf T.smallEtaleTopology A ≌ Sheaf (topology T) A := by
  let e := (ULiftHom.equiv : T.Etale ≌ Site T)
  have : e.inverse.IsDenseSubsite (topology T) T.smallEtaleTopology := by
    change e.inverse.IsDenseSubsite (e.inverse.inducedTopology T.smallEtaleTopology)
      T.smallEtaleTopology
    infer_instance
  exact e.sheafCongr T.smallEtaleTopology (topology T) A

/-- The specified equivalence of fixed-coefficient sheaves on the two site presentations.
Source: the size convention and Stacks 07A4
(blueprint: def-pur-etale-ringed-projection-presentation). -/
def nativeEquivalence (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) ≌ Fixed (topology T) Λ :=
  presentationEquivalence T (ModuleCat.{u + 1} Λ)

/-- Constant scalar restriction followed by the specified site transport to the native site.
Source: Stacks 03CY, 07A4 and 0B56
(blueprint: def-pur-etale-ringed-projection-presentation). -/
def toNative (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    Modules (topology T) Λ ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  restriction (topology T) Λ ⋙ (nativeEquivalence T Λ).inverse

/-- The literal site restriction is additive on the unchanged section homomorphisms.
Source: Stacks 03CY (blueprint: def-pur-etale-ringed-projection-presentation). -/
instance toNative_additive (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    (toNative T Λ).Additive where
  map_add := by
    intros
    ext U x
    rfl

/-- The same site restriction is an equivalence, with the scalar extension inverse.
Source: Stacks 03CY (blueprint: def-pur-etale-ringed-projection-presentation). -/
instance toNative_equivalence (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    (toNative T Λ).IsEquivalence := by
  unfold toNative
  have : ((nativeEquivalence T Λ).inverse).IsEquivalence :=
    (nativeEquivalence T Λ).isEquivalence_inverse
  infer_instance

/-- The actual small ringed-site corner, with its ordinary K-flat localization tensor.
Source: Stacks 06YU and 07A4
(blueprint: def-pur-etale-ringed-projection-presentation). -/
def corner (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{w} (Modules (topology T) Λ)] :
    SheafOfModules.RingedTensorCorner.{u + 1, w} where
  site := Site T
  topology := topology T
  ring := ring (topology T) Λ
  tensor := Functor.uncurry.obj (curriedTensor (DerivedCategory (Modules (topology T) Λ)))

/-- The derived constant-scalar restriction on the specified site presentation.
Source: Stacks 03CY and 07A4
(blueprint: def-pur-etale-ringed-projection-presentation). -/
abbrev derivedToNative (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{u + 1} (Modules (topology T) Λ)] :=
  (toNative T Λ).mapDerivedCategory

/-- The ordinary scalar restriction, normalized on pure tensors and constant units.
This also fixes the tensor structure of the otherwise purely categorical site transport.
Source: Stacks 03CY and 0GMW
(blueprint: def-pur-etale-ringed-projection-presentation). -/
structure NativeOrdinaryTensorData (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] where
  braided : (toNative T Λ).Braided
  pure : ∀ (M N : Modules (topology T) Λ) (U : T.Etaleᵒᵖ)
    (x : M.val.obj ((ULiftHom.equiv : T.Etale ≌ Site T).functor.op.obj U))
    (y : N.val.obj ((ULiftHom.equiv : T.Etale ≌ Site T).functor.op.obj U)),
    ((@Functor.OplaxMonoidal.δ _ _ _ _ _ _ (toNative T Λ)
      braided.toMonoidal.toOplaxMonoidal M N).hom.app U)
        (ringPure (topology T) Λ M N
          ((ULiftHom.equiv : T.Etale ≌ Site T).functor.op.obj U) x y) =
      fixedPure T.smallEtaleTopology Λ ((toNative T Λ).obj M) ((toNative T Λ).obj N) U x y
  unit : ∀ (U : T.Etaleᵒᵖ) (b : Λ),
    ((@Functor.OplaxMonoidal.η _ _ _ _ _ _ (toNative T Λ)
      braided.toMonoidal.toOplaxMonoidal).hom.app U)
        ((toSheafify (topology T)
          ((Functor.const (Site T)ᵒᵖ).obj (CommRingCat.of Λ))).app
            ((ULiftHom.equiv : T.Etale ≌ Site T).functor.op.obj U) b) =
      fixedUnitScalar T.smallEtaleTopology Λ U b

/-- The normalized signed-total tensor comparison for this literal scalar restriction.
The braided structure records both unitors, associativity and Koszul symmetry.
Source: Stacks 03CY, 06YU and 07A4
(blueprint: def-pur-etale-ringed-projection-presentation). -/
def NativeTensorData (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{u + 1} (Modules (topology T) Λ)]
    (m : (toNative T Λ).Braided) :=
  letI := m
  DerivedComparisonData (Modules (topology T) Λ)
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (toNative T Λ)
    (fun P ↦ P.IsKFlatIndependentCoefficients)

/-- The actual ringed-site edge of the scalar-extension geometric datum.
The pullback is termwise because the constant-ring structural map is an isomorphism;
the adjunction is the specified K-injective derived adjunction.
Source: Stacks 07A4, 07A6 and 0B56
(blueprint: def-pur-etale-ringed-projection-presentation). -/
def edge {X Y : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{u + 1} (Modules (topology Y) Λ)]
    [HasDerivedCategory.{u + 1} (Modules (topology X) Λ)]
    (d : GeometricData (topology Y) (topology X) Λ) (x : ExactData d) :
    SheafOfModules.RingedTensorEdge (corner Y Λ) (corner X Λ) := by
  letI := x
  exact {
  inverse := d.inverse
  direct := d.direct
  adjunction := d.geometric
  inverseRing := d.inverseRing
  algebraic := d.algebraic
  ringMap := d.scalarIso.hom
  pullback := d.pullR
  object_eq := d.object_eq
  map_eq := d.map_eq
  additive := d.pullR_additive
  ordinaryTensor :=
    { q := d.ringTensor.q
      q_one := d.ringTensor.q_one
      mu := d.ringTensor.mu
      naturality := d.ringTensor.naturality
      pure := d.ringTensor.pure }
  pushforward := d.pushR
  moduleAdjunction := d.ringAdj
  left := d.pullR.mapDerivedCategory
  epsilon := d.pullR.mapDerivedCategoryFactorsh.hom
  isLeftDerived := inferInstance
  right := d.pushR.rightDerivedFunctor
  derivedAdjunction := d.ringAdj.mapDerivedCategoryRightDerivedAdjunction }

/-- Canonical representative normalization of the corner model. The comparison is the
inverse of the localization tensorator on flat-term K-flat pairs.
Source: Stacks 06YU and 07A4
(blueprint: def-pur-etale-ringed-projection-presentation). -/
def ModelNormalized (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{u + 1} (Modules (topology T) Λ)]
    (a : SheafOfModules.RingedTensorModel (corner T Λ)) : Prop :=
  ∀ (P Q : CochainComplex (Modules (topology T) Λ) ℤ)
    (hP : (corner T Λ).mateFlat P) (hQ : (corner T Λ).mateFlat Q),
    Functor.LaxMonoidal.μ DerivedCategory.Q P Q ≫
      a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) = 𝟙 _


/-- The inverse image on the lifted presentation, with its canonical site transport.
Source: Stacks 00YV and 07A4
(blueprint: def-pur-etale-ringed-projection-presentation). -/
def transportedInverse {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] :
    Sheaf (topology Y) A ⥤ Sheaf (topology X) A :=
  (presentationEquivalence Y A).inverse ⋙ upperStar A f ⋙
    (presentationEquivalence X A).functor

/-- The corresponding direct image on the lifted presentation.
Source: Stacks 00YV and 07A6
(blueprint: def-pur-etale-ringed-projection-presentation). -/
def transportedDirect {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type a) [Category.{u + 1} A] :
    Sheaf (topology X) A ⥤ Sheaf (topology Y) A :=
  (presentationEquivalence X A).inverse ⋙ lowerStar A f ⋙
    (presentationEquivalence Y A).functor

/-- The ordinary inverse-image comparison after the specified change of presentation.
Its scalar-extension comparison is the mate of the underlying direct-image identity.
Source: Stacks 03EL and 07A6
(blueprint: def-pur-etale-ringed-projection-presentation). -/
def ordinaryNativeLeft {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ]
    (d : GeometricData (topology Y) (topology X) Λ)
    (o : OrdinaryIdentification d)
    (hL : d.pullA = transportedInverse f (ModuleCat.{u + 1} Λ)) :
    d.pullR ⋙ toNative X Λ ≅ toNative Y Λ ⋙ upperStar (ModuleCat.{u + 1} Λ) f :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight o.left (nativeEquivalence X Λ).inverse ≪≫
    isoWhiskerRight (isoWhiskerLeft (restriction (topology Y) Λ) (eqToIso hL))
      (nativeEquivalence X Λ).inverse ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (restriction (topology Y) Λ)
      (Functor.associator _ _ _ ≪≫
        isoWhiskerLeft (nativeEquivalence Y Λ).inverse
          (Functor.associator _ _ _ ≪≫
            isoWhiskerLeft (upperStar (ModuleCat.{u + 1} Λ) f)
              (nativeEquivalence X Λ).unitIso.symm ≪≫ Functor.rightUnitor _)) ≪≫
    (Functor.associator _ _ _).symm

/-- The direct-image comparison, identity on the underlying sections, followed by
canonical cancellation of the chosen site equivalence.
Source: Stacks 03EL and 07A6
(blueprint: def-pur-etale-ringed-projection-presentation). -/
def ordinaryNativeRight {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ]
    (d : GeometricData (topology Y) (topology X) Λ)
    (o : OrdinaryIdentification d)
    (hR : d.pushA = transportedDirect f (ModuleCat.{u + 1} Λ)) :
    d.pushR ⋙ toNative Y Λ ≅ toNative X Λ ⋙ lowerStar (ModuleCat.{u + 1} Λ) f :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight o.right (nativeEquivalence Y Λ).inverse ≪≫
    isoWhiskerRight (isoWhiskerLeft (restriction (topology X) Λ) (eqToIso hR))
      (nativeEquivalence Y Λ).inverse ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (restriction (topology X) Λ)
      (Functor.associator _ _ _ ≪≫
        isoWhiskerLeft (nativeEquivalence X Λ).inverse
          (Functor.associator _ _ _ ≪≫
            isoWhiskerLeft (lowerStar (ModuleCat.{u + 1} Λ) f)
              (nativeEquivalence Y Λ).unitIso.symm ≪≫ Functor.rightUnitor _)) ≪≫
    (Functor.associator _ _ _).symm


end AlgebraicGeometry.Etale.RingedProjectionIdentification
