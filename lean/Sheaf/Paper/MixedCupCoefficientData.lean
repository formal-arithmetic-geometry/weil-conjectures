module

public import Sheaf.Paper.PodMixedSupportCupProduct
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.Paper.AdmissibleCupCoefficientPassages
public import Sheaf.Paper.MixedCupNormalizedScalars
import Sheaf.Paper.IntegralResidueTor
import Sheaf.Paper.DirectImagesConstructible
import Sheaf.Paper.ClosedScalarDomains
import Sheaf.Paper.FiniteCompactSupportScalarTransport
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated

/-! # Coefficient comparisons for the mixed-support cup

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
def-pod-mixed-support-cup-product, final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings
namespace WeilConjectures.MixedCupCoefficientChange
open scoped WeilConjectures.MixedCupCoefficientChange

variable {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)

private theorem integral_domain (X : SixFunctorSpace D)
    (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (K : sfIntegralConstructibleCategory C.l (FieldAt C F) X.obj.left) :
    finiteTorConstructibleIntegral C.l (FieldAt C F) X.obj.left K.obj := by
  let : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) := fun x ↦
    (show IsUnit (C.l : X.obj.left.residueField x) by
      simpa only [map_natCast] using (finiteFieldDatumPrimeUnit D C.l C.different).map
        (X.obj.hom.residueFieldAlgebraMap x)).invertible
  exact (congrFun (integral_residue_tor D C.l C.different (FieldAt C F)
    X.obj.left).2 _).mp K.property

private theorem finite_domain_iso (W : Scheme.{u})
    (F : Padic.FiniteCoefficientFields C.l C.Qbar) (n : ℕ)
    {K L : ambient C W (.finite F n)} (e : K ≅ L)
    (h : domain C W (.finite F n) K) : domain C W (.finite F n) L := by
  let := Padic.finite_coefficientExtensionRing C.l (FieldAt C F) (n + 1) (Nat.succ_pos n)
  have : (intrinsicFiniteTorsionConstructible C.l (FieldAt C F)
      (n + 1) (Nat.succ_pos n) W).IsClosedUnderIsomorphisms :=
    (proEtale_bounded_constructible_isTriangulated W
      (Padic.coefficientExtensionRing C.l (FieldAt C F) (n + 1))).1
  refine ⟨ObjectProperty.prop_of_iso _ e h.1, ?_⟩
  obtain ⟨a, b, ht⟩ := h.2
  refine ⟨a, b, ht.1, ?_⟩
  intro M P hM f hf hP N i hi
  exact ht.2 M P (hM.map (fun j ↦ j ≪≫ e.symm)) f hf hP N i hi

/-- A simultaneous choice of the existing normalized operations at every finite
field and positive quotient level; no extra operations are supplied.
Source: blueprint final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-data). -/
abbrev Operations := ∀ (F : Padic.FiniteCoefficientFields C.l C.Qbar) (n : ℕ),
  SixFunctorDatum D C (FieldAt C F) (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- Ordinary and compact cohomology in exactly the coefficient-complex universe.
Field-stage cohomology is transported by the recorded fully faithful carrier lift.
Source: blueprint final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-data). -/
def cohomology (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left)
    (compact : Bool) : (a : Stage C) → (domain C X.obj.left a).FullSubcategory ⥤
      DerivedCategory (ModuleCat.{u + 1} (ring C a))
  | .finite F n =>
      ObjectProperty.lift (intrinsicFiniteTorsionConstructible C.l (FieldAt C F) (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) X.obj.left)
        (domain C X.obj.left (.finite F n)).ι (fun K ↦ K.property.1) ⋙
      (if compact then (S F n).finite.support (sixFunctorStructure X) c
        else (S F n).finite.direct (sixFunctorStructure X)) ⋙
      (intrinsicFiniteTorsionConstructible C.l (FieldAt C F) (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).ι ⋙
      (pointFiniteSections D.k
        (Padic.coefficientExtensionRing C.l (FieldAt C F) (n + 1))).mapDerivedCategory
  | .integral F => (domain C X.obj.left (.integral F)).ι ⋙
      (if compact then (S F 0).higher.integral.support (sixFunctorStructure X) c
        else (S F 0).higher.integral.direct (sixFunctorStructure X)) ⋙
      (sfIntegralConstructible C.l (FieldAt C F) (Spec (.of D.k))).ι ⋙
      pointFibreIntegralAmbient D C.l (FieldAt C F)
  | .rational F => (domain C X.obj.left (.rational F)).ι ⋙
      (if compact then (S F 0).higher.rational.support (sixFunctorStructure X) c
        else (S F 0).higher.rational.direct (sixFunctorStructure X)) ⋙
      pointRationalFibre D C.l C.different (FieldAt C F) ⋙
      (DerivedCategory.pointFiniteDimensional (FieldAt C F)).ι ⋙
      (pointFibreModuleLift (FieldAt C F)).mapDerivedCategory
  | .closed => (domain C X.obj.left .closed).ι ⋙
      (if compact then (S (Padic.finiteCoefficientBase C.l C.Qbar) 0).closure.commonStage.support
          (sixFunctorStructure X) c
        else (S (Padic.finiteCoefficientBase C.l C.Qbar) 0).closure.commonStage.direct
          (sixFunctorStructure X)) ⋙
      pointQbarFibre D C.l C.different C.Qbar ⋙
      DerivedCategory.pointFdQbarRealization C.l C.Qbar ⋙
      (pointFibreModuleLift C.Qbar).mapDerivedCategory

/-- The actual mixed-support cup arrow at each coefficient stage. Field arrows
are read in the common section universe through the canonical tensor lift.
Source: blueprint final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-data). -/
def cup (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left) :
    (a : Stage C) → (domain C X.obj.left a).FullSubcategory →
      (domain C X.obj.left a).FullSubcategory → Arrow (DerivedCategory (ModuleCat.{u + 1}
        (ring C a)))
  | .finite F n, K, L => Arrow.mk
      (SixFunctorDatum.finitePairingCup (S F n) X c K L)
  | .integral F, K, L => Arrow.mk
      (SixFunctorDatum.integralPairingCup (S F 0) X c
        ⟨K.obj.obj, K.property⟩ ⟨L.obj.obj, L.property⟩)
  | .rational F, K, L => Arrow.mk
      ((pointFibreModuleLift (FieldAt C F)).mapDerivedCategory.map
        (SixFunctorDatum.rationalPairingCup (S F 0) X c K.obj L.obj))
  | .closed, K, L => Arrow.mk
      ((pointFibreModuleLift C.Qbar).mapDerivedCategory.map
        (SixFunctorDatum.commonPairingCup (S (Padic.finiteCoefficientBase C.l C.Qbar) 0)
          X c K.obj L.obj))



/-- The coefficient functor preserves precisely the required finite-Tor domains.
Proof: finite coefficients use finiteCompactSupportDomains and the scalar/pullback
cube; integral reduction uses the uniform Tor interval; finite-free integral
extension preserves constructibility and integral finite Tor; rational and common
stages have the full constructible domain. Identities and composites follow.
Source: final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-data). -/
theorem change_domain (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    {a b : Stage C} (f : Passage C a b) (K : (domain C X.obj.left a).FullSubcategory) :
    domain C X.obj.left b ((siteChange C X.obj.left f).obj K.obj) := by
  induction f with
  | @finite F G n m φ =>
      let := Padic.finite_coefficientExtensionRing C.l (FieldAt C F) (n + 1)
        (Nat.succ_pos n)
      let := Padic.finite_coefficientExtensionRing C.l (FieldAt C G) (m + 1)
        (Nat.succ_pos m)
      let A := Padic.coefficientExtensionRing C.l (FieldAt C F) (n + 1)
      let B := Padic.coefficientExtensionRing C.l (FieldAt C G) (m + 1)
      let EA := sfIntrinsicDerivedEquivalence X.obj.left A
      let EB := sfIntrinsicDerivedEquivalence X.obj.left B
      let M := EA.inverse.obj K.obj
      let e := EA.counitIso.app K.obj
      have hM := finite_domain_iso C X.obj.left F n e.symm K.property
      obtain ⟨a, b, ht⟩ := hM.2
      let : LocallyOfFiniteType X.obj.hom := X.property.1
      let : QuasiCompact X.obj.hom := X.property.2
      have h := (closedScalarDomains_scalar D C.l C.different (FieldAt C F)
        (FieldAt C G) n m φ X.obj a b ht.1 M hM ht).1.1
      let eB : EB.functor.obj ((closedScalarExtension φ X.obj.left).obj M) ≅
          (siteChange C X.obj.left (.finite φ)).obj K.obj :=
        ((FiniteCompactScalar.realizationScalarIso φ X.obj.left).app M).symm ≪≫
          (siteChange C X.obj.left (.finite φ)).mapIso e
      exact finite_domain_iso C X.obj.left G m eB h
  | reduction F n =>
      obtain ⟨a, b, hab, ht⟩ := K.property.2
      obtain ⟨_, c, d, hcd, hc⟩ := K.obj.property
      exact ⟨(hc n).1, a, b, ht n⟩
  | integral h => exact integral_domain C X _ _
  | rational h => trivial
  | localization F => trivial
  | closure F => trivial
  | identity a => exact K.property
  | comp f g ihf ihg => exact ihg ⟨_, ihf K⟩

/-- Restriction of the specified scalar functor, with the same object and arrow maps.
Source: final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-data). -/
def change (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    {a b : Stage C} (f : Passage C a b) :
    (domain C X.obj.left a).FullSubcategory ⥤ (domain C X.obj.left b).FullSubcategory :=
  (domain C X.obj.left b).lift ((domain C X.obj.left a).ι ⋙ siteChange C X.obj.left f)
    (change_domain C X f)

/-- The two-argument tensor object used in the target of the actual cup.
Source: final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-data). -/
def tensorObject (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] : (a : Stage C) →
    (domain C X.obj.left a).FullSubcategory →
    (domain C X.obj.left a).FullSubcategory → ambient C X.obj.left a
  | .finite F n, K, L => (((S F n).finiteTensorDomainStage X).obj K).obj L |>.obj
  | .integral F, K, L => (((S F 0).higher.integralTensor X).obj K.obj).obj L.obj
  | .rational F, K, L => (((S F 0).higher.rationalTensor X).obj K.obj).obj L.obj
  | .closed, K, L => (((S (Padic.finiteCoefficientBase C.l C.Qbar) 0).closure.commonStageTensor
      X).obj K.obj).obj L.obj

/-- Tensor closure on the stipulated finite-Tor inputs.
Proof: finite closure is the datum finite tensor domain; integral tensor agrees
with the recorded completed tensor and finite Tor is stable under tensor by adding
the uniform reduction intervals. The two field domains are the full categories.
Source: final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-data). -/
theorem tensor_domain (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (a : Stage C)
    (K L : (domain C X.obj.left a).FullSubcategory) :
    domain C X.obj.left a (tensorObject C S X a K L) := by
  cases a with
  | finite F n => exact ((((S F n).finiteTensorDomainStage X).obj K).obj L).property
  | integral F =>
      exact integral_domain C X F
        ((((S F 0).higher.integralTensor X).obj K.obj).obj L.obj)
  | rational F => trivial
  | closed => trivial

/-- The tensor object in the same full subcategory, with its proven domain membership.
Source: final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-data). -/
def tensorInput (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (a : Stage C)
    (K L : (domain C X.obj.left a).FullSubcategory) :
    (domain C X.obj.left a).FullSubcategory :=
  ⟨tensorObject C S X a K L, tensor_domain C S X a K L⟩

/-- The canonical fully faithful lift tensorator, fixed on pure tensors by the
recorded simultaneous point comparison.
Source: final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-data). -/
def liftTensor (F : Type u) [Field F]
    (K L : DerivedCategory (ModuleCat.{u} F)) :
    (pointFibreModuleLift F).mapDerivedCategory.obj (K ⊗ L) ≅
      (pointFibreModuleLift F).mapDerivedCategory.obj K ⊗
        (pointFibreModuleLift F).mapDerivedCategory.obj L :=
  (@Functor.Monoidal.μIso _ _ _ _ _ _ (pointFibreModuleLift F).mapDerivedCategory
    ((pairingPointIdentifications D C).property.some.lift F).strong K L).symm

/-- The actual cup source in tensor-of-cohomology coordinates.
Source: final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-data). -/
def sourceCoordinates (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left) :
    (a : Stage C) → (K L : (domain C X.obj.left a).FullSubcategory) →
    (cup C S X c a K L).left ≅
      (cohomology C S X c true a).obj K ⊗ (cohomology C S X c false a).obj L
  | .finite _ _, _, _ => Iso.refl _
  | .integral _ , _, _ => Iso.refl _
  | .rational F, K, L => liftTensor C (FieldAt C F)
      ((pointRationalFibre D C.l C.different (FieldAt C F)).obj
        (((S F 0).higher.rational.support (sixFunctorStructure X) c).obj K.obj)).obj
      ((pointRationalFibre D C.l C.different (FieldAt C F)).obj
        (((S F 0).higher.rational.direct (sixFunctorStructure X)).obj L.obj)).obj
  | .closed, K, L => liftTensor C C.Qbar
      ((pointQbarFibre D C.l C.different C.Qbar ⋙
        DerivedCategory.pointFdQbarRealization C.l C.Qbar).obj
        (((S (Padic.finiteCoefficientBase C.l C.Qbar) 0).closure.commonStage.support
          (sixFunctorStructure X) c).obj K.obj))
      ((pointQbarFibre D C.l C.different C.Qbar ⋙
        DerivedCategory.pointFdQbarRealization C.l C.Qbar).obj
        (((S (Padic.finiteCoefficientBase C.l C.Qbar) 0).closure.commonStage.direct
          (sixFunctorStructure X)).obj L.obj))

/-- The target of the recorded cup is compact cohomology of the recorded tensor.
Source: final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-data). -/
def targetCoordinates (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left) :
    (a : Stage C) → (K L : (domain C X.obj.left a).FullSubcategory) →
    (cup C S X c a K L).right ≅
      (cohomology C S X c true a).obj (tensorInput C S X a K L)
  | .finite _ _, _, _ => Iso.refl _
  | .integral _, _, _ => Iso.refl _
  | .rational _, _, _ => Iso.refl _
  | .closed, _, _ => Iso.refl _

/-- The recorded cup, expressed with exactly the source and target of the node.
Source: final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-data). -/
def normalizedCup (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left)
    (a : Stage C) (K L : (domain C X.obj.left a).FullSubcategory) :=
  (sourceCoordinates C S X c a K L).inv ≫ (cup C S X c a K L).hom ≫
    (targetCoordinates C S X c a K L).hom

/-- The actual normalized point tensor comparison, not a supplied tensor map.
Its K-flat normalization is part of ordinaryDerivedChangeOfRings.
Source: the left vertical arrow in the displayed coefficient square
(blueprint: def-sf-mixed-cup-coefficient-data). -/
def pointTensor {a b : Stage C} (f : Passage C a b)
    (K L : DerivedCategory (ModuleCat.{u + 1} (ring C a))) :
    (pointChange C f).obj (K ⊗ L) ≅
      (pointChange C f).obj K ⊗ (pointChange C f).obj L :=
  (@Functor.Monoidal.μIso _ _ _ _ _ _ (pointChange C f)
    (ModuleCat.ordinaryDerivedExtendScalarsMonoidal (coefficientMap C f).hom) K L).symm

/-- The cochain normalization of the scalar identity comparison.
Source: identity coefficient passages, ordinary balancing x tensor 1 maps to x
(blueprint: def-sf-mixed-cup-coefficient-data). -/
def PointUnitNormalized (a : Stage C)
    (e : pointChange C (.identity a) ≅ 𝟭 _) : Prop :=
  ∀ P : CochainComplex (ModuleCat.{u + 1} (ring C a)) ℤ,
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} (ring C a)) (.up ℤ)).kFlat P →
    e.hom.app (DerivedCategory.Q.obj P) =
      (ModuleCat.ordinaryDerivedChangeOfRings (coefficientMap C (.identity a)).hom).counit.app P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex
            (ModuleCat.extendScalarsId.{u + 1, u + 1} (ring C a)) (.up ℤ) ≪≫
            Functor.mapHomologicalComplexIdIso (ModuleCat.{u + 1} (ring C a)) (.up ℤ)).hom.app P)

/-- The cochain normalization of successive scalar extension. Its ordinary map
is the canonical balanced reassociation, determined by 1 tensor x tensor 1.
Source: successive coefficient passages
(blueprint: def-sf-mixed-cup-coefficient-data). -/
def PointCompNormalized {a b d : Stage C} (f : Passage C a b) (g : Passage C b d)
    (e : pointChange C (.comp f g) ≅ pointChange C f ⋙ pointChange C g) : Prop :=
  ∀ P : CochainComplex (ModuleCat.{u + 1} (ring C a)) ℤ,
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} (ring C a)) (.up ℤ)).kFlat P →
    e.hom.app (DerivedCategory.Q.obj P) ≫
      (pointChange C g).map
        ((ModuleCat.ordinaryDerivedChangeOfRings (coefficientMap C f).hom).counit.app P) ≫
      (ModuleCat.ordinaryDerivedChangeOfRings (coefficientMap C g).hom).counit.app
        (((ModuleCat.extendScalars (coefficientMap C f).hom).mapHomologicalComplex
          (.up ℤ)).obj P) =
      (ModuleCat.ordinaryDerivedChangeOfRings
        (coefficientMap C (.comp f g)).hom).counit.app P ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex
          (ModuleCat.extendScalarsComp.{u + 1, u + 1} (coefficientMap C f).hom
          (coefficientMap C g).hom) (.up ℤ)).hom.app P)

/-- Equal coefficient maps give the identical normalized ordinary-module
universal pair, so their point identification is equality transport.
Source: independence of the expression for a successive passage
(blueprint: def-sf-mixed-cup-coefficient-data). -/
def pointCongruence {a b : Stage C} (f g : Passage C a b)
    (h : coefficientMap C f = coefficientMap C g) : pointChange C f ≅ pointChange C g :=
  eqToIso (congrArg (fun φ : ring C a ⟶ ring C b ↦
    ModuleCat.ordinaryDerivedExtendScalars φ.hom) h)

/-- Morphism action of the existing two-variable tensor, restricted to the domain.
Source: tensor morphisms in the coefficient square
(blueprint: def-sf-mixed-cup-coefficient-data). -/
def tensorMap (S : Operations C) (X : SixFunctorSpace D) [IsSeparated X.obj.hom] :
    (a : Stage C) → {K K' L L' : (domain C X.obj.left a).FullSubcategory} →
      (K ⟶ K') → (L ⟶ L') → (tensorInput C S X a K L ⟶ tensorInput C S X a K' L')
  | .finite F n, _, _, _, _, k, l => ObjectProperty.homMk
      ((Functor.uncurry.obj ((S F n).finiteTensorDomainStage X)).map (Prod.mkHom k l)).hom
  | .integral F, _, _, _, _, k, l => ObjectProperty.homMk
      ((Functor.uncurry.obj ((S F 0).higher.integralTensor X)).map
        (Prod.mkHom k.hom l.hom))
  | .rational F, _, _, _, _, k, l => ObjectProperty.homMk
      ((Functor.uncurry.obj ((S F 0).higher.rationalTensor X)).map
        (Prod.mkHom k.hom l.hom))
  | .closed, _, _, _, _, k, l => ObjectProperty.homMk
      ((Functor.uncurry.obj
        ((S (Padic.finiteCoefficientBase C.l C.Qbar) 0).closure.commonStageTensor X)).map
        (Prod.mkHom k.hom l.hom))

/-- The actual site scalar-tensor comparison, expressed on the finite-Tor domains.
This type retains both objects; it is not an extra assumed tensor structure.
Source: the target vertical arrow in the coefficient square
(blueprint: def-sf-mixed-cup-coefficient-data). -/
abbrev TensorComparison (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] {a b : Stage C} (f : Passage C a b) :=
  ∀ K L : (domain C X.obj.left a).FullSubcategory,
    (change C X f).obj (tensorInput C S X a K L) ≅
      tensorInput C S X b ((change C X f).obj K) ((change C X f).obj L)

end WeilConjectures.MixedCupCoefficientChange
