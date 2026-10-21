/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.Paper.LocalizingClosure
public import Sheaf.Paper.FiniteDiscreteCondensedRing
public import Sheaf.Paper.FiniteDiscreteSchemeRing
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.AlgebraicGeometry.UnboundedSiteComparison
import Sheaf.Paper.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Sheaf.Paper.FiniteComparisonFaithful
import Sheaf.Paper.ConstantInternalModuleSheafEquivalence
import all Sheaf.Paper.InternalModuleAbEquivalence

/-!
# Finite coefficient comparison on localizing closures

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ctf-finite-comparison/
sk-prop-ctf-finite-comparison-localizing.md
(blueprint: det-ctf-finite-comparison-localizing).

## Main definitions

* `finiteComparisonRealization`: the specified finite-discrete coefficient transport.
* `finiteComparisonEtaleClosure`, `finiteComparisonProEtaleClosure`: the two closures.
* `finiteComparisonOpenIso`, `finiteComparisonCompactSupportMap`: the canonical arrows.

## Main statements

* `finiteComparisonRealization_exact`: exactness of the specified coefficient transport.
* `finiteComparisonLocalizing`: the equivalence and its compatibility with operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct ZeroObject

section LocalizingArgument
universe w v₁ v₂
namespace CategoryTheory

variable {C : Type w} {D : Type w} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

private theorem closureLocalizing (S : ObjectProperty C) :
    IsLocalizingSubcategory (localizingClosure S) := by
  have hiso : (localizingClosure S).IsClosedUnderIsomorphisms := by
    constructor
    intro K L e hK P hP hS
    let := hP.2.1
    exact P.prop_of_iso e (hK P hP hS)
  let := hiso
  have hzero : (localizingClosure S).ContainsZero := by
    refine ⟨0, isZero_zero _, ?_⟩
    intro P hP hS
    let := hP.1
    let := hP.2.1
    exact P.prop_zero
  let := hzero
  have hshift : (localizingClosure S).IsStableUnderShift ℤ := by
    constructor
    intro n
    constructor
    intro K hK
    rw [ObjectProperty.prop_shift_iff]
    intro P hP hS
    let := hP.1
    exact P.le_shift n K (hK P hP hS)
  let := hshift
  have htri : (localizingClosure S).IsTriangulated := by
    refine { ext₂' := ?_ }
    intro T hT h₁ h₃
    apply ObjectProperty.le_isoClosure
    intro P hP hS
    let := hP.1
    let := hP.2.1
    exact P.ext_of_isTriangulatedClosed₂ T hT (h₁ P hP hS) (h₃ P hP hS)
  refine ⟨htri, hiso, ?_⟩
  intro I F hF hK
  change ∀ P, IsLocalizingSubcategory P → (∀ K, S K → P K) → _
  intro P hP hS
  exact hP.2.2 F hF (fun i ↦ hK i P hP hS)

private theorem inverseImageLocalizing (P : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [∀ I : Type w, PreservesColimitsOfShape (Discrete I) F]
    (hP : IsLocalizingSubcategory P) :
    IsLocalizingSubcategory (P.inverseImage F) := by
  let := hP.1
  let := hP.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I G hG hPG
  let := hG
  let : HasColimit (G ⋙ F) := ⟨_, isColimitOfPreserves F (colimit.isColimit G)⟩
  exact P.prop_of_iso (preservesColimitIso F G).symm
    (hP.2.2 (G ⋙ F) inferInstance hPG)

private theorem imageLocalizing (P : ObjectProperty C) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [Coreflective F] (hP : IsLocalizingSubcategory P) :
    IsLocalizingSubcategory (P.map F) := by
  let := hP.1
  let := hP.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I H hH hPH
  let := hH
  have hHF (j : Discrete I) : F.essImage (H.obj j) := by
    obtain ⟨K, _, e⟩ := hPH j.as
    exact ⟨K, e⟩
  let G := Functor.essImage.liftFunctor H F hHF
  let e := Functor.essImage.liftFunctorCompIso H F hHF
  let : HasColimit (G ⋙ F) := hasColimit_of_iso e
  let : HasColimit G := hasColimit_of_coreflective G F
  have hPG (i : I) : P (G.obj (Discrete.mk i)) := by
    obtain ⟨K, hK, ⟨iK⟩⟩ := hPH i
    exact P.prop_of_iso (F.preimageIso (iK ≪≫ (e.app (Discrete.mk i)).symm)) hK
  refine ⟨colimit G, hP.2.2 G inferInstance hPG, ⟨?_⟩⟩
  exact (preservesColimitIso F G) ≪≫ HasColimit.isoOfNatIso e


private theorem closureEquivalence (S : ObjectProperty C) (T : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [Coreflective F]
    (hS : ∀ K, S K → localizingClosure T (F.obj K))
    (hT : ∀ K, T K → (localizingClosure S).map F K) :
    ∃ hpres : ∀ K, localizingClosure S K → localizingClosure T (F.obj K),
      ((localizingClosure T).lift ((localizingClosure S).ι ⋙ F)
        (fun K ↦ hpres K.obj K.property)).IsEquivalence := by
  have hpres (K : C) (hK : localizingClosure S K) :
      localizingClosure T (F.obj K) := by
    exact hK ((localizingClosure T).inverseImage F)
      (inverseImageLocalizing _ _ (closureLocalizing T)) hS
  refine ⟨hpres, ?_⟩
  let H := (localizingClosure T).lift ((localizingClosure S).ι ⋙ F)
    (fun K ↦ hpres K.obj K.property)
  have himage (K : D) (hK : localizingClosure T K) :
      (localizingClosure S).map F K :=
    hK _ (imageLocalizing _ F (closureLocalizing S)) hT
  have : H.EssSurj := by
    constructor
    intro K
    obtain ⟨L, hL, ⟨e⟩⟩ := himage K.obj K.property
    exact ⟨⟨L, hL⟩, ⟨ObjectProperty.isoMk _ e⟩⟩
  exact { }

end CategoryTheory
end LocalizingArgument

namespace AlgebraicGeometry.ProEtale


/-- View fixed-scalar module presheaves as internal modules before sheafification.
Source: blueprint finite comparison, coefficient identification in proof step 1
(blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonPresheaf (X : Scheme.{u}) (B : Type) [CommRing B] :
    (X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} B)) ⥤
      Mod (X.ProEtᵒᵖ ⥤ Ab.{u + 1})
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) where
  obj F := by
    let act :
        (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B)) ⊗
            (F ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) ⟶
          (F ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) :=
      { app U := InternalAbelianSheafModule.ordinaryAction
          (S := ULift.{u + 1} B) (N := F.obj U)
        naturality U V f := by
          apply AddCommGrpCat.hom_ext_toIntLinearMap
          apply TensorProduct.ext'
          intro r m
          exact ((F.map f).hom.map_smul r m).symm }
    letI : ModObj
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B)))
        (F ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) :=
      ModObj.mk' _ act (by
        apply NatTrans.ext
        funext U
        apply AddCommGrpCat.hom_ext_toIntLinearMap
        apply TensorProduct.ext'
        intro z m
        exact Int.cast_smul_eq_zsmul (M := F.obj U) (ULift.{u + 1} B) z.down m) (by
        apply NatTrans.ext
        funext U
        apply AddCommGrpCat.hom_ext_toIntLinearMap
        apply TensorProduct.ext_threefold
        intro r s m
        exact mul_smul (α := ULift.{u + 1} B) (β := F.obj U) r s m)
    exact ⟨F ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}⟩
  map f := Mod.homMk (Functor.whiskerRight f (forget₂ _ Ab.{u + 1})) (by
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro r m
    exact (f.app U).hom.map_smul r m)
  map_id F := by apply Mod.hom_ext; rfl
  map_comp f g := by apply Mod.hom_ext; rfl


/-- Sheafify the ordinary fixed-scalar action as an internal constant-ring action.
Source: blueprint finite comparison, proof step 1
(blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonConstantRealization (X : Scheme.{u}) (B : Type) [CommRing B] :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B)))) :=
  sheafToPresheaf _ _ ⋙ finiteComparisonPresheaf X B ⋙
    (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapMod _

private noncomputable def finiteComparisonPresheafEncodingIso
    (X : Scheme.{u}) (B : Type) [CommRing B] :
    finiteComparisonPresheaf X B ⋙
        ConstantInternalModuleSheafEncoding.modulePresheafEncoding
          (C := X.ProEt) (ULift.{u + 1} B) (internalToModule (ULift.{u + 1} B)) ≅
      𝟭 (X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} B)) := by
  refine NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun U ↦ ?_) ?_) ?_
  · exact ModuleCat.isoMk (Iso.refl _) (fun r ↦ by ext m; rfl)
  · intro U V f
    ext m
    rfl
  · intro F G f
    ext U m
    rfl

private theorem finiteComparisonConstantRealization_isEquivalence
    (X : Scheme.{u}) (B : Type) [CommRing B] :
    (finiteComparisonConstantRealization X B).IsEquivalence := by
  let J := Scheme.ProEt.topology X
  let R := ULift.{u + 1} B
  let A := ConstantInternalModuleSheafEncoding.A (C := X.ProEtᵒᵖ) R
  let G := internalToModule R
  let : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
  let H := ConstantInternalModuleSheafEncoding.sheafEncoding J R G rfl
  let L := finiteComparisonConstantRealization X B
  let E := sheafToPresheaf J (ModuleCat.{u + 1} R) ⋙ finiteComparisonPresheaf X B
  let P := ConstantInternalModuleSheafEncoding.modulePresheafEncoding (C := X.ProEt) R G
  let adj := (sheafificationAdjunction J Ab.{u + 1}).mapModAdjunction A
  have hu (M : Sheaf J (ModuleCat.{u + 1} R)) : IsIso (adj.unit.app (E.obj M)) := by
    rw [← isIso_iff_of_reflects_iso _ (Mod.forget A)]
    change IsIso ((adj.unit.app (E.obj M)).hom)
    rw [Adjunction.mapModAdjunction_unit_app_hom]
    exact isIso_toSheafify J
      ((sheafCompose J (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1})).obj M).property
  let η := Functor.whiskerRight (Functor.whiskerLeft E adj.unit) P
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    exact Functor.map_isIso P (adj.unit.app (E.obj M))
  let e0 : E ⋙ P ≅ sheafToPresheaf J (ModuleCat.{u + 1} R) :=
    Functor.isoWhiskerLeft _ (finiteComparisonPresheafEncodingIso X B)
  let e : (L ⋙ H) ⋙ sheafToPresheaf J (ModuleCat.{u + 1} R) ≅
      (𝟭 _) ⋙ sheafToPresheaf J (ModuleCat.{u + 1} R) :=
    (asIso η).symm ≪≫ e0
  let i := ((fullyFaithfulSheafToPresheaf J (ModuleCat.{u + 1} R)).whiskeringRight _)
    |>.preimageIso e
  have : (L ⋙ H).IsEquivalence := Functor.isEquivalence_of_iso i.symm
  exact Functor.isEquivalence_of_comp_right L H


variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DiscreteTopology B] [Finite B]

/-- Transport the sheafified scalar action along the specified coefficient ring isomorphism.
The isomorphism is exactly the pullback of the finite-discrete point identification.
Source: blueprint finite comparison, proof step 1
(blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonRealization (X : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom] :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X) :=
  finiteComparisonConstantRealization X B ⋙
    Mod.comap (finiteDiscreteSchemeRingIso B X eR).inv

/-- The specified coefficient transport is an exact equivalence.
Source: blueprint finite comparison, coefficient paragraph and proof step 1
(blueprint: det-ctf-finite-comparison-localizing).

Proof: an internal presheaf action is precisely the sectionwise scalar action.
Monoidal sheafification extends it uniquely to the associated constant ring sheaf.
Restriction along constant sections is inverse: local scalar representatives and
sheaf uniqueness recover both the action and every linear map. The unit and counit
are the sheafification identifications on underlying abelian sheaves. Transport along
`finiteDiscreteSchemeRingIso` has inverse transport along its inverse ring map.
The two composite functors are inverse and retain the underlying additive sheaves,
so preserve finite limits, finite colimits, and addition. This includes the zero ring
and empty scheme. -/
theorem finiteComparisonRealization_exact (X : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom] :
    (finiteComparisonRealization B X eR).IsEquivalence ∧
    (finiteComparisonRealization B X eR).Additive ∧
    PreservesFiniteLimits (finiteComparisonRealization B X eR) ∧
    PreservesFiniteColimits (finiteComparisonRealization B X eR) := by
  let _ : DiscreteTopology B := inferInstance
  let _ : Finite B := inferInstance
  have : (finiteComparisonConstantRealization X B).IsEquivalence :=
    finiteComparisonConstantRealization_isEquivalence X B
  have : (Mod.comap (finiteDiscreteSchemeRingIso B X eR).inv).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (finiteDiscreteSchemeRingIso B X eR).inv)
      |>.isEquivalence_functor
  have : (finiteComparisonRealization B X eR).IsEquivalence := by
    unfold finiteComparisonRealization
    infer_instance
  have : (finiteComparisonRealization B X eR).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

variable (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
  ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
    Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]

/-- Additivity of the specified coefficient transport, from the coefficient paragraph.
Source: blueprint finite comparison (blueprint: det-ctf-finite-comparison-localizing). -/
instance finiteComparisonRealization_additive (X : Scheme.{u}) :
    (finiteComparisonRealization B X eR).Additive :=
  (finiteComparisonRealization_exact B X eR).2.1

/-- Left exactness of the coefficient transport, from the coefficient paragraph.
Source: blueprint finite comparison (blueprint: det-ctf-finite-comparison-localizing). -/
instance finiteComparisonRealization_limits (X : Scheme.{u}) :
    PreservesFiniteLimits (finiteComparisonRealization B X eR) :=
  (finiteComparisonRealization_exact B X eR).2.2.1

/-- Right exactness of the coefficient transport, from the coefficient paragraph.
Source: blueprint finite comparison (blueprint: det-ctf-finite-comparison-localizing). -/
instance finiteComparisonRealization_colimits (X : Scheme.{u}) :
    PreservesFiniteColimits (finiteComparisonRealization B X eR) :=
  (finiteComparisonRealization_exact B X eR).2.2.2

/-- The etale generators: the recorded bounded constructible property and finite Tor
amplitude tested against every module sheaf in degree zero.
Source: blueprint finite comparison, statement
(blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonEtaleGenerators (X : Scheme.{u}) :
    ObjectProperty (Etale.DerivedCategoryModule (ULift.{u + 1} B) X) :=
  Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} B) X ⊓
    _root_.DerivedCategory.finiteTorAmplitude _

/-- The pro-etale generators transported from the recorded constant-model definition.
Source: blueprint finite comparison, coefficient paragraph and definition of Dctf
(blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonProEtaleGenerators (X : Scheme.{u}) :
    ObjectProperty (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)))) :=
  fun K ↦ (constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} B) X ⊓
    _root_.DerivedCategory.finiteTorAmplitude _)
      ((finiteComparisonRealization B X eR).mapDerivedCategory.obj K)

/-- The etale localizing closure uses the recorded intersection convention.
Source: blueprint finite comparison (blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonEtaleClosure (X : Scheme.{u}) :=
  CategoryTheory.localizingClosure (finiteComparisonEtaleGenerators B X)

/-- The ordinary pro-etale localizing closure, with the transported Dctf generators.
Source: blueprint finite comparison (blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonProEtaleClosure (X : Scheme.{u}) :=
  CategoryTheory.localizingClosure (finiteComparisonProEtaleGenerators B eR X)

/-- The canonical open-extension comparison, applied termwise and localized.
Source: blueprint finite comparison, Operations; Stacks Tag 09AF
(blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonOpenIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} B)) j).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) U).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} B)) j).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- For the chosen open/proper factorization, the compact-support comparison is exactly
alpha at j_! K followed by Rp_* of the open comparison. All values are ambient.
Source: blueprint finite comparison, final paragraph of proof
(blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonCompactSupportMap {X P Y : Scheme.{u}} (j : X ⟶ P) (p : P ⟶ Y)
    [IsOpenImmersion j]
    (K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X) :=
  unboundedDirectImageComparisonMap (ULift.{u + 1} B) p
      ((Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) j).mapDerivedCategory.obj K) ≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) p).rightDerivedFunctor.map
      ((finiteComparisonOpenIso B j).hom.app K)

/-- The finite-Tor constructible generators correspond under the comparison functor.
Source: blueprint finite comparison, opening paragraph
(blueprint: lem-ctf-finite-comparison-generators).

Proof: apply the finite Noetherian coefficient comparison to the coefficient-sized small
site models, then transport its restricted equivalence through the constant-scalar
presentations, site equivalences, and the specified finite discrete scheme-ring
isomorphism. These transports preserve constructibility, finite Tor amplitude, and the
ambient derived comparison, yielding both generator inclusions. The empty scheme and
zero ring are included by the same equivalence argument. -/
theorem finiteComparisonGenerators_identification (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    (∀ K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X,
      finiteComparisonEtaleGenerators B X K →
        finiteComparisonProEtaleGenerators B eR X
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
            X).mapDerivedCategory.obj K)) ∧
    (∀ K : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B))),
      finiteComparisonProEtaleGenerators B eR X K →
        (finiteComparisonEtaleGenerators B X).map
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
            X).mapDerivedCategory K) := by
  sorry

/-- Comparison identifies the two localizing closures, exactly and with ambient sums,
and the canonical pullback, direct-image, open-extension and compact-support comparisons
are invertible on the indicated inputs. No stability assertion for direct images occurs.

Source: blueprint main-20261015, sk-prop-ctf-finite-comparison-localizing.md and its proof
(blueprint: det-ctf-finite-comparison-localizing).

Proof, following the node's five steps:
1. The finite-discrete condensed-ring and scheme-ring identifications transport module
   actions exactly, preserving sums, tensor and the finite constant models. The unbounded
   site comparison is exact, fully faithful and sum-preserving
   (lem-sfb-unbounded-site-comparison). The finite Noetherian coefficient comparison
   det-pe-finite-tor-comparison-noetherian identifies the Dctf generators.
2. The inverse image of the pro-etale closure is replete, triangulated and sum-closed.
   It contains the etale generators, so the defining intersection of
   sk-def-localizing-closure gives preservation of the etale closure.
3. The replete essential image of that closure is sum-closed and shift-closed.
   Fullness lifts any arrow between image objects, and exactness sends its cone to
   a cone of the given arrow. Thus the essential image is triangulated, including zero
   from the empty sum. It contains all pro-etale generators by step 1. Minimality gives
   the reverse inclusion. Full faithfulness restricts, giving the equivalence; triangles
   and sums are the ambient ones.
4. The pullback square is sk-thm-pe-direct-image-comparison. For open extension use
   lem-cbc-proetale-extension-zero-comparison and the two extension-exactness nodes:
   applying the sheaf isomorphism degreewise gives a natural complex isomorphism and
   exactness descends it through quasi-isomorphisms. For finite-type direct image use
   lem-sfb-unbounded-direct-image-comparison. Restrict these ambient maps to closure inputs.
5. For a chosen compactification compose alpha on j_! K with Rp_* of the open
   comparison. Both factors are isomorphisms in the ambient category, naturally in K.
   Their composite is exactly the stipulated comparison for Rf_! = Rp_* j_!; no closure
   stability of direct image is used. -/
theorem finiteComparisonLocalizing
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]
    [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p)
    (hB : ∃ n : ℕ, (ℓ : B) ^ n = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] :
    ∃ hpres : ∀ K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X,
        finiteComparisonEtaleClosure B X K →
          finiteComparisonProEtaleClosure B eR X
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
              X).mapDerivedCategory.obj K),
      ((finiteComparisonProEtaleClosure B eR X).lift
        ((finiteComparisonEtaleClosure B X).ι ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).mapDerivedCategory)
        (fun K ↦ hpres K.obj K.property)).IsEquivalence ∧
      (∀ T : Triangle (Etale.DerivedCategoryModule (ULift.{u + 1} B) X),
        finiteComparisonEtaleClosure B X T.obj₁ →
        finiteComparisonEtaleClosure B X T.obj₂ →
        finiteComparisonEtaleClosure B X T.obj₃ →
        T ∈ distTriang _ →
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
          X).mapDerivedCategory.mapTriangle.obj T) ∈ distTriang _) ∧
      (∀ (I : Type (u + 2)) (K : I → Etale.DerivedCategoryModule (ULift.{u + 1} B) X),
        (∀ i : I, finiteComparisonEtaleClosure B X (K i)) →
        ∀ c : Cofan K, IsColimit c → finiteComparisonEtaleClosure B X c.pt ∧
          Nonempty (IsColimit
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
              X).mapDerivedCategory.mapCocone c))) ∧
      (∀ (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
        [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
        (g : X ⟶ Y) [g.IsOver (Spec (.of k))] [LocallyOfFiniteType g] [QuasiCompact g],
        (∀ K : Etale.DerivedCategoryModule (ULift.{u + 1} B) Y,
          finiteComparisonEtaleClosure B Y K →
          IsIso ((unboundedDirectImagePullbackIso (ULift.{u + 1} B) g).hom.app K)) ∧
        (∀ K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X,
          finiteComparisonEtaleClosure B X K →
          IsIso (unboundedDirectImageComparisonMap (ULift.{u + 1} B) g K))) ∧
      (∀ (U : Scheme.{u}) [U.Over (Spec (.of k))]
        [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
        (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j]
        (K : Etale.DerivedCategoryModule (ULift.{u + 1} B) U),
        finiteComparisonEtaleClosure B U K → IsIso ((finiteComparisonOpenIso B j).hom.app K)) ∧
      (∀ (P Y : Scheme.{u}) [P.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
        [LocallyOfFiniteType (P ↘ Spec (.of k))] [QuasiCompact (P ↘ Spec (.of k))]
        [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
        (j : X ⟶ P) (r : P ⟶ Y) [j.IsOver (Spec (.of k))] [r.IsOver (Spec (.of k))]
        [IsOpenImmersion j] [IsProper r]
        (K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X),
        finiteComparisonEtaleClosure B X K →
          IsIso (finiteComparisonCompactSupportMap B j r K)) := by
  let A : Type (u + 1) := ULift.{u + 1} B
  have hA : ∃ n : ℕ, (ℓ : A) ^ n = 0 := by
    obtain ⟨n, hn⟩ := hB
    exact ⟨n, ULift.ext _ _ hn⟩
  let : CharP k p :=
    charP_of_injective_algebraMap (RingHom.injective (algebraMap (ZMod p) k)) p
  have hunit : IsUnit (algebraMap ℤ k (ℓ : ℤ)) := by
    rw [map_natCast, isUnit_iff_ne_zero]
    change (ℓ : k) ≠ 0
    intro hzero
    exact hℓ ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp
      ((CharP.cast_eq_zero_iff k p ℓ).mp hzero)).symm
  let : IsAlgClosed k := IsAlgClosure.isAlgClosed (ZMod p)
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let F := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  obtain ⟨hFF⟩ := finiteComparisonOrdinary_fullyFaithful A k
    (Or.inr inferInstance) hunit hA X
  let : F.Full := hFF.full
  let : F.Faithful := hFF.faithful
  let adj := (comparisonAdjunction (ModuleCat.{u + 1} A) X)
    |>.mapDerivedCategoryRightDerivedAdjunction
  let : Coreflective F := { R := _, adj := adj }
  obtain ⟨hgen, hgen'⟩ := finiteComparisonGenerators_identification B eR X
  obtain ⟨hpres, hequiv⟩ := closureEquivalence
    (finiteComparisonEtaleGenerators B X) (finiteComparisonProEtaleGenerators B eR X) F
    (fun K hK P _ hP ↦ hP _ (hgen K hK))
    (fun K hK ↦ by
      obtain ⟨L, hL, e⟩ := hgen' K hK
      exact ⟨L, fun P _ hP ↦ hP _ hL, e⟩)
  refine ⟨hpres, hequiv, ?_, ?_, ?_, ?_, ?_⟩
  · intro T _ _ _ hT
    exact F.map_distinguished T hT
  · intro I K hK c hc
    let S := finiteComparisonEtaleClosure B X
    have hloc : IsLocalizingSubcategory S := closureLocalizing _
    let := hloc.2.1
    let : HasColimit (Discrete.functor K) := ⟨c, hc⟩
    refine ⟨S.prop_of_iso
      ((colimit.isColimit _).coconePointUniqueUpToIso hc)
      (hloc.2.2 (Discrete.functor K) inferInstance hK), ?_⟩
    exact ⟨isColimitOfPreserves F hc⟩
  · intro Y _ _ _ g _ _ _
    constructor
    · intro K _
      infer_instance
    · intro K _
      exact unboundedDirectImageComparison k (Or.inr inferInstance) hunit A hA g K
  · intro U _ _ _ j _ _ K _
    infer_instance
  · intro P Y _ _ _ _ _ _ j r _ _ _ _ K _
    unfold finiteComparisonCompactSupportMap
    have := unboundedDirectImageComparison k (Or.inr inferInstance) hunit A hA r
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K)
    infer_instance

end AlgebraicGeometry.ProEtale
