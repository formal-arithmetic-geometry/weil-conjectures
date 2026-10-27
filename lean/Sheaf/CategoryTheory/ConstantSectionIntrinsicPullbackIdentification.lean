module

public import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.Grp.LeftExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Constant-scalar and intrinsic constant-ring module pullback

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3; Sites, Tag 00YV;
Categories, Tag 0B65; Derived Categories, Tag 015F
(blueprint: lem-sfb-constant-section-intrinsic-pullback-identification).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u w₁ w₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory
open ConstantLeftModuleInverseImage

/-- The canonical constant-ring map for sectionwise direct image. It is the unique
extension of the constant-presheaf unit, precomposed with the site functor.
Source: Stacks Project, Tags 03D2, 03D3 and 03CY
(blueprint: lem-sfb-constant-section-intrinsic-pullback-identification). -/
def constantSectionRingMap
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (B : Type u) [CommRing B] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}] (uF : C ⥤ D) [uF.IsContinuous J K] :
    (constantSheaf J RingCat.{u}).obj (RingCat.of B) ⟶
      (uF.sheafPushforwardContinuous RingCat.{u} J K).obj
        ((constantSheaf K RingCat.{u}).obj (RingCat.of B)) :=
  ((sheafificationAdjunction J RingCat.{u}).homEquiv _ _).symm
    { app := fun T ↦
        (toSheafify K ((Functor.const Dᵒᵖ).obj (RingCat.of B))).app (uF.op.obj T)
      naturality := fun _ _ f ↦
        (toSheafify K ((Functor.const Dᵒᵖ).obj (RingCat.of B))).naturality (uF.op.map f) }

namespace ConstantSectionIntrinsicPullback

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (B : Type u) [CommRing B] [HasWeakSheafify J RingCat.{u}]
  [HasWeakSheafify K RingCat.{u}] (uF : C ⥤ D) [uF.IsContinuous J K]

/-- Intrinsic module pullback along the canonical constant-ring map, using Mathlib's
module adjunction. Its tensor-extension description is the ringed-topos module
adjunction of Tags 03D2--03D3; no second module pullback is constructed here.
Source: Stacks Project, Tags 03D2 and 03D3
(blueprint: lem-sfb-constant-section-intrinsic-pullback-identification). -/
abbrev intrinsic := SheafOfModules.pullback.{u} (constantSectionRingMap J K B uF)

/-- Intrinsic direct image: sections at `U` are `N(uF(U))`, with scalars restricted
along the canonical constant-ring map.
Source: Stacks Project, Tags 03D2 and 03D3
(blueprint: lem-sfb-constant-section-intrinsic-pullback-identification). -/
abbrev direct := SheafOfModules.pushforward.{u} (constantSectionRingMap J K B uF)

/-- The intrinsic module adjunction, with its own specified unit.
Source: Stacks Project, Tag 03D3
(blueprint: lem-sfb-constant-section-intrinsic-pullback-identification). -/
abbrev intrinsicAdjunction :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} (constantSectionRingMap J K B uF)

/-- The normalized comparison, including identity on the identified section groups,
both unit equations, inverse identities, exactness, and termwise derived localization.
The derived categories can be formed in independent localization universes.

Source: Stacks Project, Tags 03D2, 03D3, 00YV, 0B65 and 015F
(blueprint: lem-sfb-constant-section-intrinsic-pullback-identification). -/
structure Identification
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (adj : L ⊣ uF.sheafPushforwardContinuous (Type u) J K)
    (hL : PreservesFiniteLimits L)
    (sc : ConstantLeftModuleInverseImageLift J K B L
      (uF.sheafPushforwardContinuous (Type u) J K) adj hL) where
  /-- The right-adjoint comparison. -/
  rho : sc.moduleDirect ≅ direct J K B uF
  /-- Under the given underlying-section identifications this is the identity. -/
  rho_sections : ∀ (N : Modules K B) (T : Cᵒᵖ)
    (x : (sc.moduleDirect.obj N).val.obj T),
    (rho.hom.app N).val.app T x =
      (sc.abelianDirectSetIso.hom.app ((V K B).obj N)).hom.app T
        ((sc.directUnderlyingIso.hom.app N).hom.app T x)
  /-- The transported unit is the scalar unit followed by rho. -/
  transportedAdjunction : sc.moduleFunctor ⊣ direct J K B uF
  transported_unit : ∀ M : Modules J B,
    transportedAdjunction.unit.app M =
      sc.moduleAdj.unit.app M ≫ rho.hom.app (sc.moduleFunctor.obj M)
  /-- The uniquely unit-normalized left-adjoint comparison. -/
  comparison : intrinsic J K B uF ≅ sc.moduleFunctor
  unit_equation : ∀ M : Modules J B,
    (intrinsicAdjunction J K B uF).unit.app M ≫
      (direct J K B uF).map (comparison.hom.app M) =
        sc.moduleAdj.unit.app M ≫ rho.hom.app (sc.moduleFunctor.obj M)
  unique : ∀ a : intrinsic J K B uF ≅ sc.moduleFunctor,
    (∀ M : Modules J B, (intrinsicAdjunction J K B uF).unit.app M ≫
      (direct J K B uF).map (a.hom.app M) =
        sc.moduleAdj.unit.app M ≫ rho.hom.app (sc.moduleFunctor.obj M)) → a = comparison
  inverse_unit : ∀ M : Modules J B,
    (sc.moduleAdj.unit.app M ≫ rho.hom.app (sc.moduleFunctor.obj M)) ≫
      (direct J K B uF).map (comparison.inv.app M) =
        (intrinsicAdjunction J K B uF).unit.app M
  inverse_hom : ∀ M : Modules J B,
    comparison.hom.app M ≫ comparison.inv.app M = 𝟙 ((intrinsic J K B uF).obj M)
  hom_inverse : ∀ M : Modules J B,
    comparison.inv.app M ≫ comparison.hom.app M = 𝟙 (sc.moduleFunctor.obj M)
  intrinsic_additive : (intrinsic J K B uF).Additive
  intrinsic_limits : PreservesFiniteLimits (intrinsic J K B uF)
  intrinsic_colimits : PreservesFiniteColimits (intrinsic J K B uF)
  scalar_additive : sc.moduleFunctor.Additive
  scalar_limits : PreservesFiniteLimits sc.moduleFunctor
  scalar_colimits : PreservesFiniteColimits sc.moduleFunctor
  /-- Applying the same comparison degreewise descends to ordinary derived functors,
  and restricts to bounded below categories, with the two localization squares. -/
  derived : ∀ [HasDerivedCategory.{w₁} (Modules J B)]
    [HasDerivedCategory.{w₂} (Modules K B)]
    [(intrinsic J K B uF).Additive]
    [PreservesFiniteLimits (intrinsic J K B uF)]
    [PreservesFiniteColimits (intrinsic J K B uF)]
    [sc.moduleFunctor.Additive] [PreservesFiniteLimits sc.moduleFunctor]
    [PreservesFiniteColimits sc.moduleFunctor],
    ∃ (aD : (intrinsic J K B uF).mapDerivedCategory ≅ sc.moduleFunctor.mapDerivedCategory)
      (aPlus : (intrinsic J K B uF).mapDerivedCategoryPlus ≅
        sc.moduleFunctor.mapDerivedCategoryPlus),
      (∀ X : CochainComplex (Modules J B) ℤ,
        aD.hom.app (DerivedCategory.Q.obj X) ≫
          sc.moduleFunctor.mapDerivedCategoryFactors.hom.app X =
        (intrinsic J K B uF).mapDerivedCategoryFactors.hom.app X ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex comparison.hom (ComplexShape.up ℤ)).app X)) ∧
      (∀ X : DerivedCategory.Plus (Modules J B),
        DerivedCategory.Plus.ι.map (aPlus.hom.app X) ≫
          sc.moduleFunctor.mapDerivedCategoryPlusCompatibility.hom.app X =
        (intrinsic J K B uF).mapDerivedCategoryPlusCompatibility.hom.app X ≫
          aD.hom.app (DerivedCategory.Plus.ι.obj X)) ∧
      (∀ X : HomotopyCategory.Plus (Modules J B),
        aPlus.hom.app (DerivedCategory.Plus.Qh.obj X) ≫
          sc.moduleFunctor.mapDerivedCategoryPlusFactorsh.hom.app X =
        (intrinsic J K B uF).mapDerivedCategoryPlusFactorsh.hom.app X ≫
          DerivedCategory.Plus.Qh.map
            ((NatTrans.mapHomotopyCategoryPlus comparison.hom).app X))

end ConstantSectionIntrinsicPullback

namespace ConstantSectionIntrinsicPullback

section Helpers
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (B : Type u) [CommRing B] [HasWeakSheafify J RingCat.{u}]
  [HasWeakSheafify K RingCat.{u}]

private def constantHom {M N : Modules J B}
    (f : (V J B).obj M ⟶ (V J B).obj N)
    (hf : ∀ (T : Cᵒᵖ) (r : B) (x : M.val.obj T),
      f.hom.app T ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app T r • x) =
        (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app T r •
        (show N.val.obj T from f.hom.app T x)) :
    M ⟶ N := by
  let α := toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))
  let g : (PresheafOfModules.restrictScalars α).obj M.val ⟶
      (PresheafOfModules.restrictScalars α).obj N.val :=
    PresheafOfModules.homMk f.hom hf
  exact ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective α N.isSheaf).symm g⟩

private def abScalar (M : Modules J B) (r : B) : (V J B).obj M ⟶ (V J B).obj M where
  hom :=
    { app := fun T ↦ AddCommGrpCat.ofHom
        { toFun := fun x ↦
            (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app T r • x
          map_zero' := smul_zero _
          map_add' := smul_add _ }
      naturality := by
        intro T S f
        ext x
        change M.val.obj T at x
        change
          (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app S r •
              M.val.map f x =
            M.val.map f
              ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app T r • x)
        rw [M.val.map_smul]
        congr 1
        exact congrArg (fun k ↦ k r)
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).naturality f) }

private def scalar (M : Modules J B) (r : B) : M ⟶ M :=
  constantHom J B (abScalar J B M r) (by
    intro T s x
    change
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app T r •
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app T s • x) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app T s •
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app T r • x)
    rw [smul_smul, smul_smul, ← map_mul, ← map_mul, mul_comm r s])

private theorem scalar_apply (M : Modules J B) (r : B) (T : Cᵒᵖ) (x : M.val.obj T) :
    (scalar J B M r).val.app T x =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app T r • x := rfl

private theorem scalar_naturality {M N : Modules J B} (f : M ⟶ N) (r : B) :
    scalar J B M r ≫ f = f ≫ scalar J B N r := by
  ext T x
  exact (f.val.app T).hom.map_smul _ x

private def additiveNatTrans
    {A : Type*} [Category.{u} A] [Preadditive A] [HasFiniteBiproducts A]
    (F G : A ⥤ AddCommGrpCat.{u}) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) : F ⟶ G := by
  let H := (AddCommGrpCat.leftExactFunctorForgetEquivalence A).functor
  exact (H.preimage (X := LeftExactFunctor.of F) (Y := LeftExactFunctor.of G)
    (ObjectProperty.homMk α)).hom

private theorem additiveNatTrans_forget
    {A : Type*} [Category.{u} A] [Preadditive A] [HasFiniteBiproducts A]
    (F G : A ⥤ AddCommGrpCat.{u}) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) :
    Functor.whiskerRight (additiveNatTrans F G α) (forget AddCommGrpCat) = α := by
  let H := (AddCommGrpCat.leftExactFunctorForgetEquivalence A).functor
  exact congrArg (fun f ↦ f.hom) (H.map_preimage
    (X := LeftExactFunctor.of F) (Y := LeftExactFunctor.of G) (ObjectProperty.homMk α))

variable (uF : C ⥤ D) [uF.IsContinuous J K]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (adj : L ⊣ uF.sheafPushforwardContinuous (Type u) J K)
    (hL : PreservesFiniteLimits L)
    (sc : ConstantLeftModuleInverseImageLift J K B L
      (uF.sheafPushforwardContinuous (Type u) J K) adj hL)

private theorem inverse_scalar (M : Modules J B) (r : B) :
    sc.moduleFunctor.map (scalar J B M r) = scalar K B (sc.moduleFunctor.obj M) r := by
  apply (V K B).map_injective
  apply (cancel_mono (sc.underlyingIso.hom.app M)).mp
  rw [show (V K B).map (sc.moduleFunctor.map (scalar J B M r)) ≫
      sc.underlyingIso.hom.app M = _ from
    sc.underlyingIso.hom.naturality (scalar J B M r)]
  exact (sc.scalar_compatibility M r (abScalar J B M r)
    (abScalar K B (sc.moduleFunctor.obj M) r) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)).symm

private theorem direct_scalar (N : Modules K B) (r : B) :
    sc.moduleDirect.map (scalar K B N r) = scalar J B (sc.moduleDirect.obj N) r := by
  apply (sc.moduleAdj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [inverse_scalar J K B uF L adj hL sc]
  exact (sc.moduleAdj.counit.naturality (scalar K B N r)).trans
    (scalar_naturality K B (sc.moduleAdj.counit.app N) r).symm

private def sectionComparison :
    sc.moduleDirect ⋙ W J B ≅ direct J K B uF ⋙ W J B :=
  Functor.isoWhiskerRight sc.directUnderlyingIso (U J) ≪≫
    Functor.isoWhiskerLeft (V K B) sc.abelianDirectSetIso

private theorem coefficient_constant (T : Cᵒᵖ) (r : B) :
    (constantSectionRingMap J K B uF).hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app T r) =
        (toSheafify K ((Functor.const Dᵒᵖ).obj (RingCat.of B))).app (uF.op.obj T) r := by
  have h := ((sheafificationAdjunction J RingCat.{u}).homEquiv
    ((Functor.const Cᵒᵖ).obj (RingCat.of B))
    ((uF.sheafPushforwardContinuous RingCat.{u} J K).obj
      ((constantSheaf K RingCat.{u}).obj (RingCat.of B)))).apply_symm_apply
    (show (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ _ from
      { app := fun T ↦
          (toSheafify K ((Functor.const Dᵒᵖ).obj (RingCat.of B))).app (uF.op.obj T)
        naturality := fun _ _ f ↦
          (toSheafify K ((Functor.const Dᵒᵖ).obj (RingCat.of B))).naturality
            (uF.op.map f) })
  exact congrArg (fun f ↦ f.app T r) h

private theorem rightComparison :
    ∃ rho : sc.moduleDirect ≅ direct J K B uF,
      ∀ (N : Modules K B) (T : Cᵒᵖ) (x : (sc.moduleDirect.obj N).val.obj T),
        (rho.hom.app N).val.app T x =
          (sc.abelianDirectSetIso.hom.app ((V K B).obj N)).hom.app T
            ((sc.directUnderlyingIso.hom.app N).hom.app T x) := by
  have : PreservesLimits sc.moduleDirect := sc.moduleAdj.rightAdjoint_preservesLimits
  have : PreservesLimits (direct J K B uF) :=
    (intrinsicAdjunction J K B uF).rightAdjoint_preservesLimits
  let : HasFiniteBiproducts (Modules K B) := .of_hasFiniteProducts
  let e := sectionComparison J K B uF L adj hL sc
  let F (T : Cᵒᵖ) := sc.moduleDirect ⋙
    SheafOfModules.evaluation ((constantSheaf J RingCat.{u}).obj (RingCat.of B)) T ⋙
      forget₂ _ AddCommGrpCat
  let G (T : Cᵒᵖ) := direct J K B uF ⋙
    SheafOfModules.evaluation ((constantSheaf J RingCat.{u}).obj (RingCat.of B)) T ⋙
      forget₂ _ AddCommGrpCat
  let a (T : Cᵒᵖ) : F T ⋙ forget AddCommGrpCat ⟶ G T ⋙ forget AddCommGrpCat :=
    { app := fun N ↦ (e.hom.app N).hom.app T
      naturality := by
        intro N N' f
        exact congrArg (fun g ↦ g.hom.app T) (e.hom.naturality f) }
  let b (T : Cᵒᵖ) := additiveNatTrans (F T) (G T) (a T)
  have hb (T : Cᵒᵖ) (N : Modules K B) :
      (forget AddCommGrpCat).map ((b T).app N) = (e.hom.app N).hom.app T :=
    congr_app (additiveNatTrans_forget (F T) (G T) (a T)) N
  let f (N : Modules K B) : (V J B).obj (sc.moduleDirect.obj N) ⟶
      (V J B).obj ((direct J K B uF).obj N) :=
    { hom :=
      { app := fun T ↦ (b T).app N
        naturality := by
          intro T S g
          apply (forget AddCommGrpCat).map_injective
          rw [Functor.map_comp, Functor.map_comp, hb, hb]
          exact (e.hom.app N).hom.naturality g } }
  have hf (N : Modules K B) (T : Cᵒᵖ) (r : B)
      (x : (sc.moduleDirect.obj N).val.obj T) :
      (f N).hom.app T
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app T r • x) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app T r •
        (show ((direct J K B uF).obj N).val.obj T from (f N).hom.app T x) := by
    have h := congrArg (fun g ↦ g.hom.app T x) (e.hom.naturality (scalar K B N r))
    change (forget AddCommGrpCat).map ((b T).app N) _ = _
    rw [hb]
    change (e.hom.app N).hom.app T
        ((sc.moduleDirect.map (scalar K B N r)).val.app T x) =
      ((direct J K B uF).map (scalar K B N r)).val.app T
        ((e.hom.app N).hom.app T x) at h
    rw [direct_scalar J K B uF L adj hL sc] at h
    change (e.hom.app N).hom.app T
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app T r • x) =
      (toSheafify K ((Functor.const Dᵒᵖ).obj (RingCat.of B))).app (uF.op.obj T) r •
        (show N.val.obj (uF.op.obj T) from (e.hom.app N).hom.app T x) at h
    change _ = (constantSectionRingMap J K B uF).hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app T r) •
        (show N.val.obj (uF.op.obj T) from
          (forget AddCommGrpCat).map ((b T).app N) x)
    rw [hb, coefficient_constant]
    exact h
  let t : sc.moduleDirect ⟶ direct J K B uF :=
    { app := fun N ↦ constantHom J B (f N) (hf N)
      naturality := by
        intro N N' g
        ext T x
        exact congrArg (fun k ↦ k.hom x) ((b T).naturality g) }
  have ht (N : Modules K B) (T : Cᵒᵖ) (x : (sc.moduleDirect.obj N).val.obj T) :
      (t.app N).val.app T x = (e.hom.app N).hom.app T x :=
    congrArg (fun k ↦ k x) (hb T N)
  have (N : Modules K B) : IsIso (t.app N) := by
    have (T : Cᵒᵖ) : IsIso ((t.app N).val.app T) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      have h : Function.Bijective ((e.hom.app N).hom.app T) :=
        (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
      exact (show ((t.app N).val.app T : _ → _) = (e.hom.app N).hom.app T from
        funext (ht N T)).symm ▸ h
    let i := PresheafOfModules.isoMk
      (fun T ↦ asIso ((t.app N).val.app T))
      (fun {_ _} g ↦ (t.app N).val.naturality g)
    have : IsIso (t.app N).val := by
      change IsIso i.hom
      infer_instance
    have : IsIso ((SheafOfModules.forget _).map (t.app N)) :=
      inferInstanceAs (IsIso (t.app N).val)
    exact isIso_of_reflects_iso (t.app N) (SheafOfModules.forget _)
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact ⟨asIso t, ht⟩

end Helpers
end ConstantSectionIntrinsicPullback

/-- The scalar-endomorphism and intrinsic constant-ring constructions have the same
normalized adjunction, exactness and ordinary derived functors.

Source: Stacks Project, Tags 03D2, 03D3, 03D7, 00YV, 03CY, 0B65 and 015F
(blueprint: lem-sfb-constant-section-intrinsic-pullback-identification).

Proof:
1. Restrict along the constant-ring sheafification unit. Its local surjectivity
   makes restriction fully faithful, so multiplication by a constant scalar is a
   module endomorphism (commutativity is used only for two constant scalars).
2. The lift's scalar compatibility identifies the inverse image of that endomorphism.
   Taking mates under the module adjunction identifies its direct image as well.
3. Compose the two given underlying-set comparisons. Both direct images preserve
   finite limits. On each section, fullness of the forgetful equivalence for left
   exact functors from an additive category proves that this comparison is additive.
   Naturality for scalar endomorphisms proves constant-scalar linearity; fullness of
   restriction extends it to every section of the constant ring. The coefficient
   equation follows directly from the sheafification adjunction. The resulting
   module maps are sectionwise bijective and therefore form a natural isomorphism.
4. Transport the scalar adjunction along this right comparison. Uniqueness of left
   adjoints gives the comparison and its unit equation. Injectivity of the Hom
   bijection gives uniqueness; functoriality gives the inverse unit equation.
5. Transport additivity and finite limit and colimit preservation through the iso.
6. Apply the existing exact-functor natural-isomorphism constructions on the derived
   category and its bounded-below restriction. Their normalization lemmas give the
   complex localization, inclusion, and bounded homotopy localization squares. -/
theorem constant_section_intrinsic_pullback_identification
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (B : Type u) [CommRing B] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}] (uF : C ⥤ D) [uF.IsContinuous J K]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (adj : L ⊣ uF.sheafPushforwardContinuous (Type u) J K)
    (hL : PreservesFiniteLimits L)
    (sc : ConstantLeftModuleInverseImageLift J K B L
      (uF.sheafPushforwardContinuous (Type u) J K) adj hL) :
    Nonempty (ConstantSectionIntrinsicPullback.Identification.{u, w₁, w₂}
      J K B uF L adj hL sc) := by
  classical
  open ConstantSectionIntrinsicPullback in
    obtain ⟨rho, hrho⟩ := rightComparison J K B uF L adj hL sc
  let tadj := sc.moduleAdj.ofNatIsoRight rho
  let iadj := ConstantSectionIntrinsicPullback.intrinsicAdjunction J K B uF
  let a := iadj.leftAdjointUniq tadj
  have ht (M : Modules J B) : tadj.unit.app M =
      sc.moduleAdj.unit.app M ≫ rho.hom.app (sc.moduleFunctor.obj M) := rfl
  have hu (M : Modules J B) : iadj.unit.app M ≫
      (ConstantSectionIntrinsicPullback.direct J K B uF).map (a.hom.app M) =
        sc.moduleAdj.unit.app M ≫ rho.hom.app (sc.moduleFunctor.obj M) :=
    (iadj.unit_leftAdjointUniq_hom_app tadj M).trans (ht M)
  let := sc.additive
  let := sc.preservesFiniteLimits
  let := sc.preservesFiniteColimits
  let : (ConstantSectionIntrinsicPullback.intrinsic J K B uF).Additive :=
    Functor.additive_of_iso a.symm
  let : PreservesFiniteLimits (ConstantSectionIntrinsicPullback.intrinsic J K B uF) :=
    preservesFiniteLimits_of_natIso a.symm
  let : PreservesFiniteColimits (ConstantSectionIntrinsicPullback.intrinsic J K B uF) :=
    preservesFiniteColimits_of_natIso a.symm
  refine ⟨{
    rho := rho
    rho_sections := hrho
    transportedAdjunction := tadj
    transported_unit := ht
    comparison := a
    unit_equation := hu
    unique := ?_
    inverse_unit := ?_
    inverse_hom := fun M ↦ a.hom_inv_id_app M
    hom_inverse := fun M ↦ a.inv_hom_id_app M
    intrinsic_additive := inferInstance
    intrinsic_limits := inferInstance
    intrinsic_colimits := inferInstance
    scalar_additive := sc.additive
    scalar_limits := sc.preservesFiniteLimits
    scalar_colimits := sc.preservesFiniteColimits
    derived := ?_ }⟩
  · intro b hb
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (iadj.homEquiv _ _).injective
    exact (hb M).trans (hu M).symm
  · intro M
    rw [← hu M, Category.assoc, ← Functor.map_comp, a.hom_inv_id_app, Functor.map_id]
    exact Category.comp_id _
  · intro _ _ _ _ _ _ _ _
    refine ⟨Functor.mapDerivedCategoryNatIso a, Functor.mapDerivedCategoryPlusNatIso a,
      Functor.mapDerivedCategoryNatIso_fac a, ?_,
      Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh a⟩
    intro X
    simp only [Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom, NatTrans.id_app,
      Category.id_comp]
    exact Category.comp_id _

end CategoryTheory
