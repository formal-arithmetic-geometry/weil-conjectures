/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Central scalar linearity of the unbounded ringed-topos direct image

Source: Stacks Project, Derived Categories, Tags 070K and 070Y; Modules on Sites,
Tag 03D6; Differential Graded Algebra, Tags 09MJ and 09MK
(blueprint: lem-pur-ringed-derived-pushforward-linear).

Global sections are compatible families, using Mathlib's `RingCat.sectionsSubring`.
Scalar compatibility is tested on generalized elements, as in `RingedToposMorphism`;
no functor between the presenting sites or exactness of module direct image is imposed.
The existential linear structures are characterized on every section of every Hom.
The derived functor is the existing universal K-injective construction, whose unit and
resolution comparisons are those of `rightDerivedFunctorOfQuasiIsoResolutions`.
-/

@[expose] public section

set_option autoImplicit false

universe u v wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private def centralSectionEnd
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A : Sheaf J RingCat.{u}) (R : Type v) [CommRing R]
    (s : R →+* RingCat.sectionsSubring A.obj)
    (central : ∀ (r : R) (U : Cᵒᵖ) (a : A.obj.obj U),
      (s r).val U * a = a * (s r).val U)
    (M : ringedSiteModules.{u} A) (r : R) : M ⟶ M where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := fun x ↦ (s r).val U • x
          map_add' := smul_add _
          map_smul' := fun a x ↦ by
            change (s r).val U • (a • x) = a • ((s r).val U • x)
            rw [← mul_smul, central, mul_smul] }
      naturality := fun {U V} f ↦ by
        ext x
        exact ((M.val.map_smul f ((s r).val U) x).trans
          (congrArg (· • M.val.map f x) ((s r).property f))).symm }

private def centralSectionEndHom
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A : Sheaf J RingCat.{u}) (R : Type v) [CommRing R]
    (s : R →+* RingCat.sectionsSubring A.obj)
    (central : ∀ (r : R) (U : Cᵒᵖ) (a : A.obj.obj U),
      (s r).val U * a = a * (s r).val U)
    (M : ringedSiteModules.{u} A) : R →+* End M where
  toFun := centralSectionEnd A R s central M
  map_one' := by
    apply SheafOfModules.hom_ext
    ext U x
    change (s 1).val U • x = x
    simp
  map_zero' := by
    apply SheafOfModules.hom_ext
    ext U x
    change (s 0).val U • x = 0
    simp
  map_mul' r t := by
    apply SheafOfModules.hom_ext
    ext U x
    change (s (r * t)).val U • x = (s r).val U • ((s t).val U • x)
    simp [mul_smul]
  map_add' r t := by
    apply SheafOfModules.hom_ext
    ext U x
    change (s (r + t)).val U • x = (s r).val U • x + (s t).val U • x
    simp [add_smul]

private lemma centralSectionEnd_naturality
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A : Sheaf J RingCat.{u}) (R : Type v) [CommRing R]
    (s : R →+* RingCat.sectionsSubring A.obj)
    (central : ∀ (r : R) (U : Cᵒᵖ) (a : A.obj.obj U),
      (s r).val U * a = a * (s r).val U)
    {M N : ringedSiteModules.{u} A} (f : M ⟶ N) (r : R) :
    f ≫ centralSectionEnd A R s central N r =
      centralSectionEnd A R s central M r ≫ f := by
  ext U x
  exact ((f.val.app U).hom.map_smul ((s r).val U) x).symm

@[instance_reducible]
private def centralSectionLinear
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A : Sheaf J RingCat.{u}) (R : Type v) [CommRing R]
    (s : R →+* RingCat.sectionsSubring A.obj)
    (central : ∀ (r : R) (U : Cᵒᵖ) (a : A.obj.obj U),
      (s r).val U * a = a * (s r).val U) :
    Linear R (ringedSiteModules.{u} A) where
  homModule M N := Module.compHom (M ⟶ N) (centralSectionEndHom A R s central N)
  smul_comp M N P r f g := by
    change (f ≫ centralSectionEnd A R s central N r) ≫ g =
      (f ≫ g) ≫ centralSectionEnd A R s central P r
    rw [Category.assoc, ← centralSectionEnd_naturality, Category.assoc]
  comp_smul M N P f r g := (Category.assoc _ _ _).symm

private def sectionAsGeneralizedElement
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A : Sheaf J RingCat.{u}) (s : RingCat.sectionsSubring A.obj)
    (T : Sheaf J (Type u)) : T ⟶ (sheafCompose J (forget RingCat)).obj A :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ s.val U)
     naturality := fun {U V} f ↦ by
       ext t
       exact (s.property f).symm }⟩

private lemma derivedLinearOfEnough
    {E H : Type*} [Category E] [Category H] [Abelian E] [Abelian H]
    [HasDerivedCategory E] [HasDerivedCategory H]
    (R : Type v) [CommRing R] [Linear R E] [Linear R H]
    (F : E ⥤ H) [F.Additive] [F.Linear R]
    (enough : ∀ N : CochainComplex E ℤ,
      ∃ (I : CochainComplex E ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a) :
    (F.rightDerivedFunctorOfQuasiIsoResolutions enough).Additive ∧
      (F.rightDerivedFunctorOfQuasiIsoResolutions enough).Linear R := by
  classical
  -- The localization restricted to K-injectives is full and essentially surjective.
  let π := HomotopyCategory.quotient E (.up ℤ)
  let ι := inducedFunctor (fun I : {I : CochainComplex E ℤ // I.IsKInjective} ↦ π.obj I.val)
  let L := ι ⋙ (DerivedCategory.Qh : _ ⥤ DerivedCategory E)
  have : L.Full :=
    { map_surjective := fun {I J} f ↦ by
        have : J.val.IsKInjective := J.property
        obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
          (π.obj I.val) J.val).surjective f
        exact ⟨InducedCategory.homMk g, hg⟩ }
  have : L.EssSurj := by
    constructor
    intro X
    obtain ⟨I, a, hI, ha⟩ := enough (DerivedCategory.Q.objPreimage X)
    have := ha
    exact ⟨⟨I, hI⟩, ⟨(DerivedCategory.quotientCompQhIso E).symm.app I ≪≫
      (asIso (DerivedCategory.Q.map a)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso X⟩⟩
  -- On this category the canonical unit transports both additive and linear structures.
  let η := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit enough
  have : IsIso (Functor.whiskerLeft ι η) := by
    have : ∀ I, IsIso ((Functor.whiskerLeft ι η).app I) := fun I ↦ by
      have : I.val.IsKInjective := I.property
      exact F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso enough I.val
    exact NatIso.isIso_of_isIso_app _
  let e := asIso (Functor.whiskerLeft ι η)
  have : (L ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions enough).Additive :=
    Functor.additive_of_iso e
  have : (L ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions enough).Linear R :=
    Functor.linear_of_iso R e
  exact ⟨Functor.additive_of_full_essSurj_comp L _,
    Functor.linear_of_full_essSurj_comp L _⟩

/-- Compatible locally central sections give the prescribed scalar structures, and the
canonical unbounded right derived module direct image is additive and linear for their
induced derived structures. In particular its value on scalar multiplication is scalar
multiplication by the actual target section, as stated by the final identity.

Source: Stacks Tags 070K and 070Y, with the module action of Tag 03D6 and the definitions
of Tags 09MJ and 09MK (blueprint: lem-pur-ringed-derived-pushforward-linear).

Proof plan:
1. On each module Hom set set (r f)_U(x) = s(r)_U f_U(x). Local centrality makes this
   sectionwise module-linear; compatibility of the global section with restrictions makes
   it natural. The ring-map and module axioms give the module and bilinear-composition
   axioms, hence the two claimed `Linear` structures.
2. Transpose generalized elements using the adjunction of `u`. Its `module_linear`
   identity and scalar compatibility identify s_A(r)x with s_B(r) times the transpose.
   Naturality then gives u_*(r f) = r u_*(f). Additivity is part of the module direct image.
3. `lem-weil-pbc-ring-sheaves-grothendieck` and
   `lem-pur-kinjective-degreewise-existence` supply the K-injective resolution hypothesis.
   Additivity preserves homotopies, shifts and cone triangles, so
   `lem-weil-pbc-kinjective-total-derived` supplies the existing universal derived pair.
4. For resolutions a:N→I and b:N'→J use
   `lem-sf-kinjective-derived-map-computation`: a derived morphism h is represented by
   the unique homotopy class g with Qg = Qb h (Qa)⁻¹, and its derived image, conjugated
   by the specified comparison isomorphisms c_a,c_b, is Q(u_*g).
5. The linearity of Q from `lem-weil-linear-abelian-derived-category` shows that rg
   represents rh and g+t represents h+k. Step 2 gives Q(u_*(rg)) = r Q(u_*g), and
   additivity gives Q(u_*(g+t)) = Q(u_*g)+Q(u_*t). Cancel the fixed comparison
   isomorphisms, using bilinearity, to get both equalities on all derived morphisms.
   Transport along presentation isomorphisms covers every derived object.
6. For h = id the scalar map is multiplication by the actual section s_B(r) on a
   representative. Linearity and preservation of identity identify its image with
   multiplication by s_A(r) on the direct-image representative. -/
theorem ringedDerivedPushforward_linear
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J RingCat.{u}) (B : Sheaf K RingCat.{u})
    [HasDerivedCategory.{wA} (ringedSiteModules.{u} A)]
    [HasDerivedCategory.{wB} (ringedSiteModules.{u} B)]
    (u : RingedToposMorphism B A) (R : Type v) [CommRing R]
    (sA : R →+* RingCat.sectionsSubring A.obj)
    (sB : R →+* RingCat.sectionsSubring B.obj)
    (centralA : ∀ (r : R) (U : Cᵒᵖ) (a : A.obj.obj U),
      (sA r).val U * a = a * (sA r).val U)
    (centralB : ∀ (r : R) (V : Dᵒᵖ) (b : B.obj.obj V),
      (sB r).val V * b = b * (sB r).val V)
    (compatible : ∀ (r : R) (T : Sheaf J (Type u))
      (z : T ⟶ (sheafCompose J (forget RingCat)).obj A),
      (∀ (U : Cᵒᵖ) (t : T.obj.obj U), z.hom.app U t = (sA r).val U) →
      ∀ (V : Dᵒᵖ) (t : (u.inverse.obj T).obj.obj V),
        ((u.inverse.map z) ≫ u.ringMap).hom.app V t = (sB r).val V) :
    ∃ (LA : Linear R (ringedSiteModules.{u} A))
      (LB : Linear R (ringedSiteModules.{u} B))
      (enough : ∀ N : CochainComplex (ringedSiteModules.{u} B) ℤ,
        ∃ (I : CochainComplex (ringedSiteModules.{u} B) ℤ) (a : N ⟶ I),
          I.IsKInjective ∧ QuasiIso a),
      (fun [_iA : Linear R (ringedSiteModules.{u} A)]
        [_iB : Linear R (ringedSiteModules.{u} B)] ↦
        (∀ (M N : ringedSiteModules.{u} A) (f : M ⟶ N) (r : R)
          (U : Cᵒᵖ) (x : M.val.obj U),
          (r • f).val.app U x = (sA r).val U • f.val.app U x) ∧
        (∀ (M N : ringedSiteModules.{u} B) (f : M ⟶ N) (r : R)
          (V : Dᵒᵖ) (x : M.val.obj V),
          (r • f).val.app V x = (sB r).val V • f.val.app V x) ∧
        (u.modules.rightDerivedFunctorOfQuasiIsoResolutions enough).Additive ∧
        Functor.Linear R (u.modules.rightDerivedFunctorOfQuasiIsoResolutions enough) ∧
        (∀ (N : DerivedCategory (ringedSiteModules.{u} B)) (r : R),
          (u.modules.rightDerivedFunctorOfQuasiIsoResolutions enough).map (r • 𝟙 N) =
            r • 𝟙 ((u.modules.rightDerivedFunctorOfQuasiIsoResolutions enough).obj N)))
        (_iA := LA) (_iB := LB) := by
  classical
  let LA := centralSectionLinear A R sA centralA
  let LB := centralSectionLinear B R sB centralB
  let := LA
  let := LB
  have hA (M N : ringedSiteModules.{u} A) (f : M ⟶ N) (r : R)
      (U : Cᵒᵖ) (x : M.val.obj U) :
      (r • f).val.app U x = (sA r).val U • f.val.app U x := rfl
  have hB (M N : ringedSiteModules.{u} B) (f : M ⟶ N) (r : R)
      (V : Dᵒᵖ) (x : M.val.obj V) :
      (r • f).val.app V x = (sB r).val V • f.val.app V x := rfl
  have : IsGrothendieckAbelian.{u} (ringedSiteModules.{u} B) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses K B
  have enough (N : CochainComplex (ringedSiteModules.{u} B) ℤ) :
      ∃ (I : CochainComplex (ringedSiteModules.{u} B) ℤ) (a : N ⟶ I),
        I.IsKInjective ∧ QuasiIso a := by
    obtain ⟨I, hI, a, _, ha⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective N
    exact ⟨I, a, hI, ha⟩
  have : u.modules.Linear R := by
    rw [Functor.linear_iff]
    intro M r
    let UA : ringedSiteModules.{u} A ⥤ Sheaf J (Type u) :=
      SheafOfModules.toSheaf A ⋙ sheafCompose J (forget AddCommGrpCat)
    let UB : ringedSiteModules.{u} B ⥤ Sheaf K (Type u) :=
      SheafOfModules.toSheaf B ⋙ sheafCompose K (forget AddCommGrpCat)
    let T := UA.obj (u.modules.obj M)
    let z₀ : T ⟶ T :=
      ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (0 : (u.modules.obj M).val.obj U))
         naturality := fun {U V} f ↦ by
           ext t
           exact ((u.modules.obj M).val.map f).hom.map_zero.symm }⟩
    -- The combined action/addition axiom also determines the transpose of zero.
    have hz₀ (V : Dᵒᵖ) (t : (u.inverse.obj T).obj.obj V) :
        @Eq (M.val.obj V)
          (((u.adj.homEquiv T _).symm (z₀ ≫ u.underlying.hom.app M)).hom.app V t) 0 := by
      have h := u.module_linear M T
        (sectionAsGeneralizedElement A (sA 1) T) z₀ z₀ z₀ (by
          intro U x
          change 0 = (sA 1).val U • (0 : (u.modules.obj M).val.obj U) + 0
          simp) V t
      have hOne := u.ring_one T (sectionAsGeneralizedElement A (sA 1) T)
        (fun U x ↦ by change (sA 1).val U = 1; simp) V t
      rw [hOne] at h
      let q : M.val.obj V :=
        ((u.adj.homEquiv T _).symm (z₀ ≫ u.underlying.hom.app M)).hom.app V t
      change q = (1 : B.obj.obj V) • q + q at h
      rw [one_smul] at h
      exact add_eq_left.mp h.symm
    -- Compare scalar identity maps by transposing the universal generalized element.
    have hscalar := u.module_linear M T
      (sectionAsGeneralizedElement A (sA r) T) (𝟙 T) z₀
      (UA.map (r • 𝟙 (u.modules.obj M))) (by
        intro U x
        change (r • 𝟙 (u.modules.obj M)).val.app U x =
          (sA r).val U • (show (u.modules.obj M).val.obj U from x) + 0
        rw [hA]
        exact (add_zero _).symm)
    apply UA.map_injective
    apply (cancel_mono (u.underlying.hom.app M)).mp
    apply (u.adj.homEquiv T _).symm.injective
    have hn : UA.map (u.modules.map (r • 𝟙 M)) ≫ u.underlying.hom.app M =
        u.underlying.hom.app M ≫ u.direct.map (UB.map (r • 𝟙 M)) :=
      u.underlying.hom.naturality (r • 𝟙 M)
    rw [hn, u.adj.homEquiv_naturality_right_symm]
    ext V t
    have hcomp := compatible r T (sectionAsGeneralizedElement A (sA r) T)
      (fun _ _ ↦ rfl) V t
    have hh := hscalar V t
    rw [hcomp, hz₀] at hh
    let q : M.val.obj V :=
      ((u.adj.homEquiv T _).symm (𝟙 T ≫ u.underlying.hom.app M)).hom.app V t
    let z : M.val.obj V := ((u.adj.homEquiv T _).symm
      (UA.map (r • 𝟙 (u.modules.obj M)) ≫ u.underlying.hom.app M)).hom.app V t
    change z = (sB r).val V • q + 0 at hh
    rw [add_zero] at hh
    change (r • 𝟙 M).val.app V
      (((u.adj.homEquiv T _).symm (u.underlying.hom.app M)).hom.app V t) = _
    rw [hB]
    simpa only [q, z, Category.id_comp, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply, TypeCat.Fun.toFun_apply] using hh.symm
  obtain ⟨hadd, hlin⟩ := derivedLinearOfEnough R u.modules enough
  refine ⟨LA, LB, enough, hA, hB, hadd, hlin, ?_⟩
  let := hlin
  intro N r
  simp

end CategoryTheory
