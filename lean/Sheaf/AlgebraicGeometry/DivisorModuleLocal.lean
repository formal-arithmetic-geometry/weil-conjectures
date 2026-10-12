/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.DivisorModule
public import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf

/-!
# Local generators of the divisor module on a smooth connected curve

Source: Stacks Project, Divisors, Tags 0BE9 and 0AGA; Algebra, Tag 031T;
blueprint lem-sc-divisor-class-curve (blueprint: lem-sc-divisor-module-local).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

private theorem ord_zpow_local (C : Scheme.{u}) [IsIntegral C] [IsNoetherian C]
    (g : C.functionField) (hg : g ≠ 0) (n : ℤ) (Q : closedPoints C) :
    C.ord (g ^ n) Q.val = n * C.ord g Q.val := by
  have h := congrArg (fun E : C.Divisor ↦ E Q)
    (map_zsmul (C.div) n (Additive.ofMul (Units.mk0 g hg)))
  simpa only [div_apply, toMul_zsmul, Units.val_zpow_eq_zpow_val,
    Finsupp.smul_apply, Pi.smul_apply, zsmul_eq_mul, toMul_ofMul, Units.val_mk0,
    Int.cast_id] using h

/-- The local divisor-section image inside the function-field-valued functions.
Source: Stacks Project, Divisors, 0AGA and proof of 0BE9; Algebra, 031T.
(blueprint: lem-sc-divisor-module-local)

Proof: A uniformizer t is nonzero, so its image and every integer power of its image are
nonzero. Remove the other points in the finite support of D and in the divisor of t. On the
remaining neighbourhood U of P, ord_Q(t) is one at P and zero at every other closed point,
and D(Q) is zero away from P. For a locally constant function s on a nonempty V contained in
U, integrality makes s constant. The order inequalities defining O(D)(V) say exactly that
all orders of t^(D(P)) s are nonnegative. At the generic point the order is zero, and every
other point of this smooth curve is closed. The regular-section gluing theorem therefore
produces a section a with rational value t^(D(P)) s. Thus s = t^(-D(P)) a. Conversely a regular
section has nonnegative orders, so multiplication by t^(-D(P)) satisfies exactly the required
bounds. Zero satisfies both descriptions separately. This proves equality of the specified
subsets; finite support is used only to construct U. -/
private theorem Divisor.local_section_image (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] (D : C.Divisor) :
    letI : IsNoetherian C := isNoetherian_of_locallyOfFiniteType f
    letI : IsRegular C := IsRegular.of_smooth f
    letI : IsIntegral C := (C.smooth_connected_curve_local_rings k f).choose
    ∀ (P : closedPoints C) (t : C.presheaf.stalk P.val),
      IsLocalRing.maximalIdeal (C.presheaf.stalk P.val) = Ideal.span {t} →
      let c := (algebraMap (C.presheaf.stalk P.val) C.functionField t) ^ (-D P)
      c ≠ 0 ∧ ∃ U : C.Opens, P.val ∈ U ∧
        ∀ (V : C.Opens), V ≤ U → Nonempty V →
          (D.sectionModule C V : Set (V → C.functionField)) =
            Set.range (fun a : Γ(C, V) ↦
              fun x : V ↦ c * divisorScalarMap C V a x) := by
  classical
  let : IsNoetherian C := isNoetherian_of_locallyOfFiniteType f
  let : IsRegular C := IsRegular.of_smooth f
  let : IsIntegral C := (C.smooth_connected_curve_local_rings k f).choose
  let : SmoothOfRelativeDimension 1 f :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := f))
  dsimp only
  intro P t ht
  have hP1 := coheight_eq_one_of_isClosed f P.property
  have := isDiscreteValuationRing_stalk_of_coheight_eq_one f hP1
  have hirr := (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr ht
  let b := algebraMap (C.presheaf.stalk P.val) C.functionField t
  have hb : b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    hirr.ne_zero
  have hbord : C.ord b P.val = 1 := by
    have : Ring.KrullDimLE 1 (C.presheaf.stalk P.val) := krullDimLE_of_coheight_le hP1.le
    rw [ord_eq_iff hP1 hb]
    exact Ring.ordFrac_irreducible hirr
  let E := C.div (Additive.ofMul (Units.mk0 b hb))
  let S := (D.support ∪ E.support).erase P
  let U : C.Opens := ⟨(⋃ Q ∈ S, ({Q.val} : Set C))ᶜ,
    (isClosed_biUnion_finset (fun Q _ ↦ Q.property)).isOpen_compl⟩
  have hPU : P.val ∈ U := by
    change P.val ∉ ⋃ Q ∈ S, ({Q.val} : Set C)
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, not_exists]
    intro Q hQ heq
    have heq' : Q = P := Subtype.ext heq.symm
    subst Q
    exact (Finset.mem_erase.mp hQ).1 rfl
  have haway (Q : closedPoints C) (hQ : Q.val ∈ U) (hne : Q ≠ P) :
      D Q = 0 ∧ C.ord b Q.val = 0 := by
    have hnot : Q ∉ S := by
      intro hs
      exact hQ (Set.mem_iUnion.mpr ⟨Q, Set.mem_iUnion.mpr ⟨hs, rfl⟩⟩)
    have hn : Q ∉ D.support ∪ E.support := by
      intro h
      exact hnot (Finset.mem_erase.mpr ⟨hne, h⟩)
    have hd : D Q = 0 := Finsupp.notMem_support_iff.mp
      (fun h ↦ hn (Finset.mem_union_left _ h))
    have he : E Q = 0 := Finsupp.notMem_support_iff.mp
      (fun h ↦ hn (Finset.mem_union_right _ h))
    exact ⟨hd, he⟩
  let c := b ^ (-D P)
  have hc : c ≠ 0 := zpow_ne_zero _ hb
  have hcord (Q : closedPoints C) (hQ : Q.val ∈ U) : C.ord c Q.val = -D Q := by
    rw [ord_zpow_local C b hb]
    by_cases heq : Q = P
    · subst Q
      rw [hbord, mul_one]
    · rw [(haway Q hQ heq).1, (haway Q hQ heq).2, mul_zero, neg_zero]
  refine ⟨hc, U, hPU, ?_⟩
  intro V hVU hV
  have := hV
  have hpre : PreirreducibleSpace V := V.isOpenEmbedding.preirreducibleSpace
  have hconn : PreconnectedSpace V := PreirreducibleSpace.preconnectedSpace V
  ext s
  constructor
  · intro hs
    change D.sectionCondition C V s at hs
    obtain ⟨x⟩ := hV
    have hconst : ∀ y : V, s y = s x := fun y ↦
      @IsLocallyConstant.apply_eq_of_preconnectedSpace V C.functionField _ hconn s hs.1 y x
    by_cases hz : s x = 0
    · refine ⟨0, ?_⟩
      funext y
      simp only [map_zero, Pi.zero_apply, mul_zero, hconst y, hz]
    have hnonneg : ∀ y ∈ V, 0 ≤ C.ord (c⁻¹ * s x) y := by
      intro y hy
      by_cases hclosed : IsClosed ({y} : Set C)
      · let Q : closedPoints C := ⟨y, hclosed⟩
        have hbound : 0 ≤ C.ord (s x) y + D Q := by
          rcases hs.2 ⟨y, hy⟩ hclosed with hz' | hh
          · exact (hz ((hconst ⟨y, hy⟩).symm.trans hz')).elim
          · simpa only [hconst ⟨y, hy⟩] using hh
        have hi : C.ord c⁻¹ y = D Q := by
          have hm := ord_mul (X := C) (x := y) hc (inv_ne_zero hc)
          rw [mul_inv_cancel₀ hc, ord_one, hcord Q (hVU hy)] at hm
          omega
        rw [ord_mul (inv_ne_zero hc) hz, hi]
        omega
      · rw [ord_eq_zero_of_coheight_neq_one (fun h ↦ hclosed
          (isClosed_of_coheight_eq_one f h))]
    obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_ord_nonneg f hnonneg
    refine ⟨a, ?_⟩
    funext y
    change c * algebraMap (C.presheaf.stalk y.val) C.functionField
      (C.presheaf.germ V y.val y.property a) = s y
    rw [algebraMap_germ_eq_germToFunctionField, ha, ← mul_assoc, mul_inv_cancel₀ hc,
      one_mul, hconst y]
  · rintro ⟨a, rfl⟩
    change D.sectionCondition C V (fun x ↦ c * divisorScalarMap C V a x)
    refine ⟨IsLocallyConstant.of_constant _ ?_, ?_⟩
    · intro x y
      change c * algebraMap (C.presheaf.stalk x.val) C.functionField
          (C.presheaf.germ V x.val x.property a) =
        c * algebraMap (C.presheaf.stalk y.val) C.functionField
          (C.presheaf.germ V y.val y.property a)
      simp only [algebraMap_germ_eq_germToFunctionField]
    · intro x hx
      by_cases ha : divisorScalarMap C V a x = 0
      · left
        exact mul_eq_zero_of_right c ha
      · right
        change 0 ≤ C.ord (c * divisorScalarMap C V a x) x.val + D ⟨x.val, hx⟩
        rw [ord_mul hc ha, hcord ⟨x.val, hx⟩ (hVU x.property)]
        have hh := ord_germToFunctionField_nonneg a x.property
        change 0 ≤ -D ⟨x.val, hx⟩ + C.ord
          (algebraMap (C.presheaf.stalk x.val) C.functionField
            (C.presheaf.germ V x.val x.property a)) x.val + D ⟨x.val, hx⟩
        rw [algebraMap_germ_eq_germToFunctionField]
        omega

private theorem divisor_over_iso
    (C : Scheme.{u}) [IsIntegral C] [IsNoetherian C] [IsRegular C]
    (D : C.Divisor) (U : C.Opens) (c : C.functionField)
    (hlocal : ∀ (V : C.Opens), V ≤ U → Nonempty V →
      ∃ e : Γ(C, V) ≃ₗ[Γ(C, V)] D.sectionModule C V,
        ∀ (a : Γ(C, V)) (x : V), (e a).val x = c *
          algebraMap (C.presheaf.stalk x.val) C.functionField
            (C.presheaf.germ V x.val x.property a)) :
    Nonempty ((D.associatedModule C).over U ≅
      SheafOfModules.unit (C.ringCatSheaf.over U)) := by
  classical
  have hex (V : C.Opens) (hV : V ≤ U) :
      ∃ e : Γ(C, V) ≃ₗ[Γ(C, V)] D.sectionModule C V,
        ∀ (a : Γ(C, V)) (x : V), (e a).val x = c *
          algebraMap (C.presheaf.stalk x.val) C.functionField
            (C.presheaf.germ V x.val x.property a) := by
    by_cases hne : Nonempty V
    · exact hlocal V hV hne
    · have : Subsingleton Γ(C, V) := CommRingCat.subsingleton_of_isTerminal
        (C.sheaf.isTerminalOfEqEmpty (by
          ext z
          exact iff_false_intro (fun hz ↦ hne ⟨⟨z, hz⟩⟩)))
      have : Subsingleton (D.sectionModule C V) := ⟨fun a b ↦
        Subtype.ext (funext fun x ↦ (hne ⟨x⟩).elim)⟩
      exact ⟨LinearEquiv.ofSubsingleton _ _, fun _ x ↦ (hne ⟨x⟩).elim⟩
  choose e he using hex
  let ep : (SheafOfModules.unit (C.ringCatSheaf.over U)).val ≅
      ((D.associatedModule C).over U).val :=
    PresheafOfModules.isoMk
      (fun V ↦ (e V.unop.left (leOfHom V.unop.hom)).toModuleIso)
      (by
        intro V W i
        ext
        apply Subtype.ext
        funext x
        change ((e W.unop.left (leOfHom W.unop.hom))
            (C.presheaf.map i.unop.left.op 1)).val x =
          ((e V.unop.left (leOfHom V.unop.hom)) 1).val
            ⟨x.val, leOfHom i.unop.left x.property⟩
        rw [he, he, TopCat.Presheaf.germ_res_apply])
  exact ⟨(SheafOfModules.forget (C.ringCatSheaf.over U)).preimageIso ep.symm⟩

/-- Compatible local generators give invertibility.
Source: Stacks Project, Divisors, proof of 0BE9 and 0AGA.
(blueprint: lem-sc-divisor-module-local)

Proof: Choose a uniformizer at each closed point (its stalk is a DVR). The section
isomorphisms in the hypothesis commute with restriction: their values are multiplication by
one fixed rational scalar, and germs of restricted structure sections have the same rational
value. On the empty open there is the unique map. They therefore define a sheaf isomorphism
between the structure module and the divisor module on each chosen neighbourhood. The closed
points and the generic point are all points of the curve; the generic point belongs to every
nonempty open, and a closed point exists. Consequently these neighbourhoods cover, proving
invertibility. -/
private theorem Divisor.module_invertible_of_local_generators (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] (D : C.Divisor) :
    letI : IsNoetherian C := isNoetherian_of_locallyOfFiniteType f
    letI : IsRegular C := IsRegular.of_smooth f
    letI : IsIntegral C := (C.smooth_connected_curve_local_rings k f).choose
    let M := D.moduleOfSmoothConnectedCurve k C f
    (∀ (P : closedPoints C) (t : C.presheaf.stalk P.val),
      IsLocalRing.maximalIdeal (C.presheaf.stalk P.val) = Ideal.span {t} →
      let c := (algebraMap (C.presheaf.stalk P.val) C.functionField t) ^ (-D P)
      c ≠ 0 ∧ (∃ U : C.Opens, P.val ∈ U ∧
        ∀ (V : C.Opens), V ≤ U → Nonempty V →
          ∃ e : Γ(C, V) ≃ₗ[Γ(C, V)] D.sectionModule C V,
            ∀ (a : Γ(C, V)) (x : V),
              (e a).val x = c *
                algebraMap (C.presheaf.stalk x.val) C.functionField
                  (C.presheaf.germ V x.val x.property a))) →
    M.IsInvertible := by
  classical
  let : IsNoetherian C := isNoetherian_of_locallyOfFiniteType f
  let : IsRegular C := IsRegular.of_smooth f
  let : IsIntegral C := (C.smooth_connected_curve_local_rings k f).choose
  dsimp only
  intro hlocal
  have hcurve := (C.smooth_connected_curve_local_rings k f).choose_spec
  rcases hcurve with ⟨_, hgeneric, _, _, _, hnongeneric, _, ⟨P₀, hP₀⟩, hdvr⟩
  have hclosed (P : closedPoints C) : ∃ U : C.Opens, P.val ∈ U ∧
      Nonempty ((Modules.pullback U.ι).obj (D.moduleOfSmoothConnectedCurve k C f) ≅
        SheafOfModules.unit _) := by
    have := (hdvr P.val P.property).1
    obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (C.presheaf.stalk P.val)
    have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht
    obtain ⟨hc, U, hPU, hU⟩ := hlocal P t hmax
    obtain ⟨e⟩ := divisor_over_iso C D U _ hU
    refine ⟨U, hPU, ⟨?_⟩⟩
    exact (Modules.restrictFunctorIsoPullback U.ι).symm.app _ ≪≫
      (Modules.overFunctorEquiv U).symm.app _ ≪≫
      (Modules.overEquiv U).functor.mapIso e ≪≫
      (Modules.overEquivFunctorObjUnitIso U).symm
  constructor
  intro x
  by_cases hx : x ∈ closedPoints C
  · exact hclosed ⟨x, hx⟩
  · have hη : x = genericPoint C := by
      by_contra hne
      exact hx (hnongeneric x hne)
    obtain ⟨U, hPU, he⟩ := hclosed ⟨P₀, hP₀⟩
    refine ⟨U, ?_, he⟩
    rw [hη]
    apply (hgeneric.mem_open_set_iff U.isOpen).mpr
    simpa only [Set.univ_inter] using (show (U : Set C).Nonempty from ⟨P₀, hPU⟩)


private theorem divisor_equiv_of_section_image
    (C : Scheme.{u}) [IsIntegral C] [IsNoetherian C] [IsRegular C]
    (D : C.Divisor) (V : C.Opens) [Nonempty V] (c : C.functionField) (hc : c ≠ 0)
    (himage : (D.sectionModule C V : Set (V → C.functionField)) =
      Set.range (fun a : Γ(C, V) ↦ fun x : V ↦ c * divisorScalarMap C V a x)) :
    ∃ e : Γ(C, V) ≃ₗ[Γ(C, V)] D.sectionModule C V,
      ∀ (a : Γ(C, V)) (x : V),
        (e a).val x = c * algebraMap (C.presheaf.stalk x.val) C.functionField
          (C.presheaf.germ V x.val x.property a) := by
  let : Module Γ(C, V) (V → C.functionField) :=
    @Algebra.toModule _ _ _ _ (divisorFunctionAlgebra C V)
  let φ : Γ(C, V) →ₗ[Γ(C, V)] (V → C.functionField) :=
    { toFun := fun a x ↦ c * divisorScalarMap C V a x
      map_add' := by
        intro a b
        funext x
        simp only [map_add, Pi.add_apply, mul_add]
      map_smul' := by
        intro a b
        funext x
        change c * divisorScalarMap C V (a * b) x =
          divisorScalarMap C V a x * (c * divisorScalarMap C V b x)
        simp only [map_mul, Pi.mul_apply]
        ring }
  let ψ := φ.codRestrict (D.sectionModule C V) (fun a ↦ by
    change φ a ∈ (D.sectionModule C V : Set (V → C.functionField))
    rw [himage]
    exact ⟨a, rfl⟩)
  have hinj : Function.Injective ψ := by
    intro a b hab
    obtain ⟨x⟩ := ‹Nonempty V›
    have hx := congrArg (fun s : D.sectionModule C V ↦ s.val x) hab
    change c * divisorScalarMap C V a x = c * divisorScalarMap C V b x at hx
    have heq := mul_left_cancel₀ hc hx
    apply C.germToFunctionField_injective V
    change algebraMap (C.presheaf.stalk x.val) C.functionField
        (C.presheaf.germ V x.val x.property a) =
      algebraMap (C.presheaf.stalk x.val) C.functionField
        (C.presheaf.germ V x.val x.property b) at heq
    simpa only [algebraMap_germ_eq_germToFunctionField] using heq
  have hsurj : Function.Surjective ψ := by
    intro s
    have hs : s.val ∈ Set.range
        (fun a : Γ(C, V) ↦ fun x : V ↦ c * divisorScalarMap C V a x) := by
      rw [← himage]
      exact s.property
    obtain ⟨a, ha⟩ := hs
    exact ⟨a, Subtype.ext ha⟩
  exact ⟨LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩, fun _ _ ↦ rfl⟩

private theorem divisor_stalk_embedding
    (C : Scheme.{u}) [IsIntegral C] [IsNoetherian C] [IsRegular C]
    (D : C.Divisor) (P : C) :
    ∃ j : (D.associatedModule C).presheaf.stalk P →ₗ[C.presheaf.stalk P] C.functionField,
      Function.Injective j ∧ ∀ (V : C.Opens) (hP : P ∈ V) (s : D.sectionModule C V),
        j ((D.associatedModule C).presheaf.germ V P hP s) = s.val ⟨P, hP⟩ := by
  let M := D.associatedModule C
  let ℓ : M.presheaf.stalk P →+ C.functionField :=
    ConcreteCategory.hom (CategoryTheory.Limits.colimit.desc _
      { pt := AddCommGrpCat.of C.functionField
        ι :=
          { app U := AddCommGrpCat.ofHom
              { toFun s := (show D.sectionModule C U.unop.1 from s).val ⟨P, U.unop.2⟩
                map_zero' := rfl
                map_add' _ _ := rfl }
            naturality _ _ _ := rfl } })
  have hℓ (V : C.Opens) (hP : P ∈ V) (s : D.sectionModule C V) :
      ℓ (M.presheaf.germ V P hP s) = s.val ⟨P, hP⟩ := by
    dsimp only [ℓ]
    rw [TopCat.Presheaf.germ]
    erw [CategoryTheory.Limits.colimit.ι_desc_apply]
    rfl
  let j := Modules.stalkLinearMapMk ℓ (fun V hP r s ↦ by
    rw [hℓ, hℓ]
    rfl)
  have hj (V : C.Opens) (hP : P ∈ V) (s : D.sectionModule C V) :
      j (M.presheaf.germ V P hP s) = s.val ⟨P, hP⟩ := hℓ V hP s
  refine ⟨j, ?_, hj⟩
  apply (injective_iff_map_eq_zero j).mpr
  intro m hm
  obtain ⟨V, hP, s, rfl⟩ := M.presheaf.exists_germ_eq m
  have hzero : (show D.sectionModule C V from s) = 0 := by
    apply Subtype.ext
    funext x
    have hpre : PreirreducibleSpace V := V.isOpenEmbedding.preirreducibleSpace
    have hconn : PreconnectedSpace V := PreirreducibleSpace.preconnectedSpace V
    change (show D.sectionModule C V from s).val x = 0
    rw [@IsLocallyConstant.apply_eq_of_preconnectedSpace V C.functionField _ hconn
      _ (show D.sectionModule C V from s).property.1 x ⟨P, hP⟩]
    exact (hj V hP s).symm.trans hm
  rw [hzero, map_zero]

private theorem divisor_stalk_of_local_generator
    (C : Scheme.{u}) [IsIntegral C] [IsNoetherian C] [IsRegular C]
    (D : C.Divisor) (P : C) (c : C.functionField) (U : C.Opens) (hPU : P ∈ U)
    (hlocal : ∀ (V : C.Opens), V ≤ U → Nonempty V →
      ∃ e : Γ(C, V) ≃ₗ[Γ(C, V)] D.sectionModule C V,
        ∀ (a : Γ(C, V)) (x : V), (e a).val x = c *
          algebraMap (C.presheaf.stalk x.val) C.functionField
            (C.presheaf.germ V x.val x.property a)) :
    ∃ j : (D.associatedModule C).presheaf.stalk P →ₗ[C.presheaf.stalk P] C.functionField,
      Function.Injective j ∧
      (∀ (V : C.Opens) (hP : P ∈ V) (s : D.sectionModule C V),
        j ((D.associatedModule C).presheaf.germ V P hP s) = s.val ⟨P, hP⟩) ∧
      Set.range j = {g : C.functionField | ∃ a : C.presheaf.stalk P,
        g = c * algebraMap (C.presheaf.stalk P) C.functionField a} := by
  obtain ⟨j, hinj, hj⟩ := divisor_stalk_embedding C D P
  refine ⟨j, hinj, hj, ?_⟩
  ext g
  constructor
  · rintro ⟨m, rfl⟩
    obtain ⟨V, hPV, s, rfl⟩ := (D.associatedModule C).presheaf.exists_germ_eq m
    let W := V ⊓ U
    have hPW : P ∈ W := ⟨hPV, hPU⟩
    have hW : Nonempty W := ⟨⟨P, hPW⟩⟩
    obtain ⟨e, he⟩ := hlocal W inf_le_right hW
    let sW := D.restrictSection C (homOfLE (inf_le_left : W ≤ V)) s
    let a := e.symm sW
    refine ⟨C.presheaf.germ W P hPW a, ?_⟩
    rw [hj]
    have hae := he a ⟨P, hPW⟩
    rw [LinearEquiv.apply_symm_apply] at hae
    exact hae
  · rintro ⟨a, rfl⟩
    obtain ⟨V, hPV, a, rfl⟩ := C.presheaf.exists_germ_eq a
    let W := V ⊓ U
    have hPW : P ∈ W := ⟨hPV, hPU⟩
    have hW : Nonempty W := ⟨⟨P, hPW⟩⟩
    obtain ⟨e, he⟩ := hlocal W inf_le_right hW
    let aW := C.presheaf.map (homOfLE (inf_le_left : W ≤ V)).op a
    refine ⟨(D.associatedModule C).presheaf.germ W P hPW (e aW), ?_⟩
    rw [hj, he]
    rw [TopCat.Presheaf.germ_res_apply]

private theorem divisor_zero_sections (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    [IsIntegral C] [IsNoetherian C] [IsRegular C] (V : C.Opens) :
    ((0 : C.Divisor).sectionModule C V : Set (V → C.functionField)) =
      Set.range (divisorScalarMap C V) := by
  let : SmoothOfRelativeDimension 1 f :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := f))
  ext s
  constructor
  · intro hs
    change (0 : C.Divisor).sectionCondition C V s at hs
    rcases isEmpty_or_nonempty V with hV | hV
    · refine ⟨0, ?_⟩
      funext x
      exact (hV.false x).elim
    · have := hV
      have hpre : PreirreducibleSpace V := V.isOpenEmbedding.preirreducibleSpace
      have hconn : PreconnectedSpace V := PreirreducibleSpace.preconnectedSpace V
      obtain ⟨x⟩ := hV
      have hconst : ∀ y : V, s y = s x :=
        fun y ↦ @IsLocallyConstant.apply_eq_of_preconnectedSpace V C.functionField
          _ hconn s hs.1 y x
      have hnonneg : ∀ y ∈ V, 0 ≤ C.ord (s x) y := by
        intro y hy
        by_cases hc : IsClosed ({y} : Set C)
        · rcases hs.2 ⟨y, hy⟩ hc with hz | hz
          · rw [← hconst ⟨y, hy⟩, hz, ord_zero]
            exact le_rfl
          · simpa only [Finsupp.zero_apply, add_zero, hconst ⟨y, hy⟩] using hz
        · rw [ord_eq_zero_of_coheight_neq_one (fun h ↦ hc
            (isClosed_of_coheight_eq_one f h))]
      obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_ord_nonneg f hnonneg
      refine ⟨a, ?_⟩
      funext y
      change algebraMap (C.presheaf.stalk y.val) C.functionField
        (C.presheaf.germ V y.val y.property a) = s y
      rw [algebraMap_germ_eq_germToFunctionField, ha, hconst y]
  · rintro ⟨a, rfl⟩
    change (0 : C.Divisor).sectionCondition C V (divisorScalarMap C V a)
    refine ⟨IsLocallyConstant.of_constant _ ?_, ?_⟩
    · intro x y
      have : Nonempty V := ⟨x⟩
      change algebraMap (C.presheaf.stalk x.val) C.functionField
          (C.presheaf.germ V x.val x.property a) =
        algebraMap (C.presheaf.stalk y.val) C.functionField
          (C.presheaf.germ V y.val y.property a)
      simp only [algebraMap_germ_eq_germToFunctionField]
    · intro x hx
      have : Nonempty V := ⟨x⟩
      right
      change 0 ≤ C.ord (algebraMap (C.presheaf.stalk x.val) C.functionField
        (C.presheaf.germ V x.val x.property a)) x.val + 0
      rw [algebraMap_germ_eq_germToFunctionField, add_zero]
      exact ord_germToFunctionField_nonneg a x.property

/-- The divisor module is locally generated by the inverse coefficient power of a uniformizer,
is invertible, has the corresponding fractional stalk, and equals the structure sheaf for zero.
Source: Stacks Project, Divisors, proof of Tag 0BE9 and Tag 0AGA; Algebra, Tag 031T
(blueprint: lem-sc-divisor-module-local).

Proof:
1. By `lem-sc-smooth-connected-curve-local-rings`, the curve is integral and Noetherian,
   and each closed stalk is a DVR. Remove the other points in the support of D and the other
   zeros and poles of t, a finite set by `lem-sc-divisor-finite-support`. On the remaining
   neighbourhood U, t has order one at P and zero at every other closed point, and D has
   coefficient zero at every other closed point.
2. On any nonempty open V, regular sections are precisely the rational functions in every
   closed stalk: use `lem-sc-function-field-sections-glue`, together with the fact that every
   point is closed or generic (`lem-sc-smooth-connected-curve-local-rings`).
3. For V contained in U, the order of t^{n_P}g at Q equals v_Q(g)+n_Q. Thus the defining
   inequalities of `def-sc-divisor` hold exactly when t^{n_P}g is a regular section on V.
   The zero case satisfies both conditions separately.
4. Multiplication by t^{-n_P} is therefore a linear bijection on sections, compatible with
   restriction since both section models restrict pointwise. These bijections give the stated
   local module isomorphism. Such neighbourhoods cover the curve, including its generic point,
   so the module is invertible (`def-sc-invertible-module`).
5. Neighbourhoods contained in U are cofinal at P. Evaluation at P of a locally constant
   section induces the injective map from the module stalk to the function field. Taking the
   union of the section images in step 3 identifies its range with t^{-n_P} O_{C,P}
   (`def-weil-pbc-module-stalk`).
6. For D=0 the order inequalities say exactly that g lies in every closed stalk, so step 2
   identifies all sections with regular sections. This equality commutes with pointwise
   restriction; on the empty open both sides consist of the unique empty function.

The section equivalences are specified by their values at every point, so their restriction
compatibility and hence the sheaf isomorphism are determined, not merely abstract existence.
The stalk embedding is specified on all germs, so its range equality is an equality inside
k(C), not just an abstract stalk isomorphism. -/
theorem Divisor.module_local (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (D : C.Divisor) :
    letI : IsNoetherian C := isNoetherian_of_locallyOfFiniteType f
    letI : IsRegular C := IsRegular.of_smooth f
    letI : IsIntegral C := (C.smooth_connected_curve_local_rings k f).choose
    let M := D.moduleOfSmoothConnectedCurve k C f
    ∀ (P : closedPoints C) (t : C.presheaf.stalk P.val),
      IsLocalRing.maximalIdeal (C.presheaf.stalk P.val) = Ideal.span {t} →
      let c := (algebraMap (C.presheaf.stalk P.val) C.functionField t) ^ (-D P)
      (∃ U : C.Opens, P.val ∈ U ∧
        ∀ (V : C.Opens), V ≤ U → Nonempty V →
          ∃ e : Γ(C, V) ≃ₗ[Γ(C, V)] D.sectionModule C V,
            ∀ (a : Γ(C, V)) (x : V),
              (e a).val x = c *
                algebraMap (C.presheaf.stalk x.val) C.functionField
                  (C.presheaf.germ V x.val x.property a)) ∧
      M.IsInvertible ∧
      (∃ j : M.presheaf.stalk P.val →ₗ[C.presheaf.stalk P.val] C.functionField,
        Function.Injective j ∧
        (∀ (V : C.Opens) (hP : P.val ∈ V) (s : D.sectionModule C V),
          j (M.presheaf.germ V P.val hP s) = s.val ⟨P.val, hP⟩) ∧
        Set.range j =
          {g : C.functionField | ∃ a : C.presheaf.stalk P.val,
            g = c * algebraMap (C.presheaf.stalk P.val) C.functionField a}) ∧
      (∀ V : C.Opens,
        ((0 : C.Divisor).sectionModule C V : Set (V → C.functionField)) =
          Set.range (divisorScalarMap C V)) := by
  let : IsNoetherian C := isNoetherian_of_locallyOfFiniteType f
  let : IsRegular C := IsRegular.of_smooth f
  let : IsIntegral C := (C.smooth_connected_curve_local_rings k f).choose
  dsimp only
  have hlocal : ∀ (P : closedPoints C) (t : C.presheaf.stalk P.val),
      IsLocalRing.maximalIdeal (C.presheaf.stalk P.val) = Ideal.span {t} →
      let c := (algebraMap (C.presheaf.stalk P.val) C.functionField t) ^ (-D P)
      c ≠ 0 ∧ (∃ U : C.Opens, P.val ∈ U ∧
        ∀ (V : C.Opens), V ≤ U → Nonempty V →
          ∃ e : Γ(C, V) ≃ₗ[Γ(C, V)] D.sectionModule C V,
            ∀ (a : Γ(C, V)) (x : V),
              (e a).val x = c *
                algebraMap (C.presheaf.stalk x.val) C.functionField
                  (C.presheaf.germ V x.val x.property a)) := by
    intro P t ht
    obtain ⟨hc, U, hP, hU⟩ := Divisor.local_section_image k C f D P t ht
    refine ⟨hc, U, hP, ?_⟩
    intro V hV hnonempty
    have := hnonempty
    exact divisor_equiv_of_section_image C D V _ hc (hU V hV hnonempty)
  have hinvertible := Divisor.module_invertible_of_local_generators k C f D hlocal
  intro P t ht
  obtain ⟨hc, U, hPU, hU⟩ := hlocal P t ht
  refine ⟨⟨U, hPU, hU⟩, hinvertible, ?_, divisor_zero_sections k C f⟩
  exact divisor_stalk_of_local_generator C D P.val _ U hPU hU

end AlgebraicGeometry.Scheme
