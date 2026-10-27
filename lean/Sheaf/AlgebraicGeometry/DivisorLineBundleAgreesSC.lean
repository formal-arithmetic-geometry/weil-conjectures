module

public import Sheaf.AlgebraicGeometry.DivisorModule
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
import Sheaf.AlgebraicGeometry.DivisorModuleTensorAdd

/-!
# Agreement of divisor modules and effective-Cartier line bundles

Source: literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-rr/
lem-pc-divisor-line-bundle-agrees-sc (blueprint: lem-pc-divisor-line-bundle-agrees-sc).

## Main statement

For an effective divisor `D = ∑ n_P [P]` (`0 ≤ D`) on a smooth connected curve, the closed
subscheme `D` has ideal sheaf `∏_P I_P ^ n_P`, the product (in the semiring
`Scheme.IdealSheafData`) of powers of the vanishing ideals of the reduced closed points. Its
dual `Scheme.Modules.dual` (the module of def-pc-divisor-line-bundle) is isomorphic to the
divisor module `Divisor.moduleOfSmoothConnectedCurve` (the module of def-sc-divisor).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

/-- A nonzero rational function whose order cancels D is a free generator of O(D).
Source: the local calculation in lem-pc-divisor-line-bundle-agrees-sc and the proved
regular-section criterion in Curve.DivisorIdealSheaf. Divide a divisor section by c;
the resulting rational function has nonnegative orders and therefore is regular.
The empty open is handled separately by uniqueness of its sections. -/
private theorem divisor_generator_of_orders
    {k : Type u} [Field k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f]
    [IsIntegral C] [IsNoetherian C] [IsRegular C]
    (D : C.Divisor) (U : C.Opens) (c : C.functionField) (hc : c ≠ 0)
    (hord : ∀ P : closedPoints C, P.val ∈ U → C.ord c P.val + D P = 0) :
    ∃ t : Γ(D.associatedModule C, U), Modules.IsFreeGenerator t ∧
      ∀ x : U, t.val x = c := by
  classical
  let t : D.sectionModule C U := ⟨fun _ ↦ c,
    IsLocallyConstant.const c, fun x hx ↦ Or.inr (by
      have h := hord ⟨x.val, hx⟩ x.property
      change C.ord c x.val + D ⟨x.val, hx⟩ = 0 at h
      change 0 ≤ C.ord c x.val + D ⟨x.val, hx⟩
      omega)⟩
  refine ⟨t, ?_, fun _ ↦ rfl⟩
  intro V hVU
  by_cases hV : Nonempty V
  · have := hV
    have hpre : PreirreducibleSpace V := V.isOpenEmbedding.preirreducibleSpace
    have hconn : PreconnectedSpace V := PreirreducibleSpace.preconnectedSpace V
    constructor
    · intro a b hab
      obtain ⟨x⟩ := hV
      have hx := congrArg (fun s : D.sectionModule C V ↦ s.val x) hab
      change divisorScalarMap C V a x * c = divisorScalarMap C V b x * c at hx
      have hh := mul_right_cancel₀ hc hx
      apply C.germToFunctionField_injective V
      simpa only [divisorScalarMap, RingHom.pi_apply,
        RingHom.comp_apply, algebraMap_germ_eq_germToFunctionField] using hh
    · intro s
      obtain ⟨x⟩ := hV
      have hs (y : V) : s.val y = s.val x :=
        @IsLocallyConstant.apply_eq_of_preconnectedSpace V C.functionField _ hconn
          s.val s.property.1 y x
      by_cases hz : s.val x = 0
      · refine ⟨0, ?_⟩
        apply Subtype.ext
        funext y
        change divisorScalarMap C V 0 y * c = s.val y
        simp only [map_zero, Pi.zero_apply, zero_mul, hs y, hz]
      have hn : ∀ y ∈ V, 0 ≤ C.ord (s.val x / c) y := by
        intro y hy
        by_cases hclosed : IsClosed ({y} : Set C)
        · have hh := hord ⟨y, hclosed⟩ (hVU hy)
          change C.ord c y + D ⟨y, hclosed⟩ = 0 at hh
          have hb : 0 ≤ C.ord (s.val x) y + D ⟨y, hclosed⟩ := by
            rcases s.property.2 ⟨y, hy⟩ hclosed with hzero | hb
            · exact (hz ((hs ⟨y, hy⟩).symm.trans hzero)).elim
            · simpa only [hs ⟨y, hy⟩] using hb
          rw [ord_div hz hc]
          omega
        · rw [ord_eq_zero_of_coheight_neq_one (fun h ↦ hclosed
            (isClosed_of_coheight_eq_one f h))]
      obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_ord_nonneg f hn
      refine ⟨a, ?_⟩
      apply Subtype.ext
      funext y
      change divisorScalarMap C V a y * c = s.val y
      change algebraMap (C.presheaf.stalk y.val) C.functionField
        (C.presheaf.germ V y.val y.property a) * c = s.val y
      rw [algebraMap_germ_eq_germToFunctionField, ha, div_mul_cancel₀ _ hc, hs y]
  · have : Subsingleton Γ(C, V) := CommRingCat.subsingleton_of_isTerminal
      (C.sheaf.isTerminalOfEqEmpty (by
        ext z
        exact iff_false_intro (fun hz ↦ hV ⟨⟨z, hz⟩⟩)))
    have : Subsingleton (D.sectionModule C V) := ⟨fun a b ↦
      Subtype.ext (funext fun x ↦ (hV ⟨x⟩).elim)⟩
    change Function.Bijective (fun r : Γ(C, V) ↦
      (r • (D.associatedModule C).presheaf.map (homOfLE hVU).op t :
        D.sectionModule C V))
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, by
      apply Subtype.ext
      funext x
      exact (hV ⟨x⟩).elim⟩⟩

/-- The point-ideal product is the explicit negative-divisor module.
Source: lem-pc-divisor-line-bundle-agrees-sc, local principal-ideal comparison.
A local ideal generator has order E(P), so it also generates O(-E). The local
identifications have the same transitions since both map to the same rational function. -/
private theorem ideal_iso_negative
    {k : Type u} [Field k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f]
    [IsIntegral C] [IsNoetherian C] [IsRegular C]
    (E : closedPoints C →₀ ℕ) :
    Nonempty ((Divisor.idealSheaf E).toModules ≅
      Divisor.associatedModule C (-(E.mapRange Nat.cast Nat.cast_zero) : C.Divisor)) := by
  classical
  let J := Divisor.idealSheaf E
  let D : C.Divisor := -(E.mapRange Nat.cast Nat.cast_zero)
  have hJ := Divisor.isInvertible_idealSheaf f E
  have key (x : C) : ∃ (U : C.affineOpens) (_ : x ∈ U.1)
      (s : Γ(J.toModules, U.1)) (t : Γ(D.associatedModule C, U.1)),
      Modules.IsFreeGenerator s ∧ Modules.IsFreeGenerator t ∧
      ∀ (hU : Nonempty U.1) (y : U.1),
        t.val y = C.germToFunctionField U.1 (J.sectionsι U.1 s) := by
    obtain ⟨U, hxU, -, b, hb⟩ := hJ.isLocallyPrincipal.exists_ideal_eq_span
      (O := ⊤) (y := x) trivial
    have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
    have hb0 := hJ.germToFunctionField_ne_zero hb
    obtain ⟨s, hs, hsf⟩ := hJ.exists_isFreeGenerator hb
    obtain ⟨t, htf, ht⟩ := divisor_generator_of_orders C f D U.1
      (C.germToFunctionField U.1 b) hb0 (by
        intro P hP
        rw [← J.ordAt_eq hP hb, Divisor.ordAt_idealSheaf f E P]
        simp [D])
    exact ⟨U, hxU, s, t, hsf, htf, fun _ y ↦ (ht y).trans (by rw [hs])⟩
  choose U hxU s t hs ht hst using key
  refine Modules.nonempty_iso_of_isFreeGenerator (U := fun x ↦ (U x).1)
    (e := s) (f := t)
    (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩) hs ?_ ht
  intro i j W hi hj a b hab
  apply Subtype.ext
  funext y
  have : Nonempty W := ⟨y⟩
  have : Nonempty (U i).1 := ⟨⟨y.val, hi y.property⟩⟩
  have : Nonempty (U j).1 := ⟨⟨y.val, hj y.property⟩⟩
  have hab' := congrArg (fun m ↦ C.germToFunctionField W (J.sectionsι W m)) hab
  rw [IdealSheafData.germToFunctionField_sectionsι_smul_map,
    IdealSheafData.germToFunctionField_sectionsι_smul_map] at hab'
  change divisorScalarMap C W a y * (t i).val ⟨y.val, hi y.property⟩ =
    divisorScalarMap C W b y * (t j).val ⟨y.val, hj y.property⟩
  rw [hst i, hst j]
  simpa only [divisorScalarMap, RingHom.pi_apply, RingHom.comp_apply,
    algebraMap_germ_eq_germToFunctionField] using hab'

/-- The constant rational function one globally generates O(0).
Source: def-sc-divisor and the zero-divisor clause of lem-sc-divisor-module-local.
Apply the rational-generator criterion to one and glue the resulting trivialization. -/
private theorem zero_divisor_iso_unit
    {k : Type u} [Field k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f]
    [IsIntegral C] [IsNoetherian C] [IsRegular C] :
    Nonempty ((0 : C.Divisor).associatedModule C ≅ SheafOfModules.unit C.ringCatSheaf) := by
  obtain ⟨t, ht, -⟩ := divisor_generator_of_orders C f 0 ⊤ 1 one_ne_zero
    (by intro P hP; simp [ord_one])
  suffices h : Nonempty (SheafOfModules.unit C.ringCatSheaf ≅
      (0 : C.Divisor).associatedModule C) from ⟨h.some.symm⟩
  refine Modules.nonempty_iso_of_isFreeGenerator (U := fun _ : Unit ↦ ⊤)
    (e := fun _ ↦ (1 : Γ(C, ⊤))) (f := fun _ ↦ t) (by simp)
    (fun _ ↦ Modules.isFreeGenerator_one ⊤) ?_ (fun _ ↦ ht)
  intro i j W hi hj a b hab
  have heq : a = b := by
    change a * C.presheaf.map (homOfLE hi).op 1 =
      b * C.presheaf.map (homOfLE hj).op 1 at hab
    simpa using hab
  subst b
  rfl

/-- For an effective divisor `D` on a smooth connected curve, the dual of the ideal sheaf
`∏_P I_P ^ n_P` of `D` (def-pc-divisor-line-bundle) and the divisor module `O_C(D)` of
def-sc-divisor are isomorphic.
Source: blueprint node lem-pc-divisor-line-bundle-agrees-sc
(blueprint: lem-pc-divisor-line-bundle-agrees-sc). -/
theorem divisorLineBundle_agrees_sc (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (D : C.Divisor) (hD : 0 ≤ D) :
    Nonempty (Scheme.Modules.dual (D.prod fun P n ↦
        IdealSheafData.vanishingIdeal ⟨{P.val}, P.prop⟩ ^ n.toNat).toModules ≅
      D.moduleOfSmoothConnectedCurve k C f) := by
  classical
  let : IsNoetherian C := isNoetherian_of_locallyOfFiniteType f
  let : ConnectedSpace C := IsConnectedCurve.connectedSpace' f
  let : IsRegular C := IsRegular.of_smooth f
  let : IsIntegral C := IsRegular.isIntegral C
  let : SmoothOfRelativeDimension 1 f :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := f))
  let E := D.mapRange Int.toNat Int.toNat_zero
  have hE : E.mapRange Nat.cast Nat.cast_zero = D := by
    ext P
    simp only [Finsupp.mapRange_apply]
    exact Int.toNat_of_nonneg (hD P)
  have hJ : Divisor.idealSheaf E = D.prod (fun P n ↦
      IdealSheafData.vanishingIdeal ⟨{P.val}, P.prop⟩ ^ n.toNat) := by
    simp [Divisor.idealSheaf, E, Finsupp.prod_mapRange_index]
  obtain ⟨e⟩ := ideal_iso_negative C f E
  rw [hE] at e
  let M (A : C.Divisor) := A.moduleOfSmoothConnectedCurve k C f
  have e' : (Divisor.idealSheaf E).toModules ≅ M (-D) := e
  have := (Divisor.isInvertible_idealSheaf f E).isInvertible_toModules
  obtain ⟨z⟩ := zero_divisor_iso_unit C f
  obtain ⟨t⟩ := Divisor.nonempty_module_tensor_add_iso k C f (-D) D
  have t' : (Divisor.idealSheaf E).toModules ⊗ M D ≅ 𝟙_ C.Modules :=
    whiskerRightIso e' (M D) ≪≫ t ≪≫ eqToIso (by rw [neg_add_cancel]; rfl) ≪≫ z
  obtain ⟨d⟩ := Modules.nonempty_tensorObj_dual_iso_unit (Divisor.idealSheaf E).toModules
  let iso : Modules.dual (Divisor.idealSheaf E).toModules ≅ M D :=
    (λ_ _).symm ≪≫ whiskerRightIso t'.symm _ ≪≫ α_ _ _ _ ≪≫
      whiskerLeftIso _ (β_ _ _) ≪≫ (α_ _ _ _).symm ≪≫
      whiskerRightIso d _ ≪≫ λ_ _
  rw [← hJ]
  exact ⟨iso⟩

end AlgebraicGeometry.Scheme
