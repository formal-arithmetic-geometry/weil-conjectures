/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.CofilteredSystem
public import WeilConjectures.CategoryTheory.EssentiallyConstantSystem
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Sheaf.CategoryTheory.MittagLefflerExactSequence
import WeilConjectures.CategoryTheory.MittagLefflerLimitExact

/-!
# Homology of the limit of a Mittag-Leffler system of four-term complexes

Source: Stacks Project, Homology, Lemma 12.31.7, Tag 070E
(blueprint: lem-weil-pbc-mittag-leffler-complex-limit-homology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem kernel_sequence_shortExact
    {A B : ℕᵒᵖ ⥤ AddCommGrpCat.{u}} (f : A ⟶ B) [Epi f] (n : ℕᵒᵖ) :
    ((ShortComplex.kernelSequence f).map
      ((evaluation ℕᵒᵖ AddCommGrpCat).obj n)).ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · exact (ShortComplex.kernelSequence_exact f).map_of_mono_of_preservesKernel
      ((evaluation ℕᵒᵖ AddCommGrpCat).obj n) inferInstance inferInstance
  · change Mono ((kernel.ι f).app n)
    infer_instance
  · change Epi (f.app n)
    infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem ml_of_epi {A B : ℕᵒᵖ ⥤ AddCommGrpCat.{u}} (f : A ⟶ B)
    [Epi f] (hA : (A ⋙ CategoryTheory.forget AddCommGrpCat).IsMittagLeffler) :
    (B ⋙ CategoryTheory.forget AddCommGrpCat).IsMittagLeffler :=
  (ShortComplex.mittagLeffler_quotient_and_limit_exact
    (ShortComplex.kernelSequence f) (kernel_sequence_shortExact f)).1 hA

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem epi_kernel_lift_of_exact
    (S : ShortComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{u}))
    (hS : ∀ n, (S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj n)).Exact) :
    Epi (kernel.lift S.g S.f S.zero) := by
  have : ∀ n, Epi ((kernel.lift S.g S.f S.zero).app n) := by
    intro n
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro x
    have hx : S.g.app n ((kernel.ι S.g).app n x) = 0 := by
      have hz := congrArg (fun f : kernel S.g ⟶ S.X₃ ↦ f.app n) (kernel.condition S.g)
      exact ConcreteCategory.congr_hom hz x
    obtain ⟨a, ha⟩ :=
      ((S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj n)).ab_exact_iff.mp (hS n)) _ hx
    change S.f.app n a = (kernel.ι S.g).app n x at ha
    refine ⟨a, ?_⟩
    apply (AddCommGrpCat.mono_iff_injective ((kernel.ι S.g).app n)).mp inferInstance
    change ((kernel.lift S.g S.f S.zero) ≫ kernel.ι S.g).app n a = _
    simpa only [kernel.lift_ι] using ha
  exact NatTrans.epi_of_epi_app _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem ml_middle_of_exact
    (S : ShortComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{u}))
    (hS : ∀ n, (S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj n)).Exact)
    [Epi S.g] (hA : (S.X₁ ⋙ CategoryTheory.forget AddCommGrpCat).IsMittagLeffler)
    (hC : S.X₃.IsEssentiallyConstant) :
    (S.X₂ ⋙ CategoryTheory.forget AddCommGrpCat).IsMittagLeffler := by
  have := epi_kernel_lift_of_exact S hS
  have hB := ml_of_epi (kernel.lift S.g S.f S.zero) hA
  exact (ShortComplex.isMittagLeffler_iff_of_isEssentiallyConstant
    (ShortComplex.kernelSequence S.g) (kernel_sequence_shortExact S.g) hC).mp hB

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def cycleSequence {ι : Type*} {c : ComplexShape ι}
    (K : ℕᵒᵖ ⥤ HomologicalComplex AddCommGrpCat.{u} c) (i j : ι) :
    ShortComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  ShortComplex.mk
    (X₁ := K ⋙ eval AddCommGrpCat c i)
    (X₂ := K ⋙ cyclesFunctor AddCommGrpCat c j)
    (X₃ := K ⋙ homologyFunctor AddCommGrpCat c j)
    { app := fun n ↦ (K.obj n).toCycles i j
      naturality := by
        intro n m f
        apply (cancel_mono ((K.obj m).iCycles j)).mp
        simp only [Category.assoc, Functor.comp_map, cyclesFunctor_map,
          cyclesMap_i, toCycles_i_assoc, toCycles_i, eval_map]
        exact (K.map f).comm i j }
    (Functor.whiskerLeft K (natTransHomologyπ AddCommGrpCat c j))
    (by apply NatTrans.ext; funext n; exact (K.obj n).toCycles_comp_homologyπ i j)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem cycleSequence_exact {ι : Type*} {c : ComplexShape ι}
    (K : ℕᵒᵖ ⥤ HomologicalComplex AddCommGrpCat.{u} c) (i j : ι)
    (hi : c.prev j = i) (n : ℕᵒᵖ) :
    ((cycleSequence K i j).map ((evaluation ℕᵒᵖ AddCommGrpCat).obj n)).Exact := by
  apply ShortComplex.exact_of_g_is_cokernel
  exact (K.obj n).homologyIsCokernel i j hi

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem cycleSequence_epi {ι : Type*} {c : ComplexShape ι}
    (K : ℕᵒᵖ ⥤ HomologicalComplex AddCommGrpCat.{u} c) (i j : ι) :
    Epi (cycleSequence K i j).g := by
  have : ∀ n, Epi ((cycleSequence K i j).g.app n) := by
    intro n
    change Epi ((K.obj n).homologyπ j)
    infer_instance
  exact NatTrans.epi_of_epi_app _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def boundarySequence {ι : Type*} {c : ComplexShape ι}
    (K : ℕᵒᵖ ⥤ HomologicalComplex AddCommGrpCat.{u} c) (i j : ι) :
    ShortComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  let S := cycleSequence K i j
  ShortComplex.mk
    (X₁ := K ⋙ cyclesFunctor AddCommGrpCat c i)
    (X₂ := K ⋙ eval AddCommGrpCat c i) (X₃ := kernel S.g)
    { app := fun n ↦ (K.obj n).iCycles i
      naturality := by
        intro n m f
        exact cyclesMap_i (K.map f) i }
    (kernel.lift S.g S.f S.zero)
    (by
      apply NatTrans.ext
      funext n
      apply (cancel_mono ((kernel.ι S.g).app n)).mp
      change (K.obj n).iCycles i ≫ ((kernel.lift S.g S.f S.zero ≫ kernel.ι S.g).app n) = _
      rw [kernel.lift_ι]
      apply (cancel_mono ((K.obj n).iCycles j)).mp
      change (K.obj n).iCycles i ≫ (K.obj n).toCycles i j ≫
        (K.obj n).iCycles j = 0 ≫ (kernel.ι S.g).app n ≫ (K.obj n).iCycles j
      simp only [toCycles_i, iCycles_d, zero_comp])

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem boundarySequence_shortExact {ι : Type*} {c : ComplexShape ι}
    (K : ℕᵒᵖ ⥤ HomologicalComplex AddCommGrpCat.{u} c) (i j : ι)
    (hi : c.prev j = i) (hj : c.next i = j) (n : ℕᵒᵖ) :
    ((boundarySequence K i j).map ((evaluation ℕᵒᵖ AddCommGrpCat).obj n)).ShortExact := by
  let S := cycleSequence K i j
  have hq := epi_kernel_lift_of_exact S (cycleSequence_exact K i j hi)
  apply ShortComplex.ShortExact.mk'
  · apply (ShortComplex.ab_exact_iff _).mpr
    intro x hx
    change (kernel.lift S.g S.f S.zero).app n x = 0 at hx
    have hd : (K.obj n).d i j x = 0 := by
      have hfac : (kernel.lift S.g S.f S.zero).app n ≫ (kernel.ι S.g).app n ≫
          (K.obj n).iCycles j = (K.obj n).d i j := by
        rw [← Category.assoc, ← NatTrans.comp_app, kernel.lift_ι]
        exact (K.obj n).toCycles_i i j
      rw [← hfac]
      change (K.obj n).iCycles j ((kernel.ι S.g).app n
        ((kernel.lift S.g S.f S.zero).app n x)) = 0
      rw [hx, map_zero, map_zero]
    have hx' : ((K.obj n).sc i).g x = 0 := by
      change (K.obj n).d i (c.next i) x = 0
      rw [hj]
      exact hd
    refine ⟨((K.obj n).sc i).abCyclesIso.inv ⟨x, hx'⟩, ?_⟩
    exact ((K.obj n).sc i).abCyclesIso_inv_apply_iCycles ⟨x, hx'⟩
  · change Mono ((K.obj n).iCycles i)
    infer_instance
  · change Epi ((kernel.lift S.g S.f S.zero).app n)
    infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem cycles_preservesLimit {ι : Type*} {c : ComplexShape ι}
    (K : ℕᵒᵖ ⥤ HomologicalComplex AddCommGrpCat.{u} c) (j : ι) :
    PreservesLimit K (cyclesFunctor AddCommGrpCat c j) := by
  let e := isLimitOfPreserves (eval AddCommGrpCat c j) (limit.isLimit K)
  let e' := isLimitOfPreserves (eval AddCommGrpCat c (c.next j)) (limit.isLimit K)
  let s := (cyclesFunctor AddCommGrpCat c j).mapCone (limit.cone K)
  let t' (t : Cone (K ⋙ cyclesFunctor AddCommGrpCat c j)) : Cone (K ⋙ eval AddCommGrpCat c j) :=
    { pt := t.pt
      π :=
        { app := fun n ↦ t.π.app n ≫ (K.obj n).iCycles j
          naturality := by
            intro n m f
            dsimp
            rw [Category.id_comp, Category.assoc, ← cyclesMap_i]
            have hw := t.w f
            change t.π.app n ≫ cyclesMap (K.map f) j = t.π.app m at hw
            rw [← Category.assoc, hw] } }
  have hs : IsLimit s := by
    refine { lift := ?_, fac := ?_, uniq := ?_ }
    · intro t
      have hz : e.lift (t' t) ≫ (limit K).d j (c.next j) = 0 := by
        apply e'.hom_ext
        intro n
        dsimp
        have he := e.fac (t' t) n
        change e.lift (t' t) ≫ (limit.π K n).f j =
          t.π.app n ≫ (K.obj n).iCycles j at he
        rw [Category.assoc, ← (limit.π K n).comm, ← Category.assoc, he]
        simp only [Category.assoc, iCycles_d, comp_zero, zero_comp]
      exact (limit K).liftCycles (e.lift (t' t)) (c.next j) rfl hz
    · intro t n
      apply (cancel_mono ((K.obj n).iCycles j)).mp
      dsimp [s]
      simp only [Category.assoc, cyclesMap_i, liftCycles_i_assoc]
      exact e.fac (t' t) n
    · intro t m hm
      apply (cancel_mono ((limit K).iCycles j)).mp
      apply e.hom_ext
      intro n
      calc
        _ = t.π.app n ≫ (K.obj n).iCycles j := by
          have hc := congrArg (fun a ↦ a ≫ (K.obj n).iCycles j) (hm n)
          change (m ≫ cyclesMap (limit.π K n) j) ≫ (K.obj n).iCycles j = _ at hc
          change (m ≫ (limit K).iCycles j) ≫ (limit.π K n).f j = _
          simpa only [Category.assoc, cyclesMap_i] using hc
        _ = _ := by
          simpa only [Category.assoc, liftCycles_i_assoc] using (e.fac (t' t) n).symm
  exact preservesLimit_of_preserves_limit_cone (limit.isLimit K) hs

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem homology_comparison_of_ml_cycles {ι : Type*} {c : ComplexShape ι}
    (K : ℕᵒᵖ ⥤ HomologicalComplex AddCommGrpCat.{u} c) (i j : ι)
    (hi : c.prev j = i) (hj : c.next i = j)
    (hA : (K ⋙ eval AddCommGrpCat c i ⋙ CategoryTheory.forget AddCommGrpCat).IsMittagLeffler)
    (hZ : (K ⋙ cyclesFunctor AddCommGrpCat c i ⋙
      CategoryTheory.forget AddCommGrpCat).IsMittagLeffler) :
    IsIso (limit.post K (homologyFunctor AddCommGrpCat c j)) := by
  let S := cycleSequence K i j
  let T := boundarySequence K i j
  have hp := cycleSequence_epi K i j
  have hq := epi_kernel_lift_of_exact S (cycleSequence_exact K i j hi)
  have hB := ml_of_epi (kernel.lift S.g S.f S.zero) hA
  have hlimP := (ShortComplex.mittagLeffler_quotient_and_limit_exact
    (ShortComplex.kernelSequence S.g) (kernel_sequence_shortExact S.g)).2 hB
  have hlimQ := (ShortComplex.mittagLeffler_quotient_and_limit_exact
    T (boundarySequence_shortExact K i j hi hj)).2 hZ
  have hlimQepi : Epi (limMap (kernel.lift S.g S.f S.zero)) := hlimQ.epi_g
  have hlimPepi : Epi (limMap S.g) := hlimP.epi_g
  have hcycles := cycles_preservesLimit K j
  let z : (limit K).cycles j ⟶ limit S.X₂ :=
    limit.post K (cyclesFunctor AddCommGrpCat c j)
  let a : (limit K).X i ⟶ limit S.X₁ := limit.post K (eval AddCommGrpCat c i)
  let h : (limit K).homology j ⟶ limit S.X₃ :=
    limit.post K (homologyFunctor AddCommGrpCat c j)
  have hz : IsIso z := inferInstance
  have ha : IsIso a := inferInstance
  have hcomp : (limit K).homologyπ j ≫ h = z ≫ limMap S.g := by
    apply limit.hom_ext
    intro n
    rw [Category.assoc, Category.assoc, limMap_π]
    change (limit K).homologyπ j ≫ h ≫ limit.π S.X₃ n =
      (z ≫ limit.π S.X₂ n) ≫ (K.obj n).homologyπ j
    rw [show z ≫ limit.π S.X₂ n = cyclesMap (limit.π K n) j from limit.post_π K _ n]
    rw [show h ≫ limit.π S.X₃ n = homologyMap (limit.π K n) j from limit.post_π K _ n]
    exact homologyπ_naturality (limit.π K n) j
  have hdiff : (limit K).toCycles i j ≫ z = a ≫ limMap S.f := by
    apply limit.hom_ext
    intro n
    rw [Category.assoc, Category.assoc, limMap_π]
    change (limit K).toCycles i j ≫ z ≫ limit.π S.X₂ n =
      (a ≫ limit.π S.X₁ n) ≫ (K.obj n).toCycles i j
    rw [show z ≫ limit.π S.X₂ n = cyclesMap (limit.π K n) j from limit.post_π K _ n]
    rw [show a ≫ limit.π S.X₁ n = (limit.π K n).f i from limit.post_π K _ n]
    apply (cancel_mono ((K.obj n).iCycles j)).mp
    simp only [Category.assoc, cyclesMap_i, toCycles_i_assoc, toCycles_i]
    exact ((limit.π K n).comm i j).symm
  have hep : Epi h := by
    apply epi_of_epi_fac hcomp
  have hmono : Mono h := by
    apply (AddCommGrpCat.mono_iff_injective h).mpr
    apply (injective_iff_map_eq_zero h.hom).mpr
    intro x hx
    obtain ⟨y, rfl⟩ := (AddCommGrpCat.epi_iff_surjective ((limit K).homologyπ j)).mp
      inferInstance x
    have hy : limMap S.g (z y) = 0 := by
      change (z ≫ limMap S.g) y = 0
      rw [← hcomp]
      exact hx
    obtain ⟨b, hb⟩ :=
      ((ShortComplex.kernelSequence S.g).map lim).ab_exact_iff.mp hlimP.exact (z y) hy
    obtain ⟨v, hv⟩ := (AddCommGrpCat.epi_iff_surjective
      (limMap (kernel.lift S.g S.f S.zero))).mp hlimQepi b
    have hd : (limit K).toCycles i j (inv a v) = y := by
      apply (AddCommGrpCat.mono_iff_injective z).mp inferInstance
      change ((limit K).toCycles i j ≫ z) (inv a v) = z y
      rw [hdiff]
      change limMap S.f (a (inv a v)) = z y
      have hav : a (inv a v) = v :=
        ConcreteCategory.congr_hom (IsIso.inv_hom_id a) v
      rw [hav]
      have hfac : limMap S.f =
          limMap (kernel.lift S.g S.f S.zero) ≫ limMap (kernel.ι S.g) := by
        change lim.map S.f =
          lim.map (kernel.lift S.g S.f S.zero) ≫ lim.map (kernel.ι S.g)
        rw [← lim.map_comp, kernel.lift_ι]
      rw [hfac]
      change limMap (kernel.ι S.g) (limMap (kernel.lift S.g S.f S.zero) v) = z y
      rw [hv]
      exact hb
    rw [← hd]
    exact ConcreteCategory.congr_hom ((limit K).toCycles_comp_homologyπ i j) (inv a v)
  exact isIso_of_mono_of_epi h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical map from degree-zero cohomology of the limit complex to the limit of
its degree-zero cohomologies is an isomorphism (Stacks Project, Tag 070E).
(blueprint: lem-weil-pbc-mittag-leffler-complex-limit-homology)

The shape in the statement is the interval `0 → 1 → 2 → 3`: these indices represent
cochain degrees `-2, -1, 0, 1`. Its relation uses natural-number values, so there is no
arrow from `3` to `0`. Tower index `n : ℕ` represents the source's index `n + 1`.

Proof (Stacks, Tag 070E):
1. Put `Z_i^j = ker d_i^j` and `I_i^j = im d_i^{j-1}`. Commutation with transitions
   gives systems and the four short exact sequences involving these, the terms, and H.
2. Kernels commute with limits, so `ker d^0 = lim Z_i^0`.
3. The systems `I_i^{-1}` and `I_i^0` are ML as quotients of the two ML term systems
   (lem-weil-pbc-mittag-leffler-limit-exact, Tag 02N1(2)).
4. The short exact sequence `0 → I_i^{-1} → Z_i^{-1} → H_i^{-1} → 0` makes
   `Z_i^{-1}` ML since its quotient is essentially constant
   (lem-weil-pbc-exact-sequence-ml, Tag 070D).
5. Apply Tag 02N1(3) to `0 → Z_i^{-1} → A_i^{-1} → I_i^0 → 0` to get
   surjectivity on limits, hence `im d^{-1} = lim I_i^0`.
6. Left exactness (lem-weil-pbc-tower-limit-exact-surjective-kernels) and Tag 02N1(3)
   give `0 → lim I_i^0 → lim Z_i^0 → lim H_i^0 → 0`.
7. Quotienting the kernel in step 2 by the image in step 5 gives the asserted canonical
   isomorphism, sending the class of a compatible cycle family to its family of classes. -/
theorem isIso_limitPost_homology_of_mittagLeffler :
    let c : ComplexShape (Fin 4) :=
      { Rel := fun i j => i.val + 1 = j.val
        next_eq := fun h h' => Fin.ext (h.symm.trans h')
        prev_eq := fun h h' => Fin.ext (Nat.add_right_cancel (h.trans h'.symm)) }
    ∀ (K : ℕᵒᵖ ⥤ HomologicalComplex AddCommGrpCat.{u} c),
      (K ⋙ eval AddCommGrpCat c 0 ⋙ CategoryTheory.forget AddCommGrpCat).IsMittagLeffler →
      (K ⋙ eval AddCommGrpCat c 1 ⋙ CategoryTheory.forget AddCommGrpCat).IsMittagLeffler →
      (K ⋙ homologyFunctor AddCommGrpCat c 1).IsEssentiallyConstant →
      IsIso (limit.post K (homologyFunctor AddCommGrpCat c 2)) := by
  dsimp only
  intro K h0 h1 hH
  have hp1 := cycleSequence_epi K 0 1
  have hZ1 := ml_middle_of_exact (cycleSequence K 0 1)
    (cycleSequence_exact K 0 1 (by exact ComplexShape.prev_eq' _ (by rfl))) h0 hH
  exact homology_comparison_of_ml_cycles K 1 2
    (ComplexShape.prev_eq' _ (by rfl)) (ComplexShape.next_eq' _ (by rfl)) h1 hZ1

end HomologicalComplex
