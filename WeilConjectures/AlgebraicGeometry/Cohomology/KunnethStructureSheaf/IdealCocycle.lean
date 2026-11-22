/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Kunneth
public import WeilConjectures.AlgebraicGeometry.Cohomology.KunnethStructureSheaf.CechComap
public import WeilConjectures.AlgebraicGeometry.TheoremOfCube.Slices

/-!
# Čech cocycles of `𝒪` vanishing on two slices

Let `X`, `Y` be schemes over a field `K` with `K`-points `x`, `y` and let `i : X ⟶ X ×_K Y`,
`j : Y ⟶ X ×_K Y` be the base changes of `y` and `x`. A Čech `1`-cocycle of `𝒪_{X ×_K Y}`, for
a product of finite affine covers, which vanishes on both slices takes values in the ideal
`pr_X⁻¹ I_x ⊓ pr_Y⁻¹ I_y`; by the Künneth argument it is a coboundary if `I_x` and `I_y` have
no nonzero global sections.

## Main statements

- `AlgebraicGeometry.Scheme.exists_cechComplex_d_eq_of_unitToPushforwardObjUnit_eq_zero`
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

open IdealSheafData.Kunneth

variable {K : Type u} [Field K] {X Y : Scheme.{u}} [X.Over (Spec (.of K))]
  [Y.Over (Spec (.of K))]

/-- Let `x`, `y` be `K`-points of `X`, `Y` whose ideal sheaves have no nonzero global
sections, and let `i : X ⟶ X ×_K Y`, `j : Y ⟶ X ×_K Y` be the base changes of `y` and `x` along
the projections. For finite affine covers `Ux`, `Vy` of `X`, `Y` with affine pairwise
intersections, whose product cover `W` of `X ×_K Y` has affine finite intersections, every
Čech `1`-cocycle of `𝒪` for `W` killed by `i^♯` and `j^♯` is a coboundary. -/
lemma exists_cechComplex_d_eq_of_unitToPushforwardObjUnit_eq_zero {α β : Type u} [Finite α]
    [Finite β] (Ux : α → X.Opens) (Vy : β → Y.Opens) (hUx : ∀ a, IsAffineOpen (Ux a))
    (hVy : ∀ b, IsAffineOpen (Vy b)) (hUx₂ : ∀ a a', IsAffineOpen (Ux a ⊓ Ux a'))
    (hVy₂ : ∀ b b', IsAffineOpen (Vy b ⊓ Vy b')) (hUcov : iSup Ux = ⊤) (hVcov : iSup Vy = ⊤)
    (hW : ∀ (k : ℕ) (q : Fin (k + 1) → α × β),
      IsAffineOpen (⨅ l, prodOpen K X Y (Ux (q l).1) (Vy (q l).2)))
    (x : Spec (.of K) ⟶ X) [IsClosedImmersion x] (y : Spec (.of K) ⟶ Y) [IsClosedImmersion y]
    (hI : ∀ s ∈ x.ker.idealOfOpens ⊤, s = 0) (hI' : ∀ s ∈ y.ker.idealOfOpens ⊤, s = 0)
    (i : X ⟶ prod K X Y) (j : Y ⟶ prod K X Y)
    (hi : IsPullback i (X ↘ Spec (.of K)) (prodSnd K X Y) y)
    (hj : IsPullback j (Y ↘ Spec (.of K)) (prodFst K X Y) x)
    (c : TopCat.Presheaf.CechCochain (fun p : α × β ↦ prodOpen K X Y (Ux p.1) (Vy p.2))
      (prod K X Y).unitPresheaf 1)
    (hc : ((TopCat.Presheaf.cechComplex (fun p : α × β ↦ prodOpen K X Y (Ux p.1) (Vy p.2))).obj
      (prod K X Y).unitPresheaf).d 1 2 c = 0)
    (hci : ((TopCat.Presheaf.cechComplex (fun p : α × β ↦ prodOpen K X Y (Ux p.1) (Vy p.2))).map
      ((SheafOfModules.toSheaf _).map
        (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)).hom).f 1 c = 0)
    (hcj : ((TopCat.Presheaf.cechComplex (fun p : α × β ↦ prodOpen K X Y (Ux p.1) (Vy p.2))).map
      ((SheafOfModules.toSheaf _).map
        (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)).hom).f 1 c = 0) :
    ∃ b, ((TopCat.Presheaf.cechComplex (fun p : α × β ↦ prodOpen K X Y (Ux p.1) (Vy p.2))).obj
      (prod K X Y).unitPresheaf).d 0 1 b = c := by
  let W : α × β → (prod K X Y).Opens := fun p ↦ prodOpen K X Y (Ux p.1) (Vy p.2)
  let J := prodIdeal (K := K) x.ker y.ker
  have : IsClosedImmersion i := MorphismProperty.of_isPullback hi.flip inferInstance
  have : IsClosedImmersion j := MorphismProperty.of_isPullback hj.flip inferInstance
  let c' (q : Fin 2 → α × β) : Γ(prod K X Y, ⨅ l, W (q l)) := c q
  have hmem (q : Fin 2 → α × β) : c' q ∈ J.idealOfOpens (⨅ l, W (q l)) := by
    have hV : (⨅ l, W (q l)) ∈ (prod K X Y).affineOpens := hW 1 q
    have h : c' q ∈ (j.ker ⊓ i.ker).idealOfOpens (⨅ l, W (q l)) := by
      rw [IdealSheafData.idealOfOpens_eq_ideal _ ⟨_, hV⟩, IdealSheafData.ideal_inf]
      refine Ideal.mem_inf.2 ⟨?_, ?_⟩
      · rw [Hom.ker_apply, RingHom.mem_ker]
        exact (congrFun hcj q).trans (Pi.zero_apply _)
      · rw [Hom.ker_apply, RingHom.mem_ker]
        exact (congrFun hci q).trans (Pi.zero_apply _)
    rwa [hj.ker_fst_eq_comap, hi.ker_fst_eq_comap] at h
  have hlift (q : Fin 2 → α × β) : ∃ a : Γ(J.toModules, ⨅ l, W (q l)),
      J.toModulesι.app _ a = c' q := by
    have h := hmem q
    rw [← SetLike.mem_coe, ← IdealSheafData.range_toModulesι_app_eq_idealOfOpens] at h
    exact h
  choose t ht using hlift
  let ιC := (TopCat.Presheaf.cechComplex W).map
    ((SheafOfModules.toSheaf _).map J.toModulesι).hom
  have hιt : ιC.f 1 t = c := funext ht
  have hdt : ((TopCat.Presheaf.cechComplex W).obj
      ((SheafOfModules.toSheaf _).obj J.toModules).obj).d 1 2 t = 0 := by
    have h : ιC.f 2 (((TopCat.Presheaf.cechComplex W).obj
        ((SheafOfModules.toSheaf _).obj J.toModules).obj).d 1 2 t) =
        ((TopCat.Presheaf.cechComplex W).obj (prod K X Y).unitPresheaf).d 1 2 (ιC.f 1 t) :=
      (ConcreteCategory.congr_hom (ιC.comm 1 2) t).symm
    rw [hιt, hc] at h
    funext q
    exact J.injective_toModulesι_app _ ((congrFun h q).trans (map_zero _).symm)
  have hex := exactAt_one_cechComplex_prodIdeal (K := K) x.ker y.ker Ux Vy hUx hVy hUx₂ hVy₂
    hUcov hVcov hI hI'
  obtain ⟨b, hb⟩ := (TopCat.Presheaf.exactAt_cechComplex_iff W _ 0).1 hex t hdt
  refine ⟨ιC.f 0 b, ?_⟩
  have h : ((TopCat.Presheaf.cechComplex W).obj (prod K X Y).unitPresheaf).d 0 1 (ιC.f 0 b) =
      ιC.f 1 (((TopCat.Presheaf.cechComplex W).obj
        ((SheafOfModules.toSheaf _).obj J.toModules).obj).d 0 1 b) :=
    ConcreteCategory.congr_hom (ιC.comm 0 1) b
  rw [h]
  exact (congrArg (ιC.f 1) hb).trans hιt

end AlgebraicGeometry.Scheme
