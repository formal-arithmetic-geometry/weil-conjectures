/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PrescribedPointSystemData
import WeilConjectures.DeligneLaumon.BertiniSections
import WeilConjectures.AlgebraicGeometry.PrescribedPointInfinitesimalModel
import WeilConjectures.AlgebraicGeometry.ProjectiveTwistRestrictionSurjective
import WeilConjectures.AlgebraicGeometry.GeneratingSystemOpenTransport

/-!
# High-degree prescribed first-order linear systems

Source: Stacks Project, Tags 0FD5 and 0B5T, and the finite first-neighbourhood argument
in blueprint main-20261015, finite-cover-curve proof, paragraph 2.
(blueprint: lem-zl-prescribed-point-eventual-jet-system).
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules MonoidalCategory

noncomputable section

attribute [local irreducible] prescribedPointJet prescribedPointRestrictedFamily
  prescribedPointCombination prescribedPointVanishes tensorPullback Scheme.Modules.pullback

private noncomputable def sectionsIsoLinearEquiv
    {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
    {M P : Y.Modules} (e : M ≅ P) :
    letI : Module k Γ(M, ⊤) := Module.compHom _
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom
    let : Module k Γ(P, ⊤) := Module.compHom _
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom
    Γ(M, ⊤) ≃ₗ[k] Γ(P, ⊤) := by
  letI : Module k Γ(M, ⊤) := Module.compHom _
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom
  let : Module k Γ(P, ⊤) := Module.compHom _
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom
  exact
    { toFun := e.hom.app ⊤
      invFun := e.inv.app ⊤
      left_inv := fun v ↦ by
        change (e.hom ≫ e.inv).app ⊤ v = v
        rw [e.hom_inv_id]
        rfl
      right_inv := fun v ↦ by
        change (e.inv ≫ e.hom).app ⊤ v = v
        rw [e.inv_hom_id]
        rfl
      map_add' := fun a b ↦ map_add (e.hom.app ⊤).hom a b
      map_smul' := fun a v ↦ Hom.app_smul e.hom _ v }

private theorem kernel_iso_iff {Y Z : Scheme.{u}} (i : Z ⟶ Y)
    {M P : Y.Modules} (e : M ≅ P) (v : Γ(M, ⊤)) :
    pullbackΓ i P (e.hom.app ⊤ v) = 0 ↔ pullbackΓ i M v = 0 := by
  rw [← pullbackΓ_naturality]
  constructor
  · intro h
    have h' := congrArg (((Scheme.Modules.pullback i).map e.inv).app ⊤) h
    change (((Scheme.Modules.pullback i).map e.hom ≫ (Scheme.Modules.pullback i).map e.inv).app ⊤)
      (pullbackΓ i M v) = _ at h'
    rw [← Functor.map_comp, e.hom_inv_id, (Scheme.Modules.pullback i).map_id] at h'
    simpa only [Hom.id_app, ConcreteCategory.id_apply, map_zero] using h'
  · intro h
    rw [h, map_zero]

set_option maxHeartbeats 1500000 in
-- One construction combines the finite kernel basis, adjunction comparisons and jet lifts.
/-- The kernel system eventually generates off a finite set, immerses its complement,
and separates simultaneous first-order values. No smoothness or dimension assumption
is required here.

Source: Stacks Project, Tags 0FD5 and 0B5T; blueprint main-20261015,
finite-cover-curve proof, paragraph 2.
(blueprint: lem-zl-prescribed-point-eventual-jet-system).

Proof: Let L be the pullback of O(1). The closed projective embedding makes it very
ample; its n-th tensor power is canonically isomorphic to the pullback of O(n).
Form the reduced closed subscheme Z supported on the images of S. These images are
closed, since X and Y are finite type over the algebraically closed field and the
points of S are closed. Its ideal I and I squared are coherent on the Noetherian
scheme Y. Tag 0FD5 gives eventual generation and immersion for the kernel of
restriction to Z. The residue-fibre vanishing test is exactly that kernel. Choose a
finite basis, using finite-dimensionality of proper coherent global sections.

Tensor 0 -> I squared -> I -> I/I squared -> 0 with L to the n-th power.
Serre vanishing for I squared makes the map of global sections onto the quotient
surjective for all sufficiently large n. The quotient sheaf is supported on Z;
its global sections are the product of its stalks, by extension by zero from an
open excluding the other points. The stalk at x is the cotangent space tensored
with the line-bundle stalk. The quotient map sends a vanishing section to the
stated jet: in a frame its coefficient a maps to [a] tensor the frame generator.
Thus it is the simultaneous jet map, independently of the frame. Enlarge the
bound for both applications and transport the basis, generation and immersion
along the tensor-power isomorphisms and the open immersion X minus S -> Y minus Z.
-/
theorem exists_eventual_prescribedPoint_jetSystem
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (S : Finset X) (hS : S.Nonempty) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (N : ℕ) (Y : Scheme.{u}) [IsReduced Y]
    (c : Y ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))) [IsClosedImmersion c]
    (j : X ⟶ Y) [IsOpenImmersion j] (hdense : DenseRange j)
    (hchart : Set.range j = c ⁻¹' (ProjectiveSpace.standardOpen
      (ULift.{u} (Fin (N + 1))) (Spec (.of k)) ⟨0⟩ : Set _))
    (hover : j ≫ c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)) =
      X ↘ Spec (.of k)) :
    ∃ (n₀ : ℕ) (U : X.Opens),
      (∀ x : X, x ∈ U ↔ x ∉ S) ∧
      ∀ n : ℕ, n₀ ≤ n →
        ∃ (I : Type u) (_ : Fintype I) (s : I → Γ(prescribedPointTwist c n, ⊤)),
          (∀ v : Γ(prescribedPointTwist c n, ⊤),
            prescribedPointVanishes ((tensorPullback j).obj (prescribedPointTwist c n)) S
                (tensorSectionsUnit j (prescribedPointTwist c n) v) ↔
              ∃! a : I → k, prescribedPointCombination
                (c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)))
                (prescribedPointTwist c n) s a = v) ∧
          (∃ ht : Epi ((((tensorPullback (U.ι ≫ j)).obj
              (prescribedPointTwist c n)).freeHomEquiv).symm
                (prescribedPointRestrictedFamily (prescribedPointTwist c n) j U s)),
            IsImmersion (@ProjectiveSpace.homOfGeneratingSections I inferInstance
              U.toScheme (Spec (.of k)) (U.ι ≫ (X ↘ Spec (.of k)))
              ((tensorPullback (U.ι ≫ j)).obj (prescribedPointTwist c n))
              ((@id (∀ L : Y.Modules, L.IsInvertible → _)
                (invertible_pullback_tensor (U.ι ≫ j)).1) (prescribedPointTwist c n)
                ((invertible_pullback_tensor c).1 (ProjectiveSpace.twist _ _ (n : ℤ))).2).2
              (prescribedPointRestrictedFamily (prescribedPointTwist c n) j U s) ht)) ∧
          Function.Surjective (fun a : I → k ↦ fun x : S ↦
            @prescribedPointJet X ((tensorPullback j).obj (prescribedPointTwist c n))
              ((@id (∀ L : Y.Modules, L.IsInvertible → _)
                (invertible_pullback_tensor j).1) (prescribedPointTwist c n)
                ((invertible_pullback_tensor c).1 (ProjectiveSpace.twist _ _ (n : ℤ))).2).2
              x.val
              (tensorSectionsUnit j (prescribedPointTwist c n)
                (prescribedPointCombination
                  (c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)))
                  (prescribedPointTwist c n) s a))) := by
  classical
  have _ := hS
  have _ := hdense
  have _ := hchart
  let f := c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k))
  let : Y.Over (Spec (.of k)) := ⟨f⟩
  have : IsProper (Y ↘ Spec (.of k)) := by
    change IsProper f
    dsimp only [f]
    infer_instance
  obtain ⟨Z, W, i, w, hi, hw, hrange, hfinite, _hsquare, hmodel⟩ :=
    exists_prescribedPoint_infinitesimalModel j hover S hclosed
  let : IsClosedImmersion i := hi
  let : IsClosedImmersion w := hw
  let L := (Scheme.Modules.pullback c).obj (ProjectiveSpace.twist
    (ULift.{u} (Fin (N + 1))) (Spec (.of k)) 1)
  have : L.IsInvertible := inferInstance
  have hvery : IsVeryAmple f L :=
    ⟨ULift.{u} (Fin (N + 1)), c, inferInstance, inferInstance, rfl, ⟨Iso.refl _⟩⟩
  have hample : IsAmple f L := ⟨inferInstance, 1, Nat.one_pos,
    hvery.of_iso (ρ_ L).symm⟩
  obtain ⟨a, V, hV, hsystems⟩ := exists_eventual_immersion_vanishingSections k L hample i
  obtain ⟨b, hres⟩ := exists_eventual_projectiveTwist_restriction_surjective c w hfinite
  let U := j ⁻¹ᵁ V
  refine ⟨max a b, U, ?_, ?_⟩
  · intro x
    change j x ∈ V ↔ x ∉ S
    rw [hV, hrange]
    constructor
    · intro hx hxS
      exact hx ⟨x, hxS, rfl⟩
    · rintro hx ⟨y, hy, heq⟩
      have hxy : y = x := j.isOpenEmbedding.injective heq
      exact hx (hxy ▸ hy)
  intro n hn
  obtain ⟨Vn, I, hI, s, t, hkernel, hspan, hlin, hvalue, ht, himm⟩ :=
    hsystems n ((le_max_left a b).trans hn)
  have : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let P := prescribedPointTwist c n
  have : P.IsInvertible :=
    ((invertible_pullback_tensor c).1 (ProjectiveSpace.twist
      (ULift.{u} (Fin (N + 1))) (Spec (.of k)) (n : ℤ))).2
  let adj : tensorPullback c ⊣ Scheme.Modules.pushforward c :=
    Classical.choose (exists_tensorPullbackAdjunction c)
  let cmp : tensorPullback c ≅ Scheme.Modules.pullback c :=
    adj.leftAdjointUniq (pullbackPushforwardAdjunction c)
  let epow := (nonempty_pullback_tensorPow_iso c (ProjectiveSpace.twist
    (ULift.{u} (Fin (N + 1))) (Spec (.of k)) 1) n).some
  let etwist := (ProjectiveSpace.nonempty_tensorPow_twist_one_iso
    (ULift.{u} (Fin (N + 1))) (Spec (.of k)) n).some
  let e : L.tensorPow n ≅ P :=
    epow.symm ≪≫ (Scheme.Modules.pullback c).mapIso etwist ≪≫ (cmp.app (ProjectiveSpace.twist
      (ULift.{u} (Fin (N + 1))) (Spec (.of k)) (n : ℤ))).symm
  let s' : I → Γ(P, ⊤) := fun z ↦ e.hom.app ⊤ ((s z).val (op ⊤))
  have hPj : ((tensorPullback j).obj P).IsInvertible :=
    ((invertible_pullback_tensor j).1 P).2
  have hPU : ((tensorPullback (U.ι ≫ j)).obj P).IsInvertible :=
    ((invertible_pullback_tensor (U.ι ≫ j)).1 P).2
  have hvan_iff (v : Γ(L.tensorPow n, ⊤)) :
      prescribedPointVanishes ((tensorPullback j).obj P) S
        (tensorSectionsUnit j P (e.hom.app ⊤ v)) ↔ v ∈ Vn := by
    rw [← (hmodel P).1, kernel_iso_iff, ← hkernel]
  let : Module k Γ(L.tensorPow n, ⊤) := Module.compHom _
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom
  let : Module k Γ(P, ⊤) := Module.compHom _
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom
  let s0 : I → Γ(L.tensorPow n, ⊤) := fun q ↦ (s q).val (op ⊤)
  change Submodule.span k (Set.range s0) = Vn at hspan
  change LinearIndependent k s0 at hlin
  let E : Γ(L.tensorPow n, ⊤) ≃ₗ[k] Γ(P, ⊤) := sectionsIsoLinearEquiv f e
  have hcomb (z : I → k) : prescribedPointCombination f P s' z =
      E (∑ q, z q • s0 q) := by
    unfold prescribedPointCombination
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro q _
    exact (E.map_smul (z q) (s0 q)).symm
  have hcoeff (v : Γ(P, ⊤)) :
      prescribedPointVanishes ((tensorPullback j).obj P) S (tensorSectionsUnit j P v) ↔
        ∃! z : I → k, prescribedPointCombination f P s' z = v := by
    constructor
    · intro hv
      have hvV : E.symm v ∈ Vn := (hvan_iff (E.symm v)).mp
        (by
          change prescribedPointVanishes ((tensorPullback j).obj P) S
            (tensorSectionsUnit j P (E (E.symm v)))
          rw [E.apply_symm_apply]
          exact hv)
      rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at hvV
      obtain ⟨z, hz⟩ := hvV
      have hrep : prescribedPointCombination f P s' z = v := by
        rw [hcomb, hz, E.apply_symm_apply]
      refine ⟨z, hrep, ?_⟩
      intro z' hz'
      apply hlin.fintypeLinearCombination_injective
      apply E.injective
      change E (∑ q, z' q • s0 q) =
        E (∑ q, z q • s0 q)
      rw [← hcomb, ← hcomb, hz', hrep]
    · rintro ⟨z, hz, _⟩
      have hzV : (∑ q, z q • s0 q) ∈ Vn := by
        rw [← hspan, Submodule.mem_span_range_iff_exists_fun]
        exact ⟨z, rfl⟩
      have hv := (hvan_iff (∑ q, z q • s0 q)).mpr hzV
      change prescribedPointVanishes ((tensorPullback j).obj P) S
        (tensorSectionsUnit j P (E (∑ q, z q •
          s0 q))) at hv
      simpa only [← hcomb, hz] using hv
  obtain ⟨ht', himm'⟩ := generatingSystem_open_transport f j V (L.tensorPow n) P e I s t
    hvalue ht himm hPU
  refine ⟨I, inferInstance, s', hcoeff, ?_, ?_⟩
  · exact ⟨ht', by simpa only [f, Category.assoc, hover] using himm'⟩
  · intro jets
    obtain ⟨q, hq⟩ := (hmodel P).2 hPj jets
    obtain ⟨v, hv⟩ := hres n ((le_max_right a b).trans hn) q
    obtain ⟨hvS, hvjets⟩ := hq v hv
    obtain ⟨z, hz, _⟩ := (hcoeff v).mp hvS
    refine ⟨z, ?_⟩
    funext x
    change @prescribedPointJet X ((tensorPullback j).obj P) hPj x.val
      (tensorSectionsUnit j P (prescribedPointCombination f P s' z)) = jets x
    rw [hz]
    exact hvjets x

end

end AlgebraicGeometry
