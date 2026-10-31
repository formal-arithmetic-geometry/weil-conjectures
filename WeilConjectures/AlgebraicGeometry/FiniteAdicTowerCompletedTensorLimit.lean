/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedConstantRealizationDataSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedConstantSheafReductionSupplement
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # The completed-linear comparison for a standard finite adic tower

Source: latest blueprint, smooth-proper purity, Step 1, Passage to the limit
(blueprint: lem-zl-finite-adic-tower-completed-tensor-limit). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.FiniteLocalSystemLimit
open Scheme

private theorem complete_base_normalized (Y : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) [IsAdicComplete I A] :
    let e := AdicCompletion.ofAlgEquiv I
    let φ := (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom e.symm.toRingHom) ≫ CompletedConstantReduction.base Y I
    (∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem Y I) (op n) =
      (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom)) ∧
    completedConstantBaseMap Y I φ = CompletedConstantReduction.base Y I := by
  let e := AdicCompletion.ofAlgEquiv I
  let S := constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}
  let a := CompletedConstantReduction.base Y I
  have ha (n : ℕ) : a ≫ limit.π (adicLisseRingSystem Y I) (op n) =
      S.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) :=
    (CompletedConstantReduction.base_exists Y I).choose_spec.1 n
  constructor
  · intro n
    change (S.map (CommRingCat.ofHom e.symm.toRingHom) ≫ a) ≫ _ = _
    rw [Category.assoc, ha, ← S.map_comp]
    apply congrArg S.map
    apply CommRingCat.hom_ext
    ext x
    exact AdicCompletion.mk_ofAlgEquiv_symm I (n + 1) x
  · change S.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A))) ≫
      (S.map (CommRingCat.ofHom e.symm.toRingHom) ≫ a) = a
    rw [← Category.assoc, ← S.map_comp]
    have he : (CommRingCat.ofHom (algebraMap A (AdicCompletion I A))) ≫
        CommRingCat.ofHom e.symm.toRingHom = 𝟙 (CommRingCat.of A) := by
      apply CommRingCat.hom_ext
      ext x
      exact e.symm_apply_apply x
    rw [he, S.map_id, Category.id_comp]


private theorem complete_module_finite
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    (N : ModuleCat.{u + 1} A) (hN : Module.Finite A N) :
    Module.Finite (AdicCompletion I A)
      ((ModuleCat.restrictScalars (AdicCompletion.ofAlgEquiv I).symm.toRingHom).obj N) := by
  let C := AdicCompletion I A
  let e : A ≃+* C := (AdicCompletion.ofAlgEquiv I).toRingEquiv
  let N' := (ModuleCat.restrictScalars e.symm.toRingHom).obj N
  let : Module.Finite A N := hN
  let q : N →ₛₗ[e.toRingHom] N' :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a x ↦ by
        change a • x = e.symm (e a) • x
        rw [e.symm_apply_apply] }
  exact Module.Finite.of_surjective q Function.surjective_id


private def complete_module_restriction_iso
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    (N : ModuleCat.{u + 1} A) :
    (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
      ((ModuleCat.restrictScalars (AdicCompletion.ofAlgEquiv I).symm.toRingHom).obj N) ≅ N :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (AdicCompletion.ofAlgEquiv I).toRingEquiv).counitIso.app N

private theorem complete_module_restriction_iso_hom
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    (N : ModuleCat.{u + 1} A) (x : N) :
    (complete_module_restriction_iso I N).hom x = x := by
  rfl


private def quotient_iso {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) {M N : ModuleCat.{u + 1} A} (e : M ≅ N) (n : ℕ) :
    ModuleCat.of A (M ⧸ (I ^ (n + 1) • ⊤ : Submodule A M)) ≅
      ModuleCat.of A (N ⧸ (I ^ (n + 1) • ⊤ : Submodule A N)) where
  hom := completedConstantQuotientMap I e.hom n
  inv := completedConstantQuotientMap I e.inv n
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change Submodule.Quotient.mk (e.inv (e.hom x)) = Submodule.Quotient.mk x
      congr 1
      exact ConcreteCategory.congr_hom e.hom_inv_id x
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change Submodule.Quotient.mk (e.hom (e.inv x)) = Submodule.Quotient.mk x
      congr 1
      exact ConcreteCategory.congr_hom e.inv_hom_id x

private def adic_module_system_iso (Y : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    {M N : ModuleCat.{u + 1} A} (e : M ≅ N) :
    adicLisseModuleSystem Y I M ≅ adicLisseModuleSystem Y I N := by
  let E (n : ℕ) := (adicLisseConstantModules Y A).mapIso (quotient_iso I e n)
  let f : adicLisseModuleSystem Y I M ⟶ adicLisseModuleSystem Y I N :=
    NatTrans.ofOpSequence (fun n ↦ (E n).hom) (fun n ↦ by
      change (adicLisseModuleSystem Y I M).map (homOfLE (Nat.le_succ n)).op ≫ _ =
        _ ≫ (adicLisseModuleSystem Y I N).map (homOfLE (Nat.le_succ n)).op
      simp only [adicLisseModuleSystem, Functor.ofOpSequence_map_homOfLE_succ,
        E, Functor.mapIso_hom]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | _ x => rfl)
  exact NatIso.ofComponents (fun n ↦ E n.unop) (fun g ↦ f.naturality g)

private def complete_module_completed_iso (Y : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    (N : ModuleCat.{u + 1} A) :
    adicLisseCompletedModule Y I
      (completedConstantUnderlyingModule I
        ((ModuleCat.restrictScalars (AdicCompletion.ofAlgEquiv I).symm.toRingHom).obj N)) ≅
      adicLisseCompletedModule Y I N :=
  lim.mapIso (adic_module_system_iso Y I (complete_module_restriction_iso I N))


private def adic_quotient_cone {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (N : ModuleCat.{u + 1} A) :
    Cone (Functor.ofOpSequence
      (X := fun n : ℕ ↦ ModuleCat.of A (N ⧸ (I ^ (n + 1) • ⊤ : Submodule A N)))
      (fun n ↦ ModuleCat.ofHom (Submodule.factorPowSucc I N (n + 1)))) where
  pt := N
  π := NatTrans.ofOpSequence
    (fun n ↦ ModuleCat.ofHom (Submodule.mkQ (I ^ (n + 1) • ⊤ : Submodule A N)))
    (by
      intro n
      simp only [Functor.const_obj_map, Functor.ofOpSequence_map_homOfLE_succ]
      apply ModuleCat.hom_ext
      ext x
      rfl)

private def adic_tensor_comparison {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (N : ModuleCat.{u + 1} A)
    {C : Type v} [Category* C] [HasLimitsOfShape ℕᵒᵖ C]
    (K : ModuleCat.{u + 1} A ⥤ C) :
    K.obj N ⟶ limit ((Functor.ofOpSequence
      (X := fun n : ℕ ↦ ModuleCat.of A (N ⧸ (I ^ (n + 1) • ⊤ : Submodule A N)))
      (fun n ↦ ModuleCat.ofHom (Submodule.factorPowSucc I N (n + 1)))) ⋙ K) :=
  limit.lift _ (K.mapCone (adic_quotient_cone I N))

private theorem adic_tensor_comparison_π {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (N : ModuleCat.{u + 1} A)
    {C : Type v} [Category* C] [HasLimitsOfShape ℕᵒᵖ C]
    (K : ModuleCat.{u + 1} A ⥤ C) (n : ℕ) :
    adic_tensor_comparison I N K ≫ limit.π _ (op n) =
      K.map (ModuleCat.ofHom (Submodule.mkQ (I ^ (n + 1) • ⊤ : Submodule A N))) :=
  limit.lift_π (K.mapCone (adic_quotient_cone I N)) (op n)

/-- Completed scalar extension of a finite module is the completed-linear limit
of the extensions of its standard adic quotients.
Source: blueprint latest, smooth-proper purity, Step 1, Passage to the limit
(blueprint: lem-zl-finite-adic-tower-completed-tensor-limit).

Proof: the complete Noetherian ring A identifies with its adic completion by
the canonical completion map. The private complete_base_normalized proves the
finite projection identities for the map from constant completion scalars and
identifies its constant-A base map with the prescribed base map. Transport N
to a finite module over that ring using complete_module_finite. The private
complete_module_restriction_iso identifies its underlying A-module with N;
its homomorphism is the identity on elements. The private quotient_iso and
adic_module_system_iso transport that isomorphism through the actual quotient
tower and its successor maps. Taking its limit gives complete_module_completed_iso.
The normalized completed finite-module comparison gives an isomorphism from
its completed realization to the limit of its constant quotient sheaves,
after restriction to constant A. For modules over A/I^(n+1), the natural
quotient tensor comparison is an isomorphism on the rank-one free module by
the flat quotient theorem. Both
functors preserve colimits, so the proved upstream ModuleCat.isIso_app_of_rankOne
(CocontinuousGenerator.lean) makes it an isomorphism for every quotient module.
Thus each constant quotient sheaf identifies with the restriction of
K(N/I^(n+1)N).
The identifications commute with quotient maps by their pure-tensor formula.
The private adic_quotient_cone constructs the actual quotient maps from N,
and adic_tensor_comparison maps this cone by K and takes its limit lift.
Its projection formula is adic_tensor_comparison_π. In particular the map is
linear over completed scalars from its construction. After restriction of
scalars, the preceding quotient identifications and their generator formulas
identify it with the normalized completed finite-module comparison by testing
every finite projection. That comparison is invertible. Restriction of scalars
preserves limits and reflects isomorphisms, so the canonical completed-linear
comparison is invertible as well. Invert it to obtain the displayed orientation.
This includes zero modules and torsion summands. -/
theorem finite_adic_tower_completed_tensor_limit
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A]
    (π : A) [IsAdicComplete (Ideal.span ({π} : Set A)) A] (Y : Scheme.{u})
    (N : ModuleCat.{u + 1} A) (_hN : Module.Finite A N) :
    let I := Ideal.span ({π} : Set A)
    let D := Functor.ofOpSequence
      (X := fun n : ℕ ↦ ModuleCat.of A (N ⧸ (I ^ (n + 1) • ⊤ : Submodule A N)))
      (fun n ↦ ModuleCat.ofHom (Submodule.factorPowSucc I N (n + 1)))
    let K := adicLisseConstantModules Y A ⋙ completedConstantExtension Y
      (CompletedConstantReduction.base Y I)
    Nonempty (limit (D ⋙ K) ≅ K.obj N) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteLocalSystemLimit
