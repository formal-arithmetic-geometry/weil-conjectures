/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M7
-/
module

public import Sheaf.Paper.DerivedAutomorphismHomEvaluation
public import Sheaf.Paper.SemilinearSystemModels
import all Sheaf.Paper.WeilCompletedModuleTensorTransport
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax

/-! # Completed coefficient reindexing on tensor representatives -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
open SemilinearSections CategoryTheory.MonoidalCategory
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

/-- Reindexing completed coefficient modules preserves the ordinary tensor, with its
natural pure-tensor normalization. No residue-characteristic hypothesis is required.
Source: blueprint prop-pod-dual-tate-data-compatibility Step 5; Stacks 03EL and 07A4.
(blueprint: lem-pod-completed-ordinary-tensor).
Proof: postcomposition by g and its inverse give inverse equivalences of the pro-etale
sites. Transport the scalar action through the completed coefficient isomorphism,
whose projections are the specified quotient coefficient maps. On presheaf tensors
send x tensor y to x tensor y, using the inverse coefficient isomorphism to check the
balancing relation. The reverse rule is inverse on both pure tensors. The site
equivalence commutes with sheafification by its universal property, so these maps
sheafify to the asserted isomorphisms. Both composites in the naturality equation
send x tensor y to f(x) tensor h(y); generation by local pure tensors proves equality.
The same construction works on the empty site and for zero modules. -/
theorem podCompletedOrdinaryTensor_exists :
    ∃ e : ∀ M N : integralTowerModules l E Y,
      (podCompletedModuleInverseImage l E g).obj
          (ordinaryTensor.{u + 1, u, u} (Scheme.ProEt.topology Y)
            (completedIntegralCommRingSheafUnrestricted l E Y) M N) ≅
        ordinaryTensor.{u + 1, u, u} (Scheme.ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l E X)
          ((podCompletedModuleInverseImage l E g).obj M)
          ((podCompletedModuleInverseImage l E g).obj N),
      (∀ {M M' N N' : integralTowerModules l E Y} (a : M ⟶ M') (b : N ⟶ N'),
        (podCompletedModuleInverseImage l E g).map
            (ordinaryTensorHom.{u + 1, u, u} (Scheme.ProEt.topology Y)
              (completedIntegralCommRingSheafUnrestricted l E Y) a b) ≫
            (e M' N').hom =
          (e M N).hom ≫ ordinaryTensorHom.{u + 1, u, u} (Scheme.ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X)
            ((podCompletedModuleInverseImage l E g).map a)
            ((podCompletedModuleInverseImage l E g).map b)) ∧
      (∀ (M N : integralTowerModules l E Y) (U : X.ProEt)
        (x : M.val.obj (op ((Scheme.proEtaleIsoPostcompose g).obj U)))
        (y : N.val.obj (op ((Scheme.proEtaleIsoPostcompose g).obj U))),
        (e M N).hom.val.app (op U)
          (tensorSection.{u + 1, u, u} (Scheme.ProEt.topology Y)
            (completedIntegralCommRingSheafUnrestricted l E Y) M N
            (op ((Scheme.proEtaleIsoPostcompose g).obj U)) x y) =
          tensorSection.{u + 1, u, u} (Scheme.ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X)
            ((podCompletedModuleInverseImage l E g).obj M)
            ((podCompletedModuleInverseImage l E g).obj N) (op U) x y) := by
  let RX := completedIntegralCommRingSheafUnrestricted l E X
  let RY := completedIntegralCommRingSheafUnrestricted l E Y
  let V := Scheme.proEtaleIsoPostcompose g
  let c := inv (podCompletedRingMap l E g)
  let F := podCompletedModuleInverseImage l E g
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{u} _
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{u} _
  let := SheafOfModules.isMonoidal_W_independentCoefficients RX
  let := SheafOfModules.isMonoidal_W_independentCoefficients RY
  let := SheafOfModules.monoidalCategory RX
  let := SheafOfModules.monoidalCategory RY
  let : V.IsCocontinuous (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) := by
    let he := Scheme.proEtaleIsoPostcompose_equivalence g
    let e : X.ProEt ≌ Y.ProEt := CategoryTheory.Equivalence.mk
      V (Scheme.proEtaleIsoPostcompose (inv g)) he.2.1.some.symm he.2.2.1.some
    exact (e.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2 he.2.2.2.2.some
  obtain ⟨L, hL, _, _⟩ :=
    SheafOfModules.exists_unique_ringedPushforward_laxMonoidal V RX RY c
  let : F.LaxMonoidal := L
  have hi (M N) : IsIso (Functor.LaxMonoidal.μ F M N) :=
    pushforward_tensor_isIso V RX RY c (fun U ↦ by
      change IsIso (c.hom.app U)
      infer_instance) L hL M N
  let t (M N) := @asIso _ _ _ _ (Functor.LaxMonoidal.μ F M N) (hi M N)
  refine ⟨fun M N ↦ (t M N).symm, ?_, ?_⟩
  · intro M M' N N' a b
    change F.map (a ⊗ₘ b) ≫ (t M' N').inv =
      (t M N).inv ≫ (F.map a ⊗ₘ F.map b)
    apply (cancel_epi (t M N).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    change Functor.LaxMonoidal.μ F M N ≫ F.map (a ⊗ₘ b) ≫
      (t M' N').inv = _
    rw [← Functor.LaxMonoidal.μ_natural_assoc]
    change (F.map a ⊗ₘ F.map b) ≫ (t M' N').hom ≫ (t M' N').inv = _
    simp
  · intro M N U x y
    have h := hL M N (op U) x y
    have h' := congrArg ((t M N).inv.val.app (op U)) h
    have hc := congrArg (fun f ↦ f.val.app (op U)
      (tensorSection.{u + 1, u, u} (Scheme.ProEt.topology X) RX
        (F.obj M) (F.obj N) (op U) x y)) (t M N).hom_inv_id
    exact h'.symm.trans hc


end WeilConjectures
