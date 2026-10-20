/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction

import Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage
import all Sheaf.AlgebraicGeometry.ProEtaleSupportedReconstruction

/-!
# Supported reconstruction with actual identified-coefficient module functors

Source: Stacks Project, Pro-etale Cohomology, Tag 09AH; Categories, Tag 0037
(blueprint: lem-sfb-proetale-identified-supported-reconstruction).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Two successive support conditions give a unique normalized reconstruction in the
actual sheaf-of-modules presentation. The hypothesis on the open counit is supplied by
`proEtaleIdentifiedOpenClosed` for the complementary closed immersion `e`.

Source: Stacks Project, Tags 09AH and 0037
(blueprint: lem-sfb-proetale-identified-supported-reconstruction).

Proof: the first support condition makes the unit of the specified closed adjunction
invertible, by the closed-essential-image theorem. The open support condition makes the
open counit at the closed restriction invertible. Compose that counit with the image of
the inverse of the prescribed restriction isomorphism, obtaining an invertible map lambda.
Transpose its inverse through the closed adjunction. This is the closed unit followed by
closed direct image of the inverse lambda, hence is invertible. The two triangle
identities give its displayed restriction equation. Conversely, transposing any map
with this restriction equation and cancelling lambda gives its inverse; the closed
adjunction Hom equivalence is injective, proving uniqueness. For naturality the input
compatibility equation and naturality of the open counit give F(b) followed by lambda'
equal to lambda followed by i^*(a). Cancel both invertible lambdas and transpose this
equation through the closed adjunction. Any normalized comparison at A' has exactly the
inverse lambda' as its transpose by the same uniqueness argument. -/
theorem proEtaleIdentifiedSupportedReconstruction
    {X Z S K B : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (k : K ⟶ X) [IsOpenImmersion k] [QuasiCompact k]
    (u : S ⟶ Z) (e : B ⟶ Z)
    (hk : Set.range k = (Set.range i)ᶜ)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (Ri : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (Rs : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (Rk : Sheaf (ProEt.topology K) CommRingCat.{u + 1})
    (Re : Sheaf (ProEt.topology B) CommRingCat.{u + 1})
    (ci : (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R ≅ Ri)
    (cu : (proEtaleSheafInverseImage u CommRingCat.{u + 1}).obj Ri ≅ Rs)
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj R ≅ Rk)
    (ce : (proEtaleSheafInverseImage e CommRingCat.{u + 1}).obj Ri ≅ Re)
    (F : proEtaleRingModules S Rs ⥤ proEtaleRingModules Z Ri)
    (ao : F ⊣ proEtaleRingModulePullback u Ri Rs cu)
    (hopen : ∀ N, IsZero ((proEtaleRingModulePullback e Ri Re ce).obj N) →
      IsIso (ao.counit.app N))
    (A : proEtaleRingModules X R) (M : proEtaleRingModules S Rs)
    (σ : (proEtaleRingModulePullback u Ri Rs cu).obj
      ((proEtaleRingModulePullback i R Ri ci).obj A) ≅ M)
    (hK : IsZero ((proEtaleRingModulePullback k R Rk ck).obj A))
    (hB : IsZero ((proEtaleRingModulePullback e Ri Re ce).obj
      ((proEtaleRingModulePullback i R Ri ci).obj A))) :
    ∃ θ : A ⟶ (proEtaleRingModuleDirectImage i R Ri ci).obj (F.obj M),
      IsIso θ ∧
        (proEtaleRingModulePullback u Ri Rs cu).map
          ((proEtaleRingModulePullback i R Ri ci).map θ ≫
            (proEtaleRingModuleAdjunction i R Ri ci).counit.app (F.obj M)) =
          σ.hom ≫ ao.unit.app M ∧
        (∀ q : A ⟶ (proEtaleRingModuleDirectImage i R Ri ci).obj (F.obj M),
          (proEtaleRingModulePullback u Ri Rs cu).map
            ((proEtaleRingModulePullback i R Ri ci).map q ≫
              (proEtaleRingModuleAdjunction i R Ri ci).counit.app (F.obj M)) =
            σ.hom ≫ ao.unit.app M → q = θ) ∧
        ∀ (A' : proEtaleRingModules X R) (M' : proEtaleRingModules S Rs)
          (σ' : (proEtaleRingModulePullback u Ri Rs cu).obj
            ((proEtaleRingModulePullback i R Ri ci).obj A') ≅ M')
          (_hB' : IsZero ((proEtaleRingModulePullback e Ri Re ce).obj
            ((proEtaleRingModulePullback i R Ri ci).obj A')))
          (q' : A' ⟶ (proEtaleRingModuleDirectImage i R Ri ci).obj (F.obj M')),
          (proEtaleRingModulePullback u Ri Rs cu).map
            ((proEtaleRingModulePullback i R Ri ci).map q' ≫
              (proEtaleRingModuleAdjunction i R Ri ci).counit.app (F.obj M')) =
            σ'.hom ≫ ao.unit.app M' →
          ∀ (a : A ⟶ A') (b : M ⟶ M'),
            (proEtaleRingModulePullback u Ri Rs cu).map
              ((proEtaleRingModulePullback i R Ri ci).map a) ≫ σ'.hom = σ.hom ≫ b →
            a ≫ q' = θ ≫ (proEtaleRingModuleDirectImage i R Ri ci).map (F.map b) := by
  let ac := proEtaleRingModuleAdjunction i R Ri ci
  let P := proEtaleRingModulePullback i R Ri ci
  let G := proEtaleRingModuleDirectImage i R Ri ci
  let H := proEtaleRingModulePullback u Ri Rs cu
  let lam := F.map σ.inv ≫ ao.counit.app (P.obj A)
  have : IsIso (ao.counit.app (P.obj A)) := hopen _ hB
  have : IsIso lam := by dsimp only [lam]; infer_instance
  have : IsIso (ac.unit.app A) :=
    (proEtaleRingModule_closed_essImage_iff_and_unit_isIso i k hk R Ri Rk ci ck A).2 hK
  let θ := ac.unit.app A ≫ G.map (inv lam)
  have hθ : IsIso θ := by dsimp only [θ]; infer_instance
  have ht : P.map θ ≫ ac.counit.app (F.obj M) = inv lam := by
    change (ac.homEquiv _ _).symm ((ac.homEquiv _ _) (inv lam)) = _
    exact (ac.homEquiv _ _).symm_apply_apply _
  have hr : H.map (inv lam) = σ.hom ≫ ao.unit.app M :=
    AlgebraicGeometry.ProEtale.normalized_restrict ao σ
  refine ⟨θ, hθ, ?_, ?_, ?_⟩
  · rw [ht, hr]
  · intro q hq
    apply (ac.homEquiv _ _).symm.injective
    change P.map q ≫ ac.counit.app (F.obj M) = P.map θ ≫ ac.counit.app (F.obj M)
    rw [ht]
    exact AlgebraicGeometry.ProEtale.normalized_unique ao σ _ hq
  · intro A' M' σ' hB' q' hq' a b hab
    let lam' := F.map σ'.inv ≫ ao.counit.app (P.obj A')
    have : IsIso (ao.counit.app (P.obj A')) := hopen _ hB'
    have : IsIso lam' := by dsimp only [lam']; infer_instance
    have ht' : P.map q' ≫ ac.counit.app (F.obj M') = inv lam' :=
      AlgebraicGeometry.ProEtale.normalized_unique ao σ' _ hq'
    have hq'eq : q' = (ac.homEquiv _ _) (inv lam') := by
      apply (ac.homEquiv _ _).symm.injective
      rw [Equiv.symm_apply_apply]
      change P.map q' ≫ ac.counit.app (F.obj M') = inv lam'
      exact ht'
    have hn : F.map b ≫ lam' = lam ≫ P.map a :=
      AlgebraicGeometry.ProEtale.normalized_natural ao σ σ' (P.map a) b hab
    have hn' : P.map a ≫ inv lam' = inv lam ≫ F.map b := by
      apply (cancel_epi lam).1
      simpa only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp,
        Category.comp_id, Category.assoc, IsIso.hom_inv_id_assoc] using
        congrArg (fun t ↦ t ≫ inv lam') hn.symm
    rw [hq'eq]
    change a ≫ (ac.homEquiv _ _) (inv lam') =
      (ac.homEquiv _ _) (inv lam) ≫ G.map (F.map b)
    rw [← ac.homEquiv_naturality_left, ← ac.homEquiv_naturality_right, hn']

end AlgebraicGeometry.Scheme
