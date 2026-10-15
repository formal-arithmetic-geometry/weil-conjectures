/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-!
# Canonically normalized pro-etale module adjunctions

Source: Stacks Project, Modules on Sites, lemma-adjoint-push-pull-modules;
Cohomology on Sites, Tag 07A6 (blueprint: def-weil-pbc-proetale-operations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

set_option backward.isDefEq.respectTransparency.types false in
/-- The unique adjunction whose transpose is the model-site pullback transpose after
precomposition with the tensor unit `m ↦ 1 ⊗ m` and sheafification.
Source: Stacks, lemma-adjoint-push-pull-modules
(blueprint: def-weil-pbc-proetale-operations).
Proof: precompose with the tensor sheafification unit to obtain a map from the
inverse-image module. Transport to the small model; the equivalence on the original
and model sites acts identically on sections. Apply the canonical module pullback
adjunction on that model. This gives the indicated natural Hom equivalence and hence
an adjunction. Pure tensors generate the presheaf tensor and the sheafification unit
is universal, so the displayed formula determines the intermediate map and the Hom
equivalence uniquely. Adjunctions are determined by their Hom equivalences. -/
theorem proEtaleRingModuleAdjunction_existsUnique :
    ∃! adj : proEtaleRingModulePullback f R S c ⊣ proEtaleRingModuleDirectImage f R S c,
      ∀ (M : proEtaleRingModules Y R) (N : proEtaleRingModules X S)
        (h : (proEtaleRingModulePullback f R S c).obj M ⟶ N),
      ∃ g : (SheafOfModules.pullback.{u + 1} (proEtaleModelRingUnit f R)).obj
          ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M) ⟶
          (proEtaleModuleToModel ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))).obj
                ((SheafOfModules.restrictScalars.{u + 1}
                  ((sheafCompose (ProEt.topology X)
                    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).obj N),
        (∀ (W : (proEtaleSiteModel X)ᵒᵖ)
          (m : ((SheafOfModules.pullback.{u + 1} (proEtaleModelRingUnit f R)).obj
            ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M)).val.obj W),
          g.val.app W m = h.val.app (AsSmall.down.op.obj W)
            (((PresheafOfModules.sheafificationAdjunction.{u + 1}
              (𝟙 ((sheafCompose (ProEt.topology X)
                (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)).unit.app
                  (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
                    (J := ProEt.topology X) c.hom
                    ((proEtaleModuleInverseImage f R).obj M))).app
                      (AsSmall.down.op.obj W)
                        ((1 : S.obj.obj (AsSmall.down.op.obj W)) ⊗ₜ[_,
                          (c.hom.hom.app (AsSmall.down.op.obj W)).hom]
                            (@id (((proEtaleModuleInverseImage f R).obj M).val.obj
                              (AsSmall.down.op.obj W)) m)))) ∧
        ∀ (W : Y.ProEtᵒᵖ) (m : M.val.obj W),
          (adj.homEquiv M N h).val.app W m =
            (((SheafOfModules.pullbackPushforwardAdjunction
              (proEtaleModelRingUnit f R)).homEquiv _ _ g).val.app
                (AsSmall.up.op.obj W)) m := by
  sorry

/-- The actual module adjunction, selected from its unique tensor-unit normalization.
Source: Stacks, lemma-adjoint-push-pull-modules
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable def proEtaleRingModuleAdjunction :
    proEtaleRingModulePullback f R S c ⊣ proEtaleRingModuleDirectImage f R S c :=
  Classical.choose (proEtaleRingModuleAdjunction_existsUnique f R S c)

/-- The canonical derived adjunction is induced from the normalized module adjunction.
Source: Stacks, Tag 07A6 and Derived Categories, Tag 0DVC
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable def proEtaleRingDerivedAdjunction :
    proEtaleRingDerivedPullback f R S c ⊣ proEtaleRingDerivedDirectImage f R S c :=
  (proEtaleRingModuleAdjunction f R S c).mapDerivedCategoryRightDerivedAdjunction

end AlgebraicGeometry.Scheme
