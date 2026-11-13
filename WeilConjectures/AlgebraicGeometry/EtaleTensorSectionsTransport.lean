/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections

/-! # Normalized transport of tensor-pullback sections

Source: Stacks Project, Tag 03DR, equation-quasi-coherent-presheaf. -/

@[expose] public section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] tensorPullback tensorPullbackObj
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private noncomputable def sectionsEquiv {Y : Scheme.{u}} {M N : Y.Modules} (k : M ≅ N) :
    Γ(M, ⊤) ≃+ Γ(N, ⊤) where
  toFun := k.hom.app ⊤
  invFun := k.inv.app ⊤
  map_add' := (k.hom.app ⊤).hom.map_add
  left_inv s := by
    change (k.hom ≫ k.inv).app ⊤ s = s
    rw [k.hom_inv_id]
    rfl
  right_inv s := by
    change (k.inv ≫ k.hom).app ⊤ s = s
    rw [k.inv_hom_id]
    rfl

private theorem sectionsEquiv_apply {Y : Scheme.{u}} {M N : Y.Modules} (k : M ≅ N)
    (s : Γ(M, ⊤)) : sectionsEquiv k s = k.hom.app ⊤ s := rfl

private theorem sectionsEquiv_smul {Y : Scheme.{u}} {M N : Y.Modules} (k : M ≅ N)
    (b : Γ(Y, ⊤)) (s : Γ(M, ⊤)) : sectionsEquiv k (b • s) = b • sectionsEquiv k s :=
  Hom.app_smul k.hom b s

attribute [local irreducible] sectionsEquiv

private theorem transportForFamily
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (c : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C),
      L b ⋙ L a ≅ L (a ≫ b))
    (η : ∀ {A B : Scheme.{u}} (a : A ⟶ B) (G : B.Modules),
      Γ(G, ⊤) ⟶ Γ((L a).obj G, ⊤))
    {X : Scheme.{u}} (F : X.Modules) {U V : X.Etale} (a : V ⟶ U) :
    ∃ e : Γ((L a.left).obj ((L U.hom).obj F), ⊤) ≃+
      Γ((L V.hom).obj F, ⊤),
      ∀ (m : Γ((L U.hom).obj F, ⊤)) (b : Γ(V.left, ⊤)),
        e (b • η a.left ((L U.hom).obj F) m) =
          b • (η a.left ((L U.hom).obj F) ≫
            ((c a.left U.hom).hom.app F).app ⊤ ≫
            (eqToHom (congrArg (fun f ↦ (L f).obj F) a.w)).app ⊤) m := by
  let k : (L a.left).obj ((L U.hom).obj F) ≅ (L V.hom).obj F :=
    (c a.left U.hom).app F ≪≫ eqToIso (congrArg (fun f ↦ (L f).obj F) a.w)
  refine ⟨sectionsEquiv k, ?_⟩
  intro m b
  rw [sectionsEquiv_smul, sectionsEquiv_apply]
  congr 1

private theorem restriction_eq {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Etale} (a : V ⟶ U) :
    etaleTensorSectionsRestriction F a =
      tensorSectionsUnit a.left ((tensorPullback U.hom).obj F) ≫
        ((tensorSectionsComp a.left U.hom).hom.app F).app ⊤ ≫
        (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) a.w)).app ⊤ := rfl

/-- Transport from an iterated tensor pullback to the pullback of an etale object,
with the normalized unit equation on global sections (Stacks, Tag 03DR). -/
theorem exists_etaleTensorSectionsTransport {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Etale} (a : V ⟶ U) :
    ∃ e : Γ((tensorPullback a.left).obj ((tensorPullback U.hom).obj F), ⊤) ≃+
      Γ((tensorPullback V.hom).obj F, ⊤),
      ∀ (m : Γ((tensorPullback U.hom).obj F, ⊤)) (b : Γ(V.left, ⊤)),
        e (b • tensorSectionsUnit a.left ((tensorPullback U.hom).obj F) m) =
          b • etaleTensorSectionsRestriction F a m  := by
  have h := transportForFamily (@tensorPullback) (@tensorSectionsComp) (@tensorSectionsUnit) F a
  rw [← restriction_eq F a] at h
  exact h

end AlgebraicGeometry.Scheme.Modules
