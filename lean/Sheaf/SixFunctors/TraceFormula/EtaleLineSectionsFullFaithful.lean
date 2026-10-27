/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q38, R2
-/
module

public import Sheaf.SixFunctors.TraceFormula.SchemeEtaleLineDefinitions
import Sheaf.AlgebraicGeometry.EtaleExtensionFreePresentationsHom

/-! Auxiliary comparison for the canonical étale line-section functor. -/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme


private noncomputable def liftLinearIso {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R}
    (e : (SheafOfModules.toSheaf R).obj M ≅ (SheafOfModules.toSheaf R).obj N)
    (h : ∀ (U : Cᵒᵖ) (r : R.obj.obj U) (s : M.val.obj U),
      e.hom.hom.app U (r • s) = r • (@id (N.val.obj U) (e.hom.hom.app U s))) : M ≅ N := by
  apply (SheafOfModules.fullyFaithfulForget R).preimageIso
  refine PresheafOfModules.isoMk (fun U ↦ ModuleCat.isoMk
    (((sheafToPresheaf J AddCommGrpCat).mapIso e).app U) ?_) ?_
  · intro r
    ext s
    exact (h U r s).symm
  · intro U V f
    ext s
    exact ConcreteCategory.congr_hom (e.hom.hom.naturality f) s

/-- Full faithfulness of any line-section functor with the canonical scalar and map formulas.
Source: Stacks Project, Descent, Tag 03DX (2), full faithfulness; Tag 03DV (2).
(blueprint: lem-trf-etale-line-sections-full-faithful).

Proof: use the Hom bijection for quasi-coherent tensor extension from
`lem-trf-etale-extension-free-presentations-hom`. Invertible modules are quasi-coherent.
Its additive identification with tensor sections and alpha give linear isomorphisms
between extension and A, since both respect the displayed scalar actions. The map
formulas make these isomorphisms natural in every module map. Conjugation by these
isomorphisms identifies the Hom map of A with the bijective extension Hom map.
The full subcategories retain all module morphisms, so this proves both assertions. -/
theorem etale_line_sections_fullFaithful {X : Scheme.{u}}
    (A : TrfInvertibleModules X ⥤ TrfEtaleLineModules X)
    (α : ∀ L : TrfInvertibleModules X,
      trfLineSections (A.obj L) ≅ trfInvertibleSections L)
    (hscalar : ∀ (L : TrfInvertibleModules X) (U : X.Etale)
      (r : Γ(U.left, ⊤)) (s : (A.obj L).obj.val.obj (op U)),
      (α L).hom.hom.app (op U) (r • s) =
        (((Modules.tensorPullback U.hom).obj L.obj).smul r).hom
          ((α L).hom.hom.app (op U) s))
    (hmap : ∀ (L K : TrfInvertibleModules X) (h : L.obj ⟶ K.obj)
      (U : X.Etale) (s : (A.obj L).obj.val.obj (op U)),
      (α K).hom.hom.app (op U) ((trfComparisonMap A h).val.app (op U) s) =
        ((Modules.tensorPullback U.hom).map h).app ⊤ ((α L).hom.hom.app (op U) s)) :
    A.Full ∧ A.Faithful := by
  classical
  obtain ⟨c, _, _, _, hbij, e, he, hmapE, _⟩ :=
    Modules.etaleExtension_free_presentations_hom.{u, u, u}
  have (L : TrfInvertibleModules X) : L.obj.IsInvertible := L.property
  have (L : TrfInvertibleModules X) : L.obj.IsQuasicoherent :=
    Modules.IsInvertible.isQuasicoherent L.obj
  let q (L : TrfInvertibleModules X) := e X L.obj
  have hqi (L : TrfInvertibleModules X) (U : X.Etale)
      (s : Γ((Modules.tensorPullback U.hom).obj L.obj, ⊤)) :
      (q L).hom.hom.app (op U) ((q L).inv.hom.app (op U) s) = s :=
    Iso.inv_hom_id_apply
      (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat).mapIso (q L)).app (op U)) s
  have hqinv (L : TrfInvertibleModules X) (U : X.Etale) (r : Γ(U.left, ⊤))
      (s : Γ((Modules.tensorPullback U.hom).obj L.obj, ⊤)) :
      (q L).inv.hom.app (op U) (r • s) = r • (@id (((c X).extension.obj L.obj).val.obj (op U))
        ((q L).inv.hom.app (op U) s)) := by
    apply (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat).mapIso (q L)).app
      (op U)).addCommGroupIsoToAddEquiv.injective
    change (q L).hom.hom.app (op U) _ = (q L).hom.hom.app (op U) _
    calc
      _ = r • s := hqi L U _
      _ = r • (@id (Γ((Modules.tensorPullback U.hom).obj L.obj, ⊤))
          ((q L).hom.hom.app (op U) ((q L).inv.hom.app (op U) s))) :=
        congrArg (fun z : Γ((Modules.tensorPullback U.hom).obj L.obj, ⊤) ↦ r • z)
          (hqi L U s).symm
      _ = _ := (he X L.obj U r _).symm
  let κ (L : TrfInvertibleModules X) :
      (A.obj L).obj ≅ (c X).extension.obj L.obj :=
    liftLinearIso (α L ≪≫ (q L).symm) (by
      intro U r s
      change (q L).inv.hom.app U ((α L).hom.hom.app U (r • s)) =
        r • (@id (((c X).extension.obj L.obj).val.obj U)
          ((q L).inv.hom.app U ((α L).hom.hom.app U s)))
      rw [hscalar L U.unop, Modules.smul_apply, hqinv])
  have hκ (L K : TrfInvertibleModules X) (h : L.obj ⟶ K.obj) :
      trfComparisonMap A h ≫ (κ K).hom = (κ L).hom ≫ (c X).extension.map h := by
    apply (SheafOfModules.toSheaf (Modules.smallEtaleModuleRing X)).map_injective
    apply (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat).map_injective
    ext U s
    change (A.obj L).obj.val.obj U at s
    change (q K).inv.hom.app U ((α K).hom.hom.app U
        ((trfComparisonMap A h).val.app U s)) =
      ((c X).extension.map h).val.app U
        ((q L).inv.hom.app U ((α L).hom.hom.app U s))
    apply (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat).mapIso (q K)).app
      U).addCommGroupIsoToAddEquiv.injective
    change (q K).hom.hom.app U _ = (q K).hom.hom.app U _
    calc
      _ = (α K).hom.hom.app U ((trfComparisonMap A h).val.app U s) :=
        hqi K U.unop _
      _ = ((Modules.tensorPullback U.unop.hom).map h).app ⊤
          ((α L).hom.hom.app U s) := hmap L K h U.unop s
      _ = ((Modules.tensorPullback U.unop.hom).map h).app ⊤
          ((q L).hom.hom.app U
            ((q L).inv.hom.app U ((α L).hom.hom.app U s))) :=
        congrArg (fun z ↦ ((Modules.tensorPullback U.unop.hom).map h).app ⊤ z)
          (hqi L U.unop _).symm
      _ = _ := (ConcreteCategory.congr_hom (hmapE X L.obj K.obj h U.unop) _).symm
  have hmapbij (L K : TrfInvertibleModules X) :
      Function.Bijective (A.map : (L ⟶ K) → _) := by
    constructor
    · intro f g hfg
      apply ObjectProperty.hom_ext
      apply (hbij X L.obj K.obj).injective
      apply (cancel_epi (κ L).hom).mp
      rw [← hκ L K f.hom, ← hκ L K g.hom]
      exact congrArg (fun z : A.obj L ⟶ A.obj K ↦ z.hom ≫ (κ K).hom) hfg
    · intro f
      obtain ⟨h, hh⟩ := (hbij X L.obj K.obj).surjective
        ((κ L).inv ≫ f.hom ≫ (κ K).hom)
      refine ⟨ObjectProperty.homMk h, ?_⟩
      apply ObjectProperty.hom_ext
      apply (cancel_mono (κ K).hom).mp
      change trfComparisonMap A h ≫ (κ K).hom = _
      rw [hκ]
      calc
        _ = (κ L).hom ≫ ((κ L).inv ≫ f.hom ≫ (κ K).hom) :=
          congrArg (fun z ↦ (κ L).hom ≫ z) hh
        _ = _ := Iso.hom_inv_id_assoc (κ L) _
  exact ⟨⟨fun {L K} ↦ (hmapbij L K).surjective⟩,
    ⟨fun {L K} ↦ (hmapbij L K).injective⟩⟩

end AlgebraicGeometry.Scheme
