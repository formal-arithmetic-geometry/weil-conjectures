/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.EtaleExtensionFreePresentationsHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
/-! # Coordinates for recovery from étale presentations

Source: Stacks Project, Descent, Tag 03DX.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

attribute [local irreducible] tensorPullback tensorPullbackObj

/-- Restriction to an étale object, using the localized-site equivalence and the
identity on its section rings. Source: Stacks 03DX, proof of (2)
(blueprint: lem-trf-etale-presented-module-effective-recovery). -/
def presentedEtaleRestriction {T : Scheme.{u}} (U : T.Etale) :
    SmallEtaleModules T ⥤ SmallEtaleModules U.left :=
  letI := Functor.isContinuous_comp (Scheme.Etale.etaleToOver U) (Over.forget U)
    U.left.smallEtaleTopology (T.smallEtaleTopology.over U) T.smallEtaleTopology
  SheafOfModules.pushforward
    (F := Scheme.Etale.etaleToOver U ⋙ Over.forget U)
    (S := smallEtaleModuleRing U.left) (R := smallEtaleModuleRing T) (𝟙 _)

/-- The generator-normalized free comparison map, adjoint to the free generators
viewed on Zariski opens. Source: Stacks 03DX, proof of (2)
(blueprint: lem-trf-etale-presented-module-effective-recovery). -/
def presentedEtaleFreeMap {T : Scheme.{u}} (c : ZariskiEtaleModuleContext T)
    (I : Type u) : c.extension.obj (SheafOfModules.free I) ⟶
      SheafOfModules.free (R := smallEtaleModuleRing T) I :=
  letI := c.continuous
  (c.adjunction.homEquiv _ _).symm
    ((SheafOfModules.freeHomEquiv _).symm
      (fun i ↦ SheafOfModules.pushforwardSections (zariskiEtaleOpenRingMap T)
        (SheafOfModules.freeSection i)))

/-- Identity on a scheme, considered between two equal étale structure maps.
Source: Stacks 03DX, overlap identifications
(blueprint: lem-trf-etale-presented-module-effective-recovery). -/
def presentedEtaleSameObject {W T : Scheme.{u}} (f g : W ⟶ T)
    [Etale f] [Etale g] (h : f = g) : Scheme.Etale.mk f ≅ Scheme.Etale.mk g :=
  MorphismProperty.Over.isoMk (Iso.refl W) ((Category.id_comp g).trans h.symm)

/-- The local recovery map on every étale test object of an overlap. Composition
of tensor pullbacks and the identity on the underlying scheme supply all transports.
Source: Stacks 03DX, proof of (2)
(blueprint: lem-trf-etale-presented-module-effective-recovery). -/
def presentedEtaleLocalMap {T : Scheme.{u}} (c : ∀ X : Scheme.{u}, ZariskiEtaleModuleContext X)
    (G : SmallEtaleModules T) (U : T.Etale) (F : U.left.Modules) [F.IsQuasicoherent]
    (e : (SheafOfModules.toSheaf (smallEtaleModuleRing U.left)).obj
      ((c U.left).extension.obj F) ≅ etaleTensorSectionsSheaf F)
    (b : (c U.left).extension.obj F ≅ (presentedEtaleRestriction U).obj G)
    (W : T.Etale) (f : W.left ⟶ U.left) [Etale f] (hf : f ≫ U.hom = W.hom)
    (A : W.left.Etale) :
    Γ((tensorPullback A.hom).obj ((tensorPullback f).obj F), ⊤) →
      G.val.obj (op (Scheme.Etale.mk (A.hom ≫ W.hom))) :=
  fun s ↦ G.val.map
    (presentedEtaleSameObject ((A.hom ≫ f) ≫ U.hom) (A.hom ≫ W.hom)
      ((Category.assoc A.hom f U.hom).trans (congrArg (fun k ↦ A.hom ≫ k) hf))).inv.op
    (b.hom.val.app (op (Scheme.Etale.mk (A.hom ≫ f)))
      (e.inv.hom.app (op (Scheme.Etale.mk (A.hom ≫ f)))
        (((tensorSectionsComp A.hom f).hom.app F).app ⊤ s)))

/-- Canonical comparison of the two pullbacks of a global module to a test overlap.
Source: Stacks 03DX, proof of (2)
(blueprint: lem-trf-etale-presented-module-effective-recovery). -/
def presentedTensorOverlap {T : Scheme.{u}} (F : T.Modules) (U V W : T.Etale)
    (f : W.left ⟶ U.left) (g : W.left ⟶ V.left)
    (hf : f ≫ U.hom = W.hom) (hg : g ≫ V.hom = W.hom) :
    (tensorPullback f).obj ((tensorPullback U.hom).obj F) ≅
      (tensorPullback g).obj ((tensorPullback V.hom).obj F) :=
  (tensorSectionsComp f U.hom).app F ≪≫
    eqToIso (congrArg (fun k ↦ (tensorPullback k).obj F) (hf.trans hg.symm)) ≪≫
      ((tensorSectionsComp g V.hom).app F).symm


attribute [local irreducible] ZariskiEtaleModuleContext.extension
  zariskiEtaleModuleExtension SheafOfModules.free presentedEtaleLocalMap
  presentedTensorOverlap


end
end AlgebraicGeometry.Scheme.Modules
