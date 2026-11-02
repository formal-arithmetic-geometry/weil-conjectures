/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.EssentialImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-!
# Essential image of closed direct image on pro-etale module sheaves

Source: blueprint smooth purity, `sk-prop-sf-closed-unit`,
`lem-exc-proetale-closed-essential-image`; Stacks Project, Pro-etale Cohomology,
Tag 09AH, `lemma-ses-associated-to-open`
(blueprint: lem-exc-proetale-closed-essential-image).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private noncomputable def coefficientDirectImageIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    (proEtaleScalarEquivalence X ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)).functor ⋙
        proEtaleRingedDirectImage f R ≅ proEtaleRingModuleDirectImage f R S c := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    exact PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by intros; rfl)
  · intro M N a
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_isZero_iff_inverseImage
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M : proEtaleRingModules Y R) :
    IsZero ((proEtaleRingModulePullback f R S c).obj M) ↔
      IsZero ((proEtaleModuleInverseImage f R).obj M) := by
  let rc := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c
  let e := proEtaleScalarEquivalence X rc
  let adj := proEtaleRingExtensionAdjunction f R S c
  let t := adj.leftAdjointUniq e.symm.toAdjunction
  constructor
  · intro h
    have hz : IsZero (e.inverse.obj ((proEtaleModuleInverseImage f R).obj M)) :=
      h.of_iso (t.app _).symm
    exact (e.functor.map_isZero hz).of_iso (e.counitIso.app _).symm
  · intro h
    exact (e.inverse.map_isZero h).of_iso (t.app _)

end AlgebraicGeometry.Scheme
