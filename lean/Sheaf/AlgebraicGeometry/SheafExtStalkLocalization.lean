/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.SheafExt
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
import Sheaf.Paper.DerivedInternalHomStalkLocalization
import Sheaf.Paper.RHomCohomologyExtRing
import WeilConjectures.Topology.RingedModuleSkyscraper
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-!
# Stalk localization of sheaf Ext

Source: Stacks Project, Tag 0FZ3, proof of (1), using Tags 0GM8, 08E8 and 0A64
(blueprint: lem-sc-ext-stalk-localization).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry

private theorem skyscraper_faithful (X : Scheme.{u}) (x : X) :
    (SheafOfModules.ringedModuleSkyscraperFunctor X.toRingedSpace x).Faithful := by
  constructor
  intro M N f g h
  ext m
  have h' := congrArg (fun k ↦ (k.val.app (Opposite.op ⊤)) (fun _ ↦ m) ⟨by trivial⟩) h
  exact h'

private theorem ring_evaluation_faithful (A : Type u) [CommRing A] :
    (SheafOfModules.evaluation
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A))
      (Opposite.op (Discrete.mk PUnit.unit))).Faithful := by
  constructor
  intro M N f g h
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  rcases U with ⟨⟨⟨⟩⟩⟩
  exact h

-- Faithful skyscrapers transfer the given derived-category hom universe to stalk modules.
-- Evaluation then transfers it to the one-point sheaf category.
set_option backward.isDefEq.respectTransparency false in
@[instance_reducible]
private noncomputable def stalkRingDerivedCategory (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (x : X) :
    HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf (X.presheaf.stalk x)))) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  letI : LocallySmall.{w} C :=
    locallySmall_of_faithful (DerivedCategory.singleFunctor C 0)
  letI := skyscraper_faithful X x
  letI : LocallySmall.{w} (ModuleCat.{u} (X.presheaf.stalk x)) :=
    locallySmall_of_faithful
      (SheafOfModules.ringedModuleSkyscraperFunctor X.toRingedSpace x)
  let A := X.presheaf.stalk x
  let R := (sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (CochainComplex.onePointRingSheaf A)
  letI := ring_evaluation_faithful A
  letI : LocallySmall.{w} (ModuleCat.{u} A) := inferInstanceAs
    (LocallySmall.{w} (ModuleCat.{u} (X.presheaf.stalk x)))
  let ev : SheafOfModules.{u} R ⥤ ModuleCat.{u} A :=
    SheafOfModules.evaluation R (Opposite.op (Discrete.mk PUnit.unit))
  letI : LocallySmall.{w} (SheafOfModules.{u} R) := locallySmall_of_faithful ev
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) :=
    SheafOfModules.isGrothendieckAbelian R
  exact HasDerivedCategory.ofHasKInjectiveResolutions _

/-- Sheaf Ext between coherent modules on a Noetherian scheme has stalks equal to Ext
of their stalk modules over the local ring.
Source: Stacks Project, Tag 0FZ3, proof of (1), using Tags 0GM8, 08E8 and 0A64
(blueprint: lem-sc-ext-stalk-localization).

Proof:
1. Apply lem-sc-derived-internal-hom-stalk-localization to F and G in degree zero.
   Coherence of F on the Noetherian scheme makes F[0] pseudo-coherent by Tag 08E8;
   G[0] is bounded below. Tag 0GM8 (2) identifies the stalk of derived internal Hom
   with derived Hom over the local ring. Exactness of stalks commutes with cohomology.
2. By def-weil-pbc-sheaf-ext, the left-hand cohomology stalk is sheaf Ext in degree q.
3. By lem-sc-rhom-cohomology-ext-ring (Tag 0A64), the right-hand cohomology is Ext
   of F_x and G_x in degree q, as defined in def-pc-ext. Both identifications respect
   the local-ring action, so their composite is the displayed linear equivalence.

Natural degrees parametrize exactly the integers q >= 0. The derived-category instance
is size infrastructure for the recorded sheaf Ext definition. -/
theorem nonempty_moduleSheafExt_stalk_linearEquiv (X : Scheme.{u})
    [CompactSpace X] [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (F G : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) (x : X) (q : ℕ) :
    Nonempty (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (moduleSheafExt X (q : ℤ) F G)) ≃ₗ[X.presheaf.stalk x]
        Abelian.Ext ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G) q) := by
  have _ := hG
  let := stalkRingDerivedCategory X x
  have h := derivedInternalHom_stalk_localization X F G hF x (q : ℤ)
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := nonempty_rhom_cohomology_ext_ring (X.presheaf.stalk x)
    ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)
    ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G) q
  exact ⟨e.trans f⟩

end AlgebraicGeometry
