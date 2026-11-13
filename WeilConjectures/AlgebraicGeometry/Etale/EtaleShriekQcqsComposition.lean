/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CompatibleCompactificationTriangle
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenProperInterchange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp

/-!
# Composition of qcqs etale compact-support candidates
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- For a finite commutative coefficient ring and separated finite-type morphisms of qcqs
schemes, the bounded-below compact-support functors attached to any three chosen
compactifications compose up to natural isomorphism.

Source: Stacks Project, More on Etale Cohomology, Tags 0F7J and 0F7I. -/
theorem nonempty_iso_etaleShriek_qcqs_compactification_comp
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cgf : Compactification (f ≫ g)) :
    Nonempty
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cf ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cg ≅
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cgf) := by
  -- Choose compatible geometric models over the prescribed compactification of g.
  obtain ⟨e, _, c, hc, _, hcb, hcf, hb, _, hp, _, hpg, hfg⟩ :=
    exists_compatible_compactification_triangle f g cg
  let A := ModuleCat.{u + 1} Λ
  have : IsOpenImmersion c := hc
  have : IsOpenImmersion (Limits.pullback.fst e.g cg.i) := hb
  have : IsProper (Limits.pullback.snd e.g cg.i) := hp
  have : IsProper (e.g ≫ cg.g) := hpg
  have : QuasiCompact cg.i := cg.quasiCompact_openImmersion inferInstance
  let df : Compactification f :=
    { Z := Limits.pullback e.g cg.i
      i := c
      g := Limits.pullback.snd e.g cg.i
      comm := hcf.symm
      isOpenImmersion := hc
      isProper := hp }
  let dfg : Compactification (f ≫ g) :=
    { Z := e.Z
      i := e.i
      g := e.g ≫ cg.g
      comm := hfg.symm
      isOpenImmersion := inferInstance
      isProper := hpg }
  obtain ⟨hi⟩ := nonempty_iso_etale_open_proper_interchange Λ e.g cg.i
  -- Descend the composition of exact extensions by zero to D+.
  have ho :
      (openImmersionLowerShriek A c).mapDerivedCategoryPlus ⋙
          (openImmersionLowerShriek A (Limits.pullback.fst e.g cg.i)).mapDerivedCategoryPlus ≅
        (openImmersionLowerShriek A e.i).mapDerivedCategoryPlus := by
    have he {j j' : X ⟶ e.Z} [IsOpenImmersion j] [IsOpenImmersion j']
        (h : j = j') : openImmersionLowerShriek A j ≅ openImmersionLowerShriek A j' := by
      subst j'
      exact Iso.refl _
    exact (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso
        (openImmersionLowerShriekComp A c (Limits.pullback.fst e.g cg.i)).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso (he hcb)
  -- The bounded-below Leray isomorphism needs only preservation of injectives.
  have : (lowerStar A e.g).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction A e.g)
  let hd := Functor.rightDerivedFunctorPlusCompIso'
    (lowerStar A e.g) (lowerStar A cg.g) (lowerStarComp A e.g cg.g)
  -- Interchange the middle factors, then combine the opens and the proper maps.
  have hm : rightDerivedLowerShriekOfCompactificationPlus A df ⋙
        rightDerivedLowerShriekOfCompactificationPlus A cg ≅
      rightDerivedLowerShriekOfCompactificationPlus A dfg :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight hi _) ≪≫
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ho _ ≪≫
      Functor.isoWhiskerLeft _ hd
  -- Transport both ends back to the compactifications in the statement.
  exact ⟨Functor.isoWhiskerRight
      (rightDerivedLowerShriekOfCompactificationPlusIso Λ cf df) _ ≪≫
    hm ≪≫ rightDerivedLowerShriekOfCompactificationPlusIso Λ dfg cgf⟩

end AlgebraicGeometry.Etale
