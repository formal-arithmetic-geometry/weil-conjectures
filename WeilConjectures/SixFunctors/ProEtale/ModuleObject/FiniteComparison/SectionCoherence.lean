/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStarSectionCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStarDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStarIdCoherence

/-!
# The finite-coefficient comparison and the section isomorphisms

Let `T` be a finite discrete commutative ring, `Φ` the derived comparison between module objects
over the condensed ring `T̲` and pro-étale sheaves of `T`-modules
(`ProEtale.finiteCoefficientDerivedEquivalence`), and `β_f : Lf^* ⋙ Φ ≅ Φ ⋙ Lf^*` its commutation
with the derived pullbacks (`ProEtale.leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso`).
For a section `s` of `p : X ⟶ Y`, `β` carries the section isomorphism
`Lp^* ⋙ Ls^* ≅ L(s ≫ p)^* = L(𝟙)^* ≅ 𝟭` of module objects to that of sheaves of `T`-modules
(`ProEtale.finiteCoefficientDerivedEquivalence_map_compSectionIso`). This follows from the
compatibility of `β` with composition
(`ProEtale.finiteCoefficientDerivedUpperStarIso_compCoherence`) and with identities
(`ProEtale.finiteCoefficientDerivedUpperStarIso_hom_app_id`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- The derived commutation `β_f` is `finiteCoefficientDerivedUpperStarIso`. -/
lemma leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso_eq {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso f T =
      finiteCoefficientDerivedUpperStarIso T f :=
  rfl

/-- `β` along a morphism equal to the identity is compatible with the identity isomorphisms. -/
lemma finiteCoefficientDerivedEquivalence_map_eqToHom_comp_leftDerivedUpperStarId
    {Y : Scheme.{u}} {g : Y ⟶ Y} (hg : g = 𝟙 Y)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) Y))) :
    (finiteCoefficientDerivedEquivalence Y T).functor.map
        (eqToHom (by rw [hg]) ≫
          (CondensedRing.leftDerivedUpperStarId (Profinite.continuousMapRingObj T) Y).hom.app M) =
      (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso g T).hom.app M ≫
        (leftDerivedUpperStarCongr (ModuleCat.{u + 1} (ULift.{u + 1} T)) hg).hom.app _ ≫
        (leftDerivedUpperStarId (ModuleCat.{u + 1} (ULift.{u + 1} T)) Y).hom.app
          ((finiteCoefficientDerivedEquivalence Y T).functor.obj M) := by
  subst hg
  simp only [eqToHom_refl, Category.id_comp, leftDerivedUpperStarCongr_rfl, Iso.refl_hom,
    NatTrans.id_app]
  erw [Category.id_comp]
  exact (finiteCoefficientDerivedUpperStarIso_hom_app_id T Y M).symm

set_option maxHeartbeats 800000 in
set_option profiler true in
-- unifying the derived comparison `Φ` with `D(Φ)` in the composition coherence is expensive
/-- **The finite-coefficient comparison carries the section isomorphisms of module objects to
those of sheaves of `T`-modules.** For a section `s` of `p : X ⟶ Y` and `M` in the derived
category of module objects over `T̲` on `Y`, the image under `Φ` of
`Ls^* Lp^* M ≅ L(s ≫ p)^* M = L(𝟙)^* M ≅ M` is the pro-étale section isomorphism
`Ls^* Lp^* Φ M ≅ Φ M`, read through `β_s` and `β_p`. -/
theorem finiteCoefficientDerivedEquivalence_map_compSectionIso {X Y : Scheme.{u}} (s : Y ⟶ X)
    (p : X ⟶ Y) (h : s ≫ p = 𝟙 Y)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) Y))) :
    (finiteCoefficientDerivedEquivalence Y T).functor.map
        ((CondensedRing.leftDerivedUpperStarComp (Profinite.continuousMapRingObj T) s p).inv.app M ≫
          eqToHom (by rw [h]) ≫
          (CondensedRing.leftDerivedUpperStarId (Profinite.continuousMapRingObj T) Y).hom.app M) =
      (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso s T).hom.app
          ((CondensedRing.upperStar (Profinite.continuousMapRingObj T) p).leftDerivedFunctor.obj
            M) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) s).leftDerivedFunctor.map
          ((leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso p T).hom.app M) ≫
        (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} (ULift.{u + 1} T)) s p h).hom.app
          ((finiteCoefficientDerivedEquivalence Y T).functor.obj M) := by
  let Φ := (finiteCoefficientDerivedEquivalence Y T).functor
  let β := fun {A B : Scheme.{u}} (f : A ⟶ B) ↦
    leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso f T
  have H : (β (s ≫ p)).hom.app M ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} T)) s p).hom.app (Φ.obj M) =
      Φ.map ((CondensedRing.leftDerivedUpperStarComp
          (Profinite.continuousMapRingObj T) s p).hom.app M) ≫
        (β s).hom.app ((CondensedRing.upperStar (Profinite.continuousMapRingObj T)
          p).leftDerivedFunctor.obj M) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) s).leftDerivedFunctor.map
          ((β p).hom.app M) :=
    finiteCoefficientDerivedUpperStarIso_compCoherence T s p M
  have I := finiteCoefficientDerivedEquivalence_map_eqToHom_comp_leftDerivedUpperStarId T h M
  rw [Functor.map_comp, I]
  have H' : (β s).hom.app ((CondensedRing.upperStar (Profinite.continuousMapRingObj T)
          p).leftDerivedFunctor.obj M) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) s).leftDerivedFunctor.map
          ((β p).hom.app M) =
      Φ.map ((CondensedRing.leftDerivedUpperStarComp
          (Profinite.continuousMapRingObj T) s p).inv.app M) ≫ (β (s ≫ p)).hom.app M ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} T)) s p).hom.app (Φ.obj M) := by
    rw [H, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  rw [reassoc_of% H']
  simp only [leftDerivedUpperStarCompSectionIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  erw [Iso.hom_inv_id_app_assoc]

end AlgebraicGeometry.ProEtale
