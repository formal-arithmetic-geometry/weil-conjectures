/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-! # Conservativity of covering restrictions with condensed coefficients

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Section 3
and the proof of Lemma 4.5 (blueprint: lem-zl-condensed-cover-restriction-conservative).

The module-object presentation is the published category of modules over
`coefficientRing X Λ`, whose underlying ring object is `condensedRingObj Λ.X X`.
These are ordinary unbounded derived categories, with no completion.
`CondensedRing.upperStar` uses extension along the actual coefficient isomorphism
`condensedPullbackHom`. Its exact termwise derived functor is canonically the total
left derived inverse image by `CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`.
For an object of the small pro-etale site, localization and the inverse-image
comparison identify this functor with restriction, transporting the coefficient action.
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

private theorem module_cover_reflects_iso
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage X)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)}
    (f : M ⟶ N) (h : ∀ i, IsIso ((CondensedRing.upperStar Λ.X (𝒰.f i)).map f)) :
    IsIso f := by
  have : ∀ i, WeaklyEtale (𝒰.f i) := fun i ↦
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ ⟨i⟩
  have : IsIso f.hom := by
    refine isIso_of_isIso_localizationRestriction Ab.{u + 1} f.hom 𝒰.f 𝒰.mem₀ ?_
    intro i
    have hi := h i
    have he : IsIso ((Mod.extendScalars (condensedPullbackHom Λ.X (𝒰.f i))).map
        (((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod _).map f)) := hi
    have hc := (NatIso.isIso_map_iff
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ.X (𝒰.f i)))
      (((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod _).map f)).1 he
    have hf : IsIso ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).map f.hom) :=
      inferInstanceAs (IsIso ((Mod.forget _).map
        ((Mod.comap (asIso (condensedPullbackHom Λ.X (𝒰.f i))).inv).map
          (((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod _).map f))))
    exact (NatIso.isIso_map_iff
      (upperStarIsoLocalizationRestriction Ab.{u + 1} (𝒰.f i) inferInstance) f.hom).1 hf
  have : IsIso ((Mod.forget _).map f) := ‹IsIso f.hom›
  exact isIso_of_reflects_iso f (Mod.forget _)

/-- Derived restrictions along any pro-etale covering family jointly detect isomorphisms
and zero objects for arbitrary commutative condensed coefficients.
Source: HRS Section 3 and Lemma 4.5, proof, conservativity of restriction
(blueprint: lem-zl-condensed-cover-restriction-conservative).

Proof:
1. The published `upperStarIsoLocalizationRestriction` identifies weakly etale
   pullback of abelian sheaves with sectionwise restriction.
2. `Mod.extendScalarsIsoComapInv` identifies extension along the coefficient
   isomorphism with restriction along its inverse. Forgetting the module action
   therefore identifies the pullback of a module morphism with the pullback of
   its underlying abelian sheaf morphism.
3. Apply the published `isIso_of_isIso_localizationRestriction` to the underlying
   abelian sheaf morphism, using the given pro-etale covering presieve. The
   forgetful functor on module objects reflects isomorphisms.
4. `mapDerivedCategoryHomologyFunctorIso` compares the homology of exact
   termwise pullback with pullback of homology, naturally for every derived
   morphism. Step 3 makes every homology map invertible, and
   `DerivedCategory.isIso_iff` then makes the derived morphism invertible.
5. For zero detection, apply the isomorphism criterion to the map from K to zero.
   Additive restriction preserves zero objects, and a map between zero objects
   is invertible. This includes the empty covering of the empty scheme.
No boundedness, quasi-compactness, nonemptiness or finiteness condition is used. -/
theorem condensed_cover_restriction_conservative
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage X) :
    (∀ (K L : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
        (f : K ⟶ L),
      IsIso f ↔ ∀ i : 𝒰.I₀,
        IsIso ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.map f)) ∧
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)),
      (∀ i : 𝒰.I₀,
        IsZero ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.obj K)) →
      IsZero K) := by
  have hiso : ∀ (K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
      (f : K ⟶ L),
      IsIso f ↔ ∀ i, IsIso
        ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.map f) := by
    intro K L f
    constructor
    · intro h i
      infer_instance
    · intro h
      rw [DerivedCategory.isIso_iff]
      intro n
      refine module_cover_reflects_iso Λ X 𝒰 _ fun i ↦ ?_
      have := h i
      exact (NatIso.isIso_map_iff
        ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategoryHomologyFunctorIso n)
          f).2 (inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor _ n).map
            ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.map f))))
  refine ⟨hiso, ?_⟩
  intro K h
  have hi : IsIso (0 : K ⟶ 0) := (hiso K 0 0).2 fun i ↦ by
    have hz := h i
    exact hz.isIso (Functor.map_isZero _ (isZero_zero _)) _
  exact (asIso (0 : K ⟶ 0)).isZero_iff.mpr (isZero_zero _)

end AlgebraicGeometry.ProEtale
