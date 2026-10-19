/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

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

/-- Derived restrictions along any pro-etale covering family jointly detect isomorphisms
and zero objects for arbitrary commutative condensed coefficients.
Source: HRS Section 3 and Lemma 4.5, proof, conservativity of restriction
(blueprint: lem-zl-condensed-cover-restriction-conservative).

Proof: identify scalar extension along `condensedPullbackHom` with restriction of
scalars along its inverse, so forgetting the module action recovers abelian-sheaf
inverse image. For weakly etale maps the latter is naturally localization restriction.
The library's covering-family conservativity theorem therefore detects module-sheaf
isomorphisms, since the forgetful functor reflects isomorphisms. Apply this result
to every cohomology map, using the natural exact-functor cohomology comparison and
`DerivedCategory.isIso_iff`. Finally apply the morphism criterion to `K ⟶ 0`.
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
  have hw : ∀ i : 𝒰.I₀, WeaklyEtale (𝒰.f i) := fun i ↦
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ ⟨i⟩
  have hmod (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)) (a : M ⟶ N)
      (ha : ∀ i : 𝒰.I₀, IsIso ((CondensedRing.upperStar Λ.X (𝒰.f i)).map a)) :
      IsIso a := by
    have haHom : IsIso a.hom := by
      refine ProEtale.isIso_of_isIso_localizationRestriction _ a.hom 𝒰.f 𝒰.mem₀ ?_
      intro i
      have : IsIso ((CondensedRing.upperStar Λ.X (𝒰.f i)).map a) := ha i
      let e := Functor.isoWhiskerLeft
        ((𝒰.f i)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ.X X))
        (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ.X (𝒰.f i)))
      have hi := (NatIso.isIso_map_iff e a).1 (ha i)
      have hu : IsIso ((𝒰.f i)^*[Ab.{u + 1}].map a.hom) :=
        inferInstanceAs (IsIso ((Mod.forget _).map
          (((𝒰.f i)^*[Ab.{u + 1}].mapMod _ ⋙
            Mod.comap (asIso (condensedPullbackHom Λ.X (𝒰.f i))).inv).map a)))
      exact (NatIso.isIso_map_iff (ProEtale.upperStarIsoLocalizationRestriction
        Ab.{u + 1} (𝒰.f i) inferInstance) a.hom).1 hu
    have : IsIso ((Mod.forget _).map a) := haHom
    exact isIso_of_reflects_iso a (Mod.forget _)
  have hderived (K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
      (f : K ⟶ L)
      (hf : ∀ i : 𝒰.I₀,
        IsIso ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.map f)) :
      IsIso f := by
    rw [DerivedCategory.isIso_iff]
    intro n
    refine hmod _ _ _ fun i ↦ ?_
    have := hf i
    exact (NatIso.isIso_map_iff
      ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategoryHomologyFunctorIso n) f).2
      (inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor _ n).map
        ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.map f))))
  refine ⟨fun K L f ↦ ⟨fun _ i ↦ inferInstance, hderived K L f⟩, ?_⟩
  intro K hK
  have : IsIso (0 : K ⟶ 0) := hderived K 0 0 fun i ↦
    (hK i).isIso
      ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.map_isZero (isZero_zero _)) _
  exact (isZero_zero _).of_iso (asIso (0 : K ⟶ 0))

end AlgebraicGeometry.ProEtale
