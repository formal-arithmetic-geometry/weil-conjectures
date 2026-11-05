/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleClosedPushforward
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.CategoryTheory.Adjunction.MateBiproduct
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.FiberRank
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.PadicAlgClFaithful
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.CategoryTheory.Triangulated.RecollementTriangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfFiniteAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitRange
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Telescope
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ForgetRightDerivedLowerStar
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresentedField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClFlat

/-!
# Descent of the generators `a_! L` of bounded constructible `ℚ̄_ℓ`-complexes

Let `ℓ` be a prime and `X` a scheme with noetherian underlying space. For a locally closed
immersion `a = j ∘ i : S ⟶ U ⟶ X` (`i` a closed immersion, `j` an open immersion) and a lisse
`ℚ̄_ℓ,S`-module `L`, write `a_! L = j_! Ri_* L` for the extension by zero of `L` placed in
degree `0`.

* `ProEtale.CondensedRing.boundedConstructible_le_of_lowerShriek_isLocallyFree` (blueprint
  `det-cor-coefficient-heart-ii-generation`): every bounded constructible `ℚ̄_ℓ,X`-complex lies
  in the smallest class of complexes closed under isomorphisms and extensions in distinguished
  triangles and containing the shifts `(a_! L)[n]`. The class of `K` all of whose shifts lie in
  such a class is triangulated, so by the truncation dévissage
  (`ProEtale.prop_of_boundedConstructibleModule`) and the dévissage of constructible sheaves
  (`ProEtale.CondensedRing.prop_singleFunctor_of_isConstructibleModuleObject`) it suffices to
  treat the complexes `Rc_* V_! Rc'_* L`, `L` lisse, hence locally free. These are of the form
  `a_! L` for the open `U = X ∖ c(D ∖ V)`
  (`ProEtale.CondensedRing.rightDerivedLowerStarOpenImmersionLowerShriekSingleIso`).
* `ProEtale.descendsToPadicSubfield_lowerShriek`: each `a_! L` descends to a finite
  subextension. By the descent of lisse sheaves
  (`ProEtale.exists_isLocallyFree_extendScalars_iso`), `L ≅ ℚ̄_ℓ,S ⊗_{E_S} L_E` for a lisse
  `E_S`-module `L_E`; the complex `a_! L_E` is bounded constructible
  (`ProEtale.CondensedRing.boundedConstructible_openImmersionLowerShriek_obj_of_noetherianSpace`
  and `ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion`),
  and `T^X_{E,Ω} (a_! L_E) ≅ a_! L` by the (Shriek) isomorphism for the open immersion `j`
  (`ProEtale.CondensedRing.derivedOpenImmersionShriekIso`) and the commutation of the extension
  of scalars with the pushforward along the closed immersion `i`
  (`ProEtale.CondensedRing.derivedExtendScalarsLowerStarIsoOfIsClosedImmersion`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

namespace CondensedRing

/-- A constructible module object placed in degree `n` is a bounded constructible complex. -/
lemma boundedConstructible_singleFunctor_obj_of_isConstructibleModuleObject
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    {X : Scheme.{u}} (n : ℤ)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M) :
    boundedConstructible (condensedRingObj Λ X) ((DerivedCategory.singleFunctor _ n).obj M) := by
  refine ⟨⟨⟨n, inferInstance⟩, ⟨n, inferInstance⟩⟩, fun i ↦ ?_⟩
  rcases lt_trichotomy i n with hi | rfl | hi
  · exact isConstructibleModuleObject_of_isZero _ (DerivedCategory.isZero_of_isGE _ n i hi)
  · exact IsConstructibleModuleObject.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ i).app M).symm hM
  · exact isConstructibleModuleObject_of_isZero _ (DerivedCategory.isZero_of_isLE _ n i hi)

variable (ℓ : ℕ) [Fact ℓ.Prime]

end CondensedRing

open CondensedRing

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

end AlgebraicGeometry.ProEtale
