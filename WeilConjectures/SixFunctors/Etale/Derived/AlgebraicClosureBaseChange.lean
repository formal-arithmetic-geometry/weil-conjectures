/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.ExtendScalarsLimits
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegers
public import WeilConjectures.SixFunctors.Etale.Derived.AlgebraicClosureStage

/-!
# Base change `− ⊗_{𝒪_E} 𝒪_L` on étale sheaves

For finite extensions `E ⊆ L` of `ℚ_ℓ` inside `ℚ̄_ℓ`, the ring `𝒪_L` is finite free over `𝒪_E`
(`PadicAlgCl.finite_integers`, `PadicAlgCl.free_integers`), so extension of scalars along
`𝒪_E → 𝒪_L` preserves limits (`ModuleCat.preservesLimits_extendScalars`) and induces the base
change functor `K ↦ K ⊗_{𝒪_E} 𝒪_L` on étale sheaves
(`AlgebraicGeometry.Etale.sheafBaseChangeTransition`), the sheaf-level transition functor of
blueprint `def-weil-algebraically-closed-coefficients`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace PadicAlgCl.FiniteSubext

variable {l : ℕ} [Fact l.Prime] {E L : FiniteSubext l} (h : E ≤ L)

/-- `𝒪_L` is a finite module over `𝒪_E`, on the universe `u + 1` copies. -/
instance finite_restrictScalars_integersShrinkMap :
    Module.Finite (Shrink.{u + 1} (integers l E.field))
      ((ModuleCat.restrictScalars (integersShrinkMap.{0, u} l (incl h) (incl_compat h))).obj
        (.of _ (Shrink.{u + 1} (integers l L.field)))) := by
  let : Algebra E.field L.field := (incl h).toAlgebra
  have : IsScalarTower E.field L.field (PadicAlgCl l) :=
    .of_algebraMap_eq fun x ↦ (incl_compat h x).symm
  have : IsScalarTower ℚ_[l] E.field L.field := .of_algebraMap_eq fun _ ↦ rfl
  have : FiniteDimensional E.field L.field := .right ℚ_[l] E.field L.field
  let := integersAlgebra l E.field L.field
  have := finite_integers l E.field L.field
  let := (integersShrinkMap.{0, u} l (incl h) (incl_compat h)).toAlgebra
  exact Module.Finite.of_equiv_equiv (A₁ := integers l E.field) (B₁ := integers l L.field)
    (shrinkRingEquiv l E.field) (shrinkRingEquiv l L.field) (by
      ext x
      simp [RingHom.algebraMap_toAlgebra, integersShrinkMap]
      rfl)

/-- `𝒪_L` is a projective module over `𝒪_E`, on the universe `u + 1` copies. -/
instance projective_restrictScalars_integersShrinkMap :
    Module.Projective (Shrink.{u + 1} (integers l E.field))
      ((ModuleCat.restrictScalars (integersShrinkMap.{0, u} l (incl h) (incl_compat h))).obj
        (.of _ (Shrink.{u + 1} (integers l L.field)))) := by
  let : Algebra E.field L.field := (incl h).toAlgebra
  have : IsScalarTower E.field L.field (PadicAlgCl l) :=
    .of_algebraMap_eq fun x ↦ (incl_compat h x).symm
  have : IsScalarTower ℚ_[l] E.field L.field := .of_algebraMap_eq fun _ ↦ rfl
  have : FiniteDimensional E.field L.field := .right ℚ_[l] E.field L.field
  let := integersAlgebra l E.field L.field
  have := free_integers l E.field L.field
  have := RingHomInvPair.of_ringEquiv (shrinkRingEquiv.{0, u} l E.field)
  have := RingHomInvPair.of_ringEquiv (shrinkRingEquiv.{0, u} l E.field).symm
  exact Module.Projective.of_equiv
    (σ := (shrinkRingEquiv.{0, u} l E.field : integers l E.field →+* _))
    (σ' := ((shrinkRingEquiv.{0, u} l E.field).symm : _ →+* integers l E.field))
    { (shrinkRingEquiv l L.field).toAddEquiv with
      map_smul' a x := by
        change shrinkRingEquiv l L.field (_ * x) = _ * shrinkRingEquiv l L.field x
        simp only [integersShrinkMap, map_mul]
        congr 1
        simp
        rfl }

end PadicAlgCl.FiniteSubext

namespace AlgebraicGeometry.Etale

open PadicAlgCl PadicAlgCl.FiniteSubext

variable {l : ℕ} [Fact l.Prime] (X : Scheme.{u})

/-- The base change functor `K ↦ K ⊗_{𝒪_E} 𝒪_L` on étale sheaves of modules, for finite
extensions `E ⊆ L` of `ℚ_ℓ` inside `ℚ̄_ℓ`: the sheaf-level transition functor of blueprint
`def-weil-algebraically-closed-coefficients`. No completion is needed, `𝒪_L` being finite free
over `𝒪_E`. -/
noncomputable abbrev sheafBaseChangeTransition {E L : FiniteSubext l} (h : E ≤ L) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Shrink.{u + 1} (integers l E.field))) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Shrink.{u + 1} (integers l L.field))) :=
  sheafExtendScalars _ (integersShrinkMap.{0, u} l (incl h) (incl_compat h))

end AlgebraicGeometry.Etale

namespace PadicAlgCl.FiniteSubext

variable {l : ℕ} [Fact l.Prime] {E L : FiniteSubext l} (h : E ≤ L)

instance free_restrictScalars_integersShrinkMap :
    Module.Free (Shrink.{u + 1} (integers l E.field))
      ((ModuleCat.restrictScalars (integersShrinkMap.{0, u} l (incl h) (incl_compat h))).obj
        (.of _ (Shrink.{u + 1} (integers l L.field)))) :=
  Module.free_of_flat_of_isLocalRing

/-- The `𝒪_L`-module `Hom_{𝒪_E}(𝒪_L, 𝒪_E)` is free of rank one: a chosen identification with
`𝒪_L`, on the universe `u + 1` copies. -/
noncomputable def dualIso :
    ModuleCat.of _ (Shrink.{u + 1} (integers l L.field)) ≅
      (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1}
        (integersShrinkMap.{0, u} l (incl h) (incl_compat h))).obj
          (.of _ (Shrink.{u + 1} (integers l E.field))) :=
  (ModuleCat.nonempty_iso_coextendScalars_obj _).some

end PadicAlgCl.FiniteSubext

namespace CategoryTheory

variable {C A B : Type*} [Category* C] [Category* A] [Category* B] (J : GrothendieckTopology C)

/-- An isomorphism of functors `F ≅ G` induces `sheafCompose J F ≅ sheafCompose J G`. -/
noncomputable def sheafComposeIsoOfIso {F G : A ⥤ B} [J.HasSheafCompose F] [J.HasSheafCompose G]
    (e : F ≅ G) : sheafCompose J F ≅ sheafCompose J G where
  hom := sheafCompose_map J e.hom
  inv := sheafCompose_map J e.inv
  hom_inv_id := by rw [← sheafCompose_comp, e.hom_inv_id, sheafCompose_id]
  inv_hom_id := by rw [← sheafCompose_comp, e.inv_hom_id, sheafCompose_id]

end CategoryTheory

namespace AlgebraicGeometry.Etale

open PadicAlgCl PadicAlgCl.FiniteSubext

variable {l : ℕ} [Fact l.Prime] (X : Scheme.{u})

/-- The base change `K ↦ K ⊗_{𝒪_E} 𝒪_L` on étale sheaves is isomorphic to the coextension of
scalars `K ↦ Hom_{𝒪_E}(𝒪_L, K)` used as the transition functor, through the identification
`Hom_{𝒪_E}(𝒪_L, 𝒪_E) ≅ 𝒪_L` (`PadicAlgCl.FiniteSubext.dualIso`). -/
noncomputable def sheafBaseChangeTransitionIso {E L : FiniteSubext l} (h : E ≤ L) :
    sheafBaseChangeTransition X h ≅ sheafStageTransition X h :=
  sheafComposeIsoOfIso _ (ModuleCat.extendScalarsIsoCoextendScalars _ (dualIso h))

instance {E L : FiniteSubext l} (h : E ≤ L) : (sheafBaseChangeTransition X h).Additive :=
  Functor.additive_of_iso (sheafBaseChangeTransitionIso X h).symm

/-- Blueprint `def-weil-algebraically-closed-coefficients`: the derived transition functor
`K ↦ K ⊗_{𝒪_E} 𝒪_L` (derived base change; no completion is needed, `𝒪_L` being finite free over
`𝒪_E`) is isomorphic to the derived transition functor `derivedStageTransition` used to build the
common-stage category. -/
noncomputable def derivedBaseChangeTransitionIso {E L : FiniteSubext l} (h : E ≤ L) :
    (sheafBaseChangeTransition X h).rightDerivedFunctor ≅ derivedStageTransition X h :=
  Functor.rightDerivedFunctorNatIso (sheafBaseChangeTransitionIso X h)

end AlgebraicGeometry.Etale

namespace DerivedCategory

open CategoryTheory Limits MonoidalCategory Opposite

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R] {I : Ideal R}

/-- Derived completeness is invariant under isomorphisms. -/
lemma derivedComplete_of_iso {K K' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (φ : K ≅ K') (hK : derivedComplete J I K) : derivedComplete J I K' := by
  let := (DerivedCategory.sheafTensorStructure J R).monoidalCategory
  refine Pretriangulated.IsHomotopyLimit.of_iso
    (Functor.isoWhiskerLeft (quotPowFunctor J I) ((tensoringLeft _).mapIso φ)) hK _ φ
    fun n ↦ ?_
  simp [derivedCompletionCone, whisker_exchange]

end DerivedCategory

namespace AlgebraicGeometry.Etale

open PadicAlgCl PadicAlgCl.FiniteSubext

variable {l : ℕ} [Fact l.Prime] (X : Scheme.{u})

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- The integral transition functor `K ↦ K ⊗_{𝒪_E} 𝒪_L` of the derived complete categories:
derived base change, which preserves derived completeness, being isomorphic to the derived
coextension of scalars. -/
noncomputable def integralBaseChangeTransition {E L : FiniteSubext l} (h : E ≤ L) :
    DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E.field ⥤
      DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l L.field :=
  (DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l L.field).lift
    ((DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E.field).ι ⋙
      (sheafBaseChangeTransition X h).rightDerivedFunctor)
    (fun K ↦ DerivedCategory.derivedComplete_of_iso
      ((derivedBaseChangeTransitionIso X h).app K.1).symm ((integralStageTransition X h).obj K).2)

/-- The integral base change transition is isomorphic to the integral transition functor. -/
noncomputable def integralBaseChangeTransitionIso {E L : FiniteSubext l} (h : E ≤ L) :
    integralBaseChangeTransition X h ≅ integralStageTransition X h :=
  NatIso.ofComponents
    (fun K ↦ (ObjectProperty.fullyFaithfulι _).preimageIso
      ((derivedBaseChangeTransitionIso X h).app K.1))
    (fun f ↦ (ObjectProperty.fullyFaithfulι _).map_injective
      ((derivedBaseChangeTransitionIso X h).hom.naturality
        ((DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E.field).ι.map f)))

noncomputable instance {E L : FiniteSubext l} (h : E ≤ L) :
    (integralBaseChangeTransition X h).CommShift ℤ :=
  inferInstanceAs (((DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l L.field).lift
    ((DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E.field).ι ⋙
      (sheafBaseChangeTransition X h).rightDerivedFunctor) _).CommShift ℤ)

instance {E L : FiniteSubext l} (h : E ≤ L) : (integralBaseChangeTransition X h).IsTriangulated :=
  inferInstanceAs (((DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l L.field).lift
    ((DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E.field).ι ⋙
      (sheafBaseChangeTransition X h).rightDerivedFunctor) _).IsTriangulated)

/-- Blueprint `def-weil-rationalization-karoubi`: the scalar-extension functor
`− ⊗_E L : D_comp(X_ét, E) ⥤ D_comp(X_ét, L)`, induced on rationalizations by the derived base
change `− ⊗_{𝒪_E} 𝒪_L` of integral representatives. -/
noncomputable abbrev rationalBaseChangeTransition {E L : FiniteSubext l} (h : E ≤ L) :
    DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E.field ⥤
      DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l L.field :=
  Rationalization.mapOfTorsion (nonZeroDivisors (Shrink.{u + 1} (integers l E.field)))
    (nonZeroDivisors (Shrink.{u + 1} (integers l L.field))) (integralBaseChangeTransition X h)
    (fun K hK ↦
    ObjectProperty.prop_of_iso _ ((integralBaseChangeTransitionIso X h).app K).symm
      (torsion_integralStageTransition_obj X h K hK))

/-- The scalar-extension functor `− ⊗_E L` is isomorphic to the transition functor
`rationalStageTransition`. -/
noncomputable def rationalBaseChangeTransitionIso {E L : FiniteSubext l} (h : E ≤ L) :
    rationalBaseChangeTransition X h ≅ rationalStageTransition X h :=
  Localization.liftNatIso
    (Rationalization.Q (nonZeroDivisors (Shrink.{u + 1} (integers l E.field)))
      (DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E.field))
    (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (integers l E.field)))
      (DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E.field)) _ _ _ _
    (Functor.isoWhiskerRight (integralBaseChangeTransitionIso X h)
      (Rationalization.Q (nonZeroDivisors (Shrink.{u + 1} (integers l L.field)))
        (DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l L.field)))

end AlgebraicGeometry.Etale
