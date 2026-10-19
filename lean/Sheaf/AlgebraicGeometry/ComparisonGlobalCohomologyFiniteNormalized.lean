/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# Canonical finite-coefficient global comparison

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
`lem-weil-pbc-comparison-global-cohomology`
(blueprint: lem-weil-pbc-comparison-global-cohomology).

This interface uses bounded-below right derived evaluation directly. It avoids the
retired pro-etale lower-shriek modules, which are unrelated to ordinary global sections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Evaluation of the actual comparison adjunction unit at the terminal etale object.
Source: blueprint global-comparison proof, Step 1
(blueprint: lem-weil-pbc-comparison-global-cohomology). -/
def finiteComparisonGlobalSectionsUnit (T : Scheme.{u})
    (A : Type (u + 1)) [Ring A] :
    (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 T)))) ⋙ 𝟭 (ModuleCat.{u + 1} A) ⟶
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙
        (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
          (evaluation _ _).obj (op ((Scheme.toProEt T).obj (Scheme.Etale.mk (𝟙 T))))) where
  app F := ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F).hom.app
    (op (Scheme.Etale.mk (𝟙 T)))
  naturality F G f := by
    exact congrArg (fun t ↦ t.hom.app (op (Scheme.Etale.mk (𝟙 T))))
      ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.naturality f)

/-- Derive the adjunction-unit section map, keeping its canonical normalization.
Evaluation at the terminal object is global sections. These D+ functors are identified
with the ordinary RΓ functors by the canonical right-derived-plus compatibility.
Source: blueprint global-comparison proof, Steps 1-2
(blueprint: lem-weil-pbc-comparison-global-cohomology). -/
def finiteComparisonGlobalSections (T : Scheme.{u}) (A : Type (u + 1)) [Ring A] :=
  Functor.rightDerivedFunctorPlusBaseChange
    (G := sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 T))))
    (G' := sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op ((Scheme.toProEt T).obj (Scheme.Etale.mk (𝟙 T)))))
    (β := comparisonUpperStar (ModuleCat.{u + 1} A) T)
    (γ := 𝟭 (ModuleCat.{u + 1} A)) (finiteComparisonGlobalSectionsUnit T A)

/-- Finite-coefficient comparison induces an isomorphism on ordinary derived global
sections for every bounded-below complex. Source: blueprint global-comparison statement
(blueprint: lem-weil-pbc-comparison-global-cohomology).

Proof: The comparison inverse image is exact by
prop-weil-pbc-site-comparison-finite-level, so its right adjoint preserves injectives.
On an injective pro-etale resolution, pushforward and then etale sections is termwise
the same complex as pro-etale sections, since the terminal objects agree. Thus the
canonical Leray comparison is an isomorphism. The derived comparison unit is invertible
on bounded-below etale complexes by thm-weil-pbc-site-comparison. Composing the unit
with this Leray comparison gives precisely the derived transformation displayed here:
its underived map is evaluation of the adjunction unit, and right-derived base change
is the unit-compatible extension of that map. Therefore all its components are
isomorphisms. Canonical D+/ordinary right-derived compatibility identifies this with
the claimed ordinary RΓ comparison. -/
theorem isIso_finiteComparisonGlobalSections (T : Scheme.{u})
    (A : Type (u + 1)) [Ring A] [Finite A] :
    IsIso (finiteComparisonGlobalSections T A) := by
  let G := sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 T)))
  let G' := sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj (op ((Scheme.toProEt T).obj (Scheme.Etale.mk (𝟙 T))))
  let β := comparisonUpperStar (ModuleCat.{u + 1} A) T
  let γ := 𝟭 (ModuleCat.{u + 1} A)
  let e := finiteComparisonGlobalSectionsUnit T A
  have hβ : PreservesFiniteLimits β :=
    (siteComparison_finiteLevel T A).1
  have hβ' : PreservesFiniteColimits β :=
    (siteComparison_finiteLevel T A).2.1
  have : PreservesFiniteLimits β := hβ
  have : PreservesFiniteColimits β := hβ'
  have hu (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      IsIso ((finiteComparisonGlobalSectionsUnit T A).app F) := by
    change IsIso (((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F).hom.app
      (op (Scheme.Etale.mk (𝟙 T))))
    have := isIso_comparisonAdjunction_unit (ModuleCat.{u + 1} A) T
    infer_instance
  have : IsIso (finiteComparisonGlobalSectionsUnit T A) := NatIso.isIso_of_isIso_app _
  have hG' : PreservesFiniteLimits G' := by infer_instance
  have : PreservesFiniteLimits G' := hG'
  have h := Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
    (G := G) (G' := G') (β := β) (γ := γ) (asIso e)
    (fun I _ q ↦ isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar_obj
      (ModuleCat.{u + 1} A) T I (q + 1)
      ((Functor.rightAcyclic_of_injective I) q))
  exact h

end AlgebraicGeometry.ProEtale
