/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.ProEtaleProperOpenInterchange
import Sheaf.Compactification.CommonDenseRefinement
import Sheaf.Compactification.DenseRefinementMorphisms
import Sheaf.Paper.CartesianCoefficients
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Sheaf.Compactification.BoundaryRefinement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!
# Independence of compactification and the cocycle condition

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-cocycle (blueprint: det-sf-comp-coherence-cocycle).

The domain is the recorded ambient localizing closure. The target remains the ordinary
unbounded derived category of module objects. Comparisons are normalized by the existing
open-adjunction refinement map and the canonical derived direct-image compositor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The already defined compactification candidate, with source restricted to Loc(Dctf).
No target preservation is assumed. Source: blueprint det-sf-comp-coherence-cocycle,
opening formula and proof step 1 (blueprint: det-sf-comp-coherence-cocycle). -/
abbrev compactificationLocalizingCandidate {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f) :
    (localizingClosureProEtale Λ X).FullSubcategory ⥤
      DerivedCategory
        (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :=
  (localizingClosureProEtale Λ X).ι ⋙
    rightDerivedLowerShriekOfCompactification Λ c.obj.obj

/-- The component ρ_h : F_c(K) → F_d(K) for a boundary-preserving refinement h : d → c.
It is Rp_* of the canonical open-adjunction map, followed by the inverse derived
compositor and the structural triangle equality. This definition does not require either
compactification to be dense and makes no arbitrary choice of a comparison.
Source: blueprint det-sf-comp-coherence-cocycle, proof step 4
(blueprint: det-sf-comp-coherence-cocycle). -/
def compactificationRefinementComponent {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (h : d ⟶ c)
    (K : DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K ⟶
      (rightDerivedLowerShriekOfCompactification Λ d.obj.obj).obj K :=
  (lowerStar Λ c.obj.obj.g).rightDerivedFunctor.map (localizingRefinementMap Λ h K) ≫
    (refinementDerivedLowerStarComp Λ h.hom.hom.hom c.obj.obj.g).inv.app
      ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K) ≫
    (eqToIso (congrArg (fun g ↦ (lowerStar Λ g).rightDerivedFunctor)
      h.hom.hom.hom_g)).hom.app
        ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K)

/-- Canonical natural comparisons between all compactifications, independent of the common
scheme-theoretically dense refinement, with identity normalization and the cocycle law.
The first clause records that the refinement components used in the formula really are
isomorphisms; the next clause is φ_{c₂,c₁} ρ_{h₂} = ρ_{h₁}, equivalently
φ_{c₂,c₁} = ρ_{h₁} ρ_{h₂}⁻¹, for every common dense refinement and both its projections.
The last two clauses are equalities of natural isomorphisms, not just objectwise existence.
Source: blueprint main-20261015, det-sf-comp-coherence-cocycle
(blueprint: det-sf-comp-coherence-cocycle).

Proof, following the seven DAG steps:
1. Work with F_c = Rp_* D(j_!) on ordinary unbounded module-object derived categories,
restricting only the source to Loc(Dctf). The canonical derived composition comparison
is normalized on K-injective complexes by the underived module compositor. Exact
coefficient pullback makes direct image preserve K-injectives, so all parenthesizations
use the same complex. The underived fibre-product identifications give associativity.
2. For h : d → c with d dense, apply proper/open interchange at p = id_X and i = j_c,
with dense compactification (j_d,h). Its unique identity-on-restriction arrow is the
existing localizingRefinementMap, by the exact open derived adjunction. It is invertible
on Loc(Dctf), naturally in K, even when c is not dense.
3. Over V → X, the boundary equality identifies V ×_{Z_c} Z_d with V, with the same
coefficient action. Exact restriction and preservation of K-injectives by the right
adjoint of exact j_d! give j_c* Rh* ≅ j_d*. These identifications commute with composition.
4. Apply Rp_* to the arrow in step 2 and invert the derived compositor, giving exactly
compactificationRefinementComponent. For a further dense refinement, both open arrows
restrict to the identity; uniqueness from interchange makes them equal. Naturality and
associativity of the compositor give ρ_hk = ρ_h ρ_k. Identity follows the same way.
5. Choose a common dense refinement using det-nagata-refinement-common-dense. Define
φ_{c₂,c₁} = ρ_{h₁} ρ_{h₂}⁻¹. The two arrows are invertible by step 4, and naturality
gives an isomorphism of the restricted functors with ambient target.
6. Dominate two chosen common dense refinements by another dense refinement. Schematic
density of its source and separatedness of each proper target give equality of the two
composites to each c_a, by det-nagata-refinement-morphisms (3). Step 4 and cancellation
of the intervening isomorphisms prove the normalization for every common refinement.
7. Dominate three compactifications simultaneously using the finite-family conclusion
of common dense refinement. Independence allows all three comparisons to be computed
there, and the middle factors cancel, proving the cocycle. For φ_{c,c} use the same
projection twice; this proves identity even for a nondense c. -/
theorem compactification_coherence_cocycle
    (ℓ : ℕ) [Fact ℓ.Prime] (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ φ : ∀ c₁ c₂ : Compactification.BoundaryCompactification f,
        compactificationLocalizingCandidate Λ c₁ ≅ compactificationLocalizingCandidate Λ c₂,
      (∀ (c : Compactification.BoundaryCompactification f)
        (d : Compactification.DenseBoundaryCompactification f) (h : d.obj ⟶ c)
        (K : (localizingClosureProEtale Λ X).FullSubcategory),
        IsIso (compactificationRefinementComponent Λ h K.obj)) ∧
      (∀ (c₁ c₂ : Compactification.BoundaryCompactification f)
        (d : Compactification.DenseBoundaryCompactification f)
        (h₁ : d.obj ⟶ c₁) (h₂ : d.obj ⟶ c₂)
        (K : (localizingClosureProEtale Λ X).FullSubcategory),
        (φ c₁ c₂).hom.app K ≫ compactificationRefinementComponent Λ h₂ K.obj =
          compactificationRefinementComponent Λ h₁ K.obj) ∧
      (∀ c : Compactification.BoundaryCompactification f, φ c c = Iso.refl _) ∧
      (∀ c₁ c₂ c₃ : Compactification.BoundaryCompactification f,
        φ c₁ c₂ ≪≫ φ c₂ c₃ = φ c₁ c₃) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
