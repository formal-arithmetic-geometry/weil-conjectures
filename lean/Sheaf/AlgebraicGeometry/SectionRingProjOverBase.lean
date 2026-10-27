/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import WeilConjectures.AlgebraicGeometry.AmpleProjCanonicalMap
public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing

/-! # The canonical section-ring Proj morphism over an affine base

Source: Stacks Project, Properties, Tag 01PZ and Constructions, Tag 01N8
(blueprint: def-sfb-section-ring-proj-affine-base).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules


/-- Place a function in degree zero of the existing section ring.
Source: Stacks, Tag 01PZ (blueprint: def-sfb-section-ring-proj-affine-base). -/
def sectionRingZeroCoefficient {X : Scheme.{u}} (L : X.Modules) [L.IsInvertible]
    (a : Γ(X, ⊤)) : sectionRingGrade L 0 :=
  ⟨DirectSum.of (SectionRingComponent L) 0 (unitSectionsEquiv ⊤ a),
    ⟨unitSectionsEquiv ⊤ a, rfl⟩⟩

/-- The degree-zero coefficient inclusion has the ring operations prescribed by the section ring.
Source: Stacks, Tag 01PZ (blueprint: def-sfb-section-ring-proj-affine-base).
Proof: addition and zero are componentwise. The unit is the function one in degree zero.
For multiplication, sectionRingGMul in degree (0,0) tensors the two functions and applies
its unit unitor. In a local frame this is the ordinary product of the functions.
Thus the zeroth direct-sum inclusion preserves all four ring operations. -/
theorem sectionRingZeroCoefficient_laws {X : Scheme.{u}} (L : X.Modules) [L.IsInvertible] :
    sectionRingZeroCoefficient L 0 = 0 ∧ sectionRingZeroCoefficient L 1 = 1 ∧
      (∀ a b : Γ(X, ⊤), sectionRingZeroCoefficient L (a + b) =
        sectionRingZeroCoefficient L a + sectionRingZeroCoefficient L b) ∧
      (∀ a b : Γ(X, ⊤), sectionRingZeroCoefficient L (a * b) =
        sectionRingZeroCoefficient L a * sectionRingZeroCoefficient L b) := by
  sorry

/-- The canonical inclusion of global functions into the degree-zero section ring.
Source: Stacks, Tag 01PZ (blueprint: def-sfb-section-ring-proj-affine-base). -/
def sectionRingZeroRingHom {X : Scheme.{u}} (L : X.Modules) [L.IsInvertible] :
    Γ(X, ⊤) →+* sectionRingGrade L 0 where
  toFun := sectionRingZeroCoefficient L
  map_zero' := (sectionRingZeroCoefficient_laws L).1
  map_one' := (sectionRingZeroCoefficient_laws L).2.1
  map_add' := (sectionRingZeroCoefficient_laws L).2.2.1
  map_mul' := (sectionRingZeroCoefficient_laws L).2.2.2


/-- The canonical section-ring morphism, chosen with both of the recorded chart normalizations.
The inverse images and fraction formula determine this morphism uniquely, since standard
charts cover Proj and the section opens cover the source. No arbitrary map is chosen.
Source: Stacks, Tags 01PZ and 01N8 (blueprint: def-sfb-section-ring-proj-affine-base). -/
def sectionRingProjMap {X : Scheme.{u}} (L : X.Modules) [L.IsInvertible]
    (hcover : ∀ x : X, ∃ (d : ℕ) (s : sectionRingGrade L d),
      0 < d ∧ x ∈ nonvanishingLocus (L.tensorPow d) (s.val d)) :
    X ⟶ Proj (sectionRingGrade L) :=
  (exists_sectionRing_proj_morphism X L hcover).choose

/-- The Proj structure map induced by the base action on degree-zero functions.
Source: Stacks, Tags 01PZ and 01N8 (blueprint: def-sfb-section-ring-proj-affine-base). -/
def sectionRingProjStructure {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    (L : X.Modules) [L.IsInvertible] : Proj (sectionRingGrade L) ⟶ S :=
  Proj.toSpecZero (sectionRingGrade L) ≫
    Spec.map (CommRingCat.ofHom ((sectionRingZeroRingHom L).comp f.appTop.hom)) ≫
      S.isoSpec.inv

end AlgebraicGeometry.Scheme.Modules
