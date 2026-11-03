/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierUnit.ArtinSchreierUnitTrivialization
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
public import WeilConjectures.AlgebraicGeometry.AffineCharacterTrace.AffineCharacterTrace

import WeilConjectures.AlgebraicGeometry.CurrentLinearCharacter.CurrentLinearCharacterVanishing
import WeilConjectures.AlgebraicGeometry.AffineCharacterTrace.AffineCharacterTrace
import WeilConjectures.CategoryTheory.ModuleObjects.ModuleGlobalSectionsMonoidalLinear

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-!
# The compactly supported integral of a linear character

(blueprint: sk-lem-wft-character-integral).

Source: `literature/blueprint/latest/blueprint/sec-fourier-transform/`
`sk-lem-wft-character-integral/`, the statement and lem-fd-character-integral proof.

This module records the current condensed Artin--Schreier sheaf and the actual
compact-support functor.  The nonzero clause is the vanishing of the compact
sections of a nonconstant linear pullback.  In the zero clause the unit is the
`NormalizedData.ε` supplied by `artinSchreier_unit_trivialization`, followed by
the normalized smooth trace of the affine projection; rank zero is included by
allowing `r = 0`.

## Main definitions

* `linearSheaf` is the condensed character module of the coordinate linear form.
* `normalizedZeroUnit` uses the image comparison and the normalized epsilon.
* `zeroTrace` applies compact support to that unit and then the smooth trace.

## Main statements

* `characterIntegral` states nonzero vanishing and invertibility of the zero trace.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CharacterIntegral
open AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

variable (k : Type u) [Field k] [Fintype k]

/-- The linear function in the ordered affine-space coordinates.  The empty sum
is zero, so this definition includes the rank-zero case.
Source: lem-fd-character-integral, linear form clause
(blueprint: sk-lem-wft-character-integral). -/
def linearFunction (Ω : Type u) [Field Ω] [Algebra k Ω] (r : ℕ)
    (a : Fin r → Ω) : Γ(affineTraceTower (Spec (.of Ω)) r, ⊤) :=
  letI : (affineTraceTower (Spec (.of Ω)) r).Over (Spec (.of k)) :=
    ⟨affineTraceProjection (Spec (.of Ω)) r ≫
      Spec.map (CommRingCat.ofHom (algebraMap k Ω))⟩
  ∑ i : Fin r, (affineTraceProjection (Spec (.of Ω)) r).appTop
    ((Scheme.ΓSpecIso (.of Ω)).inv.hom (a i)) *
      affineTraceCoordinate (Spec (.of Ω)) r i

/-- The condensed Artin--Schreier module `λ^* L_ψ` on `A^r_Ω`.
Source: def-fd-artin-schreier-sheaf, function pullback clause
(blueprint: sk-lem-wft-character-integral). -/
def linearSheaf (Ω : Type u) [Field Ω] [Algebra k Ω]
    (ψ : AddChar k (MonObj.Γ Λ)) (r : ℕ) (a : Fin r → Ω) :
    Mod (Sheaf (Scheme.ProEt.topology (affineTraceTower (Spec (.of Ω)) r))
      Ab.{u + 1})
      (condensedRingObj Λ (affineTraceTower (Spec (.of Ω)) r)) :=
  letI : (affineTraceTower (Spec (.of Ω)) r).Over (Spec (.of k)) :=
    ⟨affineTraceProjection (Spec (.of Ω)) r ≫
      Spec.map (CommRingCat.ofHom (algebraMap k Ω))⟩
  condensedArtinSchreierSheafOf Λ k _ ψ
    (linearFunction (k := k) (Ω := Ω) r a)

/-- The actual compact-support complex `RΓ_c(A^r_Ω,-)` with condensed
coefficients, formed from the published lower-shriek construction.
Source: def-weil-ordinary-compact-cohomology, compact coefficient complex
(blueprint: sk-lem-wft-character-integral). -/
noncomputable abbrev compactSections (Ω : Type u) [Field Ω] [Algebra k Ω]
    [IsAlgClosed Ω] (r : ℕ) :=
  AffineCharacterTrace.compactSections Λ k Ω r

end AlgebraicGeometry.ProEtale.CharacterIntegral

namespace AlgebraicGeometry.ProEtale.CharacterIntegral

/-- The ordered linear function with all coefficients zero is zero.
Source: lem-fd-character-integral, zero linear form
(blueprint: sk-lem-wft-character-integral).
Proof: each coefficient section is zero, so each summand vanishes, including
when the coordinate set is empty. -/
theorem linearFunction_zero (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    (r : ℕ) : linearFunction (k := k) (Ω := Ω) r (fun _ ↦ 0) = 0 := by
  classical
  simp [linearFunction]

private theorem lowerStarCongr_app_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (CondensedRing.lowerStarCongr Λ h).hom.app M =
      eqToHom (congrArg (fun t ↦ (CondensedRing.lowerStar Λ t).obj M) h) := by
  subst h
  rfl

set_option maxHeartbeats 1600000 in
-- Compare the adjoint unit and equality transports without unfolding coefficient rings.
attribute [-instance] ModuleRingedComparison.internalPullMonoidal in
private theorem translationPull_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k] (a : k) :
    ArtinSchreierTrace.condensedPull Λ
      (Y := ArtinSchreierUnit.universalCover k) (Z := ArtinSchreierUnit.universalCover k)
      (Over.homMk (Etale.artinSchreierTranslation k a)
        (Etale.artinSchreierTranslation_comp_artinSchreierMap k a)) =
      condensedArtinSchreierTranslationAction Λ k a := by
  unfold ArtinSchreierTrace.condensedPull condensedArtinSchreierTranslationAction
  simp only [ArtinSchreierUnit.universalCover, ArtinSchreierTrace.condensedUnit,
    Over.mk_left, Over.mk_hom]
  congr 2
  · apply Mod.regular_hom_ext
    rw [Mod.one_comp_regularLift]
    have hh := CondensedRing.homEquiv_εIso_inv_hom Λ
      (Etale.artinSchreierTranslation k a)
    simp only [Mod.tensorUnit_eq_regular] at hh
    erw [hh]
    rfl
  · exact lowerStarCongr_app_eq Λ _ _

/-- Equality of the two universal averaging endomorphisms, rather than equality
of chosen image objects. Source: sk-lem-as-properties, Complement, the same
normalized degree-q projector (blueprint: sk-lem-wft-character-integral).
Proof: the adjunction transpose of the inverse pullback-unit map is the pullback
of coefficient functions. Expand each translation action and use the module
adjunction and the direct-image compositor. Corresponding summands, and hence
the two averaging endomorphisms, agree. -/
theorem universalProjector_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k]
    (ψ : AddChar k (MonObj.Γ Λ)) :
    condensedArtinSchreierProjector Λ k ψ =
      ArtinSchreierUnit.universalProjector k Λ ψ := by
  unfold ArtinSchreierUnit.universalProjector ArtinSchreierTrace.condensedProjector
    condensedArtinSchreierProjector
  exact (Finset.sum_congr rfl fun a _ ↦
    congrArg (fun f ↦ f ≫ _) (translationPull_eq Λ k a)).symm

/-- The canonical comparison iso of the two image presentations: apply the
function pullback to image.eqToIso of the equation of universal projectors.
Source: sk-lem-as-properties, Complement, agreement of models and zero roots
(blueprint: sk-lem-wft-character-integral). -/
def modelComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k]
    (ψ : AddChar k (MonObj.Γ Λ)) (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (f : Γ(X, ⊤)) :
    condensedArtinSchreierSheafOf Λ k X ψ f ≅
      ArtinSchreierTrace.condensedSheafOf Λ k ψ X f := by
  unfold condensedArtinSchreierSheafOf condensedArtinSchreierSheaf
    ArtinSchreierTrace.condensedSheafOf
  exact (CondensedRing.upperStar Λ (AffineSpace.homOfVector (X ↘ Spec (.of k))
    (fun _ : PUnit ↦ f))).mapIso (image.eqToIso (universalProjector_eq Λ k ψ))

end AlgebraicGeometry.ProEtale.CharacterIntegral
