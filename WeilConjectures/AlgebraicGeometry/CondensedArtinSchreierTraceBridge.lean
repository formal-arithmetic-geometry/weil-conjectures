/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierCharacters
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierTraceComparison
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.CategoryTheory.ModuleObjects.ModuleGlobalSectionsMonoidalLinear
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-! Comparison data reducing an arbitrary finite-field character to a trace character.

Source: current blueprint, sec-fourier-transform/sk-lem-as-properties/lem-fd-as-lisse.md
(blueprint: lem-fd-as-lisse).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

attribute [local instance] ZMod.algebra

namespace AlgebraicGeometry.ProEtale

open AlgebraicGeometry.ArtinSchreierTrace

/-! The comparison is deliberately only comparison data.  The lisse and tensor
clauses are obtained from the qlbar trace statements after this bridge. -/

private lemma lowerStarCongr_app_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {Y Z : Scheme.{u}} {g h : Y ⟶ Z} (w : g = h)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ Y)) :
    (ProEtale.CondensedRing.lowerStarCongr Λ w).hom.app N =
      eqToHom (congrArg (fun t ↦ (ProEtale.CondensedRing.lowerStar Λ t).obj N) w) := by
  subst h
  rfl

private lemma regular_adj_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    ((ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ g).homEquiv
      (Mod.regular (ProEtale.condensedRingObj Λ Z))
      (Mod.regular (ProEtale.condensedRingObj Λ Y))
      (Functor.Monoidal.εIso (ProEtale.CondensedRing.upperStar Λ g)).inv).hom =
      ProEtale.condensedPushforwardHom Λ g := by
  simpa only [Mod.tensorUnit_eq_regular] using
    ProEtale.CondensedRing.homEquiv_εIso_inv_hom Λ g

private lemma regularLift_eq_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    Mod.regularLift
      ((ProEtale.CondensedRing.lowerStar Λ g).obj (condensedUnit Λ Y))
      (MonObj.one ≫ ProEtale.condensedPushforwardHom Λ g) =
    (ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ g).homEquiv
      (condensedUnit Λ Z) (condensedUnit Λ Y)
      (Functor.Monoidal.εIso (ProEtale.CondensedRing.upperStar Λ g)).inv := by
  dsimp only [condensedUnit]
  apply Mod.regular_hom_ext
  rw [Mod.one_comp_regularLift, regular_adj_hom]

private lemma regularLift_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    (Mod.regularLift
      ((ProEtale.CondensedRing.lowerStar Λ g).obj
        (Mod.regular (ProEtale.condensedRingObj Λ Y)))
      (MonObj.one ≫ ProEtale.condensedPushforwardHom Λ g)).hom =
      ProEtale.condensedPushforwardHom Λ g := by
  have h := congrArg Mod.Hom.hom (regularLift_eq_unit Λ g)
  simpa only [condensedUnit, regular_adj_hom] using h

private lemma condensedPull_translation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] [Fintype k] (a : k) :
    condensedPull Λ
      (Over.homMk (Etale.artinSchreierTranslation k a)
        (Etale.artinSchreierTranslation_comp_artinSchreierMap k a) :
        Over.mk (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)) ⟶
        Over.mk (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))) =
      ProEtale.condensedArtinSchreierTranslationAction Λ k a := by
  apply Mod.hom_ext
  unfold condensedPull ProEtale.condensedArtinSchreierTranslationAction
  rw [← lowerStarCongr_app_eq Λ
    (Etale.artinSchreierTranslation_comp_artinSchreierMap k a)]
  simp only [Over.Hom.left, Over.homMk, CostructuredArrow.homMk, Over.mk_hom,
    Over.mk_left, Mod.comp_hom', ProEtale.CondensedRing.lowerStar_map_hom,
    ProEtale.CondensedRing.lowerStarComp_hom_app_hom,
    ProEtale.CondensedRing.lowerStarCongr_hom_app_hom, condensedUnit,
    Mod.tensorUnit_eq_regular, regularLift_hom, regular_adj_hom]

private lemma condensedProjector_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] [Fintype k] (χ : AddChar k (MonObj.Γ Λ)) :
    condensedProjector Λ k
      (Over.mk (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)))
      (fun a ↦ Over.homMk (Etale.artinSchreierTranslation k a)
        (Etale.artinSchreierTranslation_comp_artinSchreierMap k a)) χ =
      ProEtale.condensedArtinSchreierProjector Λ k χ := by
  classical
  unfold condensedProjector ProEtale.condensedArtinSchreierProjector
  simp only [condensedPull_translation, Over.mk_hom, Over.mk_left]

private lemma condensedSheafOf_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] [Fintype k] (χ : AddChar k (MonObj.Γ Λ))
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)) :
    Nonempty (condensedSheafOf Λ k χ X f ≅
      ProEtale.condensedArtinSchreierSheafOf Λ k X χ f) := by
  classical
  unfold condensedSheafOf ProEtale.condensedArtinSchreierSheafOf
    ProEtale.condensedArtinSchreierSheaf
  exact ⟨(ProEtale.CondensedRing.upperStar Λ
    (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ : PUnit ↦ f)).mapIso
      (image.eqToIso (condensedProjector_eq Λ k χ))⟩

/-- The comparison model `condensedSheafOf` of lem-wft-as-comparison is isomorphic to the
recorded `ProEtale.condensedArtinSchreierSheafOf` of def-fd-artin-schreier-sheaf.
Source: blueprint def-fd-artin-schreier-sheaf, condensed-coefficients paragraph
(blueprint: lem-fd-as-trace-bridge).

Proof: both are the pullback along `f : X → A^1` of the image of the averaging projector
`∑_c q⁻¹ χ(-c) σ_c^*` on the pushforward of the regular module along the degree-`q`
Artin–Schreier map of `A^1`, with the same translations. The two translation actions,
`condensedPull` (regular lift of the unit) and `condensedArtinSchreierTranslationAction`
(adjoint of the inverse monoidal unit), are the same pullback-of-functions map: both are
adjoint to the unit `A → σ_c^* A` of the regular module. Hence the projectors are equal,
the images are canonically isomorphic, and `upperStar` carries this to the claim. -/
theorem qlbar_artinSchreier_trace_bridge
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod p) k]
    (Ψ : AddChar (ZMod p) (PadicAlgCl ℓ))
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)) :
    Nonempty (condensedSheafOf (Profinite.padicAlgClRingObj ℓ) k
        (((Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar Ψ).compTrace k)
        X f ≅
      ProEtale.condensedArtinSchreierSheafOf
        (Profinite.padicAlgClRingObj ℓ) k X
        (((Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar Ψ).compTrace k) f) := by
  exact condensedSheafOf_iso (Profinite.padicAlgClRingObj ℓ) k _ X f

/-- Every nontrivial condensed character is compared with one qlbar trace character.

Proof source: lem-wft-as-comparison (1)--(2).  Choose a nontrivial character
`Ψ` of `ZMod (ringChar k₀)` with values in `PadicAlgCl ℓ`, apply the character
classification to its constant global-section character, and use the unique
nonzero shift `a`.  The second part of lem-wft-as-comparison transports the
degree-cardinality projector to the prime-degree trace projector.  The same
comparison is natural in the function and for the inverse character.  This
statement records precisely that transport data; it does not include any
lissity, tensor, or inverse conclusion.
(blueprint: lem-fd-as-lisse-trace-bridge; step of lem-fd-as-lisse). -/
theorem condensedArtinSchreier_trace_bridge
    (k₀ : Type u) [Field k₀] [Fintype k₀] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k₀).Prime] [Fact (ringChar k₀ ≠ ℓ)]
    [Algebra (ZMod (ringChar k₀)) k₀] (X₀ : Scheme.{u})
    [X₀.Over (Spec (.of k₀))]
    (ψ : AddChar k₀ (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)))
    (hψ : ψ ≠ 1) :
    ∃ (Ψ : AddChar (ZMod (ringChar k₀)) (PadicAlgCl ℓ)),
      ∃ (a : k₀ˣ),
        (Ψ ≠ 1) ∧
        (ψ = (((Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar Ψ).compTrace
          k₀).mulShift (a : k₀)) ∧
      (∀ h : Γ(X₀, ⊤),
        Nonempty (condensedArtinSchreierSheafOf
            (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ h ≅
          condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k₀ X₀
            (((Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar Ψ).compTrace k₀)
            (scalar k₀ X₀ (a : k₀) * h))) ∧
      (∀ h : Γ(X₀, ⊤),
        Nonempty (condensedArtinSchreierSheafOf
            (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ⁻¹ h ≅
          condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k₀ X₀
            (((Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar Ψ⁻¹).compTrace k₀)
            (scalar k₀ X₀ (a : k₀) * h))) := by
  sorry

end AlgebraicGeometry.ProEtale
