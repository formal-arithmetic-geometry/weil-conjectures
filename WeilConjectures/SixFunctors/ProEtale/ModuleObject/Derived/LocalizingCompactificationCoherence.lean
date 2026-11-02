/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing

/-!
# Construction and independence of compact support on the localizing closure

Source: Weil blueprint, latest, sec-six-functors-basics/sk-prop-sf-comp-coherence,
statement and sk-prop-sf-comp-coherence.proof.md
(blueprint: sk-prop-sf-comp-coherence).

All candidates are the existing unbounded module-object composite Rp_* j_!.
Their target restriction is expressed by its object predicate; distinguished triangles
and sums are the ambient ones. Refinement normalization is imposed before Rp_*.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem adjoint_transpose_naturality_generic
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (F : E ⥤ C) (G : E ⥤ D)
    (τ : F ⟶ G ⋙ R) {A B : E} (a : A ⟶ B) :
    L.map (F.map a) ≫ (adj.homEquiv (F.obj B) (G.obj B)).symm (τ.app B) =
      (adj.homEquiv (F.obj A) (G.obj A)).symm (τ.app A) ≫ G.map a := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simpa only [Equiv.apply_symm_apply, Functor.comp_obj, Functor.comp_map] using τ.naturality a

private theorem refinementMap_naturality_localizing
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.DenseBoundaryCompactification f} (r : d ⟶ c)
    {K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    (a : K ⟶ L) :
    (openImmersionLowerShriek Λ c.obj.obj.obj.i).mapDerivedCategory.map a ≫
        localizingRefinementMap Λ r.hom L =
      localizingRefinementMap Λ r.hom K ≫
        (lowerStar Λ r.hom.hom.hom.hom).rightDerivedFunctor.map
          ((openImmersionLowerShriek Λ d.obj.obj.obj.i).mapDerivedCategory.map a) := by
  let := refinementOpenRestriction_isIso Λ r.hom
  let t : (openImmersionLowerShriek Λ d.obj.obj.obj.i).mapDerivedCategory ⋙
      (lowerStar Λ r.hom.hom.hom.hom).rightDerivedFunctor ⋙
      (upperStar Λ c.obj.obj.obj.i).mapDerivedCategory ≅ 𝟭 _ :=
    Functor.isoWhiskerLeft _ (asIso (refinementOpenRestriction Λ r.hom.hom.hom)) ≪≫
      (asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ
        d.obj.obj.obj.i).unit).symm
  have h := adjoint_transpose_naturality_generic
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.obj.i)
    (𝟭 _) ((openImmersionLowerShriek Λ d.obj.obj.obj.i).mapDerivedCategory ⋙
      (lowerStar Λ r.hom.hom.hom.hom).rightDerivedFunctor) t.inv a
  simpa only [Functor.id_map, Functor.id_obj, Functor.comp_map, Functor.comp_obj,
    localizingRefinementMap, t, refinementTheta, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    NatIso.isIso_inv_app, asIso_inv, asIso_hom] using h

/-- For admissible coefficients, each compactification gives an exact, sum-preserving
functor on Loc(Dctf) preserving Dctf. Its normalized open-adjunction refinement maps
are natural, invertible on Loc(Dctf), and unital and transitive. Natural comparisons
between arbitrary compactifications are computed through every common dense strict
refinement and obey identity and cocycle laws.

Source: blueprint latest, sec-six-functors-basics/sk-prop-sf-comp-coherence,
statement and proof (blueprint: sk-prop-sf-comp-coherence).

Proof:
1. Apply det-sf-comp-coherence-single to each compactification. The target is qcqs
because it is separated and of finite type over a field. This gives the localizing
restriction, distinguished-triangle preservation, all small sums, and Dctf preservation.
2. Apply det-sf-comp-coherence-refinement to dense strict refinements. Its theta is
canonical open restriction followed by the inverse open unit; its e is the adjoint
of theta inverse. The adjunction Hom bijection proves normalization and uniqueness.
Its remaining clauses give invertibility, identity and transitivity with the recorded
canonical compositors. Naturality follows from the naturality of theta and of that
Hom bijection, for every morphism in the unbounded module-object derived category.
3. Apply det-sf-comp-coherence-cocycle to arbitrary compactifications. Its refinement
component is Rp_* of this same e followed by the inverse direct-image compositor.
The comparison equation for every common dense refinement proves independence of
the chosen refinement; the final equations are exactly identity and cocycle.
No density condition is imposed on the two compactifications being compared. -/
theorem localizingCompactificationCoherence
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    (∀ c : Compactification.BoundaryCompactification f,
    (∀ K : DerivedCategory (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      localizingClosureProEtale Λ X K →
        localizingClosureProEtale Λ Y
          ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)) ∧
    (∀ T : Pretriangulated.Triangle (DerivedCategory (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      T ∈ distTriang _ → localizingClosureProEtale Λ X T.obj₁ →
        localizingClosureProEtale Λ X T.obj₂ → localizingClosureProEtale Λ X T.obj₃ →
        (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).mapTriangle.obj T ∈
          distTriang _) ∧
    (∀ (I : Type (u + 2)) (K : Discrete I ⥤ DerivedCategory (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      (∀ i : I, localizingClosureProEtale Λ X (K.obj (Discrete.mk i))) →
        PreservesColimit K (rightDerivedLowerShriekOfCompactification Λ c.obj.obj)) ∧
    (∀ K : DerivedCategory (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      (constantModelBoundedConstructible Λ X K ∧ DerivedCategory.finiteTorAmplitude _ K) →
        constantModelBoundedConstructible Λ Y
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K) ∧
          DerivedCategory.finiteTorAmplitude _
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)) ) ∧
    (∀ (c d : Compactification.DenseBoundaryCompactification f) (r : d ⟶ c)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      ∀ b : (openImmersionLowerShriek Λ c.obj.obj.obj.i).mapDerivedCategory.obj K ⟶
        (lowerStar Λ r.hom.hom.hom.hom).rightDerivedFunctor.obj
          ((openImmersionLowerShriek Λ d.obj.obj.obj.i).mapDerivedCategory.obj K),
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.obj.i).unit.app K ≫
            (upperStar Λ c.obj.obj.obj.i).mapDerivedCategory.map b ≫
              (refinementTheta Λ r.hom K).hom = 𝟙 K ↔
          b = localizingRefinementMap Λ r.hom K) ∧
    (∀ (c d : Compactification.DenseBoundaryCompactification f) (r : d ⟶ c)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      localizingClosureProEtale Λ X K → IsIso (localizingRefinementMap Λ r.hom K)) ∧
    (∀ (c : Compactification.DenseBoundaryCompactification f)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      localizingRefinementMap Λ (𝟙 c.obj) K ≫
          (refinementDerivedLowerStarId Λ c.obj.obj.obj.Z).hom.app
            ((openImmersionLowerShriek Λ c.obj.obj.obj.i).mapDerivedCategory.obj K) = 𝟙 _) ∧
    (∀ (c d e : Compactification.DenseBoundaryCompactification f)
      (r : d ⟶ c) (s : e ⟶ d)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      localizingRefinementMap Λ (s ≫ r).hom K ≫
          (refinementDerivedLowerStarComp Λ s.hom.hom.hom.hom r.hom.hom.hom.hom).hom.app
            ((openImmersionLowerShriek Λ e.obj.obj.obj.i).mapDerivedCategory.obj K) =
        localizingRefinementMap Λ r.hom K ≫
          (lowerStar Λ r.hom.hom.hom.hom).rightDerivedFunctor.map
            (localizingRefinementMap Λ s.hom K)) ∧
    (∀ (c d : Compactification.DenseBoundaryCompactification f) (r : d ⟶ c)
      (K L : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
      (a : K ⟶ L),
      (openImmersionLowerShriek Λ c.obj.obj.obj.i).mapDerivedCategory.map a ≫
          localizingRefinementMap Λ r.hom L =
        localizingRefinementMap Λ r.hom K ≫
          (lowerStar Λ r.hom.hom.hom.hom).rightDerivedFunctor.map
            ((openImmersionLowerShriek Λ d.obj.obj.obj.i).mapDerivedCategory.map a)) ∧
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
  let _ : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let _ : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  have hcoh := localizingRefinement_coherence Λ ℓ k (ringChar k)
    (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ) _hΛ f
  rcases hcoh with ⟨hnorm, hiso, hid, hcomp⟩
  refine ⟨?_, hnorm, hiso, hid, hcomp, ?_, ?_⟩
  · intro c
    exact compactification_localizing Λ ℓ k f c _hΛ
  · intro c d r K L a
    exact refinementMap_naturality_localizing Λ r a
  · exact compactification_coherence_cocycle Λ ℓ _hΛ k f

end AlgebraicGeometry.ProEtale.CondensedRing
