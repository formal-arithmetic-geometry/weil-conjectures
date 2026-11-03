/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.AlgebraicGeometry.RationalP1.AffineLineAdjunctionAssembly
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle

/-!
# The projective line, rational coefficients

Source: literature/blueprint/latest/blueprint/part-six-operations/
  sec-constructibility-upper-shriek/sec-ladic-summary/sec-late-coefficients/
  sk-prop-p1-adjunction-rational/_section.md, Proposition sk-prop-p1-adjunction-rational,
  and sk-prop-p1-adjunction-rational.proof.md in the same folder.
(blueprint: sk-prop-p1-adjunction-rational)

Proof route recorded by the blueprint: (1) define the unit and counit from the geometric
projective-line formulas and the diagonal tensor identification; (2) use projection formula,
proper base change, and direct-image composition to reduce the two triangle composites to the
first and second diagonal integrals; (3) use the diagonal-tower trace identities to make both
integrals identities; (4) obtain the adjunction on the localizing categories; and (5) identify
those categories with the finite-Tor constructible localizing closures and transport the Brown
right adjoint along the canonical inclusion comparisons.  Uniqueness of right adjoints then
identifies the transported exceptional functor with `q^!`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.RationalP1

/-- Equal object properties give the same restricted adjunction, retaining both ambient
inclusion comparisons. This transports only the full subcategories, not the geometric maps. -/
private theorem transportRestrictions
    {C D : Type*} [Category C] [Category D]
    (P P' : ObjectProperty C) (Q Q' : ObjectProperty D)
    (hP : P = P') (hQ : Q = Q') (R : C ⥤ D) (T : D ⥤ C)
    (F : P'.FullSubcategory ⥤ Q'.FullSubcategory)
    (G : Q'.FullSubcategory ⥤ P'.FullSubcategory)
    (eF : F ⋙ Q'.ι ≅ P'.ι ⋙ R) (eG : G ⋙ P'.ι ≅ Q'.ι ⋙ T) (adj : F ⊣ G) :
    ∃ (F₀ : P.FullSubcategory ⥤ Q.FullSubcategory)
      (G₀ : Q.FullSubcategory ⥤ P.FullSubcategory),
      Nonempty (F₀ ⋙ Q.ι ≅ P.ι ⋙ R) ∧
      Nonempty (G₀ ⋙ P.ι ≅ Q.ι ⋙ T) ∧ Nonempty (F₀ ⊣ G₀) := by
  subst P'
  subst Q'
  exact ⟨F, G, ⟨eF⟩, ⟨eG⟩, ⟨adj⟩⟩

private theorem rationalClosureEquality
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Z : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z] :
    localizingClosureProEtale (coefficient l c).X Z =
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (coefficient l c).X Z) := by
  apply (localizingClosure_ctf_equals_bc l Z (coefficient l c).X ?_).1.2.2.2.1
  cases c with
  | none => exact Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))
  | some E => exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr ⟨Iso.refl _⟩⟩))

/-- The rational projective-line adjunction, stated on the literal `Loc(Dctf)` closures.
The first three clauses provide the restrictions of derived direct image and of pullback with
Tate twist and shift two, together with their adjunction.  The final clause identifies every
compactification right adjoint supplied by exceptional-adjoint existence with that restricted
Tate-twisted pullback.

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sec-late-coefficients/
sk-prop-p1-adjunction-rational/_section.md, Proposition sk-prop-p1-adjunction-rational
(blueprint: sk-prop-p1-adjunction-rational).

Proof (node steps):
1. The unit and counit on the localizing categories are the explicit transformations of
   det-prop-p1-adjunction-rational-unit-counit: the diagonal tensor identification
   `Δ_* M ≃ p₁^* M ⊗ Δ_* Λ`, the unit formula via proper base change, the counit formula via
   the projection formula, and their naturality and exactness.
2. det-prop-p1-adjunction-rational-triangle reduces both triangle composites to the diagonal
   integrations `Tr_{p_i} ∘ Rp_{i*} δ_Λ` and proves each is the identity (projection formula,
   proper base change, direct-image composition); this gives `Rq_* ⊣ q^*(1)[2]` on
   `Loc(Dbc)`. Since `Y` and `P¹_Y` are qcqs and `Λ ∈ {E, Q̄_ℓ}`,
   det-def-localizing-closure-ctf-equals-bc (2) identifies `Loc(Dctf) = Loc(Dbc)` as full
   subcategories, giving `F ⊣ G` on `localizingClosureProEtale`. For every compactification
   of `q`, a right adjoint of `localizingLowerShriek` (the `q^!` of sk-prop-sf-existence) is
   isomorphic to `G` by uniqueness of right adjoints.
-/
theorem sk_prop_p1_adjunction_rational
    (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] :
    ∃ (F : (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).FullSubcategory ⥤
        (localizingClosureProEtale (coefficient l c).X Y).FullSubcategory)
      (G : (localizingClosureProEtale (coefficient l c).X Y).FullSubcategory ⥤
        (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).FullSubcategory),
      Nonempty (F ⋙ (localizingClosureProEtale (coefficient l c).X Y).ι ≅
        (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).ι ⋙
          moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)) ∧
      Nonempty (G ⋙ (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).ι ≅
        (localizingClosureProEtale (coefficient l c).X Y).ι ⋙
          moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y) ⋙
            twist (coefficient l c).X (ProjectiveLine Y)
              (line l c (ProjectiveLine Y))) ∧
      Nonempty (F ⊣ G) ∧
      ∀ (compactification : Compactification.BoundaryCompactification (ProjectiveLine Y ↘ Y))
        (h : ∀ A, localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y) A →
          localizingClosureProEtale (coefficient l c).X Y
            ((rightDerivedLowerShriekOfCompactification (coefficient l c).X
              compactification.obj.obj).obj A))
        (G' : (localizingClosureProEtale (coefficient l c).X Y).FullSubcategory ⥤
          (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).FullSubcategory),
        (localizingLowerShriek (coefficient l c).X compactification.obj.obj h ⊣ G') →
          Nonempty (G' ≅ G) := by
  classical
  have : Fact (ringChar k).Prime := ⟨by rw [ringChar.eq k p]; exact Fact.out⟩
  have : Fact (ringChar k ≠ l) := ⟨by rw [ringChar.eq k p]; exact hpl⟩
  let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of k))
  let : IsNoetherian (ProjectiveLine Y) :=
    isNoetherian_of_locallyOfFiniteType (ProjectiveLine Y ↘ Y)
  have : LocallyOfFiniteType (firstProjection Y) := by
    unfold firstProjection
    infer_instance
  let : IsNoetherian (diagonalSurface Y) :=
    isNoetherian_of_locallyOfFiniteType (firstProjection Y)
  obtain ⟨adjBc⟩ := rationalP1_adjunction_assembly l c k Y
  have adjBc' : push l c k p hpl Y ⊣ exceptional l c k p hpl Y := by
    simpa only [ringChar.eq k p] using adjBc
  let P := localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)
  let Q := localizingClosureProEtale (coefficient l c).X Y
  obtain ⟨F, G, ⟨eF⟩, ⟨eG⟩, ⟨adj⟩⟩ := transportRestrictions P _ Q _
    (rationalClosureEquality l c (ProjectiveLine Y)) (rationalClosureEquality l c Y)
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y))
    (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y) ⋙
      twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y)))
    (push l c k p hpl Y) (exceptional l c k p hpl Y)
    (Iso.refl _) (Iso.refl _) adjBc'
  refine ⟨F, G, ⟨eF⟩, ⟨eG⟩, ⟨adj⟩, ?_⟩
  intro compactification h G' adjG'
  have : LocallyOfFiniteType (ProjectiveLine Y ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
  have : QuasiCompact (ProjectiveLine Y ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
  have : IsSeparated (ProjectiveLine Y ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
  have : (ProjectiveLine Y ↘ Y).IsOver (Spec (.of k)) := ⟨rfl⟩
  have hc : IsLocalizingAdmissibleCoefficient l (coefficient l c).X := by
    cases c with
    | none => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))
    | some E => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))
  obtain ⟨φ, _⟩ := compactification_coherence_cocycle (coefficient l c).X l hc k
    (ProjectiveLine Y ↘ Y)
  let c₀ : Compactification.BoundaryCompactification (ProjectiveLine Y ↘ Y) :=
    ⟨⟨Compactification.ofIsProper (ProjectiveLine Y ↘ Y), inferInstance⟩⟩
  let e₀ : rightDerivedLowerShriekOfCompactification (coefficient l c).X c₀.obj.obj ≅
      moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y) :=
    Functor.isoWhiskerRight
      (derivedOpenImmersionLowerShriekId (coefficient l c).X (ProjectiveLine Y)) _ ≪≫
        Functor.leftUnitor _
  let eH : localizingLowerShriek (coefficient l c).X compactification.obj.obj h ⋙ Q.ι ≅
      P.ι ⋙ moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y) :=
    φ compactification c₀ ≪≫ Functor.isoWhiskerLeft P.ι e₀
  let eHF : localizingLowerShriek (coefficient l c).X compactification.obj.obj h ≅ F :=
    Functor.fullyFaithfulCancelRight Q.ι (eH ≪≫ eF.symm)
  exact ⟨(adjG'.ofNatIsoLeft eHF).rightAdjointUniq adj⟩

end AlgebraicGeometry.ProEtale.RationalP1
