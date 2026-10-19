/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Sheaf.Paper.RationalExceptionalRestriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import Sheaf.Paper.DetThmSfCtfStabilityInternalHom
import Sheaf.SixFunctors.CtfStabilityDirectImages
import Sheaf.Paper.CompactificationCoherenceCocycle
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Restricted adjunctions on constructible finite-Tor complexes

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-adjunctions, all three clauses
(blueprint: det-thm-sf-ctf-stability-adjunctions).

Restrictions include their comparison isomorphisms with the ambient functors and the
compatibility of the Hom equivalences. The exceptional pair is restricted from the
localizing closure, not from an adjunction on all unbounded pro-etale complexes.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

/-- Packaging of the statement that an ambient adjunction restricts along two inclusions.
The comparison isomorphisms identify both functors, and the displayed equation identifies
the natural Hom bijections, hence also the unit and counit. This is the conclusion described
in the proof of blueprint det-thm-sf-ctf-stability-adjunctions, first sentence; it supplies no
new adjunction or replacement for the Mathlib restriction construction.
Source: blueprint main-20261015, sk-thm-sf-ctf-stability-adjunctions, proof paragraph
(blueprint: det-thm-sf-ctf-stability-adjunctions). -/
def HasCompatibleRestriction
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (iC : C' ⥤ C) (iD : D' ⥤ D) : Prop :=
  ∃ (F' : C' ⥤ D') (G' : D' ⥤ C')
    (eF : iC ⋙ F ≅ F' ⋙ iD) (eG : iD ⋙ G ≅ G' ⋙ iC) (a' : F' ⊣ G'),
    ∀ (M : C') (N : D') (g : F'.obj M ⟶ N),
      iC.map (a'.homEquiv M N g) =
        a.homEquiv (iC.obj M) (iD.obj N) (eF.hom.app M ≫ iD.map g) ≫ eG.hom.app N

/-- The Mathlib restriction has exactly the ambient Hom bijection. -/
private theorem hasCompatibleRestriction_of_fullyFaithful
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    {iC : C' ⥤ C} {iD : D' ⥤ D}
    (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful)
    (F' : C' ⥤ D') (G' : D' ⥤ C')
    (eF : iC ⋙ F ≅ F' ⋙ iD) (eG : iD ⋙ G ≅ G' ⋙ iC) :
    a.HasCompatibleRestriction iC iD := by
  refine ⟨F', G', eF, eG, a.restrictFullyFaithful hiC hiD eF eG, ?_⟩
  intro M N g
  rw [a.restrictFullyFaithful_homEquiv_apply hiC hiD eF eG,
    hiC.map_preimage]
  simp only [a.homEquiv_unit, Functor.map_comp, Category.assoc]

/-- Restrict both functors by lifting their object maps to the full subcategories. -/
private theorem hasCompatibleRestriction_of_preserves
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (hF : ∀ M, P M → Q (F.obj M)) (hG : ∀ N, Q N → P (G.obj N)) :
    a.HasCompatibleRestriction P.ι Q.ι := by
  exact hasCompatibleRestriction_of_fullyFaithful a P.fullyFaithfulι Q.fullyFaithfulι
    (Q.lift (P.ι ⋙ F) (fun M ↦ hF M.obj M.property))
    (P.lift (Q.ι ⋙ G) (fun N ↦ hG N.obj N.property))
    (Iso.refl _) (Iso.refl _)

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- All three adjunctions restrict to the full constructible finite-Tor categories, with
the ambient Hom bijections. In clause 3, `h`, `G`, and `a` exhibit a localizing
exceptional adjunction supplied by sk-prop-sf-existence, together with its restriction.
Uniqueness of a right adjoint identifies this with any other choice. No preservation on
Dctf is an input. The compactification is the one used to define the ambient lower shriek.
Source: blueprint main-20261015, sk-thm-sf-ctf-stability-adjunctions, clauses 1--3
(blueprint: det-thm-sf-ctf-stability-adjunctions).

Proof:
1. A full-subcategory restriction of F and G has the same Hom sets as the ambient
   categories. Restrict the natural Hom bijections of F ⊣ G; equivalently use
   Adjunction.restrictFullyFaithful. This gives the same unit and counit after inclusion.
2. det-thm-sf-ctf-stability-direct-images gives preservation of Dctf by f*, Rf*,
   Rf!, f!, and derived tensor. det-thm-sf-ctf-stability-internal-hom gives preservation
   by RHom(K,-) for K in Dctf. Thus the required restriction functors exist.
3. Apply step 1 to derivedUpperStarLowerStarAdjunction, which is the ambient derived
   adjunction of def-sfb-module-derived-pushpull-adjunction. Its Lf* is the f* of clause 1.
4. The derivedTensorHomAdjunction of sk-def-sfb-derived-tensor-hom is K tensor -
   adjoint to RHom(K,-). The commutative relative tensor has its Koszul-signed braiding
   on K-flat representatives. Transport the left adjoint along tensorLeftIsoTensorRight
   to obtain - tensor K adjoint to RHom(K,-), then apply step 1.
5. Apply step 1 to the localizingLowerShriek adjunction of sk-prop-sf-existence.
   Dctf includes fully in its localizing closure by the recorded full inclusion
   ProEtale.constantModelFiniteTorToLocalizing (module of sk-thm-restriction).
   Any choice of the ambient right adjoint gives the same conclusion by its unique
   adjunction-compatible isomorphism. This proves clause 3.
-/
theorem constructibleFiniteTor_adjunctions
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    (derivedUpperStarLowerStarAdjunction Λ f).HasCompatibleRestriction
      (constantModelBoundedConstructible Λ Y ⊓ fun K ↦
        DerivedCategory.finiteTorAmplitude _ K).ι
      (constantModelBoundedConstructible Λ X ⊓ fun K ↦
        DerivedCategory.finiteTorAmplitude _ K).ι ∧
    (∀ K : ConstantModelConstructibleFiniteTor Λ X,
      ((derivedTensorHomAdjunction Λ K.obj).ofNatIsoLeft
        (@BraidedCategory.tensorLeftIsoTensorRight _ _ _
          (DerivedCategory.braidedCategory' _) K.obj)).HasCompatibleRestriction
        (constantModelBoundedConstructible Λ X ⊓ fun M ↦
          DerivedCategory.finiteTorAmplitude _ M).ι
        (constantModelBoundedConstructible Λ X ⊓ fun M ↦
          DerivedCategory.finiteTorAmplitude _ M).ι) ∧
    (∀ c : Compactification.BoundaryCompactification f,
      ∃ (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
        ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
      (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
        (localizingClosureProEtale Λ X).FullSubcategory)
      (a : localizingLowerShriek Λ c.obj.obj h ⊣ G),
      a.HasCompatibleRestriction
        (constantModelFiniteTorToLocalizing Λ X) (constantModelFiniteTorToLocalizing Λ Y)) := by
  have hs := constructibleFiniteTor_stability_direct_images ℓ k Λ _hΛ f
  refine ⟨?_, ?_, ?_⟩
  · exact Adjunction.hasCompatibleRestriction_of_preserves
      (derivedUpperStarLowerStarAdjunction Λ f) _ _ hs.1 hs.2.2.2.1
  · intro K
    apply Adjunction.hasCompatibleRestriction_of_preserves
    · intro M hM
      exact hs.2.1 M K.obj hM K.property
    · intro M hM
      exact (internalHom_stability Λ ℓ k _hΛ K.obj M K.property hM).1
  · have : CompactSpace Y :=
      QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
    have : QuasiSeparatedSpace Y :=
      quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
    let c₀ : Compactification.BoundaryCompactification f :=
      ⟨⟨@HasCompactification.compactification X Y f
        (HasCompactification.of_isOver (S := Spec (.of k)) f),
        Compactification.quasiCompact_openImmersion _ inferInstance⟩⟩
    obtain ⟨h₀, hX, hY, hdata⟩ :=
      exists_localizingExceptionalAdjoint Λ ℓ k f c₀ _hΛ
    obtain ⟨G, s, hG⟩ := hdata.2.2.2.2
    obtain ⟨a₀, _⟩ := hG.2.2
    let PX := constantModelBoundedConstructible Λ X ⊓ fun K ↦
      DerivedCategory.finiteTorAmplitude _ K
    let PY := constantModelBoundedConstructible Λ Y ⊓ fun K ↦
      DerivedCategory.finiteTorAmplitude _ K
    let iX := constantModelFiniteTorToLocalizing Λ X
    let iY := constantModelFiniteTorToLocalizing Λ Y
    let F₀ := localizingLowerShriek Λ c₀.obj.obj h₀
    let F' := PY.lift (PX.ι ⋙ rightDerivedLowerShriekOfCompactification Λ c₀.obj.obj)
      (fun M ↦ hs.2.2.2.2.1 M.obj M.property)
    let G' := PX.lift (iY ⋙ G ⋙ (localizingClosureProEtale Λ X).ι)
      (fun N ↦ hs.2.2.2.2.2 h₀ G a₀ N.obj N.property)
    obtain ⟨φ, _⟩ := compactification_coherence_cocycle Λ ℓ _hΛ f
    intro c
    obtain ⟨h, _, _, _⟩ := exists_localizingExceptionalAdjoint Λ ℓ k f c _hΛ
    let e : F₀ ≅ localizingLowerShriek Λ c.obj.obj h :=
      NatIso.ofComponents
        (fun M ↦ ObjectProperty.isoMk _ ((φ c₀ c).app M))
        (fun g ↦ by
          apply ObjectProperty.hom_ext
          exact (φ c₀ c).hom.naturality g)
    refine ⟨h, G, a₀.ofNatIsoLeft e, ?_⟩
    exact Adjunction.hasCompatibleRestriction_of_fullyFaithful (a₀.ofNatIsoLeft e)
      (ObjectProperty.fullyFaithfulιOfLE _) (ObjectProperty.fullyFaithfulιOfLE _)
      F' G' (Functor.isoWhiskerLeft iX e.symm) (Iso.refl _)

end AlgebraicGeometry.ProEtale.CondensedRing
