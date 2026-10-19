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
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
