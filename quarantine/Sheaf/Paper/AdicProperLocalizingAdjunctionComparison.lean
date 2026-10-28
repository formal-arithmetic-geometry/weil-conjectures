module

public import Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.FiniteTorLocalizingLowerShriekOfSize
public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Sheaf.Paper.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
import Sheaf.Paper.AdicConstructibilityPredicateComparison
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.Paper.ProperExceptionalRestriction
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Proper adic adjunctions on the two constructible localizing presentations

Source: blueprint main-20261015, det-existence-restriction.proof.md, adic cases,
and sk-cor-existence-ii-restriction.proof.md, part (1)
(blueprint: lem-sfb-adic-proper-localizing-adjunction-comparison).

Both hulls use coproducts indexed in `u+1`, in the same ordinary derived category.
The comparison functors are the identity on ambient objects and morphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Equality of the bounded generators and their equally indexed hulls, compatibility
with their full inclusions, and transport of the supplied compact-support adjunction.
The refinement equation fixes the canonical proper compactification comparison, rather
than only asserting the existence of an unspecified isomorphism. The final equality is
an equality of ambient arrows, hence also of the full-subcategory arrows.
In diagrammatic order `e_M ≫ h` means `h ∘ e_M`.

Source: blueprint main-20261015, det-existence-restriction.proof.md, adic cases,
and sk-cor-existence-ii-restriction.proof.md, part (1)
(blueprint: lem-sfb-adic-proper-localizing-adjunction-comparison).

Proof:
1. Spec k is Noetherian because k is a field. Apply
   lem-weil-pbc-finite-type-over-noetherian to the two structure morphisms and
   lem-weil-pbc-locally-noetherian-quasi-separated. Both schemes are qcqs and Noetherian.
2. Eliminate def-sfb-adic-coefficient-certificate into its three actual ring objects.
   Apply lem-sfb-adic-constructibility-predicate-comparison and then
   det-def-localizing-closure-ctf-equals-bc: a bounded object in degrees [a,b] has
   Tor amplitude [a-1,b]. The converse follows from sk-def-sfb-constructible.
   Thus the two generating object properties agree, including integral torsion.
3. The intersections defining def-sfb-bounded-constructible-localizing-closure and
   sk-def-localizing-closure use the same ambient coproducts in u+1, so their
   object properties agree. The comparison inclusions send every object and arrow
   to itself; both inclusion squares therefore commute.
4. lem-sfb-adic-proper-localizing-pushforward restricts the actual ambient Rg_*.
   det-cor-existence-ii-restriction (1) compares the chosen compactification to
   the identity compactification of proper g. On the equal hulls this supplies e.
   Its arrows, inverse identities and naturality are the ambient ones.
5. Apply lem-sfb-adjunction-transport-left-iso to the supplied adjunction and e,
   identifying the hulls by the identity inclusions of step 3. The new Hom map is
   a(e_M ≫ h); its inverse sends q to a.symm(q) ≫ e_M.inv. The inverse identities
   follow from those for a and e, and naturality from their naturality.
   The given right adjoint is retained. No derived-completeness condition is used.
-/
theorem adicProperLocalizingAdjunctionComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (g : Z ⟶ Y) [IsProper g.left]
    (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance) :
    ∃ (hB : ∀ T : Over (Spec (.of k)), T = Z ∨ T = Y →
        boundedConstructible (condensedRingObj Λ T.left) =
          (constantModelBoundedConstructible Λ T.left ⊓ fun K ↦
            DerivedCategory.finiteTorAmplitude _ K))
      (hL : ∀ T : Over (Spec (.of k)), T = Z ∨ T = Y →
        boundedConstructibleLocalizingClosure Λ T.left =
          finiteTorLocalizingClosureOfSize.{u + 1} Λ T.left),
      (ObjectProperty.ιOfLE (hL Z (Or.inl rfl)).le ⋙
        (finiteTorLocalizingClosureOfSize.{u + 1} Λ Z.left).ι =
          (boundedConstructibleLocalizingClosure Λ Z.left).ι) ∧
      (ObjectProperty.ιOfLE (hL Y (Or.inr rfl)).le ⋙
        (finiteTorLocalizingClosureOfSize.{u + 1} Λ Y.left).ι =
          (boundedConstructibleLocalizingClosure Λ Y.left).ι) ∧
      (∀ (T : Over (Spec (.of k))) (hT : T = Z ∨ T = Y),
        ∃ hC : (constantModelBoundedConstructible Λ T.left ⊓ fun K ↦
            DerivedCategory.finiteTorAmplitude _ K) ≤
              finiteTorLocalizingClosureOfSize.{u + 1} Λ T.left,
          boundedConstructibleToLocalizing Λ T.left ⋙
              ObjectProperty.ιOfLE (hL T hT).le =
            ObjectProperty.ιOfLE (hB T hT).le ⋙ ObjectProperty.ιOfLE hC) ∧
      ∀ (h : ∀ K, finiteTorLocalizingClosureOfSize.{u + 1} Λ Z.left K →
          finiteTorLocalizingClosureOfSize.{u + 1} Λ Y.left
            ((rightDerivedLowerShriekOfCompactification Λ
              (compactificationOverField g)).obj K))
        (J : (finiteTorLocalizingClosureOfSize.{u + 1} Λ Y.left).FullSubcategory ⥤
          (finiteTorLocalizingClosureOfSize.{u + 1} Λ Z.left).FullSubcategory)
        (a : finiteTorLocalizingLowerShriekOfSize.{u + 1} Λ
          (compactificationOverField g) h ⊣ J),
        ∃ e : ObjectProperty.ιOfLE (hL Z (Or.inl rfl)).le ⋙
            finiteTorLocalizingLowerShriekOfSize.{u + 1} Λ
              (compactificationOverField g) h ⋙ ObjectProperty.ιOfLE (hL Y (Or.inr rfl)).ge ≅
            ellAdicLocalizingLowerStar Λ ℓ g hΛ,
          (∀ (qc : QuasiCompact (compactificationOverField g).i)
            (d : Compactification.DenseBoundaryCompactification g.left)
            (r₁ : d.obj ⟶
              (⟨⟨compactificationOverField g, qc⟩⟩ :
                Compactification.BoundaryCompactification g.left))
            (r₂ : d.obj ⟶
              (⟨⟨Compactification.ofIsProper g.left,
                  inferInstanceAs (QuasiCompact (𝟙 Z.left))⟩⟩ :
                Compactification.BoundaryCompactification g.left))
            (M : (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory),
            (e.hom.app M).hom ≫
                ((Functor.isoWhiskerRight (derivedOpenImmersionLowerShriekId Λ Z.left)
                  ((lowerStar Λ g.left).rightDerivedFunctor) ≪≫
                    Functor.leftUnitor _).inv.app M.obj) ≫
                compactificationRefinementComponent Λ r₂ M.obj =
              compactificationRefinementComponent Λ r₁ M.obj) ∧
          ∃ b : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣
              ObjectProperty.ιOfLE (hL Y (Or.inr rfl)).le ⋙ J ⋙
                ObjectProperty.ιOfLE (hL Z (Or.inl rfl)).ge,
            ∀ (M : (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
              (N : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory)
              (f : (ellAdicLocalizingLowerStar Λ ℓ g hΛ).obj M ⟶ N),
              (b.homEquiv M N f).hom =
                (a.homEquiv ((ObjectProperty.ιOfLE (hL Z (Or.inl rfl)).le).obj M)
                  ((ObjectProperty.ιOfLE (hL Y (Or.inr rfl)).le).obj N)
                  (ObjectProperty.homMk ((e.hom.app M).hom ≫ f.hom))).hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
