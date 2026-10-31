/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionFullyFaithful
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Closed direct image and the exceptional unit

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sf-closed-unit/`
`prop-sf-closed-unit-all-stages.md` (blueprint: prop-sf-closed-unit-all-stages).

The ambient direct image is the right derived functor of the condensed module pushforward.
For a closed immersion it is fully faithful.  The bounded constructible restriction and its
exceptional right adjoint are recorded together with the isomorphism of the adjunction unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- For every one of the four coefficient stages, a closed immersion has fully faithful direct
image on the ambient and bounded constructible derived categories, and the unit of its
exceptional right adjoint is invertible.

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sf-closed-unit/`
`prop-sf-closed-unit-all-stages.md`, node prop-sf-closed-unit-all-stages, order 3188
(blueprint: prop-sf-closed-unit-all-stages).

Proof (the node's five steps):
1. Put `B = Λ_X = p_X^* Λ`; the coefficient isomorphism `i^* Λ_X ≅ Λ_Z` identifies the
   ring-sheaf operations with the module operations. The ring-sheaf open–closed theorem
   (sk-prop-sf-open-closed-triangle, det-sf-open-closed-sequence-ring-sheaf) gives `i_*`
   exact with invertible counit `i^* i_* ⟶ 𝟭`; `i^*` is exact and `i^* ⊣ i_*`. Finite-type
   `k`-schemes are Noetherian, hence qcqs, and the complementary open is quasi-compact.
2. By exactness `Li^* = D(i^*)` and `Ri_* = D(i_*)`; the termwise unit and counit descend
   through localization, so the derived counit is represented by `i^* i_* ⟶ 𝟭`, which is
   termwise invertible. The counit criterion makes `Ri_*` fully faithful on the ambient
   derived categories.
3. Exactness gives `H^r(i_* K) = i_* H^r(K)`; a constructibility stratification of `Z`,
   viewed in `X`, together with the open complement `U` (where `i_* K` restricts to zero)
   witnesses constructibility. So `i_*` preserves `D^b_c`, and full faithfulness restricts
   to these full subcategories.
4. For non-finite `Λ`, sk-thm-existence (2)–(4), with `D^b_ctf = D^b_c`, supplies the
   exceptional right adjoint on `D^b_c` to `Ri_! = i_*`; for `Λ = A_{E,n}` the constructible
   exceptional adjoint and the ambient closed adjoint are those of
   prop-sf-closed-immersion-unit.
5. For `F = i_* ⊣ G = Ri^!`, the adjunction bijection carries `η_Q ∘ g` to `F g`; full
   faithfulness makes postcomposition with `η_Q` bijective for every `P`, so Yoneda makes
   `η_Q` invertible. The finite ambient assertion is prop-sf-closed-immersion-unit. -/
theorem closedUnitAllStages
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {Z X : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (hΛ :
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ, ∃ n : ℕ, 1 ≤ n ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk
          (IntegralModelsEmbedded.discreteObj
            (Padic.coefficientExtensionRing ℓ E.1 n)))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    ((i.left)_*⟦Λ⟧).rightDerivedFunctor.Full ∧
      ((i.left)_*⟦Λ⟧).rightDerivedFunctor.Faithful ∧
    ∃ hF : ∀ K, constantModelBoundedConstructible Λ Z.left K →
        constantModelBoundedConstructible Λ X.left
          (((i.left)_*⟦Λ⟧).rightDerivedFunctor.obj K),
        ∃ F : (constantModelBoundedConstructible Λ Z.left).FullSubcategory ⥤
            (constantModelBoundedConstructible Λ X.left).FullSubcategory,
          F = (constantModelBoundedConstructible Λ X.left).lift
            ((constantModelBoundedConstructible Λ Z.left).ι ⋙
              ((i.left)_*⟦Λ⟧).rightDerivedFunctor) (fun K ↦ hF K.obj K.property) ∧
          F.Full ∧ F.Faithful ∧
          ∃ G : (constantModelBoundedConstructible Λ X.left).FullSubcategory ⥤
              (constantModelBoundedConstructible Λ Z.left).FullSubcategory,
            (Nonempty (F ⊣ G) ∧
              ∀ adj : F ⊣ G, ∀ Q, IsIso (adj.unit.app Q)) ∧
          ((∃ E : PadicAlgCl.FiniteIntermediateField ℓ, ∃ n : ℕ, 1 ≤ n ∧
            Nonempty (Mon.mk Λ ≅ Mon.mk (IntegralModelsEmbedded.discreteObj
              (Padic.coefficientExtensionRing ℓ E.1 n)))) →
            ∃ H : DerivedCategory
                (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
                  (condensedRingObj Λ X.left)) ⥤
              DerivedCategory
                (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
                  (condensedRingObj Λ Z.left)),
              Nonempty (((i.left)_*⟦Λ⟧).rightDerivedFunctor ⊣ H) ∧
              ∀ adj : ((i.left)_*⟦Λ⟧).rightDerivedFunctor ⊣ H,
                ∀ Q, IsIso (adj.unit.app Q)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
