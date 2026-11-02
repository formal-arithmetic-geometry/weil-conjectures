/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.Compactification.Defs

/-! # Constructible compact-support exceptional adjoint over an arbitrary field

Source: Bhatt--Scholze, Lemmas 6.7.7 and 6.7.19, Remark 6.8.15 and Proposition 6.8.14
(blueprint: lem-per-condensed-structural-exceptional-adjoint).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

/-- The bounded constructible compact-support functor has a compactification-independent
right adjoint over an arbitrary field with `ℓ` invertible.

Source: Bhatt--Scholze, Definition 6.7.6, Lemmas 6.7.7 and 6.7.19, Remark 6.8.15 and
Proposition 6.8.14; (blueprint: lem-per-condensed-structural-exceptional-adjoint).

Proof: finite type over a field gives the Noetherian and quasi-excellent hypotheses needed by
Bhatt--Scholze. Their compactification and coefficient-comparison results show that the
ordinary derived composite `Rp_*D(j_!)` preserves constructibility and is independent of the
compactification. The finite-coefficient exceptional adjunctions at torsion and completed
levels assemble, using the finite-subextension colimit and its descent and uniqueness maps, to
a right adjoint on the `ℚ̄_ℓ` constructible category. The assembled right adjoint has values in
the same bounded constructible subcategory, and its Hom equivalences are natural by the
adjunction axioms. The zero complex and empty schemes are included by the object-property
formulation; no characteristic-zero or nonempty-scheme hypothesis is added.
-/
theorem constructibleStructuralExceptionalAdjoint
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Invertible (ℓ : k)] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k))]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (F : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) ⥤
        BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))
      (G : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) ⥤
        BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)),
      (∀ c : Compactification f,
        Nonempty (F ⋙
          (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)).ι ≅
          (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).ι ⋙
            rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) c)) ∧
      Nonempty (F ⊣ G) := by sorry

end AlgebraicGeometry.ProEtale
