/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Compactification.Defs


/-!
# Constructible condensed exceptional dual of the structural coefficient unit

Source: Bhatt--Scholze, Lemmas 6.7.13 and 6.7.19, Proposition 6.8.14 and
Remark 6.8.15 (blueprint: lem-per-condensed-structural-exceptional-dual).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory MonObj Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace Sheaf.DeligneLaumon

/--
For a separated finite-type scheme over a field in which `ℓ` is invertible, every
compactification of the structure morphism has its actual derived lower shriek restricting to
bounded constructible complexes and this restriction has a constructible right adjoint.  The
exceptional dualizing object is the image of the coefficient unit under that right adjoint, and
relative derived internal Hom into it is constructible for every constructible complex.  This is
only a statement on the constructible subcategories; no right adjoint on ambient derived
categories is asserted.

Proof plan recorded by the source.  First, the structure morphism is separated and finite type,
so every displayed compactification supplies its open and proper legs and the actual functor is
`Rp_*D(j_!)`.  Second, the constructible exceptional-adjoint theorem gives the restriction and
its right adjoint on the constructible full subcategories.  Third, applying that adjoint to the
constructible coefficient unit defines the exceptional dualizing object.  Fourth, the closed
relative derived tensor--internal-Hom structure and constructible dévissage give constructibility
of `RHom` first on coefficient sheaves and then for every bounded constructible complex.  Finally,
only invertibility of `ℓ` in the field and the finite-subextension construction of `Qbar_ℓ` are
used; no positive-characteristic or finite cohomological-dimension hypothesis, and no ambient
right adjoint, is asserted.

Source: Bhatt--Scholze, Lemmas 6.7.13 and 6.7.19, Proposition 6.8.14 and Remark 6.8.15
(blueprint: lem-per-condensed-structural-exceptional-dual).
-/
theorem condensedStructuralExceptionalDual
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Invertible (ℓ : k)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    ∃ (U : AlgebraicGeometry.ProEtale.BoundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k)))),
      Nonempty (U.obj ≅ MonoidalCategoryStruct.tensorUnit _) ∧
      ∀ (c : Compactification X.hom),
        ∃ (F : AlgebraicGeometry.ProEtale.BoundedConstructible
              (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) ⥤
            AlgebraicGeometry.ProEtale.BoundedConstructible
              (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))))
          (G : AlgebraicGeometry.ProEtale.BoundedConstructible
              (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))) ⥤
            AlgebraicGeometry.ProEtale.BoundedConstructible
              (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)),
          Nonempty (F ⋙ (boundedConstructible
            (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k)))).ι ≅
            (boundedConstructible
              (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι ⋙
              rightDerivedLowerShriekOfCompactification
                (Profinite.padicAlgClRingObj ℓ) c) ∧
          Nonempty (F ⊣ G) ∧
          ∀ K : AlgebraicGeometry.ProEtale.BoundedConstructible
              (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left),
            boundedConstructible
              (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)
              (
                ((AlgebraicGeometry.ProEtale.CondensedRing.derivedHom
                    (Profinite.padicAlgClRingObj ℓ) (X := X.left)).obj
                  (Opposite.op K.obj)).obj
                (G.obj U).obj) := by
  sorry

end Sheaf.DeligneLaumon
