/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.LocalizingClosureExistence
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.SixFunctorsBasics.DetExistenceLocalizing
import WeilConjectures.SixFunctorsBasics.DetExistenceRestriction
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Constructibility of a supplied condensed Brown right adjoint

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence;
its underlying constructibility assertion is det-def-sf-operations (vi)
(blueprint: lem-sf-native-brown-right-constructible).

The nested full subcategory below presents Dbc inside Loc(Dctf). The output lifts
retain the ambient objects and maps. The chosen Brown adjoint can be substituted for
`J`; quantifying over its adjunction avoids selecting an unrelated exceptional functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A supplied right adjoint on the condensed localizing closures preserves Dbc,
equivalently Dctf for the two field coefficients. Its unique counit-compatible comparison
with a chosen Brown right adjoint restricts to the constructible exceptional inverse image.

Source: latest blueprint, cor-coef-verdier-weil-equivariance.proof.md, final sentence,
using det-def-sf-operations (vi), det-existence-localizing (3),
det-existence-restriction and det-sp-unique-right-adjoint
(blueprint: lem-sf-native-brown-right-constructible).

Proof:
1. The base field in `D` is an algebraic closure of a finite field, so its ell-cohomological
   dimension is zero. The two coefficient alternatives are admissible. Apply
   det-existence-restriction to the Brown adjunction supplied by det-existence-localizing
   (3), for the same compactification. Its restriction is Rf^! by det-def-sf-operations (vi).
2. Apply det-sp-unique-right-adjoint, namely Adjunction.rightAdjointUniq, to the supplied
   adjunction and this Brown adjunction. Its component is the transpose of the supplied
   counit, and injectivity of the Hom equivalence gives counit-compatible uniqueness.
3. By lem-integral-ctf-equals-bc, every Dbc input has finite Tor amplitude. Transfer
   constructibility and finite Tor amplitude from its Brown image across the comparison.
   Since Dctf is full, the same component maps and inverses give the displayed restricted
   natural isomorphism. The final equation retains exactly these ambient components. -/
theorem nativeBrownRight_preserves_constructible
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hell : ell ≠ D.p) (E : PadicAlgCl.FiniteIntermediateField ell)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    {X Y : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (c : Compactification.BoundaryCompactification f.left)
    (h : ∀ K, localizingClosureProEtale Λ X.left K → localizingClosureProEtale Λ Y.left
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (G : (localizingClosureProEtale Λ Y.left).FullSubcategory ⥤
      (localizingClosureProEtale Λ X.left).FullSubcategory)
    (adjG : localizingLowerShriek Λ c.obj.obj h ⊣ G)
    (J : (localizingClosureProEtale Λ Y.left).FullSubcategory ⥤
      (localizingClosureProEtale Λ X.left).FullSubcategory)
    (adjJ : localizingLowerShriek Λ c.obj.obj h ⊣ J) :
    (constantModelBoundedConstructible Λ Y.left ≤ localizingClosureProEtale Λ Y.left) ∧
    ∃ (hG : ∀ M : (ObjectProperty.inverseImage
          (constantModelBoundedConstructible Λ Y.left)
          (localizingClosureProEtale Λ Y.left).ι).FullSubcategory,
        (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _)
          (G.obj M.obj).obj)
      (hJ : ∀ M : (ObjectProperty.inverseImage
          (constantModelBoundedConstructible Λ Y.left)
          (localizingClosureProEtale Λ Y.left).ι).FullSubcategory,
        (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _)
          (J.obj M.obj).obj),
      ∃! γ : G ≅ J,
        (∀ K, (localizingLowerShriek Λ c.obj.obj h).map (γ.hom.app K) ≫
          adjJ.counit.app K = adjG.counit.app K) ∧
        ∃ β :
          (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _).lift
            ((ObjectProperty.inverseImage (constantModelBoundedConstructible Λ Y.left)
                (localizingClosureProEtale Λ Y.left).ι).ι ⋙ G ⋙
              (localizingClosureProEtale Λ X.left).ι) hG ≅
          (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _).lift
            ((ObjectProperty.inverseImage (constantModelBoundedConstructible Λ Y.left)
                (localizingClosureProEtale Λ Y.left).ι).ι ⋙ J ⋙
              (localizingClosureProEtale Λ X.left).ι) hJ,
          ∀ M, (β.hom.app M).hom = (γ.hom.app M.obj).hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
