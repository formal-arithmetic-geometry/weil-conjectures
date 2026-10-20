/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.Paper.FormalClosedSupport
import Sheaf.Paper.CoefficientHeart
import Mathlib.CategoryTheory.Yoneda
import Sheaf.Paper.ClosedSupportConstructible

/-!
# Closed exceptional inverse image and sections with support

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-closed-adjoint-constructible/sk-prop-closed-adjoint-constructible-yoneda.md
(blueprint: det-prop-closed-adjoint-constructible-yoneda).

The comparison lives in the full localizing category, and its counit equation is written
in the ambient derived category using the specified closed-immersion normalization.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- On bounded constructible inputs the exceptional right adjoint is naturally isomorphic
to derived sections with support, compatibly with their counits. The witnesses `hK` and
`hS` only record membership in the full localizing subcategories: the two lifted functors
have exactly the ambient objects and maps. The isomorphism `closed` is the stipulated
normalization Ri_! = i_*, and `support` specifies the normalized support adjunction.

Source: blueprint main-20261015, sk-prop-closed-adjoint-constructible-yoneda, statement
and proof (blueprint: det-prop-closed-adjoint-constructible-yoneda).

Proof:
1. The equality Dctf = Dbc from sk-lem-coefficient-heart and the defining intersection
   sk-def-localizing-closure put every input K in C_X. The adjunction of
   sk-prop-sf-existence puts i^!K in C_Z. By
   det-prop-closed-adjoint-constructible-support, RΓ_Z K is Dbc, hence belongs to C_Z.
   Both localizing categories are full in the ambient derived categories.
2. For A in C_Z the two adjunctions identify Hom(A,i^!K) and Hom(A,RΓ_Z K) with
   Hom(i_*A,K), by a mapped arrow followed by the respective counit. These bijections
   are natural in A and K. Compose the first with the inverse of the second.
3. By lem-galois-yoneda-fully-faithful, this natural transformation and its inverse
   come from mutually inverse maps θ_K and ρ_K in C_Z. Evaluation at the identity
   gives i_*(θ_K) followed by the support counit equal to the exceptional counit,
   with the latter transported along `closed`. Injectivity of the support adjunction
   bijection gives uniqueness of the map satisfying this equation.
4. For q : K → K', naturality of the two counits gives the same transpose for
   RΓ_Z(q) θ_K and θ_K' i^!(q). Injectivity gives equality, hence a natural
   isomorphism. Cohomology of this isomorphism also transfers boundedness and
   constructibility from the support value to i^!K.
-/
theorem closedAdjointConstructibleYoneda
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    {X Z U : Scheme.{u}} [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (_hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj (PadicAlgCl ℓ))))
    (c : Compactification.BoundaryCompactification i)
    (h : ∀ K, localizingClosureProEtale Λ Z K → localizingClosureProEtale Λ X
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (G : (localizingClosureProEtale Λ X).FullSubcategory ⥤
      (localizingClosureProEtale Λ Z).FullSubcategory)
    (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G)
    (closed : localizingLowerShriek Λ c.obj.obj h ⋙ (localizingClosureProEtale Λ X).ι ≅
      (localizingClosureProEtale Λ Z).ι ⋙ (lowerStar Λ i).mapDerivedCategory)
    (support : FormalClosedSupportAssertions Λ i j hij) :
    ∃ (hK : ∀ K : ConstantModelBoundedConstructible Λ X,
        localizingClosureProEtale Λ X K.obj)
      (hS : ∀ K : ConstantModelBoundedConstructible Λ X,
        localizingClosureProEtale Λ Z
          ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)),
      ∃ e :
        ((localizingClosureProEtale Λ X).lift
          (constantModelBoundedConstructible Λ X).ι hK) ⋙ G ≅
        (localizingClosureProEtale Λ Z).lift
          ((constantModelBoundedConstructible Λ X).ι ⋙
            (formalClosedSupport Λ i j).rightDerivedFunctor) hS,
        ∀ K : ConstantModelBoundedConstructible Λ X,
          (lowerStar Λ i).mapDerivedCategory.map
              ((localizingClosureProEtale Λ Z).ι.map (e.hom.app K)) ≫
            support.rightAdjoint.counit.app K.obj =
          closed.inv.app (G.obj (((localizingClosureProEtale Λ X).lift
            (constantModelBoundedConstructible Λ X).ι hK).obj K)) ≫
            (localizingClosureProEtale Λ X).ι.map
              (adj.counit.app (((localizingClosureProEtale Λ X).lift
                (constantModelBoundedConstructible Λ X).ι hK).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
