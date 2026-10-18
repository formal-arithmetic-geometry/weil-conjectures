/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Compactification.BoundaryRefinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.CategoryTheory.BrownRepresentabilityRightAdjoint
import Sheaf.Paper.CompactificationLocalizing
import WeilConjectures.Compactification.Dense
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Yoneda
import Sheaf.CategoryTheory.CompactObject
import Sheaf.Paper.BrownHypothesesGeneration
import Sheaf.SixFunctorsBasics.BrownHypotheses

/-!
# Exceptional inverse image on the localizing constructible closure

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-existence,
statement and proof; Stacks Tags 0A8F, 0A8G, 0A8D (blueprint: sk-prop-sf-existence).

The lower shriek is the actual restriction of the recorded compactification composite.
The closure uses constant-model constructibility and the ordinary unbounded derived category.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Restrict the existing `Rp_* D(j_!)` to the recorded localizing closures, once its
preservation of these object properties is established. The proof argument supplies only
membership; objects and maps are exactly those of the ambient compactification functor.
Source: blueprint sk-prop-sf-existence, definition of `Rf_!`
(blueprint: sk-prop-sf-existence). -/
noncomputable def localizingLowerShriek (c : Compactification f)
    (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c).obj K)) :
    (localizingClosureProEtale Λ X).FullSubcategory ⥤
      (localizingClosureProEtale Λ Y).FullSubcategory :=
  (localizingClosureProEtale Λ Y).lift
    ((localizingClosureProEtale Λ X).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c)
    (fun K ↦ h K.obj K.property)

/-- The restricted compactification functor has the shift comparison induced from its
ambient derived functor, via the fully faithful inclusions of the localizing closures.
Source: blueprint sk-prop-sf-existence, exactness of the restricted lower shriek
(blueprint: sk-prop-sf-existence). -/
noncomputable instance localizingLowerShriekCommShift (c : Compactification f)
    (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c).obj K))
    [(localizingClosureProEtale Λ X).IsTriangulated]
    [(localizingClosureProEtale Λ Y).IsTriangulated] :
    (localizingLowerShriek Λ c h).CommShift ℤ :=
  inferInstanceAs (((localizingClosureProEtale Λ Y).lift
    ((localizingClosureProEtale Λ X).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c)
    (fun K ↦ h K.obj K.property)).CommShift ℤ)

/-- The compactification lower shriek on localizing closures has an exact right adjoint,
unique up to the unique counit-compatible isomorphism, and that adjoint preserves all small
coproducts. The existential triangulated structures are proofs that the recorded object
properties are triangulated; the full subcategories inherit their ambient triangles.
Source: blueprint main-20261015, sk-prop-sf-existence, entire statement
(blueprint: sk-prop-sf-existence).

Proof:
1. By sk-lem-brown-hypotheses the two closures are triangulated with small coproducts,
   and small skeletons of Dctf are compact generating sets. Finite type and separatedness
   imply qcqs. Nagata (sk-thm-nagata-compactification) supplies a compactification.
   For the fixed one, det-sf-comp-coherence-single proves preservation of the closures,
   exactness, preservation of coproducts and preservation of Dctf by Rp_* D(j_!).
2. Apply lem-pc-brown-representability-right-adjoint to this restricted functor F.
   This gives G and an adjunction whose Hom equivalences are natural in both objects.
3. Transpose the shifted counit to obtain G(N)[n] ≅ G(N[n]); Yoneda
   (lem-galois-yoneda-fully-faithful) and naturality give coherence and compatibility
   of the unit and counit with shifts. Apply lem-sf-triangulated-right-adjoint.
4. For another adjunction F ⊣ J, det-sp-unique-right-adjoint transposes the two
   counits to mutually inverse natural transformations G ≅ J. Injectivity of the Hom
   equivalence gives uniqueness of the counit-compatible isomorphism.
5. For a small family N_i test the canonical comparison coproduct G(N_i) → G(coproduct N_i)
   against every shifted compact generator P[n]. Both P[n] and F(P[n]) are compact,
   by sk-lem-brown-hypotheses and det-sf-comp-coherence-single. Compactness
   (def-pc-compact-object), adjunction and naturality identify this test with the
   identity on the direct sum of Hom(F(P[n]),N_i).
6. The Hom exact sequences (lem-weil-pbc-hom-into-triangle-exact) of the comparison's
   cone give Hom(P[n],cone) = 0. Compact generation in sk-lem-brown-hypotheses
   makes the cone zero (the argument of det-brown-hypotheses-generation, whose
   statement specializes to the finite-field setting). Then
   lem-kun-distinguished-cone-zero makes the comparison invertible. This includes
   the empty family, so all small coproducts are preserved.
-/
theorem exists_localizingExceptionalAdjoint
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f)
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    ∃ (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
          ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
      (hX : (localizingClosureProEtale Λ X).IsTriangulated)
      (hY : (localizingClosureProEtale Λ Y).IsTriangulated),
      (fun [triX : (localizingClosureProEtale Λ X).IsTriangulated]
          [triY : (localizingClosureProEtale Λ Y).IsTriangulated] ↦
        (localizingLowerShriek Λ c.obj.obj h).IsTriangulated ∧
        Nonempty (HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory) ∧
        Nonempty (HasCoproducts.{u + 1} (localizingClosureProEtale Λ Y).FullSubcategory) ∧
        (∀ I : Type (u + 1),
          PreservesColimitsOfShape (Discrete I) (localizingLowerShriek Λ c.obj.obj h)) ∧
        ∃ G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
            (localizingClosureProEtale Λ X).FullSubcategory,
          ∃ s : G.CommShift ℤ,
            (fun [comm : G.CommShift ℤ] ↦
              G.IsTriangulated ∧
              (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) G) ∧
              ∃ adj : localizingLowerShriek Λ c.obj.obj h ⊣ G,
                ∀ (J : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
                    (localizingClosureProEtale Λ X).FullSubcategory)
                  (adjJ : localizingLowerShriek Λ c.obj.obj h ⊣ J),
                  ∃! e : G ≅ J, ∀ N,
                    (localizingLowerShriek Λ c.obj.obj h).map (e.hom.app N) ≫
                      adjJ.counit.app N = adj.counit.app N)
              (comm := s))
        (triX := hX) (triY := hY) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
