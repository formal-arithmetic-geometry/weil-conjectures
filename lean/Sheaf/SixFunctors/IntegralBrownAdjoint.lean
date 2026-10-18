/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.SixFunctors.IntegralLocalizingCompactSupport
public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# The integral Brown exceptional adjoint

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-int-brown,
sk-prop-int-brown-adjoint.md and its proof (blueprint: det-prop-int-brown-adjoint).

The left adjoint restricts the recorded compactification composite to Loc(Dbc).
Identification with the general Loc(Dctf) adjoint is expressed in the common ambient
category, by the unique natural isomorphism satisfying the counit equation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Restriction of the recorded compactification composite to Loc(Dbc). Membership
proofs change neither its objects nor its morphisms. This is the functor in
`integralLocalizingCompactSupport`, with its codomain restricted as well.
Source: blueprint sk-prop-int-brown-adjoint, displayed left adjoint
(blueprint: det-prop-int-brown-adjoint). -/
def lowerShriek (c : Compactification f)
    (h : ∀ K, localizing Λ X K → localizing Λ Y ((image Λ c).obj K)) :
    (localizing Λ X).FullSubcategory ⥤ (localizing Λ Y).FullSubcategory :=
  (localizing Λ Y).lift ((localizing Λ X).ι ⋙ image Λ c)
    (fun K ↦ h K.obj K.property)

/-- The shift comparison of the restricted compactification functor is inherited
from the ambient derived functor through the full-subcategory lift.
Source: blueprint sk-prop-int-brown-adjoint, triangulated-category convention
(blueprint: det-prop-int-brown-adjoint). -/
instance lowerShriekCommShift (c : Compactification f)
    (h : ∀ K, localizing Λ X K → localizing Λ Y ((image Λ c).obj K))
    [(localizing Λ X).IsTriangulated] [(localizing Λ Y).IsTriangulated] :
    (lowerShriek Λ c h).CommShift ℤ :=
  inferInstanceAs (((localizing Λ Y).lift ((localizing Λ X).ι ⋙ image Λ c)
    (fun K ↦ h K.obj K.property)).CommShift ℤ)

/-- The assertions of the integral adjoint node, packaged without making a choice
of right adjoint. The closures are the recorded ordinary ambient closures.
`adj` supplies the Hom equivalences, natural in both variables. Its uniqueness
clause compares adjunctions by their counits. The last clause compares with every
right adjoint on the equal Loc(Dctf) categories, hence in particular with the one
supplied by `exists_localizingExceptionalAdjoint`. The comparison forgets only the
membership proofs, so the equation is an equation of the actual ambient counits.
Source: blueprint sk-prop-int-brown-adjoint, all conclusion clauses
(blueprint: det-prop-int-brown-adjoint). -/
def brownAdjointAssertions (c : Compactification.BoundaryCompactification f) : Prop :=
  ∃ (_eX : localizingClosureProEtale Λ X = localizing Λ X)
    (eY : localizingClosureProEtale Λ Y = localizing Λ Y)
    (h : ∀ K, localizing Λ X K → localizing Λ Y ((image Λ c.obj.obj).obj K))
    (hX : (localizing Λ X).IsTriangulated)
    (hY : (localizing Λ Y).IsTriangulated),
    (fun [_triX : (localizing Λ X).IsTriangulated]
        [_triY : (localizing Λ Y).IsTriangulated] ↦
      ∃ G : (localizing Λ Y).FullSubcategory ⥤ (localizing Λ X).FullSubcategory,
        ∃ s : G.CommShift ℤ,
          (fun [_comm : G.CommShift ℤ] ↦
            G.IsTriangulated ∧
            ∃ adj : lowerShriek Λ c.obj.obj h ⊣ G,
              (∀ (J : (localizing Λ Y).FullSubcategory ⥤
                    (localizing Λ X).FullSubcategory)
                  (adjJ : lowerShriek Λ c.obj.obj h ⊣ J),
                ∃! e : G ≅ J, ∀ N,
                  (lowerShriek Λ c.obj.obj h).map (e.hom.app N) ≫
                    adjJ.counit.app N = adj.counit.app N) ∧
              (∀ (hctf : ∀ K, localizingClosureProEtale Λ X K →
                    localizingClosureProEtale Λ Y ((image Λ c.obj.obj).obj K))
                  (J : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
                    (localizingClosureProEtale Λ X).FullSubcategory)
                  (adjJ : localizingLowerShriek Λ c.obj.obj hctf ⊣ J),
                ∃! e : G ⋙ (localizing Λ X).ι ≅
                    ObjectProperty.ιOfLE (le_of_eq eY.symm) ⋙ J ⋙
                      (localizingClosureProEtale Λ X).ι,
                  ∀ N,
                    (image Λ c.obj.obj).map (e.hom.app N) ≫
                        (localizingClosureProEtale Λ Y).ι.map
                          (adjJ.counit.app
                            ((ObjectProperty.ιOfLE (le_of_eq eY.symm)).obj N)) =
                      (localizing Λ Y).ι.map (adj.counit.app N)))
          (_comm := s))
      (_triX := hX) (_triY := hY)

/-- The integral compact-support functor has an exact right adjoint, with natural
Hom equivalences and unique counit-compatible comparisons, including comparison
with the general Brown adjoint for the same condensed integral coefficient.
Source: blueprint main-20261015, sk-prop-int-brown-adjoint.md and its proof
(blueprint: det-prop-int-brown-adjoint).

Proof plan:
1. For Z = X,Y, Spec k is affine and qcqs (lem-weil-pbc-affine-scheme-qcqs).
   The structure morphisms are quasi-compact by def-weil-finite-type-morphism
   and quasi-separated by lem-pc-separated-quasi-separated. Apply clause (2)
   of lem-weil-pbc-qcqs-morphism-permanence to see that X and Y are qcqs.
2. det-def-localizing-closure-ctf-equals-bc(2) identifies Dctf with Dbc and their
   localizing closures, inside the same unbounded module-object categories.
3. The chosen boundary compactification has quasi-compact open leg and proper
   leg (sk-def-nagata-sketch-data). det-prop-int-brown-construction uses exactly
   Rp_* D(j_!) of sk-def-sfb-module-derived-lower-shriek, so its restriction is
   the very same functor as in sk-prop-sf-existence under the equalities in step 2.
4. Specialize sk-prop-sf-existence to the condensed valuation ring O_E and this
   compactification. Transport its exact adjoint and adjunction across the equal
   full subcategories. Its Hom equivalences give the displayed natural bijections;
   its shift structure gives exactness of G, rather than assuming it from existence.
5. Apply det-sp-unique-right-adjoint: transpose each counit under the other
   adjunction. The transposes are inverse and natural, and the Hom equivalence
   makes the counit-compatible comparison unique. Apply this also to any general
   Loc(Dctf) adjoint after the identification in step 2. Full inclusions preserve
   the counits and their equations, proving precisely the final comparison clause.
-/
theorem exists_integralBrownAdjoint (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f) :
    brownAdjointAssertions (Profinite.padicIntegersRingObj ℓ E.val) c := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
