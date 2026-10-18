/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.FormalClosedSupportSheaves
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Derived sections with closed support

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-formal-closed-support,
det-lem-formal-closed-support-derived.md, clauses (1)--(3); Stacks Project, Tag 079P
(blueprint: det-lem-formal-closed-support-derived).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Derived adjunction, global RHom, injective-unit surjectivity, and the natural support
triangle and fibre formula, using exactly the kernel functor of the sheaf-support node.
Source: blueprint main-20261015, det-lem-formal-closed-support-derived, clauses (1)--(3)
(blueprint: det-lem-formal-closed-support-derived).

Proof plan:
1. Finite type over the standing field gives a finite cover by Noetherian affine charts
   (lem-wf-affine-noetherian-components). Every open is quasi-compact, hence j is
   quasi-compact and X is quasi-separated. These are consequences, not extra hypotheses.
2. The sheaf adjunction and exact i_* are det-lem-formal-closed-support-sheaves.
   The exact-left-adjoint derived adjunction is adj.mapDerivedCategoryRightDerivedAdjunction.
   On a K-injective I the total right derived functor is computed by H(I), via
   Functor.rightDerivedFunctorObjQIso. The universal pair of def-sfb-right-derived-functor
   agrees with this pair by its unit-compatible uniqueness. Apply the sheaf adjunction
   componentwise to the Hom complexes: naturality intertwines their two differentials.
   Both I and H(I) are K-injective, giving the displayed global RHom isomorphism.
3. Clause (3) of det-lem-formal-closed-support-adjunction gives the epimorphic open unit
   on injectives, after the canonical coefficient-transport comparison. Equivalently,
   extend j_!j^*I -> I along the monomorphism j_!j^*I -> j_*j^*I by injectivity;
   open full faithfulness makes the extension a section of the unit.
4. Ring-sheaf modules are Grothendieck; lem-pur-kinjective-degreewise-existence resolves
   every unbounded complex by a K-injective complex with injective terms. Exact j_! is
   left adjoint to j^*, so j^* preserves K-injectives. The kernel identification and
   step 3 give a natural degreewise short exact sequence i_*H(I) -> I -> j_*j^*I.
5. Apply lem-weil-pbc-complex-ses-triangle. Exact i_* computes its derived action.
   The termwise homotopy adjunction and the Hom bijection into K-injectives show that
   its second arrow is precisely the derived unit. Chain maps between resolutions
   represent all derived morphisms; additive functors preserve homotopies. Therefore
   the connecting arrows descend to the natural transformation delta in the statement.
6. Rotate the distinguished triangle and compare it with the cone triangle of this
   unit. TR3 and lem-sf-triangle-morphism-iso identify i_*RH(K) with its shifted cone.
   Apply exact i^* and its counit i^*i_* = id, giving the fibre formula. This uses the
   actual unit on I, not a functorial cone chosen in an arbitrary triangulated category.

The existential additive instance and ordinary adjunction only expose the structures
already asserted by the sheaf-support dependency. They impose no new assumptions.
The derived adjunction in (1) is the existing construction from this adjunction; its
counit is the first triangle arrow. The component formula specifies the natural global
RHom comparison. Every derived object admits the K-injective representative used in the
last clause, whose cone shifted by -1 is the fibre of the specified derived unit.
-/
theorem formal_closed_support_derived
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Z V : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (j : V ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (hij : Set.range j = (Set.range i)ᶜ) :
    ∃ (_ : (closedModuleSectionsWithSupport Λ i j).Additive),
      ∃ adj : lowerStar Λ i ⊣ closedModuleSectionsWithSupport Λ i j,
        (∀ (A : CochainComplex (pulledBackModuleObjects Λ Z) ℤ)
          (I : CochainComplex (pulledBackModuleObjects Λ X) ℤ) [I.IsKInjective],
          ∃ e : CochainComplex.HomComplex
              (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I ≅
            CochainComplex.HomComplex A
              (((closedModuleSectionsWithSupport Λ i j).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I),
            ∀ (n : ℤ) (a : CochainComplex.HomComplex.Cochain
              (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I n)
              (p q : ℤ) (hpq : p + n = q),
              (e.hom.f n a) ⟨p, q, hpq⟩ =
                adj.homEquiv (A.X p) (I.X q) (a ⟨p, q, hpq⟩)) ∧
        (∀ (I : pulledBackModuleObjects Λ X) [Injective I],
          Epi ((upperStarLowerStarAdjunction Λ j).unit.app I)) ∧
        (∃ δ : (upperStar Λ j).mapDerivedCategory ⋙ (lowerStar Λ j).rightDerivedFunctor ⟶
            ((closedModuleSectionsWithSupport Λ i j).rightDerivedFunctor ⋙
              (lowerStar Λ i).mapDerivedCategory) ⋙
                shiftFunctor (DerivedCategory (pulledBackModuleObjects Λ X)) (1 : ℤ),
          ∀ K : DerivedCategory (pulledBackModuleObjects Λ X),
            Triangle.mk (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app K)
              ((upperStarLowerStarAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction.unit.app
                K)
              (δ.app K) ∈ Pretriangulated.distinguishedTriangles) ∧
        (∀ (K : DerivedCategory (pulledBackModuleObjects Λ X))
          (I : CochainComplex (pulledBackModuleObjects Λ X) ℤ) [I.IsKInjective]
          (_e : K ≅ DerivedCategory.Q.obj I),
          Nonempty ((closedModuleSectionsWithSupport Λ i j).rightDerivedFunctor.obj K ≅
            (upperStar Λ i).mapDerivedCategory.obj
              (DerivedCategory.Q.obj
                ((shiftFunctor (CochainComplex (pulledBackModuleObjects Λ X) ℤ) (-1 : ℤ)).obj
                  (CochainComplex.mappingCone
                    ((NatTrans.mapHomologicalComplex (upperStarLowerStarAdjunction Λ j).unit
                      (ComplexShape.up ℤ)).app I)))))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
