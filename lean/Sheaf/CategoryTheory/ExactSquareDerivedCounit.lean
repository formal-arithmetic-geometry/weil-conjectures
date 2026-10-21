/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.SixFunctors.ResolvingDerivedAdjunction

/-!
# Counits in an exact square of derived adjunctions

Source: Stacks Project, Derived Categories, Tags 09T5 and 070Y; exact-square extraction
of tower normalization, steps 6--8 (blueprint: lem-weil-pbc-exact-square-derived-counit).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA uAp uB uBp vA vAp vB vBp wA wAp wB wBp

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type uA} {Ap : Type uAp} {B : Type uB} {Bp : Type uBp}
  [Category.{vA} A] [Category.{vAp} Ap] [Category.{vB} B] [Category.{vBp} Bp]
  [Abelian A] [Abelian Ap] [Abelian B] [Abelian Bp]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wAp} Ap]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wBp} Bp]

/-- The Hom formula specifying the derived adjunction on the fixed functors and fixed
right-derived unit, for every chain map. Source: Stacks Tag 09T5, with Tag 070Y
(blueprint: lem-weil-pbc-exact-square-derived-counit). -/
def Adjunction.HasExactDerivedHomFormula
    (F : B ⥤ A) (G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (d : F.mapDerivedCategory ⊣ RG) : Prop :=
  ∀ (M : CochainComplex B ℤ) (I : CochainComplex A ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
    d.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
        (F.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv M I f) ≫ η.app I

/-- Exact-square compatibility of canonically normalized derived adjunction counits.
Source: Stacks Tags 09T5 (lemma-derived-adjoint-functors) and 070Y
(lemma-K-injective-defined); exact-square extraction of tower normalization steps 6--8
(blueprint: lem-weil-pbc-exact-square-derived-counit).

Proof plan:
1. Use lem-weil-pbc-termwise-adjunction-homotopy for the termwise adjunctions.
   Exactness gives the canonical factorizations and universal left-derived pairs by
   lem-weil-pbc-exact-functor-derived-factorization and
   lem-weil-pbc-exact-functor-derived-functor. Apply
   lem-sfb-resolving-derived-adjunction-normalization with the whole homotopy category
   as resolving class. Work in a common ambient universe for the chosen Hom sets.
   This constructs the two adjunctions on the independently fixed right-derived pairs,
   with the displayed Hom formulas for every chain map.
2. Substitute the ordinary counit for f in the Hom formula. Its ordinary transpose is
   the identity, so inverse derived transposition gives the two counit normalizations.
3. The fixed right-derived units are invertible on K-injectives by
   def-sfb-right-derived-functor. Cancelling their left-adjoint images determines the
   counits there. Every derived object is isomorphic to such a representative by the
   resolution hypotheses and def-weil-abstract-derived-category. Naturality determines
   the counits everywhere, and hence both adjunctions uniquely from their Hom formulas.
4. At QJ for J K-injective, precompose both proposed square arrows with
   D(F)(D(s)(eta'_J)). This is invertible. The first composite is the localization of
   r applied to the ordinary primed counit, hence of the unprimed counit by hε.
   For the second use hβ and the unprimed counit normalization; rJ is K-injective by hr.
   Cancel this common invertible precomposition.
5. Both square arrows are natural. Transport their equality from QJ to any derived
   object using an isomorphism to a K-injective representative and cancel its image
   under D(r). Only hβ on K-injectives enters this calculation. -/
theorem exactSquare_derived_counit
    (hA : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q)
    (hAp : ∀ K : CochainComplex Ap ℤ,
      ∃ (J : CochainComplex Ap ℤ) (q : K ⟶ J), J.IsKInjective ∧ QuasiIso q)
    (Fp : Bp ⥤ Ap) (Gp : Ap ⥤ Bp) (F : B ⥤ A) (G : A ⥤ B)
    [Fp.Additive] [Gp.Additive] [F.Additive] [G.Additive]
    [PreservesFiniteLimits Fp] [PreservesFiniteColimits Fp]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adjp : Fp ⊣ Gp) (adj : F ⊣ G)
    (r : Ap ⥤ A) (s : Bp ⥤ B) [r.Additive] [s.Additive]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (hF : Fp ⋙ r = s ⋙ F) (hG : Gp ⋙ s = r ⋙ G)
    (hε : ∀ X : Ap, r.map (adjp.counit.app X) =
      (eqToIso hF).hom.app (Gp.obj X) ≫ F.map ((eqToIso hG).hom.app X) ≫
        adj.counit.app (r.obj X))
    (hr : ∀ J : CochainComplex Ap ℤ, J.IsKInjective →
      CochainComplex.IsKInjective ((r.mapHomologicalComplex (.up ℤ)).obj J))
    (RGp : DerivedCategory Ap ⥤ DerivedCategory Bp)
    (ηp : Gp.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RGp)
    (hRGp : RGp.IsRightDerivedFunctor ηp (HomologicalComplex.quasiIso Ap (.up ℤ)))
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (hRG : RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ)))
    (β : RGp ⋙ s.mapDerivedCategory ≅ r.mapDerivedCategory ⋙ RG)
    (hβ : ∀ J : CochainComplex Ap ℤ, J.IsKInjective →
      s.mapDerivedCategory.map (ηp.app J) ≫ β.hom.app (DerivedCategory.Q.obj J) ≫
          RG.map (r.mapDerivedCategoryFactors.hom.app J) =
        s.mapDerivedCategoryFactors.hom.app
            ((Gp.mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (eqToIso hG) (.up ℤ)).hom.app J) ≫
          η.app ((r.mapHomologicalComplex (.up ℤ)).obj J)) :
    ∃ (dp : Fp.mapDerivedCategory ⊣ RGp) (d : F.mapDerivedCategory ⊣ RG),
      Adjunction.HasExactDerivedHomFormula Fp Gp adjp RGp ηp dp ∧
      Adjunction.HasExactDerivedHomFormula F G adj RG η d ∧
      (∀ ep : Fp.mapDerivedCategory ⊣ RGp,
        Adjunction.HasExactDerivedHomFormula Fp Gp adjp RGp ηp ep → ep = dp) ∧
      (∀ e : F.mapDerivedCategory ⊣ RG,
        Adjunction.HasExactDerivedHomFormula F G adj RG η e → e = d) ∧
      (∀ I : CochainComplex A ℤ, I.IsKInjective →
        F.mapDerivedCategory.map (η.app I) ≫ d.counit.app (DerivedCategory.Q.obj I) =
          F.mapDerivedCategoryFactors.hom.app
              ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
            DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app I)) ∧
      (∀ J : CochainComplex Ap ℤ, J.IsKInjective →
        Fp.mapDerivedCategory.map (ηp.app J) ≫ dp.counit.app (DerivedCategory.Q.obj J) =
          Fp.mapDerivedCategoryFactors.hom.app
              ((Gp.mapHomologicalComplex (.up ℤ)).obj J) ≫
            DerivedCategory.Q.map ((adjp.mapHomologicalComplex (.up ℤ)).counit.app J)) ∧
      (∀ N : DerivedCategory Ap,
        r.mapDerivedCategory.map (dp.counit.app N) =
          (Functor.mapDerivedCategorySquareIso (eqToIso hF)).hom.app (RGp.obj N) ≫
            F.mapDerivedCategory.map (β.hom.app N) ≫
            d.counit.app (r.mapDerivedCategory.obj N)) := by
  sorry

end CategoryTheory
