module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.CohomologyPullbackCanonicalArrows
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.ExchangeStrictLocalCohomology
import Sheaf.AlgebraicGeometry.StrictBaseClosedPointLocalizations
import WeilConjectures.AlgebraicGeometry.StrictHenselization
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
import Sheaf.Paper.StrictHenselizationFunctoriality
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Smooth-source constructible local acyclicity

Source: literature/stacks-project/etale-cohomology.tex, Proposition 0GJQ
(proposition-smooth-locally-acyclic);
(blueprint: lem-trf-smooth-source-constructible-local-acyclicity).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The canonical morphism between the two strict-local fibre products induced by a smooth
source morphism. Source: Stacks Project, Proposition 0GJQ (blueprint:
lem-trf-smooth-source-constructible-local-acyclicity). -/
noncomputable def smoothSourceStrictLocalBaseChangeMap
    {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    {Ωt : Type u} [Field Ωt] [IsAlgClosed Ωt]
    (t : Spec (.of Ωt) ⟶ S)
    (c : Scheme.strictHenselizationScheme t ⟶
      Scheme.strictHenselizationScheme ((x ≫ h) ≫ g)) :
    pullback (Scheme.strictHenselizationMap h x ≫
      Scheme.strictHenselizationMap g (x ≫ h)) c ⟶
      pullback (Scheme.strictHenselizationMap g (x ≫ h)) c :=
  pullback.map (Scheme.strictHenselizationMap h x ≫
      Scheme.strictHenselizationMap g (x ≫ h)) c
    (Scheme.strictHenselizationMap g (x ≫ h)) c (Scheme.strictHenselizationMap h x) (𝟙 _)
    (𝟙 _)
    (by simp)
    (by simp)

/-- Derived global sections pullback map along a scheme morphism. Source: Stacks Project,
Proposition 0GJQ (blueprint: lem-trf-smooth-source-constructible-local-acyclicity). -/
noncomputable def derivedGlobalSectionsPullbackMap
    (Λ : Type (u + 1)) [CommRing Λ]
    {U V : Scheme.{u}} (q : U ⟶ V)
    (K : DerivedCategoryModule Λ V) :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) V).obj K ⟶
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) U).obj
        ((upperStar (ModuleCat.{u + 1} Λ) q).mapDerivedCategory.obj K) :=
  (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) V).map
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app K) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
      (ModuleCat.{u + 1} Λ) q).hom.app
      ((upperStar (ModuleCat.{u + 1} Λ) q).mapDerivedCategory.obj K)

/-- Smooth source local acyclicity for bounded constructible complexes. Source: Stacks Project,
Proposition 0GJQ (blueprint: lem-trf-smooth-source-constructible-local-acyclicity).
The proof follows the strict-local smooth-base-change argument of Tags 0GJQ, 0EYU and 0EZU,
then extends degreewise isomorphisms from torsion sheaves to bounded complexes by standard
truncation triangles and identifies module and abelian coefficients by exact scalar forgetting. -/
theorem smoothSourceConstructibleLocalAcyclicity
    {X Y S : Scheme.{u}} [IsNoetherian S]
    (h : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    [Smooth h] [LocallyOfFinitePresentation h] [QuasiCompact h] [QuasiSeparated h]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (m : ℤ) (hmΛ : (m : Λ) = 0) (hmS : IsUnit (m : Γ(S, ⊤)))
    (L : DerivedCategoryModule Λ Y)
    (hL : DerivedCategory.isBoundedConstructible Λ Y L)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    {Ωt : Type u} [Field Ωt] [IsAlgClosed Ωt]
    (t : Spec (.of Ωt) ⟶ S)
    (c : Scheme.strictHenselizationScheme t ⟶
      Scheme.strictHenselizationScheme ((x ≫ h) ≫ g)) :
    IsIso (derivedGlobalSectionsPullbackMap Λ
      (smoothSourceStrictLocalBaseChangeMap h g x t c)
      ((upperStar (ModuleCat.{u + 1} Λ)
        (pullback.fst (Scheme.strictHenselizationMap g (x ≫ h)) c ≫
          Scheme.strictHenselizationStructuralMap (x ≫ h))).mapDerivedCategory.obj L)) ∧
      ∀ (L' : DerivedCategoryModule Λ Y),
        DerivedCategory.isBoundedConstructible Λ Y L' →
        ∀ (φ : L ⟶ L'),
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ)
            (pullback (Scheme.strictHenselizationMap g (x ≫ h)) c)).map
              ((upperStar (ModuleCat.{u + 1} Λ)
                (pullback.fst (Scheme.strictHenselizationMap g (x ≫ h)) c ≫
                  Scheme.strictHenselizationStructuralMap (x ≫ h))).mapDerivedCategory.map φ) ≫
            derivedGlobalSectionsPullbackMap Λ
              (smoothSourceStrictLocalBaseChangeMap h g x t c)
              ((upperStar (ModuleCat.{u + 1} Λ)
                (pullback.fst (Scheme.strictHenselizationMap g (x ≫ h)) c ≫
                  Scheme.strictHenselizationStructuralMap (x ≫ h))).mapDerivedCategory.obj L') =
          derivedGlobalSectionsPullbackMap Λ
            (smoothSourceStrictLocalBaseChangeMap h g x t c)
            ((upperStar (ModuleCat.{u + 1} Λ)
              (pullback.fst (Scheme.strictHenselizationMap g (x ≫ h)) c ≫
                Scheme.strictHenselizationStructuralMap (x ≫ h))).mapDerivedCategory.obj L) ≫
            (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ)
              (pullback (Scheme.strictHenselizationMap h x ≫
                Scheme.strictHenselizationMap g (x ≫ h)) c)).map
              ((upperStar (ModuleCat.{u + 1} Λ)
                (smoothSourceStrictLocalBaseChangeMap h g x t c)).mapDerivedCategory.map
                ((upperStar (ModuleCat.{u + 1} Λ)
                  (pullback.fst (Scheme.strictHenselizationMap g (x ≫ h)) c ≫
                    Scheme.strictHenselizationStructuralMap (x ≫ h))).mapDerivedCategory.map
                  φ)) := by
  sorry

end AlgebraicGeometry.Etale
