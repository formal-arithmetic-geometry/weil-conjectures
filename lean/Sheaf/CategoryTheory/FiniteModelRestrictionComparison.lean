module

public import Sheaf.CategoryTheory.FiniteExactComplexDerivedModel
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import WeilConjectures.Algebra.Homology.FiniteStripAugmentation
import Mathlib.Algebra.Homology.ModelCategory.Injective
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Exact restriction comparison from finite cochain models

Source: blueprint direct-image stability proof, paragraph (3); Stacks Project,
Derived Categories, Tags 013P, 013S and 0156, and Homology, Tag 0133
(blueprint: lem-sfb-finite-model-restriction-comparison).

Localization comparison factors are explicit. No preservation of injective objects
by the restriction functor is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA uA' vA' uB vB uB' vB' wA wA' wB wB'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.FiniteExactComplex

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A']
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B']
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA'} A']
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wB'} B']

/-- Extract the normalized natural isomorphism supplied by the finite exact model theorem.
Its resolution formula, for every resolution, uniquely determines this isomorphism;
this is not a choice of an arbitrary derived comparison.
Source: Stacks Tag 0133 and blueprint paragraph (3)
(blueprint: lem-sfb-finite-model-restriction-comparison). -/
def normalizedModelComparison [EnoughInjectives A]
    (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G]
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    [RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ))]
    (hη : ∀ (I : CochainComplex A ℤ),
      (∃ a : ℤ, ∀ b : ℤ, b < a → IsZero (I.X b)) →
      (∀ b : ℤ, Injective (I.X b)) → IsIso (η.app I))
    (r : ℕ) (F : A ⥤ CochainComplex B ℤ) [F.Additive]
    (hF : ∀ (X : A) (a : ℤ), a < 0 ∨ (r : ℤ) < a → IsZero ((F.obj X).X a))
    (hExact : ∀ a : ℤ,
      PreservesFiniteLimits (F ⋙ HomologicalComplex.eval B (.up ℤ) a) ∧
      PreservesFiniteColimits (F ⋙ HomologicalComplex.eval B (.up ℤ) a))
    (e : G ⋙ HomologicalComplex.single B (.up ℤ) 0 ⟶ F)
    (he : ∀ (X : A) [Injective X], QuasiIso (e.app X)) :
    F ⋙ DerivedCategory.Q ≅ DerivedCategory.singleFunctor A 0 ⋙ RG :=
  Classical.choose (finite_exact_complex_derived_model G RG η hη r F hF hExact e he)

/-- Apply exact restriction to an augmentation, with its canonical single-complex transport.
Source: Stacks Tag 013P (blueprint: lem-sfb-finite-model-restriction-comparison). -/
def restrictedAugmentation (U : A' ⥤ A) [U.Additive]
    {X : A'} {J : CochainComplex A' ℤ}
    (t : (HomologicalComplex.single A' (.up ℤ) 0).obj X ⟶ J) :
    (HomologicalComplex.single A (.up ℤ) 0).obj (U.obj X) ⟶
      (U.mapHomologicalComplex (.up ℤ)).obj J :=
  (HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).inv.app X ≫
    (U.mapHomologicalComplex (.up ℤ)).map t

/-- The degreewise ordinary comparison, including the composition transports.
Source: blueprint paragraph (3), coefficient square
(blueprint: lem-sfb-finite-model-restriction-comparison). -/
def restrictionComplexComparison (G : A ⥤ B) [G.Additive]
    (G' : A' ⥤ B') [G'.Additive] (U : A' ⥤ A) [U.Additive]
    (V : B' ⥤ B) [V.Additive] (γ : U ⋙ G ≅ G' ⋙ V) (J : CochainComplex A' ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).obj ((U.mapHomologicalComplex (.up ℤ)).obj J) ≅
      (V.mapHomologicalComplex (.up ℤ)).obj ((G'.mapHomologicalComplex (.up ℤ)).obj J) :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl (U ⋙ G)) (.up ℤ)).app J ≪≫
    (NatIso.mapHomologicalComplex γ (.up ℤ)).app J ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (G' ⋙ V)) (.up ℤ)).app J).symm

/-- Exact restriction has the unique natural derived comparison specified by the finite
models, by every resolution-and-extension formula, and by the inverse unit formula.
Source: blueprint direct-image stability proof paragraph (3); Stacks Tags 013P, 013S,
0156 and 0133 (blueprint: lem-sfb-finite-model-restriction-comparison).

Proof, following the eight steps of the node:
1. Exactness of U makes Ut a quasi-isomorphism and degreewise monomorphism: degree zero
is the kernel inclusion and the other source terms are zero. Lift s along Ut into the
nonnegative injective I by lem-weil-pbc-lift-along-injective-quasi-iso. Two lifts are
homotopic by lem-weil-pbc-lift-to-injective-unique-up-to-homotopy. Additivity of G maps
this homotopy to one after G, so localization gives the asserted equality.
2. Apply lem-sfb-finite-exact-complex-derived-model separately to the two models and
resolutions, obtaining the quasi-isomorphisms c_s,b_s,c'_t,b'_t and normalized lambdas.
3. Totalize F(UJ) with d_F+(-1)^a d_J. The given theta and the canonical additive
finite-biproduct comparisons identify this total with V Tot(F'(J)). On the axes the
augmentation square gives Theta b=V(b'_t) gamma_J and Theta c=V(c'_t) theta_X.
4. Each row augmentation e_(UJ^b) is a quasi-isomorphism, since theta identifies it
with V(e'_(J^b)) and J^b is injective. Apply lem-sc-finite-strip-row-augmentation with
strip width r+1. Hence b is a quasi-isomorphism; the other axis equation gives the
same for c, using exactness of V and the finite-model theorem for c'_t.
5. The total map k induced by beta satisfies kb=b_s G(beta) and kc=c_s.
Two-of-three first proves k and then G(beta) are quasi-isomorphisms.
6. Invert these maps after Q. Substitute the two axis equations and the normalized
lambda formulas, cancelling k,b,b_s, to obtain the finite-model comparison equation.
7. That equation uniquely specifies alpha as lambda_U inverse, followed by Q(theta),
then V(lambda'). Thus it is independent of all choices and natural in X'. The formula
for every pair of resolutions and every beta records this independence explicitly.
8. Naturality of eta on beta and s=beta Ut yield
rho_s inverse followed by QG(beta) = eta_UJ followed by RG(Q(Ut)) inverse.
Invert the resolution formula for alpha. Cancelling gives exactly the final equation,
which is the inverse comparison normalized by the derived unit, without assuming UJ
injective. Exact-functor cohomology (lem-weil-pbc-exact-functor-complex-cohomology)
justifies preservation of all quasi-isomorphisms used here. -/
theorem finite_model_restriction_comparison [EnoughInjectives A] [EnoughInjectives A']
    (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G]
    (G' : A' ⥤ B') [G'.Additive] [PreservesFiniteLimits G']
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (RG' : DerivedCategory A' ⥤ DerivedCategory B')
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (η' : G'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG')
    [RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ))]
    [RG'.IsRightDerivedFunctor η' (HomologicalComplex.quasiIso A' (.up ℤ))]
    (hη : ∀ (I : CochainComplex A ℤ),
      (∃ a : ℤ, ∀ b : ℤ, b < a → IsZero (I.X b)) →
      (∀ b : ℤ, Injective (I.X b)) → IsIso (η.app I))
    (hη' : ∀ (J : CochainComplex A' ℤ),
      (∃ a : ℤ, ∀ b : ℤ, b < a → IsZero (J.X b)) →
      (∀ b : ℤ, Injective (J.X b)) → IsIso (η'.app J))
    (r : ℕ) (F : A ⥤ CochainComplex B ℤ) [F.Additive]
    (F' : A' ⥤ CochainComplex B' ℤ) [F'.Additive]
    (hF : ∀ (X : A) (a : ℤ), a < 0 ∨ (r : ℤ) < a → IsZero ((F.obj X).X a))
    (hF' : ∀ (X : A') (a : ℤ), a < 0 ∨ (r : ℤ) < a → IsZero ((F'.obj X).X a))
    (hExact : ∀ a : ℤ,
      PreservesFiniteLimits (F ⋙ HomologicalComplex.eval B (.up ℤ) a) ∧
      PreservesFiniteColimits (F ⋙ HomologicalComplex.eval B (.up ℤ) a))
    (hExact' : ∀ a : ℤ,
      PreservesFiniteLimits (F' ⋙ HomologicalComplex.eval B' (.up ℤ) a) ∧
      PreservesFiniteColimits (F' ⋙ HomologicalComplex.eval B' (.up ℤ) a))
    (e : G ⋙ HomologicalComplex.single B (.up ℤ) 0 ⟶ F)
    (e' : G' ⋙ HomologicalComplex.single B' (.up ℤ) 0 ⟶ F')
    (he : ∀ (X : A) [Injective X], QuasiIso (e.app X))
    (he' : ∀ (X : A') [Injective X], QuasiIso (e'.app X))
    (U : A' ⥤ A) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (V : B' ⥤ B) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (γ : U ⋙ G ≅ G' ⋙ V) (θ : U ⋙ F ≅ F' ⋙ V.mapHomologicalComplex (.up ℤ))
    (hcompat : ∀ X : A', e.app (U.obj X) ≫ θ.hom.app X =
      (HomologicalComplex.single B (.up ℤ) 0).map (γ.hom.app X) ≫
        (HomologicalComplex.singleMapHomologicalComplex V (.up ℤ) 0).inv.app (G'.obj X) ≫
          (V.mapHomologicalComplex (.up ℤ)).map (e'.app X)) :
    ∃! α : U ⋙ DerivedCategory.singleFunctor A 0 ⋙ RG ≅
        DerivedCategory.singleFunctor A' 0 ⋙ RG' ⋙ V.mapDerivedCategory,
      (∀ X : A',
        (normalizedModelComparison G RG η hη r F hF hExact e he).hom.app (U.obj X) ≫
            α.hom.app X =
          DerivedCategory.Q.map (θ.hom.app X) ≫
            V.mapDerivedCategoryFactors.inv.app (F'.obj X) ≫
            V.mapDerivedCategory.map
              ((normalizedModelComparison G' RG' η' hη' r F' hF' hExact' e' he').hom.app X)) ∧
      (∀ (X : A') (J : CochainComplex A' ℤ)
        (hJ : ∀ b : ℤ, b < 0 → IsZero (J.X b)) (hJinj : ∀ b : ℤ, Injective (J.X b))
        (t : (HomologicalComplex.single A' (.up ℤ) 0).obj X ⟶ J) [QuasiIso t]
        (I : CochainComplex A ℤ)
        (hI : ∀ b : ℤ, b < 0 → IsZero (I.X b)) (hIinj : ∀ b : ℤ, Injective (I.X b))
        (s : (HomologicalComplex.single A (.up ℤ) 0).obj (U.obj X) ⟶ I) [QuasiIso s],
        (∃ β : (U.mapHomologicalComplex (.up ℤ)).obj J ⟶ I,
          restrictedAugmentation U t ≫ β = s) ∧
        (∀ β₁ β₂ : (U.mapHomologicalComplex (.up ℤ)).obj J ⟶ I,
          restrictedAugmentation U t ≫ β₁ = s → restrictedAugmentation U t ≫ β₂ = s →
          Nonempty (Homotopy β₁ β₂) ∧
          DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map β₁) =
            DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map β₂)) ∧
        (∀ β : (U.mapHomologicalComplex (.up ℤ)).obj J ⟶ I,
          restrictedAugmentation U t ≫ β = s →
          QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map β) ∧
          (resolutionComparison G RG η s (hη I ⟨0, hI⟩ hIinj)).hom =
            α.hom.app X ≫
              V.mapDerivedCategory.map
                (resolutionComparison G' RG' η' t (hη' J ⟨0, hJ⟩ hJinj)).hom ≫
              V.mapDerivedCategoryFactors.hom.app ((G'.mapHomologicalComplex (.up ℤ)).obj J) ≫
              DerivedCategory.Q.map (restrictionComplexComparison G G' U V γ J).inv ≫
              DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map β)) ∧
        (α.inv.app X ≫ RG.map (DerivedCategory.Q.map (restrictedAugmentation U t)) =
          V.mapDerivedCategory.map
              (resolutionComparison G' RG' η' t (hη' J ⟨0, hJ⟩ hJinj)).hom ≫
            V.mapDerivedCategoryFactors.hom.app ((G'.mapHomologicalComplex (.up ℤ)).obj J) ≫
            DerivedCategory.Q.map (restrictionComplexComparison G G' U V γ J).inv ≫
            η.app ((U.mapHomologicalComplex (.up ℤ)).obj J))) := by
  sorry

end CategoryTheory.FiniteExactComplex
