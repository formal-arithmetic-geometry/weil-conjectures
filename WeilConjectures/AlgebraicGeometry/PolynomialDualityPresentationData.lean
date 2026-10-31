/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeDualizingPair
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
public import WeilConjectures.Algebra.Homology.DerivedCoinductionAdjunction
public import WeilConjectures.AlgebraicGeometry.SheafCoinductionAdjunction
public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage



/-! # PolynomialDualityPresentationData

Source: Stacks duality.tex, 0E2X and 0BV2; dualizing.tex, 0BZI and 0BZJ.
(blueprint: def-trf-polynomial-duality-presentation-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory TopologicalSpace
namespace AlgebraicGeometry

/-- The affine associated-sheaf functor is left adjoint to actual global sections.
Source: Stacks 01I7 (blueprint: def-trf-polynomial-duality-presentation-data). -/
instance polynomialTildeIsLeftAdjoint (A : Type u) [CommRing A] :
    (tilde.functor (.of A)).IsLeftAdjoint :=
  (tilde.adjunction (R := .of A)).isLeftAdjoint

/-- Additivity supplied by the actual tilde/Gamma adjunction.
Source: Stacks 01I7 (blueprint: def-trf-polynomial-duality-presentation-data). -/
instance polynomialTildeAdditive (A : Type u) [CommRing A] :
    (tilde.functor (.of A)).Additive := by
  let _ := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tilde.functor (.of A))
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Use the recorded exactness of affine associated sheafification.
Source: Stacks 01HV (blueprint: def-trf-polynomial-duality-presentation-data). -/
instance polynomialTildeFiniteLimits (A : Type u) [CommRing A] :
    PreservesFiniteLimits (tilde.functor (.of A)) :=
  tilde_preserves_finite_limits A

/-- An arbitrary polynomial chart, without regularity or equidimensionality assumptions.
Source: Stacks 0BV2 (blueprint: def-trf-polynomial-duality-presentation-data). -/
structure RelativeDualityPolynomialChart {X S : Scheme.{u}} (f : X ⟶ S) where
  U : X.Opens
  n : ℕ
  P : Scheme.{u}
  ambient : P ⟶ AffineSpace (ULift.{u} (Fin n)) S
  ambient_open : IsOpenImmersion ambient
  i : U.toScheme ⟶ P
  closed : IsClosedImmersion i
  factor : i ≫ ambient ≫ pullback.fst _ _ = U.ι ≫ f

/-- The top differential coefficient, in degree minus the number of variables.
Source: Stacks 0BZI (blueprint: def-trf-polynomial-duality-presentation-data). -/
def RelativeDualityPolynomialChart.coefficient {X S : Scheme.{u}} {f : X ⟶ S}
    (C : RelativeDualityPolynomialChart f)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings C.P.toRingedSpace))] :
    schemeDerivedCategory C.P :=
  ((DerivedCategory.singleFunctor _ 0).obj
    (Scheme.Modules.exteriorSheaf
      (C.ambient ≫ pullback.fst _ _).relativeDifferentials C.n))⟦(C.n : ℤ)⟧

/-- A single primary ordinary coinduction presentation, retaining its adjunction.
Source: Stacks 0BUZ (blueprint: def-trf-polynomial-duality-presentation-data). -/
structure PolynomialChartCoinductionPresentation {U P : Scheme.{u}} (i : U ⟶ P) where
  H : SheafOfModules.{u} (moduleRings P.toRingedSpace) ⥤
    SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))
  adjunction : SheafOfModules.restrictScalars.{u} i.toRingCatSheafHom ⊣ H
  normalized : ∃ e : H ⋙ SheafOfModules.restrictScalars.{u} i.toRingCatSheafHom ≅
      (SheafOfModules.homFunctor P.sheaf).obj
        (op ((SheafOfModules.restrictScalars.{u} i.toRingCatSheafHom).obj
          (SheafOfModules.unit (moduleRings (directImageAlgebraSpace i))))),
    (∀ (F : SheafOfModules.{u} (moduleRings P.toRingedSpace)) (V : P.Opens)
      (a : (moduleRings (directImageAlgebraSpace i)).obj.obj (op V))
      (φ : (H.obj F).val.obj (op V)) (W : Over V)
      (b : (moduleRings (directImageAlgebraSpace i)).obj.obj (op W.left)),
      (((e.hom.app F).val.app (op V)).hom (a • φ)).app (op W) b =
        (((e.hom.app F).val.app (op V)).hom φ).app (op W)
          ((moduleRings (directImageAlgebraSpace i)).obj.map W.hom.op a * b)) ∧
    (∀ (F : SheafOfModules.{u} (moduleRings P.toRingedSpace)) (V : P.Opens)
      (φ : (H.obj F).val.obj (op V)),
      ((adjunction.counit.app F).val.app (op V)).hom φ =
        ((((e.hom.app F).val.app (op V)).hom φ).app (op (Over.mk (𝟙 V))))
          (1 : (moduleRings (directImageAlgebraSpace i)).obj.obj (op V)))

/-- Project one complete witness of the proved evaluation-at-one adjunction once.
The functor and adjunction are selected together from that same witness.
Source: Stacks 0BUZ (blueprint: def-trf-polynomial-duality-presentation-data). -/
@[irreducible] def polynomialChartCoinductionPresentation {U P : Scheme.{u}} (i : U ⟶ P) :
    PolynomialChartCoinductionPresentation i :=
  Classical.choice (by
    obtain ⟨H, e, adj, ha, hc⟩ := sheafHom_restrictScalars_adjunction i
    exact ⟨⟨H, adj, ⟨e, ha, hc⟩⟩⟩)

/-- Ordinary Hom coinduction with its multiplication action, from the primary presentation.
Source: Stacks 0BUZ (blueprint: def-trf-polynomial-duality-presentation-data). -/
@[irreducible] def polynomialChartCoinduction {U P : Scheme.{u}} (i : U ⟶ P) :
    SheafOfModules.{u} (moduleRings P.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i)) :=
  (polynomialChartCoinductionPresentation i).H

/-- The derived chart Hom with its actual i_*O_U-action, computed on K-injectives.
Source: Stacks 0BV2, 0A70 (blueprint: def-trf-polynomial-duality-presentation-data). -/
def RelativeDualityPolynomialChart.model {X S : Scheme.{u}} {f : X ⟶ S}
    (C : RelativeDualityPolynomialChart f)
    (hAdd : (polynomialChartCoinduction C.i).Additive)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings C.P.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace C.i)))] :
    DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace C.i))) :=
  letI := hAdd
  (polynomialChartCoinduction C.i).rightDerivedFunctor.obj C.coefficient

/-- The ordered top differential module of the standard polynomial ring.
Source: Stacks 0BZI (blueprint: def-trf-polynomial-duality-presentation-data). -/
def polynomialDualityTop (R : Type u) [CommRing R] (n : ℕ) :
    ModuleCat.{u} (MvPolynomial (Fin n) R) :=
  ModuleCat.of _ (⋀[MvPolynomial (Fin n) R]^n
    (KaehlerDifferential R (MvPolynomial (Fin n) R)))

/-- The ordered volume dx_0 wedge ... wedge dx_(n-1), including the empty wedge.
Source: Stacks 0BZI (blueprint: def-trf-polynomial-duality-presentation-data). -/
def polynomialDualityVolume (R : Type u) [CommRing R] (n : ℕ) : polynomialDualityTop R n :=
  exteriorPower.ιMulti _ n (fun j : Fin n ↦
    KaehlerDifferential.D R (MvPolynomial (Fin n) R) (MvPolynomial.X j))

/-- The coefficient Omega^n[n] in the ordinary module derived category.
Source: Stacks 0BZI (blueprint: def-trf-polynomial-duality-presentation-data). -/
def polynomialDualityCoefficient (R : Type u) [CommRing R] (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (MvPolynomial (Fin n) R)) :=
  ((DerivedCategory.singleFunctor _ 0).obj (polynomialDualityTop R n))⟦(n : ℤ)⟧

/-- The polynomial model with the coinduced A-action, rather than its underlying P-object.
Source: Stacks 0BZI, 0A70 (blueprint: def-trf-polynomial-duality-presentation-data). -/
def polynomialDualityModel {R A : Type u} [CommRing R] [CommRing A]
    (n : ℕ) (p : MvPolynomial (Fin n) R →+* A) : DerivedCategory (ModuleCat.{u} A) :=
  (ModuleCat.derivedCoinduction p).obj (polynomialDualityCoefficient R n)

/-- Forget the last polynomial variable by evaluating it at g. Its kernel generator
is X_last - g, with old variables first. Source: Stacks 0BZJ
(blueprint: def-trf-polynomial-duality-presentation-data). -/
def polynomialDualityRefinement (R : Type u) [CommRing R] (n : ℕ)
    (g : MvPolynomial (Fin n) R) :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin n) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Fin.lastCases g MvPolynomial.X)

/-- Multiplication by the monic equation of a one-variable graph refinement.
Source: Stacks 0BZJ (blueprint: def-trf-polynomial-duality-presentation-data). -/
def polynomialDualityEquationMap (R : Type u) [CommRing R] (n : ℕ)
    (g : MvPolynomial (Fin n) R) : polynomialDualityTop R (n + 1) ⟶
      polynomialDualityTop R (n + 1) :=
  ModuleCat.ofHom (LinearMap.lsmul _ _
    (MvPolynomial.X (Fin.last n) - MvPolynomial.rename Fin.castSucc g))

/-- A coefficient contraction is normalized by the boundary of the actual two-term
resolution. The quotient map sends the ordered top volume to the old volume. Thus
its adjoint sends dual(X_last-g) tensor d(X_last-g) to 1. All shifts use the standard
cohomological shift functors; no independent sign convention is introduced.
Source: Stacks 0BZI, 0BZJ (blueprint: def-trf-polynomial-duality-presentation-data). -/
def IsPolynomialDualityContraction (R : Type u) [CommRing R] (n : ℕ)
    (g : MvPolynomial (Fin n) R)
    (e : (ModuleCat.derivedCoinduction (polynomialDualityRefinement R n g)).obj
      (polynomialDualityCoefficient R (n + 1)) ≅ polynomialDualityCoefficient R n) : Prop :=
  ∃ q : polynomialDualityTop R (n + 1) ⟶
      (ModuleCat.restrictScalars (polynomialDualityRefinement R n g)).obj
        (polynomialDualityTop R n),
    q (polynomialDualityVolume R (n + 1)) = polynomialDualityVolume R n ∧
    ∃ hz : polynomialDualityEquationMap R n g ≫ q = 0,
    ∃ hs : (ShortComplex.mk (polynomialDualityEquationMap R n g) q hz).ShortExact,
      e.inv = (ModuleCat.derivedCoinductionAdjunction
        (polynomialDualityRefinement R n g)).homEquiv _ _
          ((Functor.commShiftIso
            (ModuleCat.restrictScalars (polynomialDualityRefinement R n g)).mapDerivedCategory
              (n : ℤ)).hom.app
              ((DerivedCategory.singleFunctor _ 0).obj (polynomialDualityTop R n)) ≫
          (Functor.mapDerivedCategorySingleFunctor
            (ModuleCat.restrictScalars (polynomialDualityRefinement R n g)) 0).hom.app
              (polynomialDualityTop R n)⟦(n : ℤ)⟧' ≫
          hs.singleδ⟦(n : ℤ)⟧' ≫
          (shiftFunctorAdd' _ (1 : ℤ) (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)).inv.app
            ((DerivedCategory.singleFunctor _ 0).obj (polynomialDualityTop R (n + 1))))

/-- Comparison of coinduced models by the two evaluation counits. This is the canonical
coinduction transitivity comparison followed by the supplied coefficient contraction.
Source: Stacks 0A70, 0BZJ (blueprint: def-trf-polynomial-duality-presentation-data). -/
def polynomialDualityRefinementMap {R A : Type u} [CommRing R] [CommRing A]
    (n : ℕ) (p : MvPolynomial (Fin n) R →+* A) (g : MvPolynomial (Fin n) R)
    (e : (ModuleCat.derivedCoinduction (polynomialDualityRefinement R n g)).obj
      (polynomialDualityCoefficient R (n + 1)) ≅ polynomialDualityCoefficient R n) :
    polynomialDualityModel (n + 1) (p.comp (polynomialDualityRefinement R n g)) ⟶
      polynomialDualityModel n p :=
  (ModuleCat.derivedCoinductionAdjunction p).homEquiv _ _
    ((ModuleCat.derivedCoinductionAdjunction (polynomialDualityRefinement R n g)).homEquiv _ _
      (((Functor.mapDerivedCategoryNatIso
        (ModuleCat.restrictScalarsComp (polynomialDualityRefinement R n g) p) ≪≫
          Functor.mapDerivedCategoryCompIso _ _).inv.app _) ≫
        (ModuleCat.derivedCoinductionAdjunction
          (p.comp (polynomialDualityRefinement R n g))).counit.app
            (polynomialDualityCoefficient R (n + 1))) ≫ e.hom)

/-- The counit-defined comparison for any refinement and coefficient comparison.
Source: Stacks 0A70, 0BZJ (blueprint: def-trf-polynomial-duality-presentation-data). -/
def polynomialDualityCoinductionComparison {B P A : Type u}
    [CommRing B] [CommRing P] [CommRing A] (a : B →+* P) (p : P →+* A)
    (T : DerivedCategory (ModuleCat.{u} B)) (L : DerivedCategory (ModuleCat.{u} P))
    (e : (ModuleCat.derivedCoinduction a).obj T ≅ L) :
    (ModuleCat.derivedCoinduction (p.comp a)).obj T ⟶
      (ModuleCat.derivedCoinduction p).obj L :=
  (ModuleCat.derivedCoinductionAdjunction p).homEquiv _ _
    ((ModuleCat.derivedCoinductionAdjunction a).homEquiv _ _
      ((Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp a p) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).inv.app _ ≫
        (ModuleCat.derivedCoinductionAdjunction (p.comp a)).counit.app T) ≫ e.hom)

/-- Coordinate changes act on top forms by the actual universal derivations. The
adjoint of the inverse differential map specifies the coinduction coefficient comparison.
In particular a permutation acts by its exterior determinant, with its usual sign.
Source: Stacks 0BZI, canonical-normalization footnote
(blueprint: def-trf-polynomial-duality-presentation-data). -/
def IsPolynomialDualityCoordinateComparison (R : Type u) [CommRing R] (n : ℕ)
    (a : MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R)
    (e : (ModuleCat.derivedCoinduction a.toRingHom).obj
      (polynomialDualityCoefficient R n) ≅ polynomialDualityCoefficient R n) : Prop :=
  ∃ q : polynomialDualityTop R n ≅
      (ModuleCat.restrictScalars a.toRingHom).obj (polynomialDualityTop R n),
    (∀ x : Fin n → MvPolynomial (Fin n) R,
      q.hom (exteriorPower.ιMulti _ n (fun j ↦
        KaehlerDifferential.D R (MvPolynomial (Fin n) R) (x j))) =
      exteriorPower.ιMulti _ n (fun j ↦
        KaehlerDifferential.D R (MvPolynomial (Fin n) R) (a (x j)))) ∧
    e.inv = (ModuleCat.derivedCoinductionAdjunction a.toRingHom).homEquiv _ _
      (((ModuleCat.restrictScalars a.toRingHom).mapDerivedCategory.commShiftIso
        (n : ℤ)).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj (polynomialDualityTop R n)) ≫
        ((ModuleCat.restrictScalars a.toRingHom).mapDerivedCategorySingleFunctor 0).hom.app
          (polynomialDualityTop R n)⟦(n : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor _ 0).map q.inv)⟦(n : ℤ)⟧')

/-- A family of identifications with all polynomial presentations of one affine object.
The refinement equations specify the actual comparisons, including independence of
the lift g. All multi-variable comparisons are composites of these counit maps.
The coordinate equation includes ordered exchanges, so the exterior sign and the
cohomological tensor sign are retained. Comparisons between arbitrary presentations
are obtained through a common polynomial refinement; because each is alpha_Q inverse
followed by alpha_P, they compose and are independent of further refinements.
Source: Stacks 0BZI, 0BZJ (blueprint: def-trf-polynomial-duality-presentation-data). -/
structure PolynomialDualityPresentationSystem (R A : Type u) [CommRing R] [CommRing A]
    (φ : R →+* A) (M : DerivedCategory (ModuleCat.{u} A)) where
  identification : ∀ (n : ℕ) (p : MvPolynomial (Fin n) R →+* A),
    Function.Surjective p → p.comp MvPolynomial.C = φ → (M ≅ polynomialDualityModel n p)
  refinement : ∀ (n : ℕ) (p : MvPolynomial (Fin n) R →+* A)
      (hp : Function.Surjective p) (hφ : p.comp MvPolynomial.C = φ)
      (g : MvPolynomial (Fin n) R)
      (hq : Function.Surjective (p.comp (polynomialDualityRefinement R n g)))
      (hφq : (p.comp (polynomialDualityRefinement R n g)).comp MvPolynomial.C = φ),
    ∃ e : (ModuleCat.derivedCoinduction (polynomialDualityRefinement R n g)).obj
        (polynomialDualityCoefficient R (n + 1)) ≅ polynomialDualityCoefficient R n,
      IsPolynomialDualityContraction R n g e ∧
      (identification (n + 1) (p.comp (polynomialDualityRefinement R n g)) hq hφq).inv ≫
        (identification n p hp hφ).hom = polynomialDualityRefinementMap n p g e
  coordinate : ∀ (n : ℕ) (p : MvPolynomial (Fin n) R →+* A)
      (hp : Function.Surjective p) (hφ : p.comp MvPolynomial.C = φ)
      (a : MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R)
      (hq : Function.Surjective (p.comp a.toRingHom))
      (hφq : (p.comp a.toRingHom).comp MvPolynomial.C = φ),
    ∃ e : (ModuleCat.derivedCoinduction a.toRingHom).obj
        (polynomialDualityCoefficient R n) ≅ polynomialDualityCoefficient R n,
      IsPolynomialDualityCoordinateComparison R n a e ∧
      (identification n (p.comp a.toRingHom) hq hφq).inv ≫
        (identification n p hp hφ).hom =
      polynomialDualityCoinductionComparison a.toRingHom p
        (polynomialDualityCoefficient R n) (polynomialDualityCoefficient R n) e

/-- The comparison between any two presentations, hence also through a common
refinement. Its intermediate identification cancels in a composite. The refinement
and coordinate fields specify this map independently by their evaluation formulas.
Source: Stacks 0BZJ (blueprint: def-trf-polynomial-duality-presentation-data). -/
def PolynomialDualityPresentationSystem.comparison
    {R A : Type u} [CommRing R] [CommRing A] {φ : R →+* A}
    {M : DerivedCategory (ModuleCat.{u} A)} (F : PolynomialDualityPresentationSystem R A φ M)
    (n m : ℕ) (p : MvPolynomial (Fin n) R →+* A) (q : MvPolynomial (Fin m) R →+* A)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hφp : p.comp MvPolynomial.C = φ) (hφq : q.comp MvPolynomial.C = φ) :
    polynomialDualityModel n p ≅ polynomialDualityModel m q :=
  (F.identification n p hp hφp).symm ≪≫ F.identification m q hq hφq


/-- The original evaluation-normalized ordinary coinduction adjunction.
Source: Stacks 0BUZ (blueprint: def-trf-polynomial-duality-presentation-data). -/
@[irreducible] def polynomialChartOrdinaryAdjunction {U P : Scheme.{u}} (i : U ⟶ P) :
    SheafOfModules.restrictScalars.{u} i.toRingCatSheafHom ⊣ polynomialChartCoinduction i := by
  unfold polynomialChartCoinduction
  exact (polynomialChartCoinductionPresentation i).adjunction

/-- Proof data for the exact forgetful functor; no choice of mathematical data.
Source: Stacks 0BUZ (blueprint: def-trf-polynomial-duality-presentation-data). -/
structure PolynomialChartExactData {U P : Scheme.{u}} (i : U ⟶ P) where
  additive : (polynomialChartCoinduction i).Additive
  limits : PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} i.toRingCatSheafHom)
  colimits : PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} i.toRingCatSheafHom)

/-- Forgetting the algebra action as a ringed-space direct image.
Source: Stacks 0AVW (blueprint: def-trf-polynomial-duality-presentation-data). -/
def polynomialChartAlgebraMap {U P : Scheme.{u}} (i : U ⟶ P) :
    directImageAlgebraSpace i ⟶ P.toRingedSpace :=
  ⟨{ base := 𝟙 P.toTopCat, c := i.c }⟩

/-- Derived coinduction, retaining explicit additive evidence without unfolding its choice.
Source: Stacks 0BUZ (blueprint: def-trf-polynomial-duality-presentation-data). -/
def polynomialChartDerivedHom
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {U P : Scheme.{u}} (i : U ⟶ P) (d : PolynomialChartExactData i) :
    schemeDerivedCategory P ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) :=
  letI := d.additive
  (polynomialChartCoinduction i).rightDerivedFunctor

/-- The actual derived evaluation adjunction, including its original counit.
Source: Stacks 0BUZ, 0A70 (blueprint: def-trf-polynomial-duality-presentation-data). -/
def polynomialChartDerivedAdjunction
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {U P : Scheme.{u}} (i : U ⟶ P) (d : PolynomialChartExactData i) :
    RingedSpace.derivedModuleDirectImage (polynomialChartAlgebraMap i) ⊣
      polynomialChartDerivedHom i d := by
  letI : HasDerivedCategory.{w} (SheafOfModules.{u} P.ringCatSheaf) := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings P.toRingedSpace)))
  letI : HasDerivedCategory.{w} (SheafOfModules.{u}
    (((TopologicalSpace.Opens.map i.base).sheafPushforwardContinuous RingCat
      (Opens.grothendieckTopology P) (Opens.grothendieckTopology U)).obj U.ringCatSheaf)) :=
    inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))))
  letI : Abelian.HasKInjectiveResolutions (SheafOfModules.{u}
    (((Opens.map i.base).sheafPushforwardContinuous RingCat
      (Opens.grothendieckTopology P) (Opens.grothendieckTopology U)).obj U.ringCatSheaf)) :=
    inferInstanceAs (Abelian.HasKInjectiveResolutions
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))))
  letI := d.additive
  letI := d.limits
  letI := d.colimits
  exact (polynomialChartOrdinaryAdjunction i).mapDerivedCategoryRightDerivedAdjunction
    |>.ofNatIsoLeft
      (Functor.rightDerivedFunctorIsoMapDerivedCategory
        (SheafOfModules.restrictScalars.{u} i.toRingCatSheafHom)).symm

end AlgebraicGeometry
