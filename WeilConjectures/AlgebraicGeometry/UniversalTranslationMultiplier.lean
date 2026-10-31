/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.AffineSpaceTopTrace
public import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.AffineTraceTower
public import WeilConjectures.AlgebraicGeometry.AffineTraceConstruction
public import WeilConjectures.AlgebraicGeometry.AmbientAffineTranslationConstruction
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.CompactSupportActionBaseChange
import WeilConjectures.AlgebraicGeometry.ConstantSheafSectionsLocallyConstant
import WeilConjectures.CategoryTheory.ConstantLeftModuleInverseImage
import WeilConjectures.Compactification.NagataCompactification
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Topology.NoetherianSpace

/-! # The unit multiplier of universal affine translation

Source: blueprint sec-smooth-purity/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md, Step 1
(blueprint: lem-pur-universal-translation-multiplier).

A unit section is represented by its Zariski-locally constant function. Its sheaf
multiplication map is specified on constant generators over every etale object on
which that function is constant. Such objects cover, and constant generators
locally generate the sheafification, so this specifies the actual sheaf map.
The trace and exchange isomorphisms below are constrained to the published maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] ModuleCat.extendScalars
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors

/-- The local generator formula for multiplication by the unit section represented
by `b`. This is a specification of a map of the existing constant module sheaf,
not a second definition of that sheaf. Source: Step 1, coefficient-line argument;
Stacks Tag 03P5 (blueprint: lem-pur-universal-translation-multiplier). -/
def IsEtaleUnitMultiplier (A : Type (u + 1)) [CommRing A] (B : Scheme.{u})
    (b : LocallyConstant B Aˣ)
    (h : ordinaryFiniteConstant A B ⟶ ordinaryFiniteConstant A B) : Prop :=
  ∀ (U : B.Etale) (a : Aˣ), (∀ x : U.left, b (U.hom x) = a) → ∀ c : A,
    h.hom.app (Opposite.op U)
        ((toSheafify B.smallEtaleTopology
          ((Functor.const B.Etaleᵒᵖ).obj (ModuleCat.of A A))).app (Opposite.op U) c) =
      (toSheafify B.smallEtaleTopology
        ((Functor.const B.Etaleᵒᵖ).obj (ModuleCat.of A A))).app (Opposite.op U) ((a : A) * c)

/-- A trace/scalar witness with all maps fixed by parameters. Keeping the generic
category parameters explicit avoids repeatedly expanding the derived localization
when Lean generates the structure projections. Source: Step 1, conjugation of the
coefficient line (blueprint: lem-pur-universal-translation-multiplier). -/
structure CoefficientLineMultiplierWitness
    {C : Type w₁} [Category.{v₁} C] {D : Type w₂} [Category.{v₂} D]
    (F : D ⥤ C) (K : C) (L : D) (t : K ⟶ F.obj L) (r : K ⟶ K)
    (P : (L ⟶ L) → Prop) where
  /-- The specified trace, with its inverse. -/
  trace : K ≅ F.obj L
  /-- Its forward map is the prescribed trace. -/
  trace_hom : trace.hom = t
  /-- The actual coefficient multiplication map. -/
  scalar : L ⟶ L
  /-- The local multiplication formula. -/
  scalar_spec : P scalar
  /-- The actual action, stored with its defining equation. -/
  action : K ⟶ K
  /-- Fix it to the specified exchange/Tate map. -/
  action_eq : action = r
  /-- Equality of actual derived morphisms. -/
  conjugate : trace.inv ≫ action ≫ trace.hom = F.map scalar

/-- The particular scalar description of the translated coordinate-tower trace.
Every parameter of the generic witness is the corresponding published map; no
trace or action is chosen freely. Source: Step 1, coefficient-line argument
(blueprint: lem-pur-universal-translation-multiplier). -/
abbrev TranslationMultiplierWitness (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (B : Scheme.{u}) (hB : IsNoetherian B) (hNB : IsUnit (N : Γ(B, ⊤)))
    (d : ℕ) (a : Fin d → Γ(B, ⊤)) (b : LocallyConstant B Aˣ) :=
  CoefficientLineMultiplierWitness (_root_.DerivedCategory.singleFunctor _ 0)
    ((affineTraceLeft A B d).obj
      ((affineTraceRight A N hA B d).obj (ordinaryFiniteUnit A B)))
    (ordinaryFiniteConstant A B)
    (@affineTraceCounit A _ N hA
      (ambientAffineTraceTransport N hN A hA) (ambientAffineTraceDatum N hN A hA)
      B hB hNB d)
    (ambientAffineTranslationExchange A B d a
        ((affineTraceRight A N hA B d).obj (ordinaryFiniteUnit A B)) ≫
      (affineTraceLeft A B d).map
        (ambientAffineTranslationTate A N hA (ambientAffineTraceTransport N hN A hA)
          B hNB d a).hom)
    (IsEtaleUnitMultiplier A B b)

/-- The universal translation has a unique unit multiplier, compatible with every
Noetherian base change, and equal to one on the zero section.
Source: blueprint vector-bundle orientation, Step 1, and smooth-purity unit,
Agreement on the model (blueprint: lem-pur-universal-translation-multiplier).

Proof:
1. Use def-amb-affine-trace-tower to identify the parameter scheme P and all
   pulled-back towers with affine spaces. Its geometry gives Noetherian total
   spaces, separated finite-type projections and invertibility of N. Finite affine
   covers give quasi-compactness; lem-weil-pbc-locally-noetherian-quasi-separated
   gives quasi-separatedness. Apply thm-nagata-compactification. Open parts are
   quasi-compact by the descending closed-set condition of
   lem-weil-pbc-noetherian-scheme-closed-subsets-minimal. The translations by a
   and -a are inverse, including in dimension zero.
2. Apply lem-asd-etale-finite-twist-pullback to the bounded-below shifted Tate
   object. Lem-amb-compact-action-base-change makes its Ex/Tate action invertible;
   lem-amb-affine-space-top-trace makes the normalized trace invertible.
   Lem-amb-unbounded-compact-support-comparisons identifies these very maps in
   the unbounded category. Their conjugate is an automorphism of A_P[0].
3. Lem-weil-pbc-derived-single-fully-faithful lifts it and its inverse uniquely to
   sheaf maps h and k. Functoriality and faithfulness give hk = kh = 1.
4. Put b = h(1), c = k(1). Linearity and restriction compatibility give h(x)=bx
   and k(x)=cx. Evaluating the inverse equations at 1 gives bc=cb=1. Any other
   scalar description has the same sheaf map by full faithfulness and hence the
   same section by evaluation at 1. The displayed generator formula is precisely
   this multiplication map: locally constant generators locally generate A_P.
5. Lem-weil-pbc-constant-sheaf-sections-locally-constant makes b and c locally
   constant. On opens where both are constant their product is one, so b is a
   locally constant function with values in A-units, including when A is zero.
6. For arbitrary u:T->P, lem-amb-compact-action-base-change gives the action
   square. Lem-amb-affine-space-top-trace gives the trace square. The unbounded
   comparison lemma makes their exchanges the same specified pasted map.
   Conjugation gives u*(m_b[0]); lem-pe-constant-left-module-inverse-image
   identifies this with multiplication by b composed with u, since inverse image
   preserves the constant ring, its multiplication and unit, and is exact.
7. On the zero section all translation coordinates vanish. Identity normalization
   of the Tate and exchange comparisons gives rho_(1,1)=1. Step 6 then gives
   multiplication by e*b equal to identity in degree zero; full faithfulness and
   evaluation at 1 give e*b=1. No connectedness argument is used here.
-/
theorem purUniversalTranslationMultiplier (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    ∃ (b : LocallyConstant (affineTraceTower S d) Aˣ)
      (w : TranslationMultiplierWitness N hN A hA (affineTraceTower S d)
        (affineTraceNoetherian S d) (affineTraceInvertible N S hS d) d
        (affineTraceCoordinate S d) b),
      (∀ (b' : LocallyConstant (affineTraceTower S d) Aˣ)
        (_ : TranslationMultiplierWitness N hN A hA (affineTraceTower S d)
          (affineTraceNoetherian S d) (affineTraceInvertible N S hS d) d
          (affineTraceCoordinate S d) b'), b' = b) ∧
      (∀ (T : Scheme.{u}) (hT : IsNoetherian T) (v : T ⟶ affineTraceTower S d),
        ∃ (wT : TranslationMultiplierWitness N hN A hA T hT
            (affineTracePullbackInvertible N v (affineTraceInvertible N S hS d)) d
            (fun i ↦ v.appTop (affineTraceCoordinate S d i))
            (b.comap ⟨v, v.continuous⟩))
          (C : (ordinaryFinitePullback A v).obj
            ((affineTraceLeft A (affineTraceTower S d) d).obj
              ((affineTraceRight A N hA (affineTraceTower S d) d).obj
                (ordinaryFiniteUnit A (affineTraceTower S d)))) ≅
            (affineTraceLeft A T d).obj
              ((affineTraceRight A N hA T d).obj (ordinaryFiniteUnit A T))),
          C.hom = affineTraceExchange A v d
              ((affineTraceRight A N hA (affineTraceTower S d) d).obj
                (ordinaryFiniteUnit A (affineTraceTower S d))) ≫
            (affineTraceLeft A T d).map
              ((affineTraceRightBaseChange A N hA (ambientAffineTraceTransport N hN A hA)
                v (affineTraceInvertible N S hS d) d
                (ordinaryFiniteUnit A (affineTraceTower S d))).hom ≫
                (affineTraceRight A N hA T d).map (ordinaryFiniteUnitPullback A v).hom) ∧
          (ordinaryFinitePullback A v).map w.action ≫ C.hom = C.hom ≫ wT.action ∧
          C.hom ≫ wT.trace.hom =
            (ordinaryFinitePullback A v).map w.trace.hom ≫
              (ordinaryFiniteUnitPullback A v).hom) ∧
      (∀ x : S,
        b ((AffineSpace.zeroSection (ULift.{u} (Fin d)) S ≫
          (affineTraceAffineSpaceIso S d).inv) x) = 1) ∧
      ambientAffineTranslationExchange A S d
          (fun i ↦ (AffineSpace.zeroSection (ULift.{u} (Fin d)) S ≫
            (affineTraceAffineSpaceIso S d).inv).appTop (affineTraceCoordinate S d i))
          ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
        (affineTraceLeft A S d).map
          (ambientAffineTranslationTate A N hA (ambientAffineTraceTransport N hN A hA)
            S hS d (fun i ↦ (AffineSpace.zeroSection (ULift.{u} (Fin d)) S ≫
              (affineTraceAffineSpaceIso S d).inv).appTop (affineTraceCoordinate S d i))).hom =
        𝟙 _ := by
  sorry

end AlgebraicGeometry.Etale
