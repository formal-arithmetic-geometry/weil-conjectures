/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction
public import Sheaf.AlgebraicGeometry.LCICurveFundamentalClass
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.NodalCurveLCICriterion
import Sheaf.TraceFormula.LciAffineOpenLocality
import Sheaf.RingTheory.LocalCompleteIntersectionFieldChange
import Sheaf.TraceFormula.LciPointwiseCriterion
import Sheaf.TraceFormula.SyntomicPointwiseLocalModel
import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionLocalRegularSequence
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import WeilConjectures.AlgebraicGeometry.KoszulComplex
import Mathlib.Algebra.Module.LocalizedModule.Exact
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionConormalFree
import Sheaf.TraceFormula.LciKoszulDualityDeterminantComparison
import Sheaf.AlgebraicGeometry.LciCotangentPresentation
import Sheaf.TraceFormula.CanonicalTwoTermPerfectDeterminant
import WeilConjectures.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.Cohomology.FiniteFibre
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.Paper.RelativeGlobalCompleteIntersectionBaseChange
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Sheaf.CategoryTheory.DerivedHomologyInjective
import Sheaf.AlgebraicGeometry.ProperFlatDualizingPolynomialModel

/-! # Relative dualizing lines of arbitrary nodal families

Source: Stacks Project, moduli-curves.tex, Tags 0E6P--0E6R and the relative
Serre-duality display following Definition 0E6Q.
(blueprint: lem-sfb-gorenstein-curve-relative-dualizing).

The system includes every cartesian base change, including the identity family and
isomorphic families. Its fundamental map has the chart cofactor/Jacobian normalization
in the normalized adjunction line. This fixes the base-change maps on the smooth locus.
No connectedness or Noetherian assumption occurs.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The right adjoint and its actual value on the degree-zero structure module.
The preservation witness restricts the existing derived direct image to D_QCoh.
Source: Stacks, moduli-curves.tex, discussion preceding 0E6P; duality.tex, 0A9E
(blueprint: lem-sfb-gorenstein-curve-relative-dualizing). -/
structure NodalRelativeDualizingAdjunction {X T : Scheme.{u}} (f : X ⟶ T) where
  preserves : ∀ E : schemeDerivedQCohCategory X,
    schemeDerivedQCohProperty T ((schemeDerivedDirectImage f).obj E.obj)
  rightAdjoint : schemeDerivedQCohCategory T ⥤ schemeDerivedQCohCategory X
  adjunction : ((schemeDerivedQCohProperty T).lift
    ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) preserves) ⊣ rightAdjoint
  unit_quasicoherent : schemeDerivedQCohProperty T
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).obj
        (SheafOfModules.unit T.ringCatSheaf))

/-- The dualizing complex is f^! O_T itself, in the shared ambient derived category.
Source: Stacks, moduli-curves.tex, discussion preceding 0E6P
(blueprint: lem-sfb-gorenstein-curve-relative-dualizing). -/
def NodalRelativeDualizingAdjunction.complex {X T : Scheme.{u}} {f : X ⟶ T}
    (A : NodalRelativeDualizingAdjunction f) : schemeDerivedCategory X :=
  (A.rightAdjoint.obj ⟨(DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).obj
      (SheafOfModules.unit T.ringCatSheaf), A.unit_quasicoherent⟩).obj

/-- The complete relative dualizing system on all cartesian changes of base.
The line is identified with H^(-1)(f^! O), and the shifted degree-zero line with
f^! O. Local comparisons identify this very line with the actual conormal determinant.
The normalized adjunction transitions and the cofactor/Jacobian formulas fix the
fundamental differential in those comparisons, and hence its base-change comparison;
the pullback formula is evaluated on the actual generators 1 tensor da.
The Serre bijections are natural in every
quasi-coherent module, over every field, including fields that are not algebraically closed.
Source: Stacks, moduli-curves.tex, 0E6P--0E6R and relative Serre duality; duality.tex,
0E9Y--0E9Z for the differential normalization
(blueprint: lem-sfb-gorenstein-curve-relative-dualizing). -/
structure NodalRelativeDualizingSystem {X T : Scheme.{u}} (f : X ⟶ T) where
  adjoint : ∀ B : FlatLCIBaseChange f, NodalRelativeDualizingAdjunction B.p'
  omega : ∀ B : FlatLCIBaseChange f, B.X'.Modules
  invertible : ∀ B, (omega B).IsInvertible
  quasicoherent : ∀ B, (omega B).IsQuasicoherent
  homologyIso : ∀ B : FlatLCIBaseChange f,
    (omega B : SheafOfModules.{u} (moduleRings B.X'.toRingedSpace)) ≅
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings B.X'.toRingedSpace)) (-1)).obj
        (adjoint B).complex
  complexIso : ∀ B : FlatLCIBaseChange f, (adjoint B).complex ≅
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings B.X'.toRingedSpace)) 0).obj (omega B))⟦(1 : ℤ)⟧
  complex_normalization : ∀ B : FlatLCIBaseChange f,
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings B.X'.toRingedSpace)) (-1)).map (complexIso B).hom ≫
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings B.X'.toRingedSpace)) 0).shiftIso
          (1 : ℤ) (-1) 0 (by decide)).hom.app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings B.X'.toRingedSpace)) 0).obj (omega B)) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (SheafOfModules.{u} (moduleRings B.X'.toRingedSpace)) 0).hom.app (omega B) =
      (homologyIso B).inv
  localIso : ∀ (B : FlatLCIBaseChange f) (U : B.X'.Opens)
    (C : FlatLCIPresentation B.p' 1 U),
    C.line ≅ (Scheme.Modules.tensorPullback U.ι).obj (omega B)
  fundamental : ∀ B, B.p'.relativeDifferentials ⟶ omega B
  smooth : ∀ (B : FlatLCIBaseChange f) (U : B.X'.Opens),
    Smooth (U.ι ≫ B.p') →
      IsIso ((Scheme.Modules.tensorPullback U.ι).map (fundamental B))
  baseChange : ∀ (B D : FlatLCIBaseChange f) (g : D.X' ⟶ B.X') (b : D.S' ⟶ B.S'),
    IsPullback g D.p' B.p' b → g ≫ B.g = D.g → b ≫ B.b = D.b →
      ((Scheme.Modules.tensorPullback g).obj (omega B) ≅ omega D)
  identity : ∀ (B : FlatLCIBaseChange f)
    (hc : IsPullback (𝟙 B.X') B.p' B.p' (𝟙 B.S'))
    (hg : 𝟙 B.X' ≫ B.g = B.g) (hb : 𝟙 B.S' ≫ B.b = B.b),
    baseChange B B (𝟙 B.X') (𝟙 B.S') hc hg hb =
      (Scheme.Modules.tensorPullbackSectionId B.X').app (omega B)
  composition : ∀ (B D E : FlatLCIBaseChange f)
    (g : D.X' ⟶ B.X') (b : D.S' ⟶ B.S') (h : E.X' ⟶ D.X') (c : E.S' ⟶ D.S')
    (hc₁ : IsPullback g D.p' B.p' b) (hg₁ : g ≫ B.g = D.g) (hb₁ : b ≫ B.b = D.b)
    (hc₂ : IsPullback h E.p' D.p' c) (hg₂ : h ≫ D.g = E.g) (hb₂ : c ≫ D.b = E.b)
    (hc₃ : IsPullback (h ≫ g) E.p' B.p' (c ≫ b))
    (hg₃ : (h ≫ g) ≫ B.g = E.g) (hb₃ : (c ≫ b) ≫ B.b = E.b),
    baseChange B E (h ≫ g) (c ≫ b) hc₃ hg₃ hb₃ =
      (Scheme.Modules.tensorPullbackSectionComp h g).app (omega B) ≪≫
        (Scheme.Modules.tensorPullback h).mapIso (baseChange B D g b hc₁ hg₁ hb₁) ≪≫
          baseChange D E h c hc₂ hg₂ hb₂
  adjunction_normalization : FlatLCIAdjunctionSystem.IsNormalized
    { line := omega, invertible := invertible, localIso := localIso,
      baseChange := baseChange, identity := identity, composition := composition }
  fundamental_normalization : FlatLCIAdjunctionSystem.IsCurveFundamentalClass
    { line := omega, invertible := invertible, localIso := localIso,
      baseChange := baseChange, identity := identity, composition := composition } fundamental
  differential_normalization : ∀ (B D : FlatLCIBaseChange f)
    (g : D.X' ⟶ B.X') (b : D.S' ⟶ B.S')
    (hc : IsPullback g D.p' B.p' b) (hg : g ≫ B.g = D.g) (hb : b ≫ B.b = D.b)
    (U : B.X'.Opens) (a : Γ(B.X', U)),
    (baseChange B D g b hc hg hb).hom.app (g ⁻¹ᵁ U)
      (((Scheme.Modules.tensorPullback g).map (fundamental B)).app (g ⁻¹ᵁ U)
        (B.p'.relativeDifferentialsPullbackGenerator g U a)) =
      (fundamental D).app (g ⁻¹ᵁ U)
        (D.p'.relativeDifferentialsDerivation.d (X := op (g ⁻¹ᵁ U)) (g.app U a))
  baseChange_unique : ∀ (B D : FlatLCIBaseChange f)
    (g : D.X' ⟶ B.X') (b : D.S' ⟶ B.S')
    (hc : IsPullback g D.p' B.p' b) (hg : g ≫ B.g = D.g) (hb : b ≫ B.b = D.b)
    (e : (Scheme.Modules.tensorPullback g).obj (omega B) ≅ omega D),
    (∀ (U : B.X'.Opens) (a : Γ(B.X', U)),
      e.hom.app (g ⁻¹ᵁ U)
        (((Scheme.Modules.tensorPullback g).map (fundamental B)).app (g ⁻¹ᵁ U)
          (B.p'.relativeDifferentialsPullbackGenerator g U a)) =
        (fundamental D).app (g ⁻¹ᵁ U)
          (D.p'.relativeDifferentialsDerivation.d (X := op (g ⁻¹ᵁ U)) (g.app U a))) →
      e = baseChange B D g b hc hg hb
  serre : ∀ (k : Type u) [Field k] (B : FlatLCIBaseChange f)
    (q : B.S' ⟶ Spec (.of k)) [IsIso q],
    ∃ e : ∀ (F : B.X'.Modules), F.IsQuasicoherent →
      (F ⟶ omega B) ≃
        (Scheme.Modules.scalarCohomology (B.p' ≫ q) F 1 ⟶ ModuleCat.of k k),
      ∀ (F G : B.X'.Modules) (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent)
        (a : F ⟶ G) (t : G ⟶ omega B)
        (z : Scheme.Modules.scalarCohomology (B.p' ≫ q) F 1),
        e F hF (a ≫ t) z = e G hG t
          (((RingedSpace.moduleCohomology B.X'.toRingedSpace 1).map a) z)

/-- A proper flat finitely presented nodal family has its relative dualizing line,
with arbitrary-base-change coherence, smooth normalization and fibre Serre duality.
Source: Stacks, moduli-curves.tex, 0E6P--0E6R
(blueprint: lem-sfb-gorenstein-curve-relative-dualizing).

Proof plan (the node's six steps):
1. On affine opens, finite presentation gives finite-type fibre rings. Apply the nodal
LCI criterion, affine-open locality and field-change descent, then the pointwise LCI
criterion and syntomic local model, to get relative complete-intersection charts with
n=c+1. Pure dimension fixes this equality; no connectedness is used.
2. Local regularity of the equations gives Koszul exactness at primes containing their
ideal. At other primes a unit equation contracts the Koszul complex. Localization
exactness and the annihilator argument give global exactness. The conormal is free of rank c.
3. Apply lem-sfb-proper-flat-dualizing-polynomial-model. Its right adjoint gives K=f^! O.
The normalized LCI Koszul/determinant comparison identifies each chart with D_i[1],
using RHom_P(B, Omega^n)[n] and n-c=1, with the specified refinement signs.
4. Cotangent presentation and the canonical two-term determinant identify D_i with
D=det L. The normalized comparisons have exactly the determinant transitions. Glue the
H^(-1) module maps and their inverses; all other cohomology sheaves vanish stalkwise.
The single-degree concentration lemma gives K=H^(-1)(K)[1], and omega is invertible.
5. Flatness gives Tor-independent cotangent base change. Pull back the relative global
complete-intersection charts and their ordered equations. Determinant base change gives
beta; conjugate beta by omega=det L to obtain gamma. Cancellation proves the identity
and composition laws, and naturality includes family isomorphisms. On the smooth locus
the determinant is Omega^1. The local comparisons have the normalized exact-cone
determinant transitions, including the kernel-first rank sign. The fundamental map is
the conormal-first cofactor wedge in these same comparisons; its scalar expression is
the augmented Jacobian, with flatLCICurveFundamentalSign c = 1. These formulas glue and
commute with arbitrary base change, and give the displayed differential-generator formula.
6. Over any field, use degree-zero full faithfulness, K=omega[1] and the right-adjoint
Hom equivalence. The field is injective as a module over itself. The injective-target
homology bijection identifies the result with Hom_k(H^1(F),k), naturally in F. The
base-change isomorphism therefore identifies every fibre restriction with its Serre module.
-/
theorem exists_nodalRelativeDualizingSystem {X T : Scheme.{u}} (f : X ⟶ T)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hfibres : ∀ y : T,
      Nonempty ↥(pullback (C := Scheme.{u}) f
        (Spec.map (CommRingCat.ofHom
          (algebraMap (T.residueField y) (AlgebraicClosure (T.residueField y)))) ≫
            T.fromSpecResidueField y)) ∧
      IsReduced (pullback (C := Scheme.{u}) f
        (Spec.map (CommRingCat.ofHom
          (algebraMap (T.residueField y) (AlgebraicClosure (T.residueField y)))) ≫
            T.fromSpecResidueField y)) ∧
      (pullback (C := Scheme.{u}) f
        (Spec.map (CommRingCat.ofHom
          (algebraMap (T.residueField y) (AlgebraicClosure (T.residueField y)))) ≫
            T.fromSpecResidueField y)).IsPureDimension 1 ∧
      ∀ x : ↥(pullback (C := Scheme.{u}) f
        (Spec.map (CommRingCat.ofHom
          (algebraMap (T.residueField y) (AlgebraicClosure (T.residueField y)))) ≫
            T.fromSpecResidueField y)),
        x ∉ (pullback.snd (C := Scheme.{u}) f
          (Spec.map (CommRingCat.ofHom
            (algebraMap (T.residueField y) (AlgebraicClosure (T.residueField y)))) ≫
              T.fromSpecResidueField y)).smoothLocus →
        Nonempty (AdicCompletion (IsLocalRing.maximalIdeal
          ((pullback (C := Scheme.{u}) f
            (Spec.map (CommRingCat.ofHom
              (algebraMap (T.residueField y) (AlgebraicClosure (T.residueField y)))) ≫
                T.fromSpecResidueField y)).presheaf.stalk x))
          ((pullback (C := Scheme.{u}) f
            (Spec.map (CommRingCat.ofHom
              (algebraMap (T.residueField y) (AlgebraicClosure (T.residueField y)))) ≫
                T.fromSpecResidueField y)).presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) (AlgebraicClosure (T.residueField y)) ⧸
            Ideal.span {(MvPowerSeries.X 0 :
              MvPowerSeries (Fin 2) (AlgebraicClosure (T.residueField y))) *
                (MvPowerSeries.X 1 :
                  MvPowerSeries (Fin 2) (AlgebraicClosure (T.residueField y)))}))) :
    Nonempty (NodalRelativeDualizingSystem f) := by
  sorry

end AlgebraicGeometry
