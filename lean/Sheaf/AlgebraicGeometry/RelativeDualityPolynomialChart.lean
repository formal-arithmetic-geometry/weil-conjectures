/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.AlgebraicGeometry.RelativeDualizingPair
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import WeilConjectures.AlgebraicGeometry.SheafCoinductionAdjunction
public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
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
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage

import Sheaf.TraceFormula.AlgebraicShriekCalculus
import Sheaf.TraceFormula.AlgebraicShriekRelativePerfect
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.AlgebraicGeometry.FiniteAffineDerivedEquivalence
import Sheaf.AlgebraicGeometry.AffineFiniteProjectiveHomModel
import WeilConjectures.Algebra.Homology.DerivedHomFiniteFreeModel
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Sheaf.AlgebraicGeometry.RelativeDualizingPairRigidity
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import Sheaf.AlgebraicGeometry.DerivedBasisBbdDescent
import WeilConjectures.RingTheory.KoszulRegularSequenceDualComplex
import Sheaf.Algebra.Homology.AugmentedResolutionLiftHomotopy


public import Sheaf.AlgebraicGeometry.PolynomialDualityAffineCompatibility

/-! # Polynomial charts for coherent relative duality

Source: Stacks 0E2X, 0BV2, 0BZI and 0BZJ
(blueprint: lem-trf-relative-duality-polynomial-chart).
-/


@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory TopologicalSpace
namespace AlgebraicGeometry

/-- Existence of a coherent relative dualizing pair with top-differential polynomial
models and their normalized comparisons. The geometric model is over i_*O_U, so
its natural closed-source action is part of the assertion. On every affine open,
one identification with the global object is shared by all polynomial presentations.
The atlas requires the independent restriction-of-evaluation square. Affine realization
is fixed by the original tilde and derived-direct-image units. Principal-open charts
also use the normalized inverse-coordinate boundary, so changes of presentation and
localization are the specified canonical comparisons.

Source: Stacks, duality.tex, 0E2T, 0E2X, 0BV2; dualizing.tex, 0BZI and 0BZJ
(blueprint: lem-trf-relative-duality-polynomial-chart).

Proof:
1. On Spec A over Spec R choose P=R[x_0,...,x_(n-1)] surjecting onto A.
The algebraic shriek calculus and relative-perfection lemma give the coinduced
complex RHom_P(A,P)[n], pseudo-coherent and of finite R-Tor amplitude. Replace
P by its free coefficient line Omega^n using the ordered differential volume.
2. Put B=A tensor_R A. Flat base change and composition for A -> B -> A
identify A with RHom_B(A, B tensor_A K). Take the image of 1 and its
coinduction adjunct. A-linearity says that multiplication by this class is
precisely that isomorphism. All maps are evaluation adjunction maps.
3. The affine derived equivalence and affine pullback formula transfer the
class to sheaves. A bounded-above finite-free resolution of A and a bounded-below
target compute internal Hom with finitely many nonzero factors in each total
degree. The finite-projective and finite-free Hom model lemmas identify these
complexes, including the coinduced A-action.
4. Open restriction preserves the pair condition. Rigidity supplies unique
class-preserving identifications on intersections. Uniqueness gives the cocycle.
5. The scalar-rigidity isomorphism identifies RHom(K_U,K_U) with O_U[0].
Negative self-Homs vanish on affine opens. BBD descent on the whole affine basis
produces K, with no finite-cover assumption. Pseudo-coherence and relative Tor
bounds are local and therefore descend.
6. The Hom from the diagonal has only H^0 on U times_S U and vanishes off the
closed diagonal. The local classes glue, together with zero on its complement,
to xi on the full product. Its multiplication map is locally an isomorphism.
7. For Q=P[t] -> P, t -> g, the monic element t-g is a nonzerodivisor.
The two-term resolution [Q --t-g--> Q] gives the boundary class. Its ordered
top-form quotient sends dx_0 wedge ... wedge dx_(n-1) wedge d(t-g) to the old
volume; terms involving dg wedge to zero. Adjoint evaluation therefore contracts
dual(t-g) tensor d(t-g) to 1. Coinduction transitivity gives exactly the displayed
refinement map and cancels the added shift.
8. Two lifts differ by a map of an augmented projective resolution with zero
augmentation. Augmented-resolution homotopy uniqueness gives a homotopy dh+hd.
The triangular map between the two graph cones is identity on the associated
graded, so their coefficient contractions agree in the derived category.
Transitivity of evaluation counits preserves the diagonal class. Tensoring the
ordered two-term resolutions gives iterated refinements with the cohomological
Koszul signs; exchanging the top differentials supplies the corresponding wedge
sign. A common refinement and rigidity give independence and composition.
9. For a principal open D(h), present P_h as P[t]/(ht-1). The boundary of this
nonzerodivisor quotient contracts the new volume to h inverse times the localized
old volume, since dx wedge d(ht-1)=h dx wedge dt. The two coinduction counits
identify this with the presentation system on the smaller affine source. Localize
the polynomial models and their coefficient lines. Internal-Hom restriction and
affine pullback identify this with open restriction. Cover an
arbitrary open P in affine space by such affines. The same class-preserving
comparisons glue its model, including its O_U-action, to the restriction of K.
The empty chart gives zero and n=0 gives Omega^0=O with no shift. -/
theorem exists_relativeDualityPolynomialChart
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f] [IsLocallyNoetherian S] :
    ∃ (K : schemeDerivedCategory X)
      (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
        (derivedPullback (pullback.fst f f)).obj K),
      IsCoherentRelativeDualizingPair f K ξ ∧
      ∃ atlas : PolynomialDualityChartAtlas f K,
      ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
        (jA : Spec (.of A) ⟶ X) (jR : Spec (.of R) ⟶ S)
        [IsOpenImmersion jA] [IsOpenImmersion jR],
        jA ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ jR →
        ∃ (M : DerivedCategory (ModuleCat.{u} A))
          (e : (polynomialOpenRestriction jA).obj K ≅ (polynomialAffineTilde A).obj M)
          (F : PolynomialDualityPresentationSystem R A (algebraMap R A) M),
          IsPolynomialAffineAtlasCompatible atlas R A jA jR M e F ∧
          IsPolynomialLocalizedAffineAtlasCompatible atlas R A jA jR M e F := by
  sorry

end AlgebraicGeometry
