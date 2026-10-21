/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q96
-/
module

public import Sheaf.Paper.BoundaryExceptionalComparisonData
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

/-! # Comparison of the untransposed boundary tensor composites

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-pf-proetale,
`thm-sf-pf-proetale.proof.md`, comparison paragraph; expanded calculation in
`lem-weil-boundary-proetale-q-compatibility`, step 1
(blueprint: lem-weil-boundary-q-defining-composite-comparison).

The helpers are the three explicit composites s, r and t_e in the node. The pro-etale
composite is expanded in the conclusion, using the same existing projection and braiding.
All tensor products lie in the ambient unbounded derived categories, including when the four
input objects are bounded below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.BoundaryComparisonOfCoefficients

open BoundaryComparison

section Composites

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [Etale.UpperStarPreservesFlat C] [ProEtale.UpperStarPreservesFlat C]
  [∀ W : Scheme.{u}, (comparisonUpperStar C W).PreservesFlat]

/-- The node's s: tensor comparison, rho inverse in the first factor, and v in the second.
Source: blueprint projection-comparison paragraph, displayed definition of s
(blueprint: lem-weil-boundary-q-defining-composite-comparison). -/
def boundaryDefiningSourceIso {Z T : Scheme.{u}} (i : Z ⟶ T)
    (M : DerivedCategory (Sheaf T.smallEtaleTopology C))
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (B' : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C))
    (v : (comparison C Z).obj B ≅ B') :
    (comparison C Z).obj
      (((Etale.derivedTensor C Z).obj
        ((Etale.upperStar C i).leftDerivedFunctor.obj M)).obj B) ≅
      ((ProEtale.derivedTensor C Z).obj
        ((upperStar C i).leftDerivedFunctor.obj ((comparison C T).obj M))).obj B' :=
  (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso C
    ((Etale.upperStar C i).leftDerivedFunctor.obj M)).app B ≪≫
    ((ProEtale.derivedTensor C Z).mapIso ((pullbackSquare C i).symm.app M)).app
      ((comparison C Z).obj B) ≪≫
    ((ProEtale.derivedTensor C Z).obj
      ((upperStar C i).leftDerivedFunctor.obj ((comparison C T).obj M))).mapIso v

/-- The node's r: tensor comparison, v in the first factor, and rho inverse in the second.
Source: blueprint projection-comparison paragraph, displayed definition of r
(blueprint: lem-weil-boundary-q-defining-composite-comparison). -/
def boundaryDefiningTargetIso {Z T : Scheme.{u}} (i : Z ⟶ T)
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (M : DerivedCategory (Sheaf T.smallEtaleTopology C))
    (B' : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C))
    (v : (comparison C Z).obj B ≅ B') :
    (comparison C Z).obj (((Etale.derivedTensor C Z).obj B).obj
        ((Etale.upperStar C i).leftDerivedFunctor.obj M)) ≅
      ((ProEtale.derivedTensor C Z).obj B').obj
        ((upperStar C i).leftDerivedFunctor.obj ((comparison C T).obj M)) :=
  (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso C B).app
      ((Etale.upperStar C i).leftDerivedFunctor.obj M) ≪≫
    ((ProEtale.derivedTensor C Z).obj ((comparison C Z).obj B)).mapIso
      ((pullbackSquare C i).symm.app M) ≪≫
    ((ProEtale.derivedTensor C Z).mapIso v).app
      ((upperStar C i).leftDerivedFunctor.obj ((comparison C T).obj M))

/-- The node's t_e, for an arbitrary final arrow a_e, before any exceptional adjunction.
Source: blueprint projection-comparison paragraph, displayed definition of t_e
(blueprint: lem-weil-boundary-q-defining-composite-comparison). -/
def boundaryEtaleDefiningComposite {Z T : Scheme.{u}} (i : Z ⟶ T)
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (M Y : DerivedCategory (Sheaf T.smallEtaleTopology C))
    (a : (etaleImage C i).obj B ⟶ Y)
    [IsIso (((Etale.rightDerivedLowerStarProjectionMap C i).app B).app M)] :
    (etaleImage C i).obj
      (((Etale.derivedTensor C Z).obj
        ((Etale.upperStar C i).leftDerivedFunctor.obj M)).obj B) ⟶
      ((Etale.derivedTensor C T).obj M).obj Y :=
  (etaleImage C i).map
      (β_ ((Etale.upperStar C i).leftDerivedFunctor.obj M) B).hom ≫
    inv (((Etale.rightDerivedLowerStarProjectionMap C i).app B).app M) ≫
    (β_ ((etaleImage C i).obj B) M).hom ≫
    ((Etale.derivedTensor C T).obj M).map a


/-- The displayed comparison assertion as a predicate over the existing coefficient interface.
This only packages the node's quantified input objects, compatible arrows, invertible
projection components, specified square and conclusion; it supplies no assumptions.
Source: blueprint projection-comparison paragraph, all displayed formulas
(blueprint: lem-weil-boundary-q-defining-composite-comparison). -/
def BoundaryDefiningCompositeComparison {Z T : Scheme.{u}} (i : Z ⟶ T) : Prop :=
  ∀ (η : comparison C Z ⋙ proetaleImage C i ≅
      etaleImage C i ⋙ comparison C T)
    (B : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology C))
    (M Y : DerivedCategory.Plus (Sheaf T.smallEtaleTopology C))
    (B' : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Z) C))
    (v : (comparison C Z).obj B.obj ≅ B'.obj)
    (ae : (etaleImage C i).obj B.obj ⟶ Y.obj)
    (ap : (proetaleImage C i).obj B'.obj ⟶
      (comparison C T).obj Y.obj)
    (_ha : (proetaleImage C i).map v.hom ≫ ap =
      η.hom.app B.obj ≫ (comparison C T).map ae)
    [IsIso (((Etale.rightDerivedLowerStarProjectionMap
      C i).app B.obj).app M.obj)]
    [IsIso (((rightDerivedLowerStarProjectionMap C i).app B'.obj).app
      ((comparison C T).obj M.obj))]
    (_hπ :
      ((ProEtale.derivedTensor C T).map
        ((proetaleImage C i).map v.hom)).app
          ((comparison C T).obj M.obj) ≫
        ((rightDerivedLowerStarProjectionMap C i).app B'.obj).app
          ((comparison C T).obj M.obj) ≫
        (proetaleImage C i).map
          (boundaryDefiningTargetIso C i B.obj M.obj B'.obj v).inv ≫
        η.hom.app (((Etale.derivedTensor C Z).obj B.obj).obj
          ((Etale.upperStar C i).leftDerivedFunctor.obj M.obj)) =
      ((ProEtale.derivedTensor C T).map (η.hom.app B.obj)).app
          ((comparison C T).obj M.obj) ≫
        ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso C
          ((etaleImage C i).obj B.obj)).app M.obj).inv ≫
        (comparison C T).map
          (((Etale.rightDerivedLowerStarProjectionMap
            C i).app B.obj).app M.obj)),
    η.hom.app
        (((Etale.derivedTensor C Z).obj
          ((Etale.upperStar C i).leftDerivedFunctor.obj M.obj)).obj B.obj) ≫
      (comparison C T).map
        (boundaryEtaleDefiningComposite C i B.obj M.obj Y.obj ae) ≫
      ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        C M.obj).app Y.obj).hom =
    (proetaleImage C i).map
        (boundaryDefiningSourceIso C i M.obj B.obj B'.obj v).hom ≫
      (proetaleImage C i).map
        (β_ ((upperStar C i).leftDerivedFunctor.obj ((comparison C T).obj M.obj)) B'.obj).hom ≫
      inv (((rightDerivedLowerStarProjectionMap C i).app B'.obj).app
        ((comparison C T).obj M.obj)) ≫
      (β_ ((proetaleImage C i).obj B'.obj) ((comparison C T).obj M.obj)).hom ≫
      ((ProEtale.derivedTensor C T).obj
        ((comparison C T).obj M.obj)).map ap

end Composites

/-- Canonical comparison identifies the two projection-inverse/symmetry/final-arrow
composites. The symmetry is the actual descended Koszul braiding
`DerivedCategory.braidedCategory`, with no supplied symmetry or coherence assumptions. The ordinary
exact
inverse images are written through their canonical left-derived identifications in
`pullbackSquare` and the two ordinary projection transformations. No exceptional
right adjoint, constructibility or Tor-amplitude hypothesis occurs.

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-pf-proetale,
`thm-sf-pf-proetale.proof.md`, comparison paragraph; expanded calculation in
`lem-weil-boundary-proetale-q-compatibility`, step 1
(blueprint: lem-weil-boundary-q-defining-composite-comparison).

Proof:
1. The canonical tensor comparison is natural in both inputs and commutes with signed
   symmetry: use lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
   lem-sfb-ringed-derived-monoidal-comparisons and
   lem-sf-ringed-derived-closed-symmetric-monoidal, on small site representatives.
2. Put L = i_e^* M, D = L tensor B, E = B tensor L. Naturality of symmetry gives
   r C_Z(sigma_e) = sigma_p s. Set H = eta_E F_p(r inverse). Apply F_p and
   naturality of eta to obtain H F_p(sigma_p) F_p(s) = C_T(F_e(sigma_e)) eta_D.
3. Write V = F_p(v), d = eta_B V inverse and k = c_(T;F_e B,M). Compose the assumed
   projection square with k C_T(pi_e inverse) on the left and
   (V inverse tensor 1) pi_p inverse on the right. Cancel inverses to get
   k C_T(pi_e inverse) H = (d tensor 1) pi_p inverse.
4. Let g_e = (1 tensor a_e) sigma_e and g_p = (1 tensor a_p) sigma_p. The final-arrow
   hypothesis says a_p = C_T(a_e) d. Tensor-comparison naturality and signed-symmetry
   naturality give c_(T;M,Y) C_T(g_e) = g_p (d inverse tensor 1) k.
5. Expand t_e and t_p. Substitute the input identity from step 2, the output identity
   from step 4, and the inverse-projection identity from step 3. Cancel
   (d inverse tensor 1)(d tensor 1) to obtain the displayed equality. Only the two
   stipulated projection components are inverted; no projection-formula theorem is used.
-/
theorem boundary_q_defining_composite_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i] [CompactSpace T] :
    BoundaryDefiningCompositeComparison (ModuleCat.{u + 1} A) i := by
  sorry

end AlgebraicGeometry.ProEtale.BoundaryComparisonOfCoefficients
