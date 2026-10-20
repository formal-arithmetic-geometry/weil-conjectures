/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.DerivedNakayamaResolution
public import Sheaf.Paper.ModuleObjects
public import Sheaf.Paper.CoefficientHeartCommonStratification
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.SixFunctors.IntTensorProjection
import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import WeilConjectures.AlgebraicGeometry.DimensionBaseChange
import WeilConjectures.AlgebraicGeometry.DimensionAffineOpenCover
import WeilConjectures.AlgebraicGeometry.Dimension
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.CondensedConstructibleOpenClosedImages
import Sheaf.Paper.FiniteConstantCokernel
import Sheaf.Paper.FiniteRingConstructibleSheafOrigin
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.Paper.CondensedConstantConstructibility
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.Constructible

/-!
# Torsion reductions of locally closed integral lattices

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-proper-heart-bound,
`sk-lem-proper-heart-bound-torsion.md` (blueprint: det-proper-heart-bound-torsion).
The ordinary relative tensor with the actual quotient module is the canonical quotient
by the uniformizer power. The scalar equations in the origin predicate retain its module
structure when comparing with fixed finite-coefficient sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
  [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]

/-- Multiplication by an actual integral scalar on the continuous condensed integer sheaf.
Source: blueprint torsion reduction, coefficient convention
(blueprint: det-proper-heart-bound-torsion). -/
def torsionIntegerMultiply (b : Padic.coefficientExtensionIntegers ℓ E) :
    End (DerivedNakayama.integerRing ℓ E) :=
  letI := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  ⟨{
    app := fun S ↦ AddCommGrpCat.ofHom
      (AddMonoidHom.mulLeft (ULift.up (ContinuousMap.const S.unop b)))
    naturality := fun _ _ _ ↦ rfl }⟩

/-- The underlying additive scalar endomorphism, using the pulled-back scalar and the
specified internal module action. Source: blueprint torsion reduction, coefficient convention
(blueprint: det-proper-heart-bound-torsion). -/
def torsionScalar {X : Scheme.{u}}
    (M : pulledBackModuleObjects (DerivedNakayama.integerRing ℓ E) X)
    (b : Padic.coefficientExtensionIntegers ℓ E) : End M.X :=
  (λ_ M.X).inv ≫
    ((η[condensedRingObj (DerivedNakayama.integerRing ℓ E) X] ≫
      (upperStarFromPoint X).map (torsionIntegerMultiply ℓ E b)) ▷ M.X) ≫ Mod.act M.X

/-- The actual locally closed extension, with the chosen open--closed factorization.
Source: blueprint torsion statement, a_! = i_* u_!
(blueprint: det-proper-heart-bound-torsion). -/
abbrev torsionLocallyClosedExtension {S Sbar X : Scheme.{u}}
    (j : S ⟶ Sbar) [IsOpenImmersion j] (i : Sbar ⟶ X) :=
  CondensedRing.openImmersionLowerShriek (DerivedNakayama.integerRing ℓ E) j ⋙
    CondensedRing.lowerStar (DerivedNakayama.integerRing ℓ E) i

/-- The canonical quotient L / pi^n L, as ordinary relative tensor with O_E / pi^n.
Source: blueprint torsion statement, Q_n in the reduction paragraph
(blueprint: det-proper-heart-bound-torsion). -/
abbrev torsionQuotient (S : Scheme.{u}) (n : ℕ) :=
  (tensoringRight (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
    (condensedRingObj (DerivedNakayama.integerRing ℓ E) S))).obj
    ((DerivedNakayama.pullback ℓ E S).obj (DerivedNakayama.quotientModule ℓ E n))

/-- Scalar multiplication on a fixed-coefficient module sheaf, with the given scalar action.
Source: blueprint torsion statement, finite discrete coefficients
(blueprint: det-proper-heart-bound-torsion). -/
def torsionFixedScalar {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {B : Type (u + 1)} [CommRing B]
    (G : Sheaf J (ModuleCat.{u + 1} B)) (b : B) : End G :=
  ⟨{
    app := fun U ↦ ModuleCat.ofHom (b • LinearMap.id)
    naturality := fun _ _ f ↦ by
      ext m
      exact ((G.obj.map f).hom.map_smul b m).symm }⟩

/-- A finite-coefficient presentation, linear for every integral scalar, and its constructible
etale origin. The quotient action is locally generated by constant scalars, so the displayed
scalar equation says precisely that the comparison is a module isomorphism, including for
nonconstant local sections of the finite constant ring.
Source: blueprint torsion statement, classical constructibility
(blueprint: det-proper-heart-bound-torsion). -/
def TorsionClassicalOrigin (X : Scheme.{u}) (n : ℕ) (hn : 1 ≤ n)
    (N : pulledBackModuleObjects (DerivedNakayama.integerRing ℓ E) X) : Prop :=
  letI : Finite (Padic.coefficientExtensionRing ℓ E n) :=
    Padic.finite_coefficientExtensionRing ℓ E n hn
  ∃ G : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing ℓ E n))),
    ∃ e : (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing ℓ E n))) Ab.{u + 1})).obj G ≅ N.X,
      (∀ b : Padic.coefficientExtensionIntegers ℓ E,
        e.hom ≫ torsionScalar ℓ E N b =
          (sheafCompose (Scheme.ProEt.topology X)
            (forget₂ (ModuleCat.{u + 1}
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing ℓ E n))) Ab.{u + 1})).map
                (torsionFixedScalar G
                  (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E n) b))) ≫
            e.hom) ∧
      ∃ F : Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing ℓ E n))),
        Scheme.IsConstructibleEtaleModuleSheaf F ∧
          Nonempty ((comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing ℓ E n)))
              X).obj F ≅ G)

/-- The natural reduction isomorphism, its degree-zero constructible etale origin, and the
2d vanishing bound over every affine categorically weakly contractible pro-etale object.
Source: blueprint main-20261015, sk-lem-proper-heart-bound-torsion; Stacks Tags 099Y,
09AF, 095U, 09A6 and 0991 (blueprint: det-proper-heart-bound-torsion).

Proof plan:
1. By det-pe-derived-nakayama-resolution the coefficient reduction is the two-term complex
   [L -- pi^n --> L]. On a cover trivializing L it is injective on finite free summands,
   with cokernel L/pi^n L. Thus derived reduction is this ordinary quotient in degree zero.
   The quotient ring is finite by lem-weil-pbc-standard-quotients-perfect.
2. By lem-weil-pbc-finite-type-over-noetherian, pqf-def-locnoeth and
   lem-sc-affine-noetherian-underlying-space, finite affine covers make X and Sbar
   topologically Noetherian. By def-weil-constructible-subset the open immersion j and
   the complement of i are retrocompact, hence quasi-compact.
3. Use lem-weil-pbc-proetale-ringed-open-closed, sk-def-sfb-coefficient-morphisms and
   sk-def-sfb-module-lower-shriek for exactness of i_* and j_!. Apply
   det-lem-int-tensor-projection to the finite quotient coefficient. Its coefficient
   pullback is the specified quotient on S, so step 1 gives the natural isomorphism.
4. The quotient on S has finite constant free local models. Apply sk-def-sfb-constructible,
   lem-weil-pbc-condensed-constructible-open-closed-images and
   lem-weil-pbc-finite-constant-proetale-cokernel, including rank zero. Then
   lem-weil-pbc-finite-ring-constructible-sheaf-origin gives a constructible etale F.
   All comparisons preserve the integral action through its actual quotient map.
5. By lem-pc-proper-base-change p_V is proper. Use def-pc-base-change,
   lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-open-fibre-product,
   lem-pc-dimension-affine-open-cover, lem-pc-scheme-dimension-local-rings and
   lem-pc-dim-base-change to transfer the geometric fibre bound to all fibres of p_V.
   The empty fibre stays empty. By lem-weil-pbc-comparison-pullback the restriction
   is classical. Its underlying etale abelian sheaf is killed by the positive integer
   |A_n|, so lem-kun-proper-torsion-cd-bound kills R^q p_V,* above 2d, without a
   Noetherian assumption on V.
6. Proper implies qcqs by def-weil-proper-morphism, def-weil-finite-type-morphism and
   lem-pc-separated-quasi-separated. Apply sk-thm-pe-direct-image-comparison to F[0],
   with abelian coefficients. Exact inverse image gives the same pro-etale vanishing.
7. By lem-weil-proetale-weakly-etale-localization and
   lem-weil-pbc-localized-sheaves-over-representable the site of V is the slice over V.
   An epimorphism in this slice is an underlying epimorphism; projectivity of h_V,
   namely sk-def-pe-weak-contractible, lifts sections. Thus terminal evaluation is exact
   by lem-weil-pbc-proetale-weakly-contractible-evaluation-exact.
8. Apply lem-weil-pbc-ringed-topoi-derived-pushforward-composition to abelian coefficients
   and global sections (def-sfb-finite-derived-global-sections). Exact evaluation of step 7
   computes cohomology termwise by sk-def-sfb-derived-categories. Consequently
   H^q(X_V,G) = Gamma(V,R^q p_V,*G), which vanishes by step 6. -/
theorem properHeartBoundTorsion
    (k : Type u) [Field k] (hchar : ringChar k ≠ 0) (hell : ringChar k ≠ ℓ)
    {X Y S Sbar : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (V : Y.ProEt) [IsAffine V.left]
    (hV : (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} V)
    (j : S ⟶ Sbar) [IsOpenImmersion j] (i : Sbar ⟶ X) [IsClosedImmersion i]
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (
      ObjectProperty.ι (IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E)
        (X := S)) ⋙ torsionLocallyClosedExtension ℓ E j i ⋙
        DerivedCategory.singleFunctor _ 0 ⋙ DerivedNakayama.reductionFunctor ℓ E X n ≅
      ObjectProperty.ι (IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E)
        (X := S)) ⋙ torsionQuotient ℓ E S n ⋙
        torsionLocallyClosedExtension ℓ E j i ⋙ DerivedCategory.singleFunctor _ 0) ∧
    ∀ L : ObjectProperty.FullSubcategory
        (IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) (X := S)),
      TorsionClassicalOrigin ℓ E X n hn
        ((torsionLocallyClosedExtension ℓ E j i).obj ((torsionQuotient ℓ E S n).obj L.obj)) ∧
      ∀ q : ℤ, (2 * d : ℤ) < q →
        IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
          ((rightDerivedGlobalSections Ab.{u + 1} (pullback p V.hom)).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              ((Scheme.proEtaleSheafInverseImage (pullback.fst p V.hom) Ab.{u + 1}).obj
                (((torsionLocallyClosedExtension ℓ E j i).obj
                  ((torsionQuotient ℓ E S n).obj L.obj)).X))))) := by
  sorry

end AlgebraicGeometry.ProEtale
