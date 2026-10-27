/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H8
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
public import Sheaf.Paper.PfReductionProperOpenIdentities
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.Paper.ProjectionReductionWitnessedFlatDomains
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin

/-! # Scalar compatibility of the normalized proper/open projection

Source: prop-sf-pf-reduction, proper/open pasting calculation;
Stacks Tags 07A4, 07A6, 0E48 and 0GL1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport

/-- The proper counit projection, retaining the supplied tensor presentation.
Source: Stacks 0B56 (blueprint: lem-sf-projection-factor-coordinates). -/
def properProjectionData (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X (R.ring X))
    (aZ : ProEtaleTensorModel c.Z (R.ring c.Z))
    (aY : ProEtaleTensorModel Y (R.ring Y))
    (hR : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i)) :=
  (proEtaleRingDerivedAdjunction c.g (R.ring Y) (R.ring c.Z) (R.pull c.g)).rightAdjointProjectionMap
    (projectionComparisons_existsUnique R c aX aZ aY hR).exists.choose.tensorPullback.hom

/-- Tensor/scalar comparison followed by the specified scalar/pullback comparison.
Source: Stacks 07A4 (blueprint: lem-sf-projection-factor-coordinates). -/
def mixedChange {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (f : U ⟶ V)
    (aU : ProEtaleTensorModel U (R.ring U))
    (bU : ProEtaleTensorModel U (S.ring U))
    (M : DerivedCategory (proEtaleRingModules U (R.ring U)))
    (L : DerivedCategory (proEtaleRingModules V (R.ring V))) :=
  (scalarTensor (a.map U) aU bU).hom.app (M, (pull R f).obj L) ≫
    bU.tensor.map (Prod.mkHom (𝟙 _) ((scalarPull a f).hom.app L))

/-- The separate proper and open equations in the published projection coordinates.
Source: proper/open displayed identities, prop-sf-pf-reduction
(blueprint: lem-sf-projection-factor-coordinates). -/
def ProjectionFactorIdentities {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hR : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i))
    (hS : S.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (S.ring Y) (S.ring c.Z) (S.ring X) (S.pull c.g) (S.pull c.i))
    (aX : ProEtaleTensorModel X (R.ring X))
    (aZ : ProEtaleTensorModel c.Z (R.ring c.Z))
    (aY : ProEtaleTensorModel Y (R.ring Y))
    (bX : ProEtaleTensorModel X (S.ring X))
    (bZ : ProEtaleTensorModel c.Z (S.ring c.Z))
    (bY : ProEtaleTensorModel Y (S.ring Y))
    (K : DerivedCategory (proEtaleRingModules X (R.ring X)))
    (L : DerivedCategory (proEtaleRingModules Y (R.ring Y))) : Prop :=
  let M := (openExtension R c.i).mapDerivedCategory.obj K
  let LB := (pbcDerivedExtend (a.map Y)).obj L
  let MB := (pbcDerivedExtend (a.map c.Z)).obj M
  let KB := (pbcDerivedExtend (a.map X)).obj K
  ((pbcDerivedExtend (a.map Y)).map
      (((properProjectionData R c aX aZ aY hR).app M).app L) ≫
    (properComparison a c.g).app (aZ.tensor.obj (M, (pull R c.g).obj L)) ≫
    (push S c.g).map (mixedChange a c.g aZ bZ M L) =
    (scalarTensor (a.map Y) aY bY).hom.app ((push R c.g).obj M, L) ≫
    bY.tensor.map (Prod.mkHom ((properComparison a c.g).app M) (𝟙 _)) ≫
    ((properProjectionData S c bX bZ bY hS).app MB).app LB) ∧
  ((pbcDerivedExtend (a.map c.Z)).map
      (projectionOpenFactor R c aX aZ hR K L).hom ≫
    (openComparison a c.i).app (aX.tensor.obj (K, (pull R f).obj L)) ≫
    (openExtension S c.i).mapDerivedCategory.map (mixedChange a f aX bX K L) =
    mixedChange a c.g aZ bZ M L ≫
    bZ.tensor.map (Prod.mkHom ((openComparison a c.i).app K) (𝟙 _)) ≫
    (projectionOpenFactor S c bX bZ hS KB LB).hom)

/-- The proper and open equations on finite-Tor constructible inputs, expressed in
arbitrary normalized intrinsic tensor coordinates. This asserts the two factor
identities separately; it does not assert their compact-support composite or any
invertibility result.
Source: prop-sf-pf-reduction, proper counit/open unit calculations; Stacks 07A4,
07A6, 0E48, 0GL1 (blueprint: lem-sf-projection-factor-coordinates).

Proof: transport K and L through the inverse of the exact constant-coefficient
realization. Constructibility and finite Tor amplitude are preserved by this
coefficient equivalence. Choose ordered bounds for both Tor amplitudes. Apply
`exists_witnessedFlatDomains` at these bounds to obtain bounded constructible
etale origins for both inputs, with flat models at levels n+1 and m+1. Cohomology
vanishing below the lower bounds supplies the bounded-below objects required by
`FixedEtaleOriginWitness`. Reflect the Tor bounds across the etale/proetale
comparison, then use its equivalence with etale Tor amplitude. These witnesses
meet all the input and origin hypotheses of `pfReductionProperOpenIdentities`.
Choose the unit-normalized open projections supplied by
`open_scalar_tensor_normalization` and apply that theorem.

Identify each intrinsic tensor model with the selected fixed-module model using
the fully faithful restriction to pairs of flat K-flat representatives. On such
pairs the scalar and geometric tensorators commute with the comparison: both
routes send each balanced pure tensor to the same sections, preserving bidegrees
and the signed total differential. Resolving-class localization descends these
equations. The scalar comparison is the unique comparison of left adjoints with
the same restriction right adjoint. Its unit and counit equations identify the
proper scalar mates. Transpose the proper projection: both coordinates give the
same tensor comparison followed by counit tensor identity. For the open factor,
transpose its inverse: both give the prescribed open unit followed by inverse
tensor comparison. Adjunction injectivity identifies them. The pullback
compositor is the same canonical compositor. Conjugate the two supplied factor
equations by these comparisons, then use naturality at the realization counits
of K and L. This yields exactly the two displayed equations. None of these
steps asserts flatness of the quotient. -/
theorem projection_factor_coordinates
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m n : ℕ) (hmn : m ≤ n)
    (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left] (c : Compactification f.hom.left)
    (hR : (finite C.l E (n + 1) (Nat.succ_pos n)).pull (c.i ≫ c.g) =
      proEtaleRingCompositeCoefficients c.i c.g
      ((finite C.l E (n + 1) (Nat.succ_pos n)).ring Y.obj.left)
      ((finite C.l E (n + 1) (Nat.succ_pos n)).ring c.Z)
      ((finite C.l E (n + 1) (Nat.succ_pos n)).ring X.obj.left)
      ((finite C.l E (n + 1) (Nat.succ_pos n)).pull c.g)
      ((finite C.l E (n + 1) (Nat.succ_pos n)).pull c.i))
    (hS : (finite C.l E (m + 1) (Nat.succ_pos m)).pull (c.i ≫ c.g) =
      proEtaleRingCompositeCoefficients c.i c.g
      ((finite C.l E (m + 1) (Nat.succ_pos m)).ring Y.obj.left)
      ((finite C.l E (m + 1) (Nat.succ_pos m)).ring c.Z)
      ((finite C.l E (m + 1) (Nat.succ_pos m)).ring X.obj.left)
      ((finite C.l E (m + 1) (Nat.succ_pos m)).pull c.g)
      ((finite C.l E (m + 1) (Nat.succ_pos m)).pull c.i))
    (aX : ProEtaleTensorModel X.obj.left ((finite C.l E (n + 1) (Nat.succ_pos n)).ring X.obj.left))
    (aZ : ProEtaleTensorModel c.Z ((finite C.l E (n + 1) (Nat.succ_pos n)).ring c.Z))
    (aY : ProEtaleTensorModel Y.obj.left ((finite C.l E (n + 1) (Nat.succ_pos n)).ring Y.obj.left))
    (bX : ProEtaleTensorModel X.obj.left ((finite C.l E (m + 1) (Nat.succ_pos m)).ring X.obj.left))
    (bZ : ProEtaleTensorModel c.Z ((finite C.l E (m + 1) (Nat.succ_pos m)).ring c.Z))
    (bY : ProEtaleTensorModel Y.obj.left ((finite C.l E (m + 1) (Nat.succ_pos m)).ring Y.obj.left))
    (K : proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E (n + 1)))
    (L : proEtaleDerivedCategory Y.obj.left (Padic.coefficientExtensionRing C.l E (n + 1)))
    (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) X.obj.left K)
    (hL : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) Y.obj.left L) :
    ProjectionFactorIdentities
      (finiteQuotientChange C.l E (n + 1) (m + 1) (Nat.succ_pos n)
        (Nat.succ_pos m) (Nat.succ_le_succ hmn)) c hR hS
      aX aZ aY bX bZ bY K L := by sorry

end WeilConjectures.PurCompactSupport
