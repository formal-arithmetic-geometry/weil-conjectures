/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q90
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Paper.FiniteDirectImageComposition
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.DerivedPullbackTensorIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Paper.RingedProjectionTensorComposition

/-! # The finite direct-image compositor, counit and projection mate

Source: Stacks Project, Categories, Tag 0DV0, equation-compose-counits;
Cohomology on Sites, Tags 0D6D, 0D6E and 0B56, equation-projection-formula-map
(blueprint: lem-pur-pf-finite-compositor-counit).

The fixed-scalar presentation is the published ordinary unbounded category of
constant-A modules, with its size lift. The maps below are the actual K-flat
pullback compositor, K-injective fibre-product-pasting direct-image compositor,
and counit-defined projection transformation, rather than supplied isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- Specialize the published flat-pullback instance to the finite purity coefficient ring.
This constructs the existing class from finite-ring Noetherianity, without an extra
hypothesis on the coefficient datum or any derived input.
Source: Stacks Project, Tag 07A4, finite coefficient specialization
(blueprint: lem-pur-pf-finite-compositor-counit). -/
instance finiteCompositor_preservesFlat (P : PurityFiniteSetting.{u}) :
    UpperStarPreservesFlat (ModuleCat.{u + 1} P.Coefficient) :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  letI : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
  upperStarPreservesFlat_moduleCat P.Coefficient

/-- The specified finite direct-image compositor preserves the ordinary counit
and the projection mate, naturally in the arbitrary derived arguments.
Source: Stacks Project, Tags 0DV0, 0D6D, 0D6E, 07A6 and 0B56
(blueprint: lem-pur-pf-finite-compositor-counit).

Proof:
1. Write p_t and r_t for the ordinary module operations. The constant coefficient
maps identify their rings, so p_t is exact. The sectionwise pasting comparison
b is induced by U ×_W T = U ×_V (V ×_W T), preserving the scalar maps.
The composite ordinary adjunction conjugates b inverse to the canonical
pullback comparison: the two units insert tensor factors 1, with the inverse
(m tensor s) tensor r mapping to m tensor c_h(s)r. Tensor balancing checks
both inverses and equality with the single unit.
2. Choose a K-injective representative I of M by
prop-pur-kinjective-resolutions-exist. Exactness of the left adjoints implies
that the r_t preserve K-injectives (lem-weil-pbc-right-adjoint-preserves-kinjective).
In lem-weil-pbc-ringed-topoi-derived-pushforward-composition take the resolution
of r_h I to be its identity. Thus the specified finiteDirectImageComposition,
which derives b, is Q(b_I); no exactness of ordinary direct image is used.
3. Resolve a derived source by a flat-term K-flat complex K
(lem-pc-kflat-resolution). The ordinary homotopy adjunction
lem-weil-pbc-termwise-adjunction-homotopy computes the derived Hom bijection:
use the characterization of lem-pc-pre-derived-adjoint-functors-general with
identity resolutions, and lem-weil-pbc-kinjective-hom-derived for the targets.
Step 1 now identifies precomposition by the canonical a with postcomposition
by c inverse. The Hom/Yoneda characterization of def-weil-pbc-adjunction-conjugate
proves the first clause for exactly these comparisons.
4. The composite counit is epsilon_h after P_h(epsilon_g), by
 def-weil-pbc-composite-adjunction. The adjunct-counit identity
lem-weil-pbc-adjunct-counit-identity applied to the conjugacy in step 3 gives
epsilon_gh after P_gh(c inverse) equal to the composite counit after a.
Precompose with P_gh(c) and cancel its inverse to obtain the second clause.
5. Apply lem-sfb-ringed-projection-tensor-composition to the three small
pro-etale ringed topoi. Its comparisons are the finite tensor comparisons
of lem-pur-derived-pullback-tensor-iso. Its projection is precisely the mate
of tensor comparison followed by epsilon tensor 1, as in def-exchange-projection.
Steps 2--4 identify its right comparison with the specified c. Insert c_M tensor
1 at the source and R_g R_h(1 tensor a_N) after c at the target. This is the
third displayed clause, without inverting any projection.
6. All components are natural transformations (projection is a transformation
of bifunctors), so the formulas are natural in M and in (M,N), respectively.
The unit normalizations of lem-weil-derived-direct-image-composition and
lem-sfb-ringed-projection-tensor-composition also apply to identity morphisms,
as made explicit below. Nothing restricts the unbounded derived arguments. -/
theorem finiteCompositorCounit
    (P : PurityFiniteSetting.{u})
    (U V W : Over (Spec (CommRingCat.of P.field.k)))
    [IsSeparated U.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [IsSeparated V.hom] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    [IsSeparated W.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (h : U ⟶ V) (g : V ⟶ W) [IsProper h.left] [IsProper g.left] :
    (finiteDirectImageComposition P.Coefficient h.left g.left).inv = conjugateEquiv
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) g.left).comp
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) h.left))
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) (h.left ≫ g.left))
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) h.left g.left).hom ∧
    (∀ M : DerivedCategory (Sheaf (ProEt.topology U.left) (ModuleCat.{u + 1} P.Coefficient)),
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) (h.left ≫
      g.left)).counit.app M =
        L(((h.left ≫ g.left))^*[(ModuleCat.{u + 1} P.Coefficient)]).map
      ((finiteDirectImageComposition P.Coefficient h.left g.left).hom.app M) ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) h.left g.left).hom.app
      (R((g.left)_*[(ModuleCat.{u + 1} P.Coefficient)]).obj (R((h.left)_*[(ModuleCat.{u + 1}
      P.Coefficient)]).obj M)) ≫
        L((h.left)^*[(ModuleCat.{u + 1} P.Coefficient)]).map ((derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} P.Coefficient) g.left).counit.app (R((h.left)_*[(ModuleCat.{u + 1}
      P.Coefficient)]).obj M)) ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) h.left).counit.app M)
      ∧
    (∀ (M : DerivedCategory (Sheaf (ProEt.topology U.left) (ModuleCat.{u + 1} P.Coefficient))) (N :
      DerivedCategory (Sheaf (ProEt.topology W.left) (ModuleCat.{u + 1} P.Coefficient))),
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} P.Coefficient) (h.left ≫ g.left)).app
      M).app N) ≫
        (finiteDirectImageComposition P.Coefficient h.left g.left).hom.app (((derivedTensor
      (ModuleCat.{u + 1} P.Coefficient) U.left).obj M).obj (L(((h.left ≫ g.left))^*[(ModuleCat.{u +
      1} P.Coefficient)]).obj N)) ≫
        R((g.left)_*[(ModuleCat.{u + 1} P.Coefficient)]).map (R((h.left)_*[(ModuleCat.{u + 1}
      P.Coefficient)]).map (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) U.left).obj M).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) h.left g.left).hom.app N))) =
      (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) W.left).map ((finiteDirectImageComposition
      P.Coefficient h.left g.left).hom.app M)).app N) ≫
        (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} P.Coefficient) g.left).app
      (R((h.left)_*[(ModuleCat.{u + 1} P.Coefficient)]).obj M)).app N) ≫ R((g.left)_*[(ModuleCat.{u
      + 1} P.Coefficient)]).map (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1}
      P.Coefficient) h.left).app M).app (L((g.left)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj N)))
      := by
  sorry

/-- Both unit specializations use the canonical derived identity identifications.
Thus the compositor in the counit and projection equations above becomes the
identity when either proper morphism is an identity.
Source: Stacks Project, Tags 0DV0 and 0D6E, identity specializations
(blueprint: lem-pur-pf-finite-compositor-counit).

Proof: the ordinary fibre-product-pasting map with an identity factor is the
ordinary direct-image identity comparison. Derive this equality, using the
identity resolution on K-injectives as in step 2 above. The universal
right-derived unit then gives exactly rightDerivedLowerStarId and the derived
transport of lowerStarCongr. Equivalently use the identity normalization of
lem-weil-derived-direct-image-composition. The conjugacy already stated and
 def-weil-pbc-adjunction-conjugate identify the corresponding pullback units,
so substituting in finiteCompositorCounit gives its two identity cases. -/
theorem finiteCompositorCounit_identity
    (P : PurityFiniteSetting.{u})
    (U V : Over (Spec (CommRingCat.of P.field.k)))
    [IsSeparated U.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [IsSeparated V.hom] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (f : U ⟶ V) [IsProper f.left]
    (M : DerivedCategory (Sheaf (ProEt.topology U.left) (ModuleCat.{u + 1} P.Coefficient))) :
    (finiteDirectImageComposition P.Coefficient (𝟙 U.left) f.left).hom.app M ≫
      R((f.left)_*[(ModuleCat.{u + 1} P.Coefficient)]).map ((rightDerivedLowerStarId (ModuleCat.{u +
      1} P.Coefficient) U.left).hom.app M) =
        (Functor.rightDerivedFunctorNatIso (lowerStarCongr (ModuleCat.{u + 1} P.Coefficient)
      (Category.id_comp f.left))).hom.app M ∧
    (finiteDirectImageComposition P.Coefficient f.left (𝟙 V.left)).hom.app M ≫
      (rightDerivedLowerStarId (ModuleCat.{u + 1} P.Coefficient) V.left).hom.app
      (R((f.left)_*[(ModuleCat.{u + 1} P.Coefficient)]).obj M) =
        (Functor.rightDerivedFunctorNatIso (lowerStarCongr (ModuleCat.{u + 1} P.Coefficient)
      (Category.comp_id f.left))).hom.app M := by
  sorry

/-- Identity projection is the identity after the canonical pullback/direct-image
identity identifications, expressed as an equality before identifying endpoints.
Source: Stacks Project, Tags 0B56 and 0DV0, identity specializations
(blueprint: lem-pur-pf-finite-compositor-counit).

Proof: specialize the counit-defined projection mate of def-exchange-projection
to the identity map. Under its canonical identity pullback and direct-image
comparisons, its transpose is identity tensor identity, by the ordinary unit
normalization and lem-pur-derived-pullback-tensor-iso. The adjunction bijection
therefore identifies it with the identity. This is also the identity clause of
lem-sfb-ringed-projection-tensor-composition, with both endpoint comparisons
written explicitly. No inverse projection map is involved. -/
theorem finiteCompositorCounit_identityProjection
    (P : PurityFiniteSetting.{u})
    (U : Over (Spec (CommRingCat.of P.field.k)))
    [IsSeparated U.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (M N : DerivedCategory (Sheaf (ProEt.topology U.left) (ModuleCat.{u + 1} P.Coefficient))) :
    (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} P.Coefficient) (𝟙 U.left)).app M).app
      N) ≫
      (rightDerivedLowerStarId (ModuleCat.{u + 1} P.Coefficient) U.left).hom.app (((derivedTensor
      (ModuleCat.{u + 1} P.Coefficient) U.left).obj M).obj (L(((𝟙 U.left))^*[(ModuleCat.{u + 1}
      P.Coefficient)]).obj N)) ≫
      (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) U.left).obj M).map ((leftDerivedUpperStarId
      (ModuleCat.{u + 1} P.Coefficient) U.left).hom.app N)) =
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) U.left).map ((rightDerivedLowerStarId
      (ModuleCat.{u + 1} P.Coefficient) U.left).hom.app M)).app N) := by
  sorry

end WeilConjectures.PurityFiniteSetting
