/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.Paper.Pur9Invertible
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.FiniteCoefficientTensorCtf
import Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.FiniteCompactSupportConstructibility
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.DerivedPullbackTensorIso
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat

/-!
# Co-projection for a closed immersion

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-coprojection,
lem-pur-coprojection and its five-Hom-bijection proof (blueprint: lem-pur-coprojection).

The isomorphism is specified by the projection/counit equation for its inverse.
This equation identifies the canonical right-adjoint comparison, rather than merely
asserting an isomorphism between its endpoints. The exceptional functor and counit
are the transported etale ones, used only on bounded constructible objects.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The recorded intrinsic bounded constructibility predicate in fixed-scalar coordinates.
The realization is the canonical constant-scalar equivalence, applied termwise.
Source: blueprint lem-pur-coprojection, K in Dbc (blueprint: lem-pur-coprojection). -/
noncomputable def purityCoprojectionConstructible
    (P : WeilConjectures.PurityFiniteSetting.{u}) (W : Scheme.{u})
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} P.Coefficient))) : Prop :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  Scheme.intrinsicFiniteTorsionConstructible
    P.coefficients.l P.extension P.level P.level_pos W
      ((finiteCoefficientIntrinsicRealization W P.Ring).mapDerivedCategory.obj K)

/-- The canonical co-projection is an isomorphism, expressed by its inverse's counit
normalization. For F = Ri_!, G = Ri^!, and Q = Li^*, the equation is
PF(GK,L); F(e.inv); eps(K tensor L) = eps(K) tensor id(L).
Thus e.inv is precisely the exceptional transpose of the inverse projection followed
by the tensor of the exceptional counit. Equivalently e is the right-adjoint comparison
induced by projection with the inverse of L. Its direction is G(K tensor L) to GK tensor QL.
The bounded-below witnesses are conclusions, not assumptions on the input or on an
ambient pro-etale adjunction. The proper-map instance fixes the default compactification
coordinates.
Source: blueprint lem-pur-coprojection, canonical-map paragraph
(blueprint: lem-pur-coprojection). -/
noncomputable def purityCoprojectionProperty
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z W : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i]
    (aW : W ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aW] [QuasiCompact aW]
    (K L : DerivedCategory (Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} P.Coefficient))) : Prop :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  letI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace aW
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) i
  let G := rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) i
  let Q := (upperStar (ModuleCat.{u + 1} P.Coefficient) i).leftDerivedFunctor
  let tensorW := derivedTensor (ModuleCat.{u + 1} P.Coefficient) W
  let tensorZ := derivedTensor (ModuleCat.{u + 1} P.Coefficient) Z
  let KL := (tensorW.obj K).obj L
  ∃ hK : DerivedCategory.TStructure.t.plus K,
    ∃ hKL : DerivedCategory.TStructure.t.plus KL,
      ∃ e : G.obj KL ≅ (tensorZ.obj (G.obj K)).obj (Q.obj L),
        ((projectionMap (ModuleCat.{u + 1} P.Coefficient) i).app (G.obj K)).app L ≫
          F.map e.inv ≫ rightDerivedUpperShriekCounit i KL hKL =
        (tensorW.map (rightDerivedUpperShriekCounit i K hK)).app L

/-- Co-projection for a closed immersion, with an inverse in the finite-Tor constructible
category. Source: blueprint main-20261015, sk-lem-coprojection/lem-pur-coprojection.md
(blueprint: lem-pur-coprojection).

Proof:
1. Choose the inverse M. Pullback preserves finite Tor amplitude
(lem-sf-pullback-tor-amplitude) and respects tensor and unit
(lem-pur-derived-pullback-tensor-iso), so Li*L and Li*M are inverse. Tensor by each
of L, M and their pullbacks preserves Dbc (lem-sf-tensor-ctf).
2. The closed symmetric derived tensor (lem-coef-sheaf-flat-model) makes tensor by L
and M quasi-inverse. Adjointify this equivalence (lem-weil-pbc-quasi-inverse-adjoint)
and pull back its unit and counit to Z, preserving their triangle identities.
3. Use the constructible exceptional adjunction (thm-sf-ambient-adjoint-class).
Nagata and lem-kun-dimension-finite-type provide the finite-dimensional compactification;
prop-finite-compact-support-constructibility gives the constructible compact-support domain.
For every constructible A, the five natural Hom bijections are exceptional adjunction,
tensor by M adjunction, projection (fix-prop-projection-formula), exceptional adjunction,
and tensor by Li*M adjunction.
4. Yoneda (lem-galois-yoneda-fully-faithful) represents their composite and its inverse
by mutually inverse morphisms, giving the displayed isomorphism.
5. Uniqueness of right adjoints (det-sp-unique-right-adjoint) identifies it with the
comparison induced by def-exchange-projection. Its inverse is the exceptional transpose
of inverse projection followed by eps(K) tensor id(L), which is exactly the equation
in purityCoprojectionProperty. No ambient pro-etale exceptional adjunction is used. -/
theorem purity_coprojection
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z W : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))] [W.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
    [QuasiCompact (W ↘ Spec (.of P.field.k))]
    [IsSeparated (W ↘ Spec (.of P.field.k))]
    (i : Z ⟶ W) [i.IsOver (Spec (.of P.field.k))] [IsClosedImmersion i]
    (K L : DerivedCategory (Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} P.Coefficient)))
    (_hK : purityCoprojectionConstructible P W K)
    (_hL : WeilConjectures.finiteTorConstructibleProEtaleModule
      P.coefficients.l P.extension P.level P.level_pos W L)
    (_hInv : ∃ d : TensorInvertibleData (fun B C ↦ B ⊗ C) (𝟙_ _) L,
      WeilConjectures.finiteTorConstructibleProEtaleModule
        P.coefficients.l P.extension P.level P.level_pos W d.inverse) :
    purityCoprojectionProperty P i (W ↘ Spec (.of P.field.k)) K L := by
  sorry

end AlgebraicGeometry.ProEtale
