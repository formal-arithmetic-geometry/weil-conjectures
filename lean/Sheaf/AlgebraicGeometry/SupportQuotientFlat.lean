/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Homology.Single

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison

import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.SixFunctors.OpenClosedFlatness
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.SixFunctors.OpenClosed.Exact
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import WeilConjectures.SixFunctors.OpenClosed.Stalk
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-!
# Flat constant coefficients with closed support

Source: blueprint `lem-pur-kunneth-supported`, support-quotient argument, and its
stage-1 refinement (blueprint: lem-pur-support-quotient-flat).

The two quotients are actual cokernels of the extension-by-zero counits. Restriction
of the constant sheaf to the open complement is canonically the same constant sheaf.
Thus these counits are precisely the arrows induced by the inclusion of the open
object into the final object. The canonical coefficient realizations express ordinary
module-valued sheaves as modules over the constant commutative ring sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]
  {C T : Scheme.{u}} (a : C ⟶ T) [IsClosedImmersion a]

/-- The defining etale arrow, the extension-by-zero counit on the constant ring module.
It sends the generator indexed by a factorization through the open complement to one.
Source: blueprint support quotient (blueprint: lem-pur-support-quotient-flat). -/
def etaleSupportQuotientArrow :=
  (Etale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) a.openComplement.ι).counit.app
      ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))

/-- The defining pro-etale arrow, the same extension-by-zero counit.
Source: blueprint support quotient (blueprint: lem-pur-support-quotient-flat). -/
def proEtaleSupportQuotientArrow :=
  (ProEtale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) a.openComplement.ι).counit.app
      ((constantSheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))

/-- The etale support quotient is the actual cokernel, not a chosen supported object.
Source: blueprint support quotient (blueprint: lem-pur-support-quotient-flat). -/
def etaleSupportQuotient := cokernel (etaleSupportQuotientArrow A a)

/-- The pro-etale support quotient is the actual cokernel of its defining arrow.
Source: blueprint support quotient (blueprint: lem-pur-support-quotient-flat). -/
def proEtaleSupportQuotient := cokernel (proEtaleSupportQuotientArrow A a)

/-- The etale quotient map.
Source: blueprint support quotient (blueprint: lem-pur-support-quotient-flat). -/
def etaleSupportQuotientMap := cokernel.π (etaleSupportQuotientArrow A a)

/-- The pro-etale quotient map.
Source: blueprint support quotient (blueprint: lem-pur-support-quotient-flat). -/
def proEtaleSupportQuotientMap := cokernel.π (proEtaleSupportQuotientArrow A a)

/-- The canonical comparison on the constant ring module. Its adjunct extends the
constant scalar sections, so it sends the pulled-back constant one to constant one.
Source: blueprint comparison normalization (blueprint: lem-pur-support-quotient-flat). -/
def supportQuotientConstantComparison :=
  ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).homEquiv
    ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
      (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))
    ((constantSheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
      (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))).symm
    (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (Etale.isTerminalMkId T)).homEquiv _ _).symm
        ((toSheafify (ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))).app
              (op (ProEt.mk (𝟙 T)))))

/-- Both support quotients are tensor-flat and K-flat in degree zero. Their etale
geometric stalks are the coefficient ring on the closed subset, normalized by the
quotient of constant one, and zero on its complement. Comparison is uniquely normalized
by the actual quotient maps.

Source: blueprint support-quotient argument and stage-1 refinement
(blueprint: lem-pur-support-quotient-flat).

Proof:
1. Apply the etale open-closed short exact sequence to the constant ring sheaf
(lem-weil-pbc-open-closed-short-exact). Inverse image preserves constant rings
(prop-weil-pbc-inverse-image-modules-exact). Free Yoneda and sheafification identify
its counit with the defining arrow: both send the generator to one
(lem-weil-pbc-free-yoneda-presheaf-module). Thus the cokernel is canonically a_* A_C,
with the quotient map the unit. The pro-etale ringed open-closed sequence gives the
same identification (lem-weil-pbc-proetale-ringed-open-closed); its quasi-compactness
hypothesis is exactly the displayed assumption on the open complement.
2. A_C is a free rank-one module over itself, hence flat. The open-closed flatness
criterion (lem-sfb-open-closed-flatness) makes a_* A_C flat in both topologies.
The degree-zero complex is bounded above with flat terms, hence K-flat by
lem-pc-bounded-above-flat-kflat-site. The canonical realization functors merely express
these same ordinary sheaves in the ringed-site tensor and K-flat definitions.
3. A closed immersion is finite (lem-weil-pbc-closed-immersion-finite). The finite
stalk formula (lem-weil-pbc-finite-stalk-formula-restriction and
lemma-openclosed-stalk-lowerstar) is a product over the geometric fibre: empty off C,
and a singleton on C. The constant-stalk identification
(lem-weil-pbc-constant-sheaf-geometric-stalk) gives zero and A respectively, and the
unit sends the quotient of constant one to one.
4. Free Yoneda and sheafification give Hom(j_V! A_V,N) = N(V), for V=T or its open
complement. The comparison adjunction identifies these representing objects in the
two topologies, preserving their generators and the inclusion arrow. Exact comparison
inverse image (lem-sf-comparison-pullback-exact) therefore gives an isomorphism of the
cokernels with the displayed quotient-map identity. The pulled-back quotient map is
epic, so the normalized map, and thus its isomorphism, is unique. -/
theorem supportQuotient_flat_kflat_stalk_comparison [QuasiCompact a.openComplement.ι] :
    SheafOfModules.IsFlatOnSite
      ((etaleSumFlatModuleRealization T (ULift.{u + 1, u} A)).obj
        (etaleSupportQuotient A a)) ∧
    SheafOfModules.IsFlatOnSite
      ((ProEtale.finiteCoefficientIntrinsicRealization T A).obj
        (proEtaleSupportQuotient A a)) ∧
    CochainComplex.IsKFlatIndependentCoefficients
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        ((etaleSumFlatModuleRealization T (ULift.{u + 1, u} A)).obj
          (etaleSupportQuotient A a))) ∧
    CochainComplex.IsKFlatIndependentCoefficients
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        ((ProEtale.finiteCoefficientIntrinsicRealization T A).obj
          (proEtaleSupportQuotient A a))) ∧
    (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T),
      ((t (IsLocalRing.closedPoint Ω) ∈ Set.range a) →
        ∃ e : (pointSmallEtale t).sheafFiber.obj (etaleSupportQuotient A a) ≅
          ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A),
          (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
            (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))).app
              (op (Etale.mk (𝟙 T))) ≫
            (pointSmallEtale t).toPresheafFiber (Etale.mk (𝟙 T))
              (Over.homMk t (Category.comp_id t))
              ((constantSheaf T.smallEtaleTopology
                (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
                  (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))).obj ≫
            (pointSmallEtale t).sheafFiber.map (etaleSupportQuotientMap A a) ≫ e.hom = 𝟙 _) ∧
      ((t (IsLocalRing.closedPoint Ω) ∉ Set.range a) →
        IsZero ((pointSmallEtale t).sheafFiber.obj (etaleSupportQuotient A a)))) ∧
    (∃! e : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).obj
          (etaleSupportQuotient A a) ≅ proEtaleSupportQuotient A a,
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).map
          (etaleSupportQuotientMap A a) ≫ e.hom =
        supportQuotientConstantComparison A (T := T) ≫ proEtaleSupportQuotientMap A a) := by
  sorry

end AlgebraicGeometry.Scheme
