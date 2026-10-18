/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
public import Sheaf.SixFunctors.IntrinsicDerivedTensorOfUniverses
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Sheaf.SixFunctors.IntrinsicDerivedTensor
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Finiteness.Defs

import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Paper.ProEtaleLocallyConstantSheaf
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import WeilConjectures.CategoryTheory.TruncationTriangle
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.SfCommonStageWeilCohomology

/-!
# Bounded locally constant residue cohomology gives Tor bounds on every slice

Source: Stacks Project, proetale.tex, Tag 09C3, finite residue Tor-amplitude input;
derived.tex, Tag 08J5, finite truncation filtration; sites-cohomology.tex,
Tags 06YQ, 06YS and 06YU
(blueprint: lem-fix-constructible-flat-cohomology-tor-bound).

The finite coefficient index zero denotes exponent one. Vanishing is vanishing of
module sheaves on the actual localized site, with arbitrary test module sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Sheafification on a slice in a universe containing both site and coefficients.
Source: Stacks 03DA (blueprint: lem-fix-constructible-flat-cohomology-tor-bound). -/
instance residueTorSliceAbSheafify (V : Scheme.{t}) (U : V.ProEt) :
    HasSheafify ((ProEt.topology V).over U) AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  hasSheafifyEssentiallySmallSite _ _

/-- The locally bijective criterion on that same slice.
Source: Stacks 03DA (blueprint: lem-fix-constructible-flat-cohomology-tor-bound). -/
instance residueTorSliceAbLocallyBijective (V : Scheme.{t}) (U : V.ProEt) :
    ((ProEt.topology V).over U).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Standard localization for all residue coefficient sheaves on the global site.
Source: Stacks 05RU (blueprint: lem-fix-constructible-flat-cohomology-tor-bound). -/
instance residueTorGlobalDerived (V : Scheme.{t})
    (R : Sheaf (ProEt.topology V) RingCat.{max u (t + 1)}) :
    HasDerivedCategory (SheafOfModules.{max u (t + 1)} R) :=
  HasDerivedCategory.standard _

/-- Standard localization on the actual slice, including either definitionally
identical order of coefficient restriction and forgetting commutativity.
Source: Stacks 05RU (blueprint: lem-fix-constructible-flat-cohomology-tor-bound). -/
instance residueTorSliceDerived (V : Scheme.{t}) (U : V.ProEt)
    (R : Sheaf ((ProEt.topology V).over U) RingCat.{max u (t + 1)}) :
    HasDerivedCategory (SheafOfModules.{max u (t + 1)} R) :=
  HasDerivedCategory.standard _

/-- Bounded locally constant finite-dimensional residue cohomology gives the same
Tor interval after restriction to every localized site. Module.Finite for the residue
field is exactly finite dimensionality; the coefficient sheaf is R/(varpi), not a
field of characteristic zero. Source: Stacks 09C3, finite residue Tor-amplitude input;
08J5, 03ER, 03DJ, 03EL, 06YQ, 06YS and 06YU
(blueprint: lem-fix-constructible-flat-cohomology-tor-bound).

Proof:
1. Fix U and restrict K_1 to the slice. Exact restriction commutes with cohomology,
so its cohomology vanishes outside [a,b]. Pull back each trivializing cover to this
slice; its remaining cohomology has finite-dimensional constant local models.
Uses: lem-pur-site-restriction-module-adjunction-exact,
def-weil-derived-cohomology-sheaves, def-weil-proetale-locally-constant-sheaf,
def-pur-localized-ringed-site.
2. A basis of each local vector space identifies its constant module sheaf with a
finite sum of the coefficient unit. Tensor there is a finite direct sum of the
identity and is exact. Exact restriction and tensor restriction, followed by local
detection of kernels and sheafified cokernels, show each cohomology sheaf is flat.
Uses: lem-sfb-localized-site-tensor-restriction, def-pc-flat-sheaf-modules,
def-weil-sheaf-of-modules-category.
3. Put T_q = tau_le_q(K_1|U). The truncation triangles have successive quotients
H^q(K_1|U)[-q]. The support hypothesis identifies T_(a-1) with zero and T_b with
K_1|U in the derived category.
Uses: lem-weil-pbc-truncation-triangle, def-weil-abstract-derived-category.
4. Resolve arbitrary L[0] by a flat-term K-flat complex P. Derived tensor with L[0]
preserves triangles and shifts. One obtains this first for left tensor by P and
then uses signed symmetry x tensor y mapped to (-1)^(deg x deg y) y tensor x.
Uses: lem-pc-kflat-resolution, lem-pc-sheaf-modules-tensor-closed,
def-pc-tensor-complex-sheaves, lem-weil-pbc-site-derived-tensor-descent,
lem-sc-source-kflat-tensor-left-triangulated.
5. Each single flat cohomology sheaf H^q[-q] is K-flat. Its tensor with P has
cohomology H^q tensor H^(i-q)(P), by exactness of tensor with H^q; it vanishes
unless i=q. No flatness or boundedness is imposed on L.
Uses: lem-pc-bounded-above-flat-kflat-site, lem-weil-pbc-site-derived-tensor-descent,
def-pc-tensor-complex-sheaves, def-weil-derived-cohomology-sheaves.
6. Induct over a-1 through b. In the tensor image of each truncation triangle,
the long exact cohomology sequence and step 5 propagate vanishing below a and
above q. The case q=b gives the result for K_1|U. U and L were arbitrary.
Uses: lem-sf-derived-homology-long-exact. Affineness, weak contractibility and
completeness specify the intended input but are not needed in this filtration argument. -/
theorem constructible_flat_cohomology_tor_bound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (V : Scheme.{t}) [IsAffine V]
    (_hV : (ProEt.topology V).IsWeaklyContractible.{max u (t + 1)} (ProEt.mk (𝟙 V)))
    (K : DerivedCategory (scalarReductionSource l E V))
    (_hcomplete : IntegralOnSlice.IsComplete l E V none K)
    (a b : ℤ) (_hab : a ≤ b)
    (_hbounded : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((scalarReductionDerivedExtension l E V 0).obj K)))
    (_hlocal : ∀ q : ℤ,
      IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses V
        (Padic.coefficientExtensionRing l E 1)
        (fun M ↦ Module.Finite (ULift.{t + 1} (Padic.coefficientExtensionRing l E 1)) M)
        ((DerivedCategory.homologyFunctor _ q).obj
          ((scalarReductionDerivedExtension l E V 0).obj K))) :
    ∀ (U : V.ProEt)
      (L : SheafOfModules.{max u (t + 1)} ((integralCoefficientSheaf l E V 0).over U))
      (i : ℤ), i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        (SheafOfModules.ringedSiteDerivedTensorOfUniverses.{t + 1, t,
            max u (t + 1), (max u (t + 1)) + 1}
          ((integralCoefficientCommRingSheaf l E V 0).over U)
          (ringedSiteDerivedRestrictionOfUniverses.{t + 1, t, max u (t + 1),
              max u (t + 1), (max u (t + 1)) + 1, (max u (t + 1)) + 1}
            (integralCoefficientSheaf l E V 0) U
            ((scalarReductionDerivedExtension l E V 0).obj K))
          ((DerivedCategory.singleFunctor _ 0).obj L))) := by
  sorry

end WeilConjectures
