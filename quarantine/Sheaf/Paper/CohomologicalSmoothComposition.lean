/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import Sheaf.Paper.CohomologicalSmoothnessComparison

import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.FiniteCoefficientTensorCtf
import Sheaf.Algebra.Homology.DerivedTensor
import Sheaf.Paper.FiniteFieldFiber
import Sheaf.Paper.FiniteTorAmplitude
import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.Paper.SfDerivedComplete
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import Sheaf.Paper.PbcActualScalarPullback
import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
import Sheaf.Paper.DerivedPullbackTensorHom
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion
import Sheaf.AlgebraicGeometry.CompactificationProjectionExchangeCoherence
import Sheaf.AlgebraicGeometry.PullbackBoundedConstructible
import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
import Sheaf.Paper.CompactSupportExchangeTransport
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange

/-! # Composition of cohomologically smooth morphisms

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-cohsm/lem-pur-co-smooth-composition.md, node lem-pur-co-smooth-composition, order 2337
(blueprint: lem-pur-co-smooth-composition).

## Main statements

- `AlgebraicGeometry.ProEtale.cohomologicallySmooth_comp`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- Composition preserves cohomological smoothness and identifies the relative dualizing object.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-cohsm/lem-pur-co-smooth-composition.md, node lem-pur-co-smooth-composition, order 2337
(blueprint: lem-pur-co-smooth-composition).

Proof:
1. Compose the constructible exceptional adjunctions using compact-support composition and
right-adjoint uniqueness. The counit of the composite is the pasted counit. Separatedness,
local finite type and quasi-compactness are preserved by composition.
2. Apply the tensor clauses of hf and hg and the monoidal pullback comparison to identify
R(gf)^!K with L(gf)^*K tensor W, where W is omega_f tensor Lf^*omega_g. At the unit this
identifies W with omega_(gf). Transpose the resulting map under the composite adjunction:
projection-formula compatibility with composition shows that it is the specified canonical
tensor map, rather than merely an isomorphism between its endpoints.
3. If M_f and M_g are the two-sided inverses, then Lf^*M_g tensor M_f is a two-sided inverse
of W by associativity, symmetry, monoidal pullback and the two inverse identities. All objects
remain bounded constructible of finite Tor amplitude by tensor and pullback preservation.
4. For any separated finite-type map u and invertible input P, tensoring by P is an
equivalence. The compact-support adjunction and projection formula identify the Hom functors
represented by u^*P tensor omega_u and Ru^!P. Yoneda gives their isomorphism; transposing
identifies it with the canonical tensor mate, without assuming u cohomologically smooth.
5. Compact-support exchange commutes with the projection formula: expand both using a
compactification, apply proper exchange/tensor coherence, then compare the open-extension
maps by restriction and its adjunction. Pasting gives the equality for arbitrary base change.
6. Transpose this equality to compare the base-change mate on Ru^!P with the tensor mate
and the dualizing base-change mate. For invertible P the tensor mates of step 4 are
isomorphisms, so invertibility of the dualizing mate implies invertibility on Ru^!P.
7. After arbitrary base change, paste the two dualizing base-change maps of hf and hg,
using step 6 with P = omega_g and the exceptional composition comparison. Transposing and
using vertical pasting for compact-support exchange identifies this composite with the
specified base-change map for gf. It is invertible. This proves all three defining clauses
and the displayed dualizing-object isomorphism.
-/
theorem cohomologicallySmooth_comp (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (hf : IsCohomologicallySmoothCompared P f) (hg : IsCohomologicallySmoothCompared P g) :
    IsCohomologicallySmoothCompared P (f ≫ g) ∧
      Nonempty (@comparedDualizing P X Z (f ≫ g)
          (P.comparedCompactification (f ≫ g) (Z ↘ Spec (.of P.field.k))).hasCompactification ≅
        ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj
            (@comparedDualizing P X Y f
              (P.comparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification)).obj
          ((L((f)^*[ModuleCat.{u + 1} P.Coefficient])).obj
            (@comparedDualizing P Y Z g
              (P.comparedCompactification g (Z ↘ Spec (.of P.field.k))).hasCompactification))) := by
  sorry

end AlgebraicGeometry.ProEtale
