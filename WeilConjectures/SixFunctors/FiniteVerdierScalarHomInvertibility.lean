/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientVerdierData
public import WeilConjectures.SixFunctors.FiniteVerdierFixedScalarTensor

/-! # Invertibility of the normalized fixed-module Hom comparison on both sites -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures


/-- Native internal Hom commutes with a finite coefficient quotient on the fixed
module-sheaf finite-Tor constructible domains on both sites, for the normalized tensorator.

Source: blueprint thm-coef-finite-hom.proof.md and
cor-coef-finite-verdier.proof.md, finite coefficient Hom comparison on both sites;
Stacks 0A5W and 07A4.
(blueprint: lem-coef-verdier-scalar-hom-invertibility).

Proof: the canonical exact realization of fixed module sheaves as modules over the
constant coefficient sheaf preserves the ordinary tensor, its Koszul totalization,
and its tensor-Hom adjunction. Its scalar comparison is the mate of the identity
restriction square. The normalized representative equation identifies the transported
scalar tensorator with the one in the hypothesis: choose flat-term K-flat models,
use the ordinary balanced tensor square, cancel the representative isomorphisms,
and use naturality for arbitrary derived inputs. Uniqueness of the adjoint transpose
then identifies the native ihom comparison with the canonical intrinsic finite-Hom
comparison. The finite-Tor constructibility predicates are defined using this exact
realization. Apply finiteCoefficient_derivedHom_change to the realized K and M and
reflect invertibility through the realization equivalence. No Verdier pairing,
target-family compatibility, evaluation square, or coefficient cocycle is required. -/
theorem finiteVerdier_scalar_hom_isIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    {n m : ℕ} (h : m ≤ n)
    :
    letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    (∀ (K M : (finiteTorConstructibleEtale.{u}
        l E (n + 1) (by omega) X).FullSubcategory),
      letI := (finiteVerdier_fixedScalar_tensor.{u} X.smallEtaleTopology
        (finiteDualizingQuotient l E h)).choose.toMonoidal
      IsIso ((Functor.LaxMonoidal.ihomComparison
        (pbcFixedScalarExtension.{u} X.smallEtaleTopology (finiteDualizingQuotient l E h))
          K.obj).natTrans.app M.obj)) ∧
    (∀ (K M : (finiteTorConstructibleProEtaleModule.{u}
        l E (n + 1) (by omega) X).FullSubcategory),
      letI := (finiteVerdier_fixedScalar_tensor.{u} (Scheme.ProEt.topology X)
        (finiteDualizingQuotient l E h)).choose.toMonoidal
      IsIso ((Functor.LaxMonoidal.ihomComparison
        (pbcFixedScalarExtension.{u} (Scheme.ProEt.topology X) (finiteDualizingQuotient l E h))
          K.obj).natTrans.app M.obj)) := by
  sorry

end WeilConjectures
