/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Sheaf.Topology.ContinuousMapCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization

import Sheaf.AlgebraicGeometry.WeaklyEtaleStability
import Sheaf.RingTheory.IndEtaleUniverseTransport
import WeilConjectures.RingTheory.ProEtale.WeakDimension
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Spectral.Basic

/-!
# Generic restriction of continuous coefficient sections

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 7.4.10 and
Theorem 2.3.4, with the agent extension argument recorded in the DAG; Hemo--Richarz--Scholbach,
Example 3.1 (blueprint: lem-sfb-normal-generic-continuous-sections).

The canonical realization `condensedFieldContinuousMapIso` identifies the pulled-back
continuous condensed coefficients with the continuous-function sheaf. We state restriction
in these coordinates. The map `X.fromSpecStalk (genericPoint X)` has source
`Spec X.functionField`, so every pullback below is the actual generic fibre.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ProEtale

/-- On an affine pro-etale object over a normal integral locally Noetherian scheme,
restriction to the generic fibre is a bijective ring homomorphism, natural in the object
and in continuous homomorphisms of nonarchimedean normed coefficient fields.
Source: Bhatt--Scholze, Lemma 7.4.10 and Theorem 2.3.4, agent extension argument;
Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-normal-generic-continuous-sections).

Proof: (1) Cover the object by affine charts over nonempty affine opens of X. Their
coordinate rings are normal domains, by stalk localization and the local criterion for
integral closedness; the chart maps are weakly etale by `weaklyEtale_stability`.
(2) Flatness makes the map from each chart ring B into B tensor k injective.
`Algebra.WeaklyEtale.isIntegrallyClosedIn_tensorProduct` puts every generic idempotent
uniquely in B. The clopen-idempotent correspondence gives bijection on clopens.
(3) Uniqueness on a chart basis glues these clopen extensions across overlaps; this
requires no affine-intersection or quasi-separatedness assumption on X.
(4) The generic inclusion is affine, hence its base change between the affine object
and its generic fibre is between spectral spaces. The clopen bijection induces a
homeomorphism of their connected-component spaces, by
`lem-sfb-spectral-clopen-component-homeomorphism`.
(5) Ultrametric balls separate points of A by clopens. Thus A is totally disconnected,
and continuous functions on either scheme factor uniquely and continuously through
its connected-component quotient.
(6) Extend a generic function by its component factor, the inverse component
homeomorphism, and the component quotient. This is inverse to restriction. Pointwise
operations make restriction a ring homomorphism. Empty objects give singleton rings.
(7) The pullback projection equations give naturality under every morphism of affine
pro-etale objects. Associativity of composition gives coefficient naturality; bijectivity
also gives both naturalities for the inverse extensions.
(8) `condensedFieldContinuousMapIso` identifies these functions with the coefficients
pulled back from `C(-, A)`. No completeness or local compactness is used. -/
theorem normal_generic_continuous_sections (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X]
    (hnormal : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (A : Type v) [NormedField A] [IsUltrametricDist A] :
    (∀ (U : X.ProEt), IsAffine U.left →
      Function.Bijective
        (ContinuousMap.compRightAlgHom ℤ A
          (pullback.fst U.hom (X.fromSpecStalk (genericPoint X))).base.hom).toRingHom) ∧
    (∀ (U V : X.ProEt), IsAffine U.left → IsAffine V.left →
      ∀ (f : V ⟶ U) (g : C(U.left, A)),
        (g.comp f.left.base.hom).comp
            (pullback.fst V.hom (X.fromSpecStalk (genericPoint X))).base.hom =
          (g.comp (pullback.fst U.hom (X.fromSpecStalk (genericPoint X))).base.hom).comp
            (((Over.pullback (X.fromSpecStalk (genericPoint X))).map
              ((Scheme.ProEt.forget X).map f)).left.base.hom)) ∧
    (∀ (A' : Type w) [NormedField A'] [IsUltrametricDist A']
      (a : A →+* A') (ha : Continuous a) (U : X.ProEt), IsAffine U.left →
      ∀ g : C(U.left, A),
        (a.compLeftContinuous U.left ha g).comp
            (pullback.fst U.hom (X.fromSpecStalk (genericPoint X))).base.hom =
          a.compLeftContinuous
            ↥(pullback (C := Scheme.{u}) U.hom (X.fromSpecStalk (genericPoint X))) ha
              (g.comp (pullback.fst U.hom (X.fromSpecStalk (genericPoint X))).base.hom)) := by
  sorry

end AlgebraicGeometry.ProEtale
