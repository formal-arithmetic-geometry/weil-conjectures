/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Sheaf.RingTheory.IndEtaleUniverseTransport

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.StructureSheaf
import Sheaf.AlgebraicGeometry.EtaleComparison
import WeilConjectures.RingTheory.ProEtale.WeakDimension
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Flat.Basic

/-! # Normal generic affine charts and their clopens

Source: Stacks Project, Tags 092W and 00EE, with the affine-chart deduction in
lem-sfb-normal-generic-chart-clopens (blueprint: lem-sfb-normal-generic-chart-clopens).

The function field, germ map, generic inclusion, chart ring map and generic fibre are
Mathlib's canonical constructions. `IsFractionRing` and `IsLocalization` express the
canonical fraction-field and localization identifications by their universal properties.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct nonZeroDivisors

namespace AlgebraicGeometry.ProEtale

/-- Affine charts over nonempty affine base opens form a basis. Their base rings are
normal domains, their germ maps give the function field, and their weakly etale chart
maps have injective generic localization, bijective idempotents and bijective clopen
inverse image. The tensor-spectrum isomorphism is characterized by both projections.

Source: Stacks Project, Tags 01IT, 01RV, 030B, 094S, 01I4, 092W and 00EE
(blueprint: lem-sfb-normal-generic-chart-clopens).

Proof:
1. Given a point in an open of U, choose an affine neighbourhood of its image in X,
   then an affine neighbourhood inside the original open intersected with its preimage
   (`lem-weil-pbc-affine-opens-basis`). The base neighbourhood is nonempty.
2. The integral function-field lemma gives a domain R and makes the germ map a fraction
   field map (`lem-sc-integral-function-field-affine-fraction`). Affine stalk localization
   (`lem-weil-pbc-spec-domain-stalks-function-field`) identifies maximal localizations with
   the normal stalks. Apply `lem-weil-pbc-normal-domain-of-local-normal`.
3. A pro-etale object is weakly etale. Clause 4 of
   `det-pe-morphisms-etale-comparison` gives weak etaleness for the actual appLE chart map.
4. The generic point lies in every nonempty affine base open. The open inclusion is mono,
   so the fibre product over X equals the one over that open. Apply
   `lem-weil-pbc-fibre-product-affine-spectra` to obtain the tensor spectrum and its two
   projection equations. Tensoring with the fraction field is localization: send
   b tensor (a/s) to ab/s and b/s to b tensor (1/s); the universal properties make these
   inverse. The B-algebra structure is b mapped to b tensor 1.
5. The injection R into its fraction field stays injective after tensoring with the flat
   R-module B (`lem-trf-flat-tensor-preserves-injection`). Identify B tensor R with B.
6. `lem-weil-pbc-weak-etale-integral-closure` says B is integrally closed in B tensor k.
   An idempotent there satisfies the monic polynomial T squared minus T, so lies in B.
   Injectivity proves its lift is idempotent and unique; ring maps preserve idempotents.
7. `lem-weil-pbc-spec-clopen-idempotent` identifies clopens with idempotents. Prime
   contraction sends the basic open of e to the basic open of e tensor 1 under inverse
   image, giving exactly the stated clopen map. For an empty chart B and its localization
   are zero rings and both idempotent and clopen sets are singletons. Empty U makes the
   basis assertion vacuous; no nonemptiness of U or W is used. -/
theorem normal_generic_chart_clopens (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X]
    (hnormal : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.ProEt) :
    Opens.IsBasis {W : U.left.Opens | IsAffineOpen W ∧
      ∃ V : X.Opens, IsAffineOpen V ∧ Nonempty V ∧ W ≤ U.hom ⁻¹ᵁ V} ∧
    (∀ (V : X.Opens) (_hV : IsAffineOpen V) [Nonempty V]
      (W : U.left.Opens) (hW : IsAffineOpen W) (hWV : W ≤ U.hom ⁻¹ᵁ V),
      IsDomain Γ(X, V) ∧ IsIntegrallyClosed Γ(X, V) ∧
      IsFractionRing Γ(X, V) X.functionField ∧
      (fun (_a : Algebra Γ(X, V) Γ(U.left, W)) ↦
        Algebra.WeaklyEtale Γ(X, V) Γ(U.left, W) ∧
        IsLocalization ((nonZeroDivisors Γ(X, V)).map
          (algebraMap Γ(X, V) Γ(U.left, W)))
          (Γ(U.left, W) ⊗[Γ(X, V)] X.functionField) ∧
        (∃ e : pullback (W.ι ≫ U.hom) (X.fromSpecStalk (genericPoint X)) ≅
            Spec (CommRingCat.of (Γ(U.left, W) ⊗[Γ(X, V)] X.functionField)),
          e.inv ≫ pullback.fst _ _ =
            Spec.map (CommRingCat.ofHom
              (algebraMap Γ(U.left, W) (Γ(U.left, W) ⊗[Γ(X, V)] X.functionField))) ≫
                hW.isoSpec.inv ∧
          e.inv ≫ pullback.snd _ _ =
            Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeRight : X.functionField →ₐ[Γ(X, V)]
                Γ(U.left, W) ⊗[Γ(X, V)] X.functionField).toRingHom)) ∧
        Function.Injective
          (algebraMap Γ(U.left, W) (Γ(U.left, W) ⊗[Γ(X, V)] X.functionField)) ∧
        Set.BijOn
          (algebraMap Γ(U.left, W) (Γ(U.left, W) ⊗[Γ(X, V)] X.functionField))
          {e | IsIdempotentElem e} {e | IsIdempotentElem e})
        (U.hom.appLE V W hWV).hom.toAlgebra ∧
      Function.Bijective
        (fun C : Clopens W.toScheme ↦
          (⟨(pullback.fst (W.ι ≫ U.hom) (X.fromSpecStalk (genericPoint X))) ⁻¹' (C : Set _),
            C.isClopen.preimage
              (pullback.fst (W.ι ≫ U.hom)
                (X.fromSpecStalk (genericPoint X))).continuous⟩ :
            Clopens ↥(pullback (C := Scheme.{u}) (W.ι ≫ U.hom)
              (X.fromSpecStalk (genericPoint X)))))) := by
  sorry

end AlgebraicGeometry.ProEtale
