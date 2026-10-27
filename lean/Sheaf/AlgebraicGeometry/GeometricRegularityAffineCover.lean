/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.RingTheory.GRing
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Data.List.TFAE
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange
import WeilConjectures.RingTheory.GeometricallyRegularFieldExtension
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Geometric regularity on affine open covers

Source: Stacks Project, Varieties, Tag 038V, `lemma-geometrically-regular`, conditions
(2)--(5), using the intermediate test by all finite extensions
(blueprint: lem-per-geometric-regularity-affine-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Regularity after every finite field extension is equivalent to geometric regularity
of every affine section algebra, and to that condition on an affine open covering.
The algebra on sections is the composite of the inverse of `Scheme.ΓSpecIso`, pullback
of global sections along `f`, and restriction to the affine open. A covering is a set
of affine opens whose supremum is top; this includes the empty covering.
Source: Stacks Project, Varieties, Tag 038V, `lemma-geometrically-regular`
(blueprint: lem-per-geometric-regularity-affine-cover).

Proof plan from the node:
1. For an affine open W with section algebra A, the canonical chart and its structural
   square identify its base change with Spec(A tensor_k K). Use
   lem-weil-pbc-affine-open-spec-points, lem-weil-pbc-affine-opens-induced-ring-map-spec-square,
   and lem-sbc-finite-affine-tensor-base-change with one summand. The pullback universal
   property (def-pc-fibre-product) and lem-weil-pbc-open-preimage-fibre-product identify
   this chart with the inverse image of W. Such inverse images cover the base change.
2. By def-weil-regular-scheme and pqf-def-locnoeth, regularity restricts to opens: stalks
   agree. By pqf-lem-affine-open-locnoeth and lem-weil-pbc-affine-open-stalk-localization,
   an affine open in a regular scheme has a Noetherian regular section ring. Conversely,
   a covering by spectra of Noetherian regular rings gives regularity at every point.
   Scheme and ring isomorphisms preserve these conditions.
3. Condition (1) applies to every finite purely inseparable extension. The chart in
   step 1 is therefore regular, and step 2 makes its section ring regular. Tensor
   symmetry exchanges A tensor_k K with K tensor_k A, using
   lem-weil-pbc-algebra-tensor-pushout-universal-property. Together with Noetherianity
   of A, this is def-weil-pbc-g-ring and proves (2).
4. Apply lem-weil-pbc-affine-opens-basis to cover the scheme by affine opens. Condition
   (2) makes each section algebra geometrically regular, proving (3).
5. A finite field extension is finitely generated as a field. Apply
   lem-weil-pbc-geometrically-regular-finitely-generated-extensions to every section
   algebra in (3). Tensor symmetry and step 1 give an affine cover of the base change
   by regular rings, and step 2 proves (1).
6. For the empty scheme the empty affine covering remains empty after base change.
   Regularity is vacuous; its zero section ring is Noetherian and remains zero under
   tensor products, so geometric regularity holds as well. No nonemptiness, finite
   covering, nonzero section ring, or separatedness is assumed. -/
theorem geometricRegularity_affineCover_tfae
    (k : Type u) [Field k] (Z : Scheme.{u}) [IsLocallyNoetherian Z]
    (f : Z ⟶ Spec (CommRingCat.of k)) :
    List.TFAE [
      ∀ (K : Type u) [Field K] [Algebra k K] [Module.Finite k K],
        IsRegularScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
      ∀ W : Z.affineOpens,
        @Algebra.IsGeometricallyRegular k Γ(Z, W.1) _ _
          (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫
            Z.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op).hom.toAlgebra),
      ∃ S : Set Z.affineOpens,
        (⨆ W ∈ S, W.1) = ⊤ ∧
          ∀ W ∈ S, @Algebra.IsGeometricallyRegular k Γ(Z, W.1) _ _
            (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫
              Z.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op).hom.toAlgebra)
    ] := by
  sorry

end AlgebraicGeometry
