/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q76
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.CategoryTheory.Category.Preorder

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Subalgebras and directed colimits of geometrically irreducible algebras

Source: Stacks Project, Tag 037N, assertions (1) and (3),
`algebra.tex`, Lemma `lemma-subalgebra-geometrically-irreducible`
(blueprint: lem-zl-geometric-irreducibility-subalgebra-colimit).

## Main statements

* `AlgebraicGeometry.geometricallyIrreducible_spec_of_injective`: descent along an injective
  algebra homomorphism.
* `AlgebraicGeometry.geometricallyIrreducible_spec_colimit`: preservation under nonempty directed
  colimits of commutative algebras, with arbitrary transition maps.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Geometric irreducibility descends along an injective homomorphism of commutative algebras.
Source: Stacks Project, Tag 037N(1)
(blueprint: lem-zl-geometric-irreducibility-subalgebra-colimit).

Proof: Fix a field extension `K/k`. The affine fibre-product identification
[lem-weil-pbc-fibre-product-affine-spectra] identifies the base change of `Spec T` with
`Spec (T ⊗[k] K)`. The extension `K` is flat over `k`, by
[lem-weil-pbc-field-extension-base-change-faithfully-flat] applied to `D = k`,
[def-weil-pbc-faithfully-flat-ring-map], and the canonical isomorphism `k ⊗[k] K ≃ K`.
Thus [def-weil-pbc-flat-ring-map] makes `u ⊗ 1` injective. It is a unital ring map by
[lem-weil-pbc-algebra-tensor-pushout-universal-property] and generation by pure tensors
[def-weil-pbc-module-tensor-product]. The nilradical of the source is the inverse image of
that of the target, since injectivity detects vanishing of powers. The target nilradical is
proper and prime by [lem-zl-spectrum-irreducible-nilradical-prime]; hence so is its inverse
image. The same criterion makes the source spectrum irreducible. As `K/k` was arbitrary,
[def-pc-geometrically-irreducible] gives the conclusion. -/
theorem geometricallyIrreducible_spec_of_injective
    {k A S : Type u} [Field k] [CommRing A] [CommRing S] [Algebra k A] [Algebra k S]
    (u : A →ₐ[k] S) (hu : Function.Injective u)
    (hS : GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k S)))) :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
  sorry

/-- Nonempty directed colimits of geometrically irreducible commutative algebras are
geometrically irreducible; transition homomorphisms need not be injective.
Source: Stacks Project, Tag 037N(3)
(blueprint: lem-zl-geometric-irreducibility-subalgebra-colimit).

Proof: Fix a field extension `K/k`. Use [lem-weil-pbc-fibre-product-affine-spectra] and
[def-pc-geometrically-irreducible] to reduce to irreducibility of the spectra after tensoring.
The nonempty directed poset is filtered. By
[lem-weil-pbc-filtered-colimit-algebras-elementwise], the algebra colimit is a colimit of rings
and every element has a representative. It is also a colimit of `k`-modules: define the map
from representatives for a compatible family of linear maps; equality of representatives is
detected at a common later stage by [lem-weil-pbc-filtered-colimit-rings-zero], so this map is
well-defined, additive, linear, and unique. By [lem-weil-pbc-tensor-commutes-with-colimits],
tensoring with `K` preserves this module colimit. Its structure maps preserve unit and products
by [lem-weil-pbc-algebra-tensor-pushout-universal-property] and pure-tensor generation
[def-weil-pbc-module-tensor-product]. By [lem-weil-pbc-filtered-colimit-modules-elementwise],
elements of the tensor colimit have representatives and vanishing is detected at a later stage.
Each stage has proper prime nilradical by [lem-zl-spectrum-irreducible-nilradical-prime].
If `1 = 0` in the colimit, this relation holds at a stage, contradicting properness there;
nonemptiness supplies an initial representative of `1`. If `x * y` is nilpotent in the
colimit, represent both at one stage, and detect the vanishing of a power of their product
at a later stage. Primality there makes one of the two representatives nilpotent, so its
image is nilpotent in the colimit. The colimit nilradical is therefore proper and prime.
The nilradical criterion makes its spectrum irreducible. This works for every `K/k`, proving
geometric irreducibility. No finite generation, reducedness, or transition injectivity is used. -/
theorem geometricallyIrreducible_spec_colimit
    {k : Type u} [Field k] {I : Type u} [PartialOrder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (F : I ⥤ CommAlgCat.{u} k)
    (hF : ∀ i : I,
      GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k (F.obj i))))) :
    GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap k (colimit F : CommAlgCat.{u} k)))) := by
  sorry

end AlgebraicGeometry
