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
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
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

private lemma geometric_spec_iff_tensor
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A] :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k A))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IrreducibleSpace (PrimeSpectrum (TensorProduct k A K)) := by
  rw [GeometricallyIrreducible.eq_geometrically,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  apply forall_congr'
  intro K
  apply forall_congr'
  intro _
  apply forall_congr'
  intro _
  exact (pullbackSpecIso k A K).hom.homeomorph.irreducibleSpace_iff

private def algebraModules (k : Type u) [CommRing k] :
    CommAlgCat.{u} k ⥤ ModuleCat.{u} k where
  obj A := ModuleCat.of k A
  map f := ModuleCat.ofHom f.hom.toLinearMap

private theorem algebraModules_preservesColimit
    {k : Type u} [CommRing k] {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{u} k) : PreservesColimit F (algebraModules k) := by
  have : IsConnected I := IsFiltered.isConnected I
  let U := algebraModules k
  let V := forget₂ (CommAlgCat.{u} k) CommRingCat.{u}
  have : PreservesColimit F V :=
    inferInstanceAs (PreservesColimit F
      ((commAlgCatEquivUnder (CommRingCat.of k)).functor ⋙ Under.forget _))
  have : PreservesColimit F (forget (CommAlgCat.{u} k)) :=
    inferInstanceAs (PreservesColimit F (V ⋙ forget CommRingCat.{u}))
  have : PreservesColimit F (U ⋙ forget (ModuleCat.{u} k)) :=
    inferInstanceAs (PreservesColimit F (forget (CommAlgCat.{u} k)))
  have : PreservesColimit F U :=
    preservesColimit_of_reflects_of_preserves U (forget (ModuleCat.{u} k))
  exact inferInstanceAs (PreservesColimit F U)

private def tensorAlgebras (k K : Type u) [CommRing k] [CommRing K] [Algebra k K] :
    CommAlgCat.{u} k ⥤ CommAlgCat.{u} k where
  obj A := CommAlgCat.of k (TensorProduct k A K)
  map f := CommAlgCat.ofHom (Algebra.TensorProduct.map f.hom (AlgHom.id k K))
  map_id A := by
    apply CommAlgCat.hom_ext
    exact Algebra.TensorProduct.map_id
  map_comp f g := by
    apply CommAlgCat.hom_ext
    exact Algebra.TensorProduct.map_comp g.hom f.hom (AlgHom.id k K) (AlgHom.id k K)

private lemma nilradical_prime_of_filtered
    {k : Type u} [CommRing k] {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{u} k) (c : Cocone F)
    (hc : IsColimit ((algebraModules k).mapCocone c))
    (hF : ∀ i, (nilradical (F.obj i)).IsPrime) :
    (nilradical c.pt).IsPrime := by
  have hrep (x : c.pt) : ∃ (i : I) (a : F.obj i), c.ι.app i a = x :=
    by simpa [algebraModules] using
      Concrete.isColimit_exists_rep (F ⋙ algebraModules k) hc x
  have hz (i : I) (a : F.obj i) (ha : c.ι.app i a = 0) :
      ∃ (j : I) (f : i ⟶ j), F.map f a = 0 := by
    have he : ((algebraModules k).mapCocone c).ι.app i a =
        ((algebraModules k).mapCocone c).ι.app i 0 := by
      change c.ι.app i a = c.ι.app i 0
      simpa only [map_zero] using ha
    obtain ⟨j, f, g, h⟩ :=
      (Concrete.isColimit_rep_eq_iff_exists (F ⋙ algebraModules k) hc a 0).mp he
    exact ⟨j, f, by simpa [algebraModules] using h⟩
  have hw {i j : I} (f : i ⟶ j) (a : F.obj i) :
      c.ι.app j (F.map f a) = c.ι.app i a :=
    ConcreteCategory.congr_hom (c.w f) a
  refine ⟨?_, ?_⟩
  · intro ht
    have hone : IsNilpotent (1 : c.pt) := by
      rw [← mem_nilradical, ht]
      trivial
    obtain ⟨n, hn⟩ := hone
    have he : (1 : c.pt) = 0 := by simpa using hn
    let i : I := Classical.choice IsFiltered.nonempty
    obtain ⟨j, f, hf⟩ := hz i 1 (by
      change (c.ι.app i).hom 1 = 0
      simpa only [map_one] using he)
    exact (hF j).one_notMem (by
      rw [mem_nilradical]
      exact ⟨1, by simpa using hf⟩)
  · intro x y hxy
    obtain ⟨i, a, rfl⟩ := hrep x
    obtain ⟨j, b, rfl⟩ := hrep y
    let l := IsFiltered.max i j
    let f := IsFiltered.leftToMax i j
    let g := IsFiltered.rightToMax i j
    let a' := F.map f a
    let b' := F.map g b
    have ha : c.ι.app l a' = c.ι.app i a := hw f a
    have hb : c.ι.app l b' = c.ι.app j b := hw g b
    obtain ⟨n, hn⟩ := (mem_nilradical.mp hxy)
    have hz' : c.ι.app l ((a' * b') ^ n) = 0 := by
      simpa only [map_pow, map_mul, ha, hb] using hn
    obtain ⟨m, t, ht⟩ := hz l ((a' * b') ^ n) hz'
    have hm : F.map t a' * F.map t b' ∈ nilradical (F.obj m) := by
      rw [mem_nilradical]
      exact ⟨n, by simpa only [map_pow, map_mul] using ht⟩
    rcases (hF m).mem_or_mem hm with hm | hm
    · left
      rw [mem_nilradical]
      have hh := (mem_nilradical.mp hm).map (c.ι.app m).hom.toRingHom
      change IsNilpotent (c.ι.app m (F.map t a')) at hh
      rw [hw t a', ha] at hh
      exact hh
    · right
      rw [mem_nilradical]
      have hh := (mem_nilradical.mp hm).map (c.ι.app m).hom.toRingHom
      change IsNilpotent (c.ι.app m (F.map t b')) at hh
      rw [hw t b', hb] at hh
      exact hh

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
  apply geometric_spec_iff_tensor.mpr
  intro K _ _
  have hS' := (geometric_spec_iff_tensor.mp hS) K
  let v := Algebra.TensorProduct.map u (AlgHom.id k K)
  have hv : Function.Injective v :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := K) u.toLinearMap hu
  have hn : Ideal.comap v.toRingHom (nilradical (TensorProduct k S K)) =
      nilradical (TensorProduct k A K) := by
    change Ideal.comap v.toRingHom (⊥ : Ideal _).radical = (⊥ : Ideal _).radical
    rw [Ideal.comap_radical, Ideal.comap_bot_of_injective v.toRingHom hv]
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hS' ⊢
  rw [← hn]
  let := hS'
  exact Ideal.comap_isPrime v.toRingHom _

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
  apply geometric_spec_iff_tensor.mpr
  intro K _ _
  let U := algebraModules k
  have : PreservesColimit F U := algebraModules_preservesColimit F
  let T := tensorAlgebras k K
  let c := T.mapCocone (colimit.cocone F)
  have hc : IsColimit ((algebraModules k).mapCocone c) :=
    isColimitOfPreserves (MonoidalCategory.tensorRight (ModuleCat.of k K))
      (isColimitOfPreserves U (colimit.isColimit F))
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
  exact nilradical_prime_of_filtered (F ⋙ T) c hc fun i ↦
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp
      ((geometric_spec_iff_tensor.mp (hF i)) K)

end AlgebraicGeometry
