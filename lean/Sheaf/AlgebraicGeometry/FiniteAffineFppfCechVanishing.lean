/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Mathlib.LinearAlgebra.TensorProduct.Pi
import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.RingTheory.FaithfullyFlat.Amitsur

/-! # Finite affine fppf coverings have vanishing quasi-coherent Cech cohomology

Source: Stacks Project, Descent, Tags 03FI and 03FJ,
lemma-standard-covering-Cech and lemma-standard-covering-Cech-quasi-coherent, fppf case
(blueprint: lem-sfb-finite-affine-fppf-cech-vanishing).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Positive Cech cohomology vanishes for an arbitrary quasi-coherent module and a
finite affine fppf covering of an affine object of the big fppf site.
The associated sheaf uses the witness of the existing section-normalized equivalence:
its section and restriction comparisons identify it with tensor-pullback sections.
The fibre-product data `D` may be any choice satisfying the universal properties.

Source: Stacks Project, Descent, Tags 03FI and 03FJ
(blueprint: lem-sfb-finite-affine-fppf-cech-vanishing).

Proof:
1. Put G = u*F on the affine scheme V and M = Gamma(V,G). Pullback preserves
   quasi-coherence (lem-weil-pbc-module-pullback-quasi-coherent). The base-restriction
   comparison of lem-sfb-scheme-big-fppf-quasicoherent-equivalence identifies the
   associated sheaf restricted over V with the sheaf of tensor-pullback sections of G.
2. Set A = Gamma(V,O), A_i = Gamma(V_i,O), and B = product_i A_i. The affine flatness
   criterion (lem-weil-pbc-flat-morphism-affine-criterion) and
   lem-weil-pbc-finite-product-flat-modules give flatness of B over A.
   By lem-weil-pbc-finite-affine-coproduct-spectrum, Spec B is the coproduct of the V_i;
   joint surjectivity therefore makes its map to Spec A surjective. Apply
   lem-weil-pbc-flat-surjective-spectrum-faithfully-flat to obtain faithful flatness.
3. Iterating lem-weil-pbc-fibre-product-affine-spectra identifies each tuple product
   with Spec of the corresponding tensor product of the A_i. Omitting a factor
   corresponds to inserting 1 in that factor, by the projection formulas and the
   tensor universal property. By lem-weil-pbc-module-pullback-affine-sections its
   sections identify with M tensor that coordinate algebra, sending m tensor d to
   d times the pulled-back section m. No intersections of affine opens in S occur.
4. Iterating lem-weil-pbc-tensor-finite-product, with associativity and symmetry,
   gives a degreewise isomorphism from M tensor B tensor ... tensor B to the Cech
   cochains of def-weil-pbc-site-cech-complex. On pure tensors its tuple component
   uses the corresponding coordinates in the B factors and the section map in step 3.
5. Check each coface on these pure tensors. Section pullback and the normalized
   composite-pullback comparison (def-pc-module-pullback and
   lem-pc-module-pullback-identity-composition) turn the omitted-factor projection
   into insertion of 1. The coordinate of 1_B is 1 in each A_i. Thus the degreewise
   maps commute with every coface and hence with their alternating sums; pure tensors
   generate. This is an isomorphism of the Cech and Amitsur complexes.
6. Apply lem-pc-cech-exact to A, B, and the arbitrary module M. The isomorphism
   carries kernels and images onto those of the Cech differential, so its positive
   cohomology is zero. If I is empty, the cover forces V empty and all cochain groups
   are empty products, hence zero. Empty members have coordinate ring zero and do
   not affect any finite-product or tensor identification. No finiteness or flatness
   of M, nor separation or Noetherian condition on S, is used.
-/
theorem finite_affine_fppf_cech_vanishing (S : Scheme.{u}) (F : SfbZariskiQCoh S)
    (V : Over S) [IsAffine V.left] {I : Type w} [Finite I]
    (Vᵢ : I → Over S) [∀ i : I, IsAffine (Vᵢ i).left] (g : ∀ i : I, Vᵢ i ⟶ V)
    (hcover : Presieve.ofArrows (fun i : I ↦ (Vᵢ i).left) (fun i : I ↦ (g i).left) ∈
      fppfPrecoverage V.left)
    (D : SiteCechComplex Vᵢ g) (p : ℕ) (hp : 0 < p) :
    IsZero ((D.cohomologyFunctor p).obj
      (((sfbAssociated S
        ((Classical.choose scheme_big_fppf_quasicoherent_equivalence) S)).obj F).val.presheaf))
      := by
  sorry

end AlgebraicGeometry.Scheme
