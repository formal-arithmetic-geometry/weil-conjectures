/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatQuotientTensorSES
import Sheaf.Paper.EtaleKFlatCriteria
import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-! # Flat lower truncation and its K-flat kernel

Source: Stacks Project, Cohomology on Sites, Tag 0F1M
(lemma-bounded-below-tor-amplitude), lower truncation and kernel paragraphs
(blueprint: lem-kun-lower-truncation-flat-model).

The constant ring sheaf is the sheafification of the constant ring presheaf.
`K.truncGE a` and `K.πTruncGE a` are the existing good truncation and quotient map.
Its boundary object `K.opcycles a` is the cokernel of `K.d (a - 1) a`.
`kernel (K.πTruncGE a)` is the kernel in the category of complexes, whose
limits are computed degreewise. The boundary identification below commutes with
its inclusion into `K.X a`. Together with the chain-map equation for the kernel
inclusion, this identifies the boundary differential with the image factorization.
The lower-degree inclusions are isomorphisms, and the terms above `a` are zero.

The site has object universe `u + 1` and morphism universe `u`, and is small in
coefficient universe `u + 1`; its small model gives the skeleton convention.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Good lower truncation of a flat complex at a flat cokernel has flat terms,
is quasi-isomorphic to the original complex, and has a bounded-above flat K-flat
kernel, with the indicated terms and a degreewise short exact sequence.
Source: Stacks Project, Tag 0F1M, lower truncation and kernel paragraphs
(blueprint: lem-kun-lower-truncation-flat-model).

Proof:
1. The cokernel universal property induces the differential out of `K.opcycles a`.
The relations `d ≫ d = 0` give the quotient chain map: zero below `a`, the
cokernel projection at `a`, and the identity above `a`, under the standard
truncation identifications (def-kun-truncations, def-pc-cochain-complex-modules).
2. Below `a`, the original homology vanishes by hypothesis. At `a`, the kernel
of the induced differential is the original cycles modulo the original boundaries.
At `a + 1`, the boundaries agree since the cokernel projection is epic; above
that degree, adjacent terms and differentials are unchanged. Thus the quotient
is a quasi-isomorphism (def-pc-acyclic-complex-modules, def-pc-quasi-iso-modules).
3. Take the kernel degreewise: it is `K.X i` below `a`, the image of the incoming
differential at `a`, and zero above. The kernel inclusion is a chain map and
its boundary inclusion is the image monomorphism, so the incoming differential
is the image factorization. Every component of the quotient is epic. This
gives the short exact sequences in all degrees (def-pc-cochain-complex-modules).
4. Apply lem-weil-pbc-site-flat-quotient-tensor-ses to the sequence from the image
to `K.X a` to `K.opcycles a`. The middle and quotient are flat, so the image is
flat. The displayed terms of the truncation and kernel are therefore all flat;
zero sheaves are flat (def-pc-flat-sheaf-modules).
5. The kernel vanishes above `a`. Apply lem-kun-kflat-criteria (1) to its flat
terms. Signed tensor symmetry identifies that criterion's convention with
IsKFlatIndependentCoefficients (def-kun-derived-tensor, def-pc-kflat-complex). -/
theorem etale_lower_truncation_flat_model
    (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (K : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)))) ℤ)
    (a : ℤ)
    (hflat : ∀ i : ℤ,
      SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (K.X i))
    (hvanish : ∀ i : ℤ, i < a → IsZero (K.homology i))
    (hquotient : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (K.opcycles a)) :
    QuasiIso (K.πTruncGE a) ∧
    (∀ i : ℤ,
      SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} ((K.truncGE a).X i)) ∧
    (∀ i : ℤ, i < a → IsIso ((kernel.ι (K.πTruncGE a)).f i)) ∧
    (∃ e : (kernel (K.πTruncGE a)).X a ≅ image (K.d (a - 1) a),
      e.hom ≫ image.ι (K.d (a - 1) a) = (kernel.ι (K.πTruncGE a)).f a ∧
      (kernel (K.πTruncGE a)).d (a - 1) a ≫ e.hom =
        (kernel.ι (K.πTruncGE a)).f (a - 1) ≫ factorThruImage (K.d (a - 1) a)) ∧
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (image (K.d (a - 1) a)) ∧
    (∀ i : ℤ, a < i → IsZero ((kernel (K.πTruncGE a)).X i)) ∧
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      ((kernel (K.πTruncGE a)).X i)) ∧
    CochainComplex.IsKFlatIndependentCoefficients (kernel (K.πTruncGE a)) ∧
    (∀ i : ℤ, ((ShortComplex.kernelSequence (K.πTruncGE a)).map
      (HomologicalComplex.eval _ (ComplexShape.up ℤ) i)).ShortExact) := by
  sorry

end AlgebraicGeometry.Scheme
