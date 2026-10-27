/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine

/-! # Affineness of homomorphisms with finite geometric kernels over a Dedekind base

Source: Conrad, Reductive Group Schemes, proof of Proposition 6.3.16, printed p.229.
(blueprint: lem-sfb-dedekind-finite-kernel-hom-affine)

The geometric kernel is expressed as the base change of the scheme-theoretic kernel.
Both operations are actual fibre products, so this is the kernel of the base-changed
homomorphism. In particular, finiteness here concerns the scheme, including nilpotents.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite-type homomorphism of separated flat finite-type group schemes over the
spectrum of a Noetherian integrally closed one-dimensional domain is affine if all
its geometric kernels are finite.

Source: Conrad, Reductive Group Schemes, proof of Proposition 6.3.16, printed p.229.
(blueprint: lem-sfb-dedekind-finite-kernel-hom-affine)

Proof plan:
1. For a nonempty fibre over y in J, choose a point x and an algebraic closure L of
   its residue field (def-weil-algebraic-closure). Translation by the resulting
   L-point g identifies the fibre after extension to L with ker(f_L): the maps are
   a ↦ g*a and z ↦ g⁻¹*z. The group diagrams show these are inverse morphisms.
2. The hypothesis makes this kernel finite. By
   lem-weil-pbc-finite-closed-map-finite-fibres it has finitely many points.
   The field-extension spectrum map is surjective (lem-pc-field-extension-surjective),
   as is its base change (lem-weil-pbc-surjective-base-change); thus the original
   fibre is finite. Empty fibres are finite too. Finite type and
   pqf-lem-qf-finitefibres now give quasi-finiteness of f.
3. Separated cancellation (lem-weil-pbc-separated-cancellation) makes f separated.
   Apply pqf-lem-qf-locqf-qc and
   lemma-nagata-quasi-affine-morphism-of-quasi-finite to make f quasi-affine.
4. Apply lem-sfb-relative-quasiaffine-group-envelope. The canonical relative
   spectrum H over J factors f as q ∘ j, with j a quasi-compact open group immersion
   and q affine. Retain its generic-fibre structure-sheaf comparison.
5. Base change preserves open immersions (lem-weil-pbc-open-immersion-base-change).
   By lem-sfb-field-open-group-image-closed, the image of each j_s is closed.
   Over the fraction field the comparison from step 4 forces the complementary
   open to be empty: otherwise a nonzero local ring would be zero. Hence j is
   surjective on the generic fibre.
6. Apply lem-sfb-dedekind-vertical-clopen-open-affine to the image open of j in H.
   It makes j affine, without requiring H finite type. Composition with the affine
   q is affine by lem-weil-pbc-affine-composition. -/
theorem isAffineHom_of_finite_geometricKernel_over_dedekind
    (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (hB : ringKrullDim B = 1)
    (G J : Over (Spec (.of B))) [GrpObj G] [GrpObj J]
    [IsSeparated G.hom] [Flat G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [IsSeparated J.hom] [Flat J.hom] [LocallyOfFiniteType J.hom] [QuasiCompact J.hom]
    (f : G ⟶ J) [IsMonHom f] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (hker : ∀ (k : Type u) [Field k] [IsAlgClosed k] (φ : B →+* k),
      IsFinite ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj (GrpObj.ker f)).hom) :
    IsAffineHom f.left := by
  sorry

end AlgebraicGeometry
