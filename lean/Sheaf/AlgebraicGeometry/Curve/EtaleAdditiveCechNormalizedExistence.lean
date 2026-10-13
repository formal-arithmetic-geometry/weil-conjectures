/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import Sheaf.AlgebraicGeometry.EtaleTensorUnitSectionsNatural
import Sheaf.AlgebraicGeometry.EtaleQcoherentULiftFiniteCechComparison
import Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalData

/-! # Existence of normalized additive étale Čech edges
Source: Stacks Project, Tags 03P2, 01EQ and 01FD. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The additive étale Čech edge equivalence has its augmentation normalization.
This concerns one scheme, with no endomorphism or inverse-image assertion.

Source: Stacks Project, Tag 03P2, separated-case affine-cover proof; Tag 01EQ,
construction of the two augmentations; Tag 01FD, augmented double-complex diagram.
(blueprint: lem-pbc-etale-additive-cech-normalized-existence)

Proof: Use additiveCechOpenInclusion as the Zariski-to-étale functor; forgetting it
is X.restrictFunctor, so it preserves covers and finite intersections. On every
intersection the unit tensor section coordinates identify the additive sheaf
with lifted ordinary structural functions. Affine étale quasi-coherent
acyclicity makes the coefficient augmentation beta a quasi-isomorphism. The
restriction augmentation alpha is a quasi-isomorphism by injective Čech
acyclicity, applied to each resolution term and the finite total diagonals.
Lower the finite products in the coefficient complex and use the identity
scalar restriction for X.toSpecGamma. Hence its homology is the ordinary
cechOver homology. Identify global resolution homology with Sheaf.H through
exists_resolutionSection_canonical_comparison. Define a as the coefficient
augmentation homology inverse after the global augmentation and this normalized
global identification inverse. This is an additive equivalence. For another
resolution, an augmentation-preserving lift of the identity commutes with both
augmentations and with the extMk identification. Cancel its invertible total
homology map. This proves the displayed normalization on every resolution and
every supplied canonical comparison. In degree zero both augmentations restrict
a glued section to the same tuple sections. Empty intersections have zero
sections; an empty covering forces X empty and the two complexes are zero. -/
theorem exists_etaleAdditiveCech_normalized
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hcover : iSup U = ⊤)
    (n : ℕ) :
    ∃ a : Sheaf.H X.etaleAdditiveSheaf n ≃+
      (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homology n,
      IsEtaleAdditiveCechNormalized U n a := by sorry

end AlgebraicGeometry.Scheme.Modules
