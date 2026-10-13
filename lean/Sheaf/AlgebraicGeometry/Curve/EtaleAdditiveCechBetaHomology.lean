/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import Sheaf.AlgebraicGeometry.EtaleTensorUnitSectionsNatural
import Sheaf.AlgebraicGeometry.EtaleQcoherentULiftFiniteCechComparison
import Sheaf.Algebra.Homology.FirstQuadrantAugmentation

/-! # Descent of the coefficient augmentation to homology
Source: Stacks Project, Tags 03P2 and 01FD. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- Beta lifts cycles additively and descends to a bijective additive homology map.
Source: Stacks Project, Tag 03P2, Theorem 59.22.4, separated-case proof,
and Tag 01FD, Lemma 20.15.1, the coefficient augmentation.
(blueprint: lem-pbc-etale-additive-cech-beta-homology)

Proof: Forget module scalars in the ordinary unit Čech complex and apply ULift.
The structural-function coordinates restrictFunctorΓ identify each lifted
intersection section with the additive structure sheaf on that open subscheme.
Their naturality makes the coefficient augmentation into I⁰ commute with the
Čech differential. Its resolution differential is zero since I.ι is a chain
map from the single complex. Thus it is a chain map into the total, with
components given by additiveCechBeta after lifting. It takes cycles to cycles
and boundaries to boundaries; descend through the homology cokernel to obtain
b, with the stated representative formula. Each tuple intersection is affine,
so its positive étale quasi-coherent cohomology vanishes. The column
augmentations are quasi-isomorphisms, and the first-quadrant criterion applied
after flipping the double complex gives a quasi-isomorphism on totals. Exact
forgetting and ULift preserve homology; the finite-product coordinates and
identity scalar restriction identify the source homology with ordinary unit
cechOver homology. Thus b is bijective. The cycle map c is additive because
beta is additive and the inclusion of total cycles is injective. Degree zero
is the augmented kernel calculation. Empty intersections have zero sections;
an empty cover forces X empty, so all maps are between zero groups. -/
theorem exists_additiveCechBeta_homology
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hcover : iSup U = ⊤)
    (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ) :
    ∃ c : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n →+
      (additiveCechTotal U I).cycles n,
    ∃ b : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homology n →+
      (additiveCechTotal U I).homology n,
      Function.Bijective b ∧
      (∀ z, (additiveCechTotal U I).iCycles n (c z) = additiveCechBeta U I n
        ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).iCycles n z)) ∧
      (∀ z, b ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homologyπ n z) =
        (additiveCechTotal U I).homologyπ n (c z)) := by sorry

end AlgebraicGeometry.Scheme.Modules
