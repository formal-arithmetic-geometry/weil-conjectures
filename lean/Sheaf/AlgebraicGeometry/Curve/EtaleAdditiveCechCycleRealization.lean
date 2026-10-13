/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import Sheaf.AlgebraicGeometry.EtaleOpenCechInjectiveAugmentation
import Sheaf.Algebra.Homology.FirstQuadrantAugmentation

/-! # Realizing additive Čech cycles in the augmented resolution total
Source: Stacks Project, Tag 01EQ, Lemma 20.11.2. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every coefficient Čech cycle has a global-resolution representative with
matching augmentation classes. No edge equivalence or inverse image is involved.
Source: Stacks Project, Tag 01EQ, Lemma 20.11.2, the two augmentation arrows.
(blueprint: lem-pbc-etale-additive-cech-cycle-realization)

Proof: Identify unit module sections on an intersection with the lifted additive
structure-sheaf sections on its open subscheme, using restrictFunctorΓ. The
augmentation into I⁰ commutes with restrictions and has zero vertical differential.
It therefore defines the coefficient augmentation beta as a map of complexes
(after applying ULift). Thus beta of the supplied cycle is a total cycle tβ.
The restrictions from global sections define the augmentation alpha; the sign
in Čech degree zero is +1. Each resolution term is injective, so its augmented
open-cover Čech row is exact in positive degrees and computes global sections
in degree zero. The first-quadrant row filtration of the cone of alpha is finite
in each total degree and has acyclic rows, hence alpha is a quasi-isomorphism.
Choose the preimage of the class of tβ under H(alpha), then a global cycle s
representing that preimage (homologyπ is surjective). Let tα be alpha of s.
Naturality of homologyπ proves equality of the two total classes. Only the
covering condition is used, not affine acyclicity. In degree zero this is ordinary
sheaf gluing; an empty cover forces X empty and all these section groups zero.
Empty intersections and repeated opens are handled by the same restriction maps. -/
theorem etaleAdditiveCech_cycle_realization
    {X : Scheme.{u}} {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hcover : iSup U = ⊤)
    (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ)
    (z : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n) :
    ∃ (s : (additiveCechGlobal I).cycles n)
      (tα tβ : (additiveCechTotal U I).cycles n),
      (additiveCechTotal U I).iCycles n tα =
        additiveCechAlpha U I n ((additiveCechGlobal I).iCycles n s) ∧
      (additiveCechTotal U I).iCycles n tβ = additiveCechBeta U I n
        ((cechOver X.toSpecΓ U
          (SheafOfModules.unit X.ringCatSheaf)).iCycles n z) ∧
      (additiveCechTotal U I).homologyπ n tα =
        (additiveCechTotal U I).homologyπ n tβ := by sorry

end AlgebraicGeometry.Scheme.Modules
