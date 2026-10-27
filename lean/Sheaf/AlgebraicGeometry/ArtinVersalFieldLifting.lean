/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.AlgebraicGeometry.ArtinFamilyLiftingData
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.AlgebraicGeometry.FerrandSchemePushout
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.HopkinsLevitzki

/-! # Pointwise versality gives lifting at finite-type field points

Source: Stacks Project, artin.tex, Tags 07XT (lemma-versal-smooth), 07XG
(lemma-versal-change-of-field), and 07XF (definition-versal)
(blueprint: lem-sfb-artin-versal-field-lifting).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory.ArtinFamily

/-- Versality at every finite-type point gives Artinian lifting at every field point
of finite type over the Noetherian base, including finite residue-field extensions.
Source: Stacks Project, Tags 07XT, 07XG and 07XF
(blueprint: lem-sfb-artin-versal-field-lifting).

Proof:
1. Fix the field point alpha and let p be its image and k its residue field.
A finite set of R-algebra generators of l generates it over the coordinate ring
of any affine neighbourhood of p. The finite-type field-point characterization
(lem-sfb-finite-type-field-point-characterization) gives that p is a finite-type
point and l/k is finite. Artin--Tate (lem-sfb-artin-tate-subalgebra-finite-type)
gives that k is finite type over R, so the assumed versality applies at p.
2. Put C = B times_l k and C' = B' times_l k. The residue-restriction lemma
(lem-sfb-artinian-finite-residue-restriction) makes these Artinian local with
residue field k and gives the surjection C' to C. Its kernel is that of B' to B,
hence nilpotent by lem-weil-pbc-artinian-local-noetherian-nilpotent. All test
rings are finite type over R by lem-sfb-artinian-finite-type-residue-criterion.
3. The squares Spec l to Spec B (respectively Spec B'), with bottom row
Spec k to Spec C (respectively Spec C'), are scheme pushouts by the affine
clause of lem-sfb-ferrand-scheme-pushout. The residue maps are surjective and
k to l is integral because l/k is finite. Their closed immersions are nilpotent.
The first pushout glues a and the canonical point to a map from Spec C to U.
4. Apply essential surjectivity of RS to the second square to glue z with x at p,
using the prescribed isomorphism over l. Apply full faithfulness of RS to the
first square to identify the restriction over C with the pulled-back family.
Choose its B-component to be exactly the original prescribed isomorphism and
its k-component to be the identity; compatibility over l follows by construction.
5. Versality at p lifts this data through C' to C. Restrict the resulting map
and identification to B'. The lift restricts to a, and its identification restricts
to precisely the original one because of the B-component chosen in step 4. -/
theorem hasLiftingAt_of_versalAt_finiteType_points
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (F : BasedCategory.{v, w} (Over (Spec R))) (hF : IsFibredInGroupoids F)
    (hRS : IsRimSchlessinger R F)
    (U : Over (Spec R)) [LocallyOfFiniteType U.hom] (x : Functor.Fiber F.p U)
    (hx : ∀ p : U.left, LocallyOfFiniteType (U.left.fromSpecResidueField p) →
      QuasiCompact (U.left.fromSpecResidueField p) → IsVersalAt R F U x p)
    (l : Type u) [Field l] (α : Spec (.of l) ⟶ U.left)
    (hlt : LocallyOfFiniteType (α ≫ U.hom)) (hqc : QuasiCompact (α ≫ U.hom)) :
    HasLiftingAt R F U x l α := by
  sorry

end CategoryTheory.ArtinFamily
