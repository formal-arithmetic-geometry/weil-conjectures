/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.CharP.Defs
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility
import Sheaf.Paper.ProjectionCompactification
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.EtaleDerivedDirectImageCoherence
import Sheaf.AlgebraicGeometry.DerivedOpenRestriction
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import Sheaf.AlgebraicGeometry.EtaleInjectiveFiniteCechRows
import Mathlib.Topology.Constructible
import Sheaf.AlgebraicGeometry.QuasiExcellentFiniteTypeStability
import Sheaf.AlgebraicGeometry.GabberOpenImmersionSheafFiniteness

/-!
# Etale direct-image finiteness over quasi-excellent bases

Source: Bhatt--Scholze, Theorem 6.7.1, printed p. 55; Illusie--Laszlo--Orgogozo,
Expose XIII, Theorems 1.1.1--1.1.2; Stacks Project, Tags 095U, 0A3V and 0GL0
(blueprint: lem-per-quasi-excellent-etale-direct-image-finiteness).

The uniform all-sheaf vanishing bound is asserted only for proper morphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- A finitely presented morphism of qcqs schemes preserves bounded constructibility for
finite field coefficients if it is proper, or if its target is quasi-excellent and the
coefficient characteristic is invertible there. Proper morphisms additionally have a
uniform higher-direct-image vanishing bound for all module sheaves.

Source: Bhatt--Scholze, Theorem 6.7.1, printed p. 55, with R = B and maximal ideal zero;
ILO, Expose XIII, Theorems 1.1.1--1.1.2 (constructible-sheaf-dependent bound in the
nonproper case); Stacks Project, Tags 095U, 0A3V and 0GL0
(blueprint: lem-per-quasi-excellent-etale-direct-image-finiteness).

Proof:
1. For proper g, finite type and quasi-compactness of T give a uniform fibre-dimension
bound e by lem-fin-finite-type-fibre-dimension-bound. The underlying abelian sheaf of
any B-module sheaf is killed by ell. Apply lem-kun-proper-torsion-cd-bound and
lem-sbc-higher-direct-image-forget-comparison to get vanishing in degrees q > 2e.
This gives d = 2e independently of the sheaf, including in residue characteristic ell.
2. Apply lem-weil-pbc-etale-compactification-constructibility to the identity
compactification of proper g. By def-weil-pbc-projection-compactification its image is
Rg_*M; every cohomology sheaf is constructible. A nonnegative injective resolution
has no negative cohomology, and step 1 bounds the positive degrees.
3. Bounded constructible complexes are closed under shifts and distinguished triangles:
the cohomology exact sequence and thm-constructible-serre give constructibility and
finite unions of degree intervals give boundedness. Derived direct image preserves
triangles and shifts by lem-pc-right-derived-functor-triangulated. Induct on a bounded
cohomological interval using lem-sf-derived-truncation-triangle, with terms the shorter
truncation and the last cohomology sheaf shifted. This proves the proper assertion
and reduces all remaining cases to constructible sheaves.
4. For quasi-excellent T, lem-per-quasi-excellent-finite-type-stability gives
Noetherianity of T and V. For an open immersion into a Noetherian quasi-excellent
scheme with ell invertible, lem-per-gabber-open-immersion-sheaf-finiteness gives
constructible cohomology and eventual vanishing for each constructible sheaf.
Negative cohomology vanishes by the bounded-below resolution, so step 3 applies.
5. For a separated finite-type map to such a base, thm-nagata-compactification gives
an open immersion followed by a proper map. The proper source stays quasi-excellent
and Noetherian by lem-per-quasi-excellent-finite-type-stability; ell stays invertible.
By pqf-lem-lft-fp-locnoeth the proper map is finitely presented. Apply steps 1--4 and
lem-cbc-etale-derived-direct-image-coherence to their composite.
6. Restrict the target to an affine open using lem-weil-pbc-derived-open-restriction.
Restriction preserves bounded constructibility by intersecting strata and restricting
local constant trivializations. By lem-weil-pbc-qcqs-finite-affine-open-cover the source
has a finite affine cover. Every member maps separatedly to the affine target.
The overlap of a finite union with one more affine is a quasi-compact open of that
affine by pqf-lem-qs-intersection-qc; its inclusion is finite type by
lem-weil-pbc-qc-open-immersion-finite-type, so step 5 applies to it too.
7. For a two-open cover, restrict a bounded-below injective representative.
The restrictions remain injective by lem-weil-pbc-etale-restriction-injectives.
The two-open augmented rows of lem-dg-etale-injective-finite-cech-rows are split exact,
so remain exact after direct image. The resulting short exact sequence of complexes
computes the relative Mayer--Vietoris sequence. Kernels, cokernels and extensions are
constructible by thm-constructible-serre; the three finite degree intervals also give
a bound for the fourth complex.
8. Induct on the finite affine cover: the empty source gives zero, one affine is
step 5, and the two-open sequence of step 7 handles adjoining each further affine,
with overlap as in step 6. Finally use a finite affine cover of T: the finite union of
local cohomological intervals gives a global bound. Refine the finitely many local
stratifications by successive constructible differences into locally closed pieces,
using def-weil-constructible-subset. The restricted finite locally constant sheaves
remain so, giving global constructibility. This bound may depend on K. -/
theorem quasiExcellent_etale_direct_image_finiteness
    (ell : ℕ) [Fact ell.Prime] (B : Type (u + 1)) [Field B] [Finite B] [CharP B ell]
    {V T : Scheme.{u}} [CompactSpace V] [QuasiSeparatedSpace V]
    [CompactSpace T] [QuasiSeparatedSpace T]
    (g : V ⟶ T) [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (hcase : IsProper g ∨
      ((∀ U : T.affineOpens, IsQuasiExcellent Γ(T, U.1)) ∧
        ∀ t : T, IsUnit (ell : T.presheaf.stalk t))) :
    (∀ K : _root_.DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)),
      DerivedCategory.isBoundedConstructible B V K.obj →
        DerivedCategory.isBoundedConstructible B T
          ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} B) g).obj K).obj) ∧
    (IsProper g → ∃ d : ℕ,
      ∀ (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) (q : ℤ),
        (d : ℤ) < q →
          IsZero ((_root_.DerivedCategory.Plus.homologyFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj
            ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} B) g).obj
              ((_root_.DerivedCategory.Plus.singleFunctor
                (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) 0).obj M)))) := by
  sorry

end AlgebraicGeometry.Etale
