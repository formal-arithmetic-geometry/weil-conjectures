/-
Copyright (c) 2026 Q20. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q20
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Blowup.Affine.ChartAlgebra

import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Blowup.Complement

/-!
# Special-fibre blowups and section dilatation charts

Source: Stacks Project, Tags 0804, 0805, 0806, 02OS, 02NS; BLR, Neron Models,
3.2 Proposition 1 and its proof, pp. 62--63
(blueprint: lem-sfb-trait-blowup-section-charts).

The special fibre uses the canonical residue field of `R`, and the generic fibre
uses `FractionRing R`. The equality `hI` names the ideal of the given closed centre;
it supplies no independent choice of centre. Unique lifting states the bijection
on points over `R`, without making a noncanonical choice of a lift.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Special-fibre blowups preserve flat separated finite-type models and their
unramified DVR points, and admit the uniformizer dilatation open.
Source: Stacks, Tags 0804, 0805, 0806, 02OS, 02NS; BLR 3.2 Proposition 1, pp. 62--63
(blueprint: lem-sfb-trait-blowup-section-charts).

Proof plan:
1. The closed-immersion kernel is quasi-coherent (def-sbc-closed-immersion-ideal-sheaf).
A DVR is Noetherian (def-sc-discrete-valuation-ring). Finite-type affine coordinate
rings are Noetherian (lem-weil-pbc-finite-type-algebra-noetherian), so the centre
ideal is of finite type by lem-weil-pbc-quasi-coherent-finite-type-affine.
Apply lemma-nagata-blowup-proper to obtain properness of the blowup map.
2. Properness gives separatedness and finite type of the blowup map. Compose with
`f`, using lem-sfb-finite-type-composition-base-change and the separated clause of
lem-weil-pbc-proper-fp-permanence.
3. Restrict to affine opens by def-nagata-global-blowup-local-model and
lem-sfb-flat-pullback-blowup-chart-restrictions. The generator charts cover, by
prop-nagata-affine-blowup-chart-cover and prop-nagata-affine-blowup-chart, and have
rings B[I/a] in B[1/a] (def-nagata-blowup-chart-ring). Flatness of B/R implies
R-torsion-freeness (lem-trf-flat-module-torsionfree-domain). If r(c/a^n)=0, clearing
a power of a and cancelling nonzero r in B gives c/a^n=0. Thus B[1/a] and B[I/a]
are R-torsion-free. A torsion-free module over the PID R is flat
(lem-weil-pbc-pid-torsion-free-module-flat). Use the affine flatness criterion
lem-weil-pbc-flat-ring-map-iff-flat-affine and locality to obtain flatness of X'.
4. Apply thm-nagata-global-blowup-complement. The generic fibre is contained in
the complement since the centre contains pi and pi is invertible generically.
5. For each A, flatness implies pi is nonzero in A. A point's generic restriction
therefore lifts through the complement isomorphism. Proper separated valuative
extension (lemma-nagata-proper-separated-valuation-extension) gives its unique
extension to Spec A. Its composite with the blowup map is the original R-point.
6. Include pi among the finite generators of each affine centre ideal. Its chart
has ring B[I/pi]. These opens agree on overlaps by
lem-sfb-flat-pullback-blowup-chart-restrictions: on a principal refinement,
B[I/pi]_s = B_s[IB_s/pi], with identical fraction maps. They glue to D.
7. If the closed point of a lies in Z, choose an affine containing its image.
Its preimage contains the maximal ideal and hence all of Spec A. For the induced
map beta : B -> A the reduction condition is beta(I) contained in pi A.
The localization universal property (lem-weil-pbc-localization-away-universal-property)
extends beta to B[1/pi] -> Frac A, and each i/pi maps to beta(i)/pi in A.
Restriction gives B[I/pi] -> A and hence a lift into D. Valuative uniqueness
identifies it with the unique lift of step 5. Empty charts, disconnected schemes
and nilpotents in the special fibre do not affect these arguments. -/
theorem trait_blowup_section_charts
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (X : Scheme.{u}) (f : X ⟶ Spec (.of R))
    [Flat f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : Scheme.{u})
    (z : Z ⟶ pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    [IsClosedImmersion z]
    (I : X.IdealSheafData)
    (hI : I = (z ≫ pullback.fst f
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).ker) :
    IsProper I.blowupMap ∧
    Flat (I.blowupMap ≫ f) ∧
    IsSeparated (I.blowupMap ≫ f) ∧
    LocallyOfFiniteType (I.blowupMap ≫ f) ∧ QuasiCompact (I.blowupMap ≫ f) ∧
    IsIso (I.blowupMap ∣_ I.support.compl) ∧
    IsIso (pullback.snd I.blowupMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))) ∧
    ∃ D : I.blowup.Opens,
      (∀ U : X.affineOpens,
        ∃ e : (D ⊓ (I.blowupMap ⁻¹ᵁ U.1)).toScheme ≅
          Spec (.of (AffineBlowup.chartRing (I.ideal U)
            ((f.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (.of R)).inv.hom π)))),
          e.inv ≫ (D ⊓ (I.blowupMap ⁻¹ᵁ U.1)).ι ≫ I.blowupMap =
            Spec.map (CommRingCat.ofHom
              (algebraMap Γ(X, U.1) (AffineBlowup.chartRing (I.ideal U)
                ((f.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (.of R)).inv.hom π))))) ≫
              U.2.fromSpec) ∧
      ∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
        [Algebra R A] [Module.Flat R A] [IsLocalHom (algebraMap R A)],
        IsLocalRing.maximalIdeal A = Ideal.span {algebraMap R A π} →
        (∀ (a : Spec (.of A) ⟶ X),
          a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) →
          ∃! a' : Spec (.of A) ⟶ I.blowup, a' ≫ I.blowupMap = a) ∧
        (∀ (a : Spec (.of A) ⟶ X),
          a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) →
          a (IsLocalRing.closedPoint A) ∈ I.support →
          ∀ (a' : Spec (.of A) ⟶ I.blowup), a' ≫ I.blowupMap = a →
            ∃ d : Spec (.of A) ⟶ D.toScheme, d ≫ D.ι = a') := by
  sorry

end AlgebraicGeometry
