/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.CondensedActionModule
public import WeilConjectures.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.DiscreteLatticeKoszulResolution
public import WeilConjectures.CategoryTheory.LatticeKoszulTotalTriangles

import WeilConjectures.Algebra.Homology.FiniteStripAugmentation
import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.KInjectiveFiberTriangleComparison
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Injective-normalized lattice Koszul comparison

Source: current blueprint, direct-image stability proof, paragraph (3), agent lattice
expansion, injective comparison and normalization; Stacks Tags 0133, 070K, 070Y, 05TH
(blueprint: lem-sfb-lattice-koszul-injective-normalization).

The total, its invariant inclusion, its coherent signed shifts, and the predicates for
module normalization and connecting arrows are the existing `TriangulatedCup` declarations.
The formula below uses the universal computation isomorphism for every resolution, so it
compares arrows in the ordinary derived category, rather than only their cohomology.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace Profinite.DiscreteLattice
namespace InjectiveNormalization

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- The degree-zero invariant inclusion is natural on actual equivariant complexes.
Source: paragraph (3), DAG step 2
(blueprint: lem-sfb-lattice-koszul-injective-normalization).
Proof: equivariant maps carry fixed sections to fixed sections. In each input degree,
naturality of the Koszul augmentation and the total coproduct inclusion gives the
identity; all other Koszul components of the inclusion vanish. -/
theorem inclusion_naturality (r : ℕ) (K : KoszulModel R r)
    {P P' : CochainComplex (Equivariant R r) ℤ} (f : P ⟶ P') :
    ((invariants R r).mapHomologicalComplex (.up ℤ)).map f ≫
        TriangulatedCup.totalInclusion R r K P' =
      TriangulatedCup.totalInclusion R r K P ≫ (TriangulatedCup.total R r K).map f := by
  sorry

/-- On every bounded-below termwise injective complex the actual invariant inclusion
is a quasi-isomorphism, including rank zero.
Source: paragraph (3), DAG steps 1 and 2; Stacks Tag 0133, finite-strip row variant
(blueprint: lem-sfb-lattice-koszul-injective-normalization).
Proof: for an injective module I the normalized module comparison of
lem-sfb-discrete-lattice-koszul-resolution carries its invariant augmentation to the
computation unit at I[0]. This unit and the comparison are invertible, so the row
augmentation is a quasi-isomorphism. Apply lem-sc-finite-strip-row-augmentation to
K_R(J^b) in horizontal degrees 0 through r, using strip bound r+1. Its total
augmentation is precisely totalInclusion, with differential d_K+(-1)^a d_J. -/
@[instance] theorem inclusion_quasiIso (r : ℕ) (K : KoszulModel R r)
    (J : CochainComplex.Plus (Equivariant R r)) [∀ n : ℤ, Injective (J.obj.X n)] :
    QuasiIso (TriangulatedCup.totalInclusion R r K J.obj) := by
  sorry

/-- The canonical injective-resolution identification of the value of derived invariants.
Its map is RΓ(Qs) followed by the inverse computation unit at J, with the standard
quotient/localization identifications. No new resolution or value object is chosen.
Source: paragraph (3), DAG step 3; Stacks Tags 070K and 070Y
(blueprint: lem-sfb-lattice-koszul-injective-normalization). -/
def resolutionValueIso (r : ℕ)
    (J : CochainComplex.Plus (Equivariant R r)) [∀ n : ℤ, Injective (J.obj.X n)]
    {P : CochainComplex (Equivariant R r) ℤ} (s : P ⟶ J.obj) [QuasiIso s] :
    (derivedInvariants R r).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (((invariants R r).mapHomologicalComplex (.up ℤ)).obj J.obj) :=
  letI : J.obj.IsStrictlyGE (Classical.choose J.property) := Classical.choose_spec J.property
  letI : J.obj.IsKInjective :=
    CochainComplex.isKInjective_of_injective J.obj (Classical.choose J.property)
  (invariants R r).rightDerivedFunctorOfQuasiIsoResolutionsObjIso (resolutions R r) s

/-- The injective formula gives a simultaneous natural, shift-compatible triangulated
comparison, independent of every resolution and lift. The module comparisons are the
same arrows, normalized by invariant inclusion, and the rank-zero comparison is identity
under the canonical total, invariant, and normalized derived-identity identifications.

Source: current blueprint direct-image stability proof, paragraph (3), agent lattice
expansion, returned proof steps 4--6; Stacks Tags 0133, 070K, 070Y, 05TH and 08BJ
(blueprint: lem-sfb-lattice-koszul-injective-normalization).

Proof, following the seven DAG steps:
1. On an injective module the normalized module theorem identifies the invariant
augmentation with the invertible computation unit. Thus that augmentation is a
quasi-isomorphism, without consulting any choice in the proof of the module theorem.
2. The invariant inclusion is a chain map since d_K kills invariants and the vertical
sign is one in Koszul degree zero. Equivariance proves inclusion_naturality. Finite-strip
row augmentation with bound r+1 proves inclusion_quasiIso on every injective J.
3. A monic map to bounded-below J forces its source to be bounded below. Set c_s to
resolutionValueIso, and L_s to Q(Ks), then Q(b_J)^(-1), then c_s^(-1). Totalization
preserves quasi-isomorphisms, and both other factors are invertible, so L_s is invertible.
4. For any derived morphism v, lift Qt v (Qs)^(-1) to a chain map between the K-injective
resolutions. The K-injective Hom bijection gives uniqueness up to homotopy. Naturality
of the computation unit and of b gives L_t K(v)=RΓ(v)L_s. The total homotopy has sign
(-1)^a, so this equality is independent of the lift. At v=1 it is independence of the
resolution; for all v it descends to the natural isomorphism M.iso.
5. Exact trivial inflation is left adjoint to invariants, so invariants preserve
K-injectives. The fixed derived shift is normalized by the computation unit. The
Koszul shift multiplies degree a by (-1)^(a*n); b has only degree a=0. Hence these
shifts commute with L_s on J and, by shifted resolutions, on every bounded-below P.
6. Both functors are triangulated with these shifts. Naturality and step 5 give all
three squares of every distinguished triangle. The signed cone convention is -p;
TotalTriangles carries its short-exact boundary to the termwise Koszul boundary.
This gives ComparisonProperties.connecting for the simultaneous module comparisons c.
7. The chain identity K(s)b_P=b_J Γ(s) and unit naturality give the invariant-inclusion
normalization. At rank zero b, totalization and invariants are identity under their
coordinate identifications, so L_s=Q(s)^(-1)Q(s)=1, as expressed by IsRankZero.
Naturality for v=Qs gives the final resolution-compatibility equality below. -/
theorem lattice_koszul_injective_normalization (K : ∀ r : ℕ, KoszulModel R r) :
    ∃ (M : ∀ r : ℕ, TriangulatedCup.TriangulatedModel R r (K r))
      (c : ∀ r : ℕ, Comparison R r (K r)),
      (∀ r : ℕ, TriangulatedCup.ComparisonProperties R r (K r) (M r) (c r)) ∧
      TriangulatedCup.IsRankZero R (K 0) (M 0) ∧
      (∀ (r : ℕ) (P J : CochainComplex.Plus (Equivariant R r))
        [∀ n : ℤ, Injective (J.obj.X n)] (s : P.obj ⟶ J.obj) [Mono s] [QuasiIso s],
        TriangulatedCup.onComplex R r (M r) P ≫ (resolutionValueIso R r J s).hom =
          DerivedCategory.Q.map ((TriangulatedCup.total R r (K r)).map s) ≫
            inv (DerivedCategory.Q.map (TriangulatedCup.totalInclusion R r (K r) J.obj))) ∧
      (∀ (r : ℕ) (P J : CochainComplex.Plus (Equivariant R r))
        [∀ n : ℤ, Injective (J.obj.X n)] (s : P.obj ⟶ J.obj) [Mono s] [QuasiIso s],
        TriangulatedCup.onComplex R r (M r) P ≫
            (derivedInvariants R r).map (DerivedCategory.Q.map s) =
          DerivedCategory.Q.map ((TriangulatedCup.total R r (K r)).map s) ≫
            TriangulatedCup.onComplex R r (M r) J) := by
  sorry

end InjectiveNormalization
end Profinite.DiscreteLattice
