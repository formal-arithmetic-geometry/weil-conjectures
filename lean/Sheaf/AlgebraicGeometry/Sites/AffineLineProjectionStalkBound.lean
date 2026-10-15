/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.AlgebraicGeometry.Sites.SupportDimension
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimension

/-! # Higher direct image stalks of an affine-line projection

Source: blueprint `thm-sc-affine-torsion-cd`, local calculation and compactification,
proof steps 4--10.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- The higher direct image of a bounded-torsion sheaf on affine space vanishes at
points whose residue transcendence degree plus the cohomological degree exceeds the
source dimension. The hypothesis `hCartier` is the bound on punctured smooth strict localizations;
the caller proves it using the coefficient-field model and dimension induction.
The hypotheses `hP1`, `hBoundary`, and `hStalk` supply, respectively, the projective-line
bound, mixed-degree boundary acyclicity, and the strict-local stalk comparison.
The hypothesis `hLeray` supplies diagonal vanishing after exact inverse image.
The hypothesis `hAffineLine` identifies the explicit polynomial projection with
the structural morphism of a relative affine line.
This statement concerns the projection and its stalks, rather than global cohomology.

Source: blueprint `thm-sc-affine-torsion-cd`, proof steps 4--10.
(blueprint: lem-sc-affine-line-projection-stalk-bound)

Proof: Put d = n + 2, B = A^(d-1)_K, Y = P^1_B, g : Y -> B, j : A^d_K -> Y,
and i : B -> Y the infinity section. The supplied `hAffineLine` identification
followed by the standard affine chart constructs j. The two polynomial charts
give dim Y = d and show Y is smooth and integral over K.
The Cartier boundary has equation h in the infinity chart. Its complement immersion
is quasi-compact (on the charts its inverse images are the whole chart and D(h))
and separated, so the strict-henselization stalk formula applies.

At a boundary point of residue transcendence degree a, use the punctured smooth
strict-local bound `hCartier`. The boundary equation h is nonzero in the strict-local
domain and belongs to its maximal ideal; also a < d. It gives cohomological dimension
at most d-a for Spec R[1/h]. The supplied stalk comparison `hStalk` therefore gives zero stalks
of R^q j_*M when q > d-a. Away from the boundary positive direct images of j vanish
because restricting the immersion gives the identity.

For q > 0, the caller uses the closed-support equivalence to write
R^q j_*M = i_*N_q. Closed-section acyclicity then gives R^p g_*R^q j_*M = 0
for p,q positive; this is the supplied `hBoundary` statement.
Additivity preserves the annihilator N
through all direct images and right derived functors. The supplied projective-line
bound `hP1`, applied to the torsion sheaf
j_*M,
gives R^p g_* j_*M = 0 for p > 2. The caller proves this hypothesis from the
projective-line geometric-stalk comparison and the curve bound, independently of the
affine cohomological dimension theorem.

For r>2, apply the supplied Leray diagonal-vanishing statement `hLeray` after
inverse image at the chosen point of B. A diagonal term with both coordinates
positive is zero by the boundary-section calculation. The term with q=0 is zero
by the projective-line bound because p=r>2. For p=0, q=r, the finite-stalk and
inverse-image stalk formulas identify its stalk with the boundary stalk calculated
above. This proves the assertion for r>2, including r>d, without needing to choose
an edge-map isomorphism.

For r=2 the inequality d < 2 + trdeg_K kappa(y) forces y to be the generic point of
the polynomial base B. Its strict localization is a separably closed field: its
regular local ring has dimension zero. The strict-henselization stalk formula for
the affine projection then identifies this stalk with H^2 of an affine line over
that separably closed field. The affine-curve bound makes this zero. This also handles
d=2. For a merely separably closed geometric field, extend to its algebraic closure;
this is purely inseparable, so inverse image is an equivalence and reflects zero
objects. Over a separably closed field the geometric fibre functor is conservative,
so zero stalks also give the stated zero inverse-image sheaves. Thus the assertion
holds for every geometric point specified here. -/
theorem affineLineProjection_stalk_bound
    (hP1 : ∀ (S : Scheme.{u})
      (F : Sheaf (AlgebraicGeometry.ProjectiveLine S).smallEtaleTopology
        AddCommGrpCat.{u + 1}), F.IsTorsion → ∀ q : ℕ, 2 < q →
      IsZero (((Etale.lowerStar AddCommGrpCat.{u + 1}
        (AlgebraicGeometry.ProjectiveLine S ↘ S)).rightDerived q).obj F))
    (hBoundary : ∀ {U Z Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
      (i : Z ⟶ Y) [IsClosedImmersion i] (g : Y ⟶ Z),
      Set.range i.base = (Set.range j.base)ᶜ → i ≫ g = 𝟙 Z →
      ∀ (M : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (p q : ℕ),
      0 < p → 0 < q →
      IsZero (((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived p).obj
        (((Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerived q).obj M)))
    (hStalk : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
      {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}), F.IsTorsion → ∀ q : ℕ,
      Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1}
        (pullback.fst f (strictHenselizationStructuralMap s))).obj F) q) →
      IsZero ((pointSmallEtale s).sheafFiber.obj
        (((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj F)))
    (hLeray : ∀ {X Y S T : Scheme.{u}} (j : X ⟶ Y) (g : Y ⟶ S) (s : T ⟶ S)
      (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (r : ℕ),
      (∀ p q : ℕ, p + q = r →
        IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj
          (((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived p).obj
            (((Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerived q).obj M)))) →
      IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj
        (((Etale.lowerStar AddCommGrpCat.{u + 1} (j ≫ g)).rightDerived r).obj M)))
    (hAffineLine : ∀ (K : Type u) [CommRing K] (m : ℕ),
      let B := Spec (.of (MvPolynomial (Fin m) K))
      let f := Spec.map (CommRingCat.ofHom (MvPolynomial.rename
        (Fin.castSucc : Fin m → Fin (m + 1))).toRingHom)
      ∃ e : Spec (.of (MvPolynomial (Fin (m + 1)) K)) ≅ AffineSpace PUnit.{u + 1} B,
        e.hom ≫ AffineSpace PUnit.{u + 1} B ↘ B = f)
    (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ)
    (hCartier : ∀ (Y : Scheme.{u}) [IsIntegral Y]
        (f : Y ⟶ Spec (.of K)) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f]
        (a : ℕ), a < n + 2 → topologicalKrullDim Y = ((n + 2 : ℕ) : WithBot ℕ∞) →
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
          (y : Y), s (IsLocalRing.closedPoint Ω) = y →
        ∀ [Algebra K (Y.residueField y)],
          Spec.map (CommRingCat.ofHom (algebraMap K (Y.residueField y))) =
            Y.fromSpecResidueField y ≫ f →
        ∀ [Algebra (Y.residueField y) Ω],
          Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫
            Y.fromSpecResidueField y = s →
          Algebra.trdeg K (Y.residueField y) = (a : Cardinal.{u}) →
        ∀ [Algebra K (strictHenselizationRing s)],
          Spec.map (CommRingCat.ofHom (algebraMap K (strictHenselizationRing s))) =
            strictHenselizationStructuralMap s ≫ f →
        ∀ (h : strictHenselizationRing s), h ∈ IsLocalRing.maximalIdeal _ → h ≠ 0 →
          (Spec (.of (Localization.Away h))).HasTorsionCohomologicalDimensionLE (n + 2 - a))
    (M : Sheaf (Spec (.of (MvPolynomial (Fin (n + 2)) K))).smallEtaleTopology
      AddCommGrpCat.{u + 1}) (N : ℕ) (hN : 0 < N) (hM : N • 𝟙 M = 0)
    (q : ℕ) (hq : 2 ≤ q) :
      let f : Spec (.of (MvPolynomial (Fin (n + 2)) K)) ⟶
          Spec (.of (MvPolynomial (Fin (n + 1)) K)) :=
        Spec.map (CommRingCat.ofHom (MvPolynomial.rename
          (Fin.castSucc : Fin (n + 1) → Fin (n + 2))).toRingHom)
      let b := Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin (n + 1)) K)))
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (s : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin (n + 1)) K))),
        ((n + 2 : ℕ) : Cardinal.{u}) < (q : Cardinal.{u}) +
            residueFieldTrdeg b (s (IsLocalRing.closedPoint Ω)) →
          IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj
            (((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj M)) := by
  sorry

end AlgebraicGeometry.Scheme
