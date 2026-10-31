/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Borel
public import WeilConjectures.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry
import WeilConjectures.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry

/-! # Geometry and properness of homogeneous Borel quotients

Source: Milne, Algebraic Groups (2017), Corollaries 5.26--5.27, printed p.105,
Proposition 7.15, printed pp.142--143, and Theorem 17.9(a), printed p.354;
Stacks Project, Tags 036D, 0363, 056S, 0569, 033N and 01T6.
(blueprint: lem-sfb-borel-quotient-proper-geometry)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- A represented homogeneous quotient by a smooth connected closed subgroup is smooth,
geometrically integral, regular and Noetherian. Its projection is smooth with nonempty
geometrically integral fibres. If the subgroup is Borel, the quotient is proper.

`GeometricallyIntegral p.left` says that every pullback along `Spec L → X` is integral,
including nonemptiness. Equivalently, for each x and every extension L/κ(x), the fibre
G ×_X Spec L is nonempty and integral. The same predicate on the structure maps says
that G and X are integral after every extension of F. `IsNoetherian` is equivalent to
having a finite affine cover with Noetherian coordinate rings. `IsBorelGroupScheme`
uses the scheme-theoretic commutator subgroup and its iterated derived series.

Source: Milne, Corollaries 5.26--5.27, p.105; Proposition 7.15, pp.142--143;
Theorem 17.9(a), p.354; Stacks Project, Tags 036D, 0363, 056S, 0569, 033N and 01T6.
(blueprint: lem-sfb-borel-quotient-proper-geometry)

Proof plan, following the seven steps of the node:
1. Apply lem-sfb-algebraic-group-homogeneous-quotient. Local lifts and the coset criterion
   identify its separated finite-type quotient with X: lift locally, map to the other
   quotient, and glue by lem-weil-pbc-fpqc-representable-descent. The same procedure
   constructs the left G-action. The coset criterion gives the kernel-pair isomorphism
   G × H ≅ G ×_X G by (b,h) ↦ (b,bh), with inverse (b,b') ↦ (b,b⁻¹b').
2. The base change of p along itself is G × H → G, hence smooth by
   lem-pc-proper-base-change. Use lem-trf-smooth-fpqc-base-descent to descend smoothness
   to p. Apply lem-sbc-smooth-flat-surjective-source-descent to p and G → Spec F to
   prove X smooth.
3. Surjectivity makes X nonempty and connected. Apply
   lem-weil-separably-closed-geometrically-connected to G, H and X. Their extensions
   stay smooth, hence regular by lem-weil-pbc-smooth-scheme-over-field-regular, and
   integral by lem-sc-regular-connected-integral. This gives geometric integrality.
   At F it gives regularity; lem-weil-pbc-finite-type-over-noetherian gives
   Noetherianity. Local Noetherianity and quasi-compactness give a finite affine cover.
4. For x, pass to an algebraic closure Ω of κ(x). The fibre is nonempty by
   lem-weil-pbc-surjective-base-change, and finite type by
   lem-sfb-finite-type-composition-base-change. Use lem-sc-lft-over-field-jacobson-space
   and lem-weil-pbc-closed-point-residue-field-base to choose an Ω-point b. Translation
   gives H_Ω ≅ G ×_X Spec Ω, hence connectedness. Apply
   lem-weil-geometrically-connected-algebraic-closure and
   lem-trf-smooth-connected-fibre-normal-integrality for all extensions L/κ(x).
   Nonemptiness follows by base change of p; no L-rational lift is assumed.
5. Choose a smooth connected solvable subgroup B₀ of greatest dimension, starting
   with the identity subgroup. Lemmas lem-kun-dimension-finite-type and
   lem-wf-affine-dimension-drop bound these dimensions. By
   lem-sfb-solvable-subgroup-flag-realization, B₀ is the stabilizer of a complete flag
   in a faithful representation; every flag stabilizer has dimension at most dim B₀.
6. The flag scheme is proper by lem-pc-projective-proper. The orbit of this flag has
   minimum dimension by lem-sfb-smooth-group-orbit-geometry. A nonempty boundary
   would have an F-rational closed point, by the two closed-point lemmas of step 4,
   with a strictly smaller orbit. Thus this orbit is closed and proper by
   lem-sfb-solvable-subgroup-flag-realization. Identify it with G/B₀ using
   lem-sfb-homogeneous-orbit-quotient-geometry, including rational-point lifts.
7. If H is Borel, lem-sfb-solvable-proper-fixed-point gives an H-fixed point in G/B₀.
   Lift it to g ∈ G(F). The full scheme-theoretic stabilizer gives H ⊆ gB₀g⁻¹;
   maximality gives equality. The maps aH ↦ agB₀ and cB₀ ↦ cg⁻¹H descend from local
   lifts by lem-weil-pbc-fpqc-representable-descent and are inverse. Quotient
   uniqueness from step 1 identifies X with the proper scheme G/B₀. -/
theorem homogeneousQuotient_geometry {F : Type u} [Field F] [IsAlgClosed F]
    (G H : Over (Spec (.of F))) [GrpObj G] [GrpObj H]
    [IsAffine G.left] [Smooth G.hom] [ConnectedSpace G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (i : H ⟶ G) [IsClosedSubgroupScheme i] [Smooth H.hom] [ConnectedSpace H.left]
    (X : Over (Spec (.of F))) (p : G ⟶ X)
    [Flat p.left] [Surjective p.left] [LocallyOfFinitePresentation p.left]
    [QuasiCompact p.left] [QuasiSeparated p.left]
    (hcoset : ∀ (T : Over (Spec (.of F))) (a b : T ⟶ G),
      a ≫ p = b ≫ p ↔ a⁻¹ * b ∈ Set.range (fun h : T ⟶ H ↦ h ≫ i))
    (hlift : ∀ (T : Over (Spec (.of F))) (x : T ⟶ X),
      ∃ (I : Type u) (T' : I → Over (Spec (.of F))) (f : ∀ j, T' j ⟶ T),
        Presieve.ofArrows (fun j ↦ (T' j).left) (fun j ↦ (f j).left) ∈
          Scheme.fpqcPrecoverage T.left ∧
        ∀ j, ∃ g : T' j ⟶ G, g ≫ p = f j ≫ x) :
    Smooth G.hom ∧ GeometricallyIntegral G.hom ∧ IsRegularScheme G.left ∧
      IsNoetherian G.left ∧ Smooth X.hom ∧ GeometricallyIntegral X.hom ∧
      IsRegularScheme X.left ∧ IsNoetherian X.left ∧ Smooth p.left ∧
      GeometricallyIntegral p.left ∧ (IsBorelGroupScheme i → IsProper X.hom) := by
  sorry

end AlgebraicGeometry
