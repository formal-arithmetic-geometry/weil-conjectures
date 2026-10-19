/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q115
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Topology.Maps.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.AlgebraicGeometry.AffineGroupoidOrbitFibres

/-!
# Invariant affine charts of an admissible finite-group quotient

Source: ILO, Travaux de Gabber, Expose IX, 1.4, printed pp. 132--133, the admissible
quotients in (*); Stacks Project, Tags 03BJ and 03BL, for the affine integrality and
orbit-fibre assertions (blueprint: lem-per-admissible-quotient-affine-integral-charts).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- An admissible finite-group action on a scheme has an affine integral categorical
quotient, with orbit topology, geometric orbit fibres, and canonical invariant affine
charts. Source: ILO, Expose IX, 1.4, pp. 132--133; Stacks Tags 03BJ, 03BL
(blueprint: lem-per-admissible-quotient-affine-integral-charts).

The subring `C` in each chart is specified by its exact membership condition. Pullback
and restriction of a section are compared on every common subopen `D`. On a stable
open this is exactly invariance under all the restricted automorphisms, without any
choice of identifications of equal opens. The chart equation identifies the restricted
quotient with `Spec` of the actual inclusion `C.subtype`, using the canonical spectrum
isomorphism on the source. In particular the chart isomorphism is constrained by the
quotient map and is not an arbitrary identification of abstract rings.

Proof (the eleven steps of the DAG node):
1. The empty scheme has empty quotient. Otherwise take a finite orbit E in an affine
   U, and, inside any prescribed invariant open O containing E, put
   T = O intersect (the intersection of all translates of U). Finite prime avoidance
   (lem-weil-pbc-prime-avoidance) produces a basic affine neighbourhood A0 of E inside
   T (lem-weil-pbc-affine-open-section-vanishing-prime). Intersect its translates.
   They all lie inside the affine U, which is separated
   (lem-weil-pbc-affine-source-morphism-separated); their intersection W is affine
   by lem-weil-pbc-separated-affine-open-intersection. Thus stable affines cover,
   even inside each invariant open; M itself need not be separated.
2. For B = Gamma(W), use the left action h.b = (h inverse)^* b. The product of
   (t - h.b) over H is monic, invariant, and vanishes at b. Hence B is integral
   over its fixed subring C (03BJ), with no module-finiteness conclusion.
3. The action groupoid has arrows the coproduct of copies of W, indexed by H.
   Its affine coordinate ring is the product of the copies of B
   (lem-weil-pbc-finite-affine-coproduct-spectrum). Its source and target are
   finite (lem-weil-pbc-finite-coproduct) and etale (lem-sc-etale-coproduct-etale),
   hence finite locally free (def-weil-etale-morphism, def-pc-finite-locally-free).
   The equalizer of their ring maps is exactly C.
4. Apply lem-a1-affine-groupoid-orbit-fibres (03BL): Spec B -> Spec C is surjective
   with ordinary and algebraically closed-point fibres precisely H-orbits.
   It is closed by lem-weil-pbc-integral-spec-closed-map, hence a quotient map.
5. For f in C, C localized at f equals the invariants in B localized at f.
   Injectivity follows from C being a subring. An invariant fraction b/f^n admits
   a common exponent r killing every h.b-b since H is finite. Then f^r b is
   invariant. This works for zero divisors too, and commutes with restriction.
6. Define Q as the orbit space of M with quotient topology. Its projection is
   open since the saturation of an open is the union of its translates.
   Define its sheaf on V by the invariant sections on q inverse V. The sheaf
   axiom follows from gluing in O_M and uniqueness of that gluing; the section
   inclusions define its ringed-space map (def-weil-locally-ringed-space-morphism).
7. For stable affine W, identify q(W) with Spec C by Step 4. On each basic open
   the sheaf comparison is the localization isomorphism in Step 5
   (lem-weil-pbc-affine-open-section-vanishing-prime). The basic opens form a basis
   (lem-weil-pbc-spec-localization-away-basic-open), so these comparisons glue.
8. These affine charts make Q a scheme (def-pc-scheme). On each W the constructed
   map is Spec of C -> B (def-weil-affine-spectrum), so its stalk maps are local
   (def-weil-locally-ringed-space-morphism). Step 4 gives the geometric fibres.
9. The affine charts prove q affine (pqf-lem-affine-local-target). Thus every
   affine V has affine inverse image. Its section ring is the invariant subring
   by construction; the orbit polynomial proves integrality on every such V
   (def-weil-finite-integral-morphism). Surjectivity is already established.
10. An invariant M -> Z factors uniquely on orbit spaces, continuously by quotient
    topology. Its section maps land in invariant sections and therefore factor.
    The resulting ringed-space map is local on stalks: choose x over y; a unit
    image in O_Q,y would remain a unit in O_M,x, contradicting locality of the
    original morphism. Injectivity on invariant sections gives uniqueness. This
    applies to arbitrary scheme targets, including nonseparated targets.
11. For invariant open U, V = q(U) is open with q inverse V = U. The orbit
    topology and invariant sheaf restrict to U -> V, so the same factorization
    argument proves its categorical universal property. There is no affine or
    quasi-compact hypothesis on U. -/
theorem exists_admissible_quotient_affine_integral_charts
    (M : Scheme.{u}) (H : Type v) [Group H] [Finite H] (a : H →* Aut M)
    (_hadmissible : ∀ x : M, ∃ W : M.Opens,
      IsAffineOpen W ∧ ∀ h : H, (a h).hom x ∈ W) :
    ∃ (Q : Scheme.{u}) (q : M ⟶ Q),
      (∀ h : H, (a h).hom ≫ q = q) ∧
      (∀ (Z : Scheme.{u}) (f : M ⟶ Z),
        (∀ h : H, (a h).hom ≫ f = f) → ∃! g : Q ⟶ Z, q ≫ g = f) ∧
      IsAffineHom q ∧ IsIntegralHom q ∧ Surjective q ∧
      Topology.IsQuotientMap q ∧
      (∀ x y : M, q x = q y ↔ ∃ h : H, (a h).hom x = y) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
        Function.Surjective (fun t : Spec (.of Ω) ⟶ M ↦ t ≫ q) ∧
        ∀ t s : Spec (.of Ω) ⟶ M, t ≫ q = s ≫ q ↔ ∃ h : H, t ≫ (a h).hom = s) ∧
      (∀ x : M, ∃ (V : Q.Opens) (_hV : IsAffineOpen V)
          (hW : IsAffineOpen (q ⁻¹ᵁ V)),
        x ∈ q ⁻¹ᵁ V ∧
        (∀ (h : H) (y : M), (a h).hom y ∈ q ⁻¹ᵁ V ↔ y ∈ q ⁻¹ᵁ V) ∧
        q '' (q ⁻¹ᵁ V : Set M) = (V : Set Q) ∧
        ∃ C : Subring Γ(M, q ⁻¹ᵁ V),
          (∀ s : Γ(M, q ⁻¹ᵁ V), s ∈ C ↔
            ∀ (h : H) (D : M.Opens) (hD : D ≤ q ⁻¹ᵁ V)
              (hDh : D ≤ (a h).hom ⁻¹ᵁ (q ⁻¹ᵁ V)),
              ((a h).hom.appLE (q ⁻¹ᵁ V) D hDh).hom s =
                (M.presheaf.map (homOfLE hD).op).hom s) ∧
          ∃ e : V.toScheme ≅ Spec (.of C),
            hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom C.subtype) = (q ∣_ V) ≫ e.hom) ∧
      (∀ V : Q.Opens, IsAffineOpen V →
        IsAffineOpen (q ⁻¹ᵁ V) ∧ Function.Injective (q.app V).hom ∧
        ∀ s : Γ(M, q ⁻¹ᵁ V), s ∈ Set.range (q.app V).hom ↔
          ∀ (h : H) (D : M.Opens) (hD : D ≤ q ⁻¹ᵁ V)
            (hDh : D ≤ (a h).hom ⁻¹ᵁ (q ⁻¹ᵁ V)),
            ((a h).hom.appLE (q ⁻¹ᵁ V) D hDh).hom s =
              (M.presheaf.map (homOfLE hD).op).hom s) ∧
      ∀ (U : M.Opens) (_hU : ∀ (h : H) (x : M), (a h).hom x ∈ U ↔ x ∈ U),
        ∃ (V : Q.Opens) (hUV : U ≤ q ⁻¹ᵁ V),
          q '' (U : Set M) = (V : Set Q) ∧ q ⁻¹ᵁ V = U ∧
          ∀ (Z : Scheme.{u}) (f : U.toScheme ⟶ Z),
            (∀ (h : H) (D : M.Opens) (hD : D ≤ U) (hDh : D ≤ (a h).hom ⁻¹ᵁ U),
              (a h).hom.resLE U D hDh ≫ f = M.homOfLE hD ≫ f) →
            ∃! g : V.toScheme ⟶ Z, q.resLE V U hUV ≫ g = f := by
  sorry

end AlgebraicGeometry
