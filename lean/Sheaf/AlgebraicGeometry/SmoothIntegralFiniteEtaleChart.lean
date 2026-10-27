/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-! # Finite étale charts of smooth integral varieties

Source: Stacks Project, Groupoids, Tag 0BF7, proof of `lemma-algebraic-quasi-projective`,
the diagram with `W → V`; Morphisms, Tags 054L, 02NW, 04MH and 02GL
(blueprint: lem-sfb-smooth-integral-finite-etale-chart).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A smooth integral separated variety has a dense affine finite étale chart over an
open of affine space, of positive constant degree, with split rational fibres.

Source: Stacks Project, Groupoids, Tag 0BF7, diagram `G ← U → A^d`, `W → V`;
Morphisms, Tags 054L, 02NW, 04MH and 02GL
(blueprint: lem-sfb-smooth-integral-finite-etale-chart).

Proof:
1. Choose a point of the integral scheme. The étale local normal form
   `sbc-thm-etale-local-normal-form` gives a nonempty affine open `U` and an étale
   map to affine `d`-space, identified with the spectrum of `MvPolynomial (Fin d) k`.
2. The polynomial ring is finitely generated over the Noetherian field `k`.
   `lem-weil-pbc-finite-type-over-noetherian` makes its spectrum Noetherian.
3. The map from `U` is affine, hence quasi-compact and quasi-separated; étaleness
   gives local finite presentation and unramifiedness. By
   `lem-weil-pbc-unramified-quasi-finite-at-points` and `pqf-lem-qf-finitefibres`,
   its generic fibres are finite.
4. `lem-weil-pbc-generic-finite-morphism-open-neighborhood` gives a dense target
   open over which the map is finite. Its intersection with the nonempty open
   image of the étale map contains a nonempty principal affine open `V`.
5. Set `W` to its inverse image. The open-preimage fibre-product identification,
   finite base change and étale open restriction show `q : W → V` finite étale.
   Since `V` lies in the image, `q` is surjective and `W` nonempty. A finite map
   to an affine scheme has affine source.
6. A nonempty open in integral `X` is integral and dense. The polynomial ring is
   a domain, and the nonempty principal localization defining `V` is a nonzero
   domain, so `V` is integral too.
7. Finite étale implies finite locally free. By
   `lem-weil-pbc-finite-locally-free-degree-locally-constant`, its degree is locally
   constant, hence constant on integral `V`. Surjectivity makes every fibre
   nonempty; degree zero would give the zero ring and an empty fibre. Thus `n ≥ 1`.
8. A rational point has residue field `k`. Its rational-point pullback is therefore
   the scheme fibre. By `lem-weil-pbc-etale-fibre-discrete-separable-points` this
   is a disjoint union of spectra of finite separable extensions of `k`, all equal
   to `k` since `k` is algebraically closed. Global sections of `m` such components
   have dimension `m`, so `m = n`. Their points give exactly `n` distinct rational
   points of `W` above the chosen rational point.
9. Open immersions preserve smoothness under composition, and affine space is
   smooth. The localization defining `V` is a finitely generated `k`-algebra;
   finiteness of `q` and finite-type composition give finite type of `W` as well.
-/
theorem exists_smooth_integral_finite_etale_chart
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [Smooth f] [IsIntegral X] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsClosedImmersion (pullback.diagonal f)] :
    ∃ (d n : ℕ) (V : (Spec (.of (MvPolynomial (Fin d) k))).Opens)
      (W : X.Opens) (q : W.toScheme ⟶ V.toScheme),
      1 ≤ n ∧ IsAffineOpen V ∧ Nonempty V ∧ IsAffineOpen W ∧ Nonempty W ∧
      Dense (W : Set X) ∧ IsFinite q ∧ Etale q ∧ Surjective q ∧
      q ≫ V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin d) k))) =
        W.ι ≫ f ∧
      q.IsFiniteLocallyFreeOfDegree n ∧
      Smooth (W.ι ≫ f) ∧ IsIntegral W.toScheme ∧
      LocallyOfFiniteType (W.ι ≫ f) ∧ QuasiCompact (W.ι ≫ f) ∧
      Smooth (V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin d) k)))) ∧
      IsIntegral V.toScheme ∧
      LocallyOfFiniteType
        (V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin d) k)))) ∧
      QuasiCompact
        (V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin d) k)))) ∧
      ∀ v : Spec (.of k) ⟶ V.toScheme,
        v ≫ V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin d) k))) =
          𝟙 (Spec (.of k)) →
        ∃ a : Fin n → (Spec (.of k) ⟶ pullback q v),
          Nonempty (IsColimit (Cofan.mk (pullback q v) a)) ∧
          (∀ i : Fin n, a i ≫ pullback.snd q v = 𝟙 (Spec (.of k))) ∧
          Function.Injective
            (fun i : Fin n ↦ (a i ≫ pullback.fst q v) (IsLocalRing.closedPoint k)) ∧
          Set.range
            (fun i : Fin n ↦ (a i ≫ pullback.fst q v) (IsLocalRing.closedPoint k)) =
            {x : W.toScheme | q x = v (IsLocalRing.closedPoint k)} := by
  sorry

end AlgebraicGeometry
