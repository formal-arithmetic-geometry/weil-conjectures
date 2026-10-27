/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Bounded unramified points and local Néron models

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 1.1 Definition 2 and 1.3 Theorem 1
(blueprint: lem-sfb-bounded-group-local-neron-criterion).

Boundedness is written out using finite affine charts and their generating lists.
Mathlib's multiplicative valuation sends a uniformizer to `exp (-1)` and zero to zero:
its upper bound `exp (-c)` is the additive lower bound `c`, including at zero.
The field map to the fraction ring of the strict henselization is pinned by its
restriction to the base ring, hence is the unique extension of that canonical map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Bounded points over the strict henselian fraction field give a finite-type local
Néron model. The domain and DVR structures in the boundedness witness express the
DVR whose valuation the informal hypothesis uses; they are not assumptions on `R`.
The charts are spectra of commutative `E`-algebras, and the sets `C i` cover all points,
not merely the points lying in one fixed affine chart.

Source: BLR 1.1 Definition 2, 1.3 Theorem 1, and 1.2 Definition 1
(blueprint: lem-sfb-bounded-group-local-neron-criterion).

Proof:
1. Apply `lem-sfb-bounded-group-translation-model` to these coordinate lower bounds.
   It gives a smooth separated finite-type model `Y`, with nonempty special fibre,
   on which translations extend birationally over the indicated local DVRs.
2. Spread the universal left and right translations by
   `lem-sfb-smooth-trait-local-rational-spreading`. Smooth base change
   (`lem-pc-proper-base-change`) and composition (`lem-trf-smooth-composition`)
   give the required smooth products. Generic-fibre uniqueness identifies the
   two multiplications and proves associativity on their common domains.
3. Apply `lem-sfb-trait-birational-group-envelope` to obtain a smooth separated
   finite-type group model `M`, containing `Y` as a fibrewise dense open.
4. For an affine smooth finite-type test scheme `Z` and a generic morphism `a`,
   spread translation by `a` on `Z × M` with the same spreading lemma, first at
   generic points of the special fibre. Fibrewise density survives the local
   DVR base changes by that lemma's final clause.
5. The translation domain contains the generic fibre and all codimension-one
   points. Smoothness implies flatness (`lem-pc-smooth-flat`); a special-fibre
   point outside its generic points has codimension at least two. Apply
   `lem-sfb-relative-weil-codimension-extension` to the smooth source `Z × M`
   and the group `M`. Evaluating the extended translation at the identity gives
   the required extension of `a` to `Z`.
6. Cover an arbitrary smooth test scheme by affine smooth finite-type opens,
   using local finite presentation (`lem-pc-smooth-flat`). Generic-fibre
   uniqueness in the spreading lemma makes the extensions agree on overlaps,
   so they glue. It also proves uniqueness. Thus restriction is bijective.
-/
theorem exists_localNeronModel_of_bounded_strictHenselization_points
    (R E : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field E] [Algebra R E] [IsFractionRing R E]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of R))
    (hs : ∀ z : Spec (.of Ω), (s z).asIdeal = IsLocalRing.maximalIdeal R)
    (G : Over (Spec (.of E))) [GrpObj G]
    [Smooth G.hom] [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (hbounded : ∃ (_ : IsDomain (Scheme.strictHenselizationRing s))
        (_ : IsDiscreteValuationRing (Scheme.strictHenselizationRing s))
        (j : E →+* FractionRing (Scheme.strictHenselizationRing s)),
      j.comp (algebraMap R E) =
        (algebraMap (Scheme.strictHenselizationRing s)
          (FractionRing (Scheme.strictHenselizationRing s))).comp
            (Spec.preimage (Scheme.strictHenselizationStructuralMap s)).hom ∧
      ∃ (n : ℕ) (B : Fin n → CommAlgCat.{u} E)
        (ι : ∀ i : Fin n,
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap E (B i)))) ⟶ G),
        (∀ i : Fin n, IsOpenImmersion (ι i).left) ∧
        (∀ x : G.left, ∃ (i : Fin n) (y : Spec (.of (B i))), (ι i).left y = x) ∧
        ∃ (m : Fin n → ℕ) (b : ∀ i : Fin n, Fin (m i) → B i)
          (C : ∀ i : Fin n,
            Set (Over.mk (Spec.map (CommRingCat.ofHom j)) ⟶
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap E (B i))))))
          (c : Fin n → ℤ),
          (∀ i : Fin n, Algebra.adjoin E (Set.range (b i)) = ⊤) ∧
          (∀ x : Over.mk (Spec.map (CommRingCat.ofHom j)) ⟶ G,
            ∃ (i : Fin n) (y : Over.mk (Spec.map (CommRingCat.ofHom j)) ⟶
                Over.mk (Spec.map (CommRingCat.ofHom (algebraMap E (B i))))),
              y ∈ C i ∧ y ≫ ι i = x) ∧
          ∀ (i : Fin n) (x : Over.mk (Spec.map (CommRingCat.ofHom j)) ⟶
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap E (B i))))),
            x ∈ C i → ∀ k : Fin (m i),
              (IsDiscreteValuationRing.maximalIdeal (Scheme.strictHenselizationRing s)).valuation
                  (FractionRing (Scheme.strictHenselizationRing s))
                  ((Spec.preimage x.left).hom (b i k)) ≤
                ((Multiplicative.ofAdd (-c i) : Multiplicative ℤ) :
                  WithZero (Multiplicative ℤ))) :
    ∃ (M : Over (Spec (.of R)))
      (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R E)))).obj M ≅ G),
      Smooth M.hom ∧ IsSeparated M.hom ∧ LocallyOfFiniteType M.hom ∧ QuasiCompact M.hom ∧
      ∀ (X : Over (Spec (.of R))), Smooth X.hom →
        Function.Bijective (fun f : X ⟶ M ↦
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R E)))).map f ≫ e.hom) := by
  sorry

end AlgebraicGeometry
