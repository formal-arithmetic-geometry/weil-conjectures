/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison

import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerIsomorphismSections
import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicRestrictedTower
import WeilConjectures.AlgebraicGeometry.Finite.FiniteLisseTowerSectionCover

/-! # Compatible markings for a supplied algebraic stalk tower

Source: Stacks Project, proetale.tex, Tags 09BV and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso pbcDerivedRestrict constantAdicFiniteProjection

/-- Separate local markings of a fixed normalized finite algebraic tower can be
chosen compatibly on a common pro-etale cover. The tower K, its bounds and its
normalization arrows are inputs; this theorem constructs only compatible markings.
There is no Noetherian or immersion hypothesis.

Source: Stacks Project, proetale.tex, Tag 09BV (lemma-weird), the inverse system of
isomorphism sheaves and its stable images; Tag 09C6 (lemma-connected-adic-lisse),
compatibility of finite reductions.
(blueprint: lem-weil-pbc-lisse-tower-compatible-stalk-markings).

Proof: work in the localized pro-etale site over U and identify it with the site of
U.left. Transport finite constant coefficients through the canonical inverse-image
and constant-ring comparisons. Separate markings identify every level locally
with the supplied bounded finite algebraic K. Thus the derived isomorphism sheaf
at each level is finite locally constant with nonempty geometric stalks, by finite
ring derived local constancy. Universality of t and of M's normalization arrows
defines reduction on these sheaves by taking the adjoint of scalar extension.
At each stalk the images of later levels stabilize, because the sets are finite;
the stable images are nonempty and have surjective consecutive maps. Represent
these finite locally constant sheaves on affine etale charts by finite etale
schemes. Their affine inverse limits are weakly etale and jointly surjective,
by the nonempty inverse limits of the stable stalk images. Refine by weakly
contractible affines to evaluate the derived isomorphism sheaves. The compatible
sections give actual b and the consecutive normalization squares. The
identity-on-constant-sections quotient comparison sends these squares to the
specified C-linear arrows s. Coefficient restriction composition and inverse image
composition are the canonical sectionwise identity maps, hence satisfy their
associativity and identity laws after localization. Compose consecutive squares
using those laws and M.cocycle; induction on m-n gives exactly the displayed
all-pairs equation, with the identity case supplied by the identity normalization.
Generate a covering sieve in the localized site and restrict the compatible
markings along all its arrows. Empty U uses the empty cover. Zero levels have
singleton isomorphism stalks and require no exception. -/
theorem lisse_tower_compatible_stalk_markings
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (U : Y.ProEt)
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u + 1}
      (AdicCompletion d.ideal A ⧸
        (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (t : ∀ n : ℕ, K (n + 1) ⟶
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right
          (I := d.ideal.map (algebraMap A (AdicCompletion d.ideal A)))
          (Nat.le_succ (n + 1))))).mapDerivedCategory.obj
          (K n))
    (huniversal : ∀ (n : ℕ) (N : DerivedCategory (ModuleCat.{u + 1}
        (AdicCompletion d.ideal A ⧸
          (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))),
      Function.Bijective (fun k : K n ⟶ N ↦ t n ≫
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right
            (I := d.ideal.map (algebraMap A (AdicCompletion d.ideal A)))
            (Nat.le_succ (n + 1))))).mapDerivedCategory.map
            k))
    (hbounded : ∀ n : ℕ, ∃ a b : ℤ, ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (K n)))
    (hfinite : ∀ (n : ℕ) (q : ℤ), Module.Finite
      (AdicCompletion d.ideal A ⧸
          (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
          (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))) q).obj (K n)))
    (hmodels : ∀ n : ℕ, ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj (K n) ≅
          (adicTowerPullback (W.hom ≫ g)
            ((pbcAdicRings X d).obj (op n))).obj (M.level n))) :
    let C := AdicCompletion d.ideal A
    let J := d.ideal.map (algebraMap A C)
    let R (n : ℕ) := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (Ideal.Quotient.mk (J ^ (n + 1)))
    let s (n : ℕ) := (R (n + 1)).mapDerivedCategory.map (t n) ≫
      (Functor.mapDerivedCategoryCompIso
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1)))))
        (R (n + 1))).symm.inv.app (K n) ≫
      (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp'.{u + 1}
        (Ideal.Quotient.mk (J ^ (n + 2)))
        (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))
        (Ideal.Quotient.mk (J ^ (n + 1)))
        (Ideal.Quotient.factor_comp_mk _).symm)).inv.app (K n)
    ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
      ∃ b : ∀ n : ℕ,
          (constantAdicQuotientRealization (W.hom ≫ g) d n).obj (K n) ≅
            (adicTowerPullback (W.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj
              (M.level n),
        let a := constantAdicFiniteRealization (W.hom ≫ g) d
        let H (n : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d n)
        let z (n : ℕ) :=
          (constantAdicQuotientRightIso (W.hom ≫ g) d n).hom.app (K n) ≫
            (H n).map (b n).hom
        ∀ (m n : ℕ) (h : n ≤ m),
          z m ≫ (H m).map (adicTowerRestrictedTransition d (W.hom ≫ g) M m n h) ≫
            (pbcDerivedRestrictComp
              (constantAdicFiniteProjection (W.hom ≫ g) d m)
              ((adicTowerInverseImage (W.hom ≫ g)).map (pbcAdicQuotient X d m n h))
              (constantAdicFiniteProjection (W.hom ≫ g) d n)
              (constantAdicFiniteProjection_comp (W.hom ≫ g) d m n h)).hom.app
                ((adicTowerPullback (W.hom ≫ g)
                  ((pbcAdicRings X d).obj (op n))).obj (M.level n)) =
            a.map ((Functor.ofOpSequence
              (X := fun k : ℕ ↦ (R k).mapDerivedCategory.obj (K k)) s).map
                (homOfLE h).op) ≫ z n := by
  classical
  intro C J R s
  obtain ⟨I, r, ev, hI, hne, hred⟩ :=
    lisse_tower_isomorphism_sections X Y g d M U K t huniversal hbounded hfinite hmodels
  obtain ⟨ι, V, hcov, ha, hw, v, hv⟩ :=
    finite_lisse_tower_section_cover U.left I r hI hne
  let Z (i : ι) : Y.ProEt := ProEt.mk ((V i).hom ≫ U.hom)
  let f (i : ι) : Z i ⟶ U := MorphismProperty.Over.homMk (V i).hom rfl
  refine ⟨Sieve.ofArrows Z f, ?_, ?_⟩
  · apply ProEt.mem_topology_iff.mpr
    refine ⟨Presieve.ofArrows Z f, ?_, Sieve.le_generate _⟩
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact hcov
  · intro W w hw'
    obtain ⟨i, a, _⟩ := (Sieve.mem_ofArrows_iff Z f w).mp hw'
    let b (n : ℕ) := ev (V i) (ha i) (hw i) W a n (v i n)
    refine ⟨b, ?_⟩
    intro a₀ H z
    let F := Functor.ofOpSequence
      (X := fun n : ℕ ↦ (R n).mapDerivedCategory.obj (K n)) s ⋙ a₀
    let N := constantAdicRestrictedTower (W.hom ≫ g) d M
    let α : F ⟶ N := NatTrans.ofOpSequence (F := F) (G := N) z (by
      intro n
      have h := hred (V i) (ha i) (hw i) W a n (v i (n + 1))
      dsimp only at h
      rw [hv i n] at h
      simpa only [F, N, Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ,
        constantAdicRestrictedTower, constantAdicRestrictedStep, b, z, H, a₀,
        Category.assoc] using h.symm)
    intro m n h
    have hn := α.naturality (homOfLE h).op
    change _ ≫ z n = z m ≫ N.map (homOfLE h).op at hn
    rw [constantAdicRestrictedTower_map] at hn
    exact hn.symm

end AlgebraicGeometry.Scheme
