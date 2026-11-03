/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.Defs
public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.WeilSheaf.RankOneThomFiniteFibre
public import WeilConjectures.WeilSheaf.RankOneThomIntegralClass

/-!
# Rank-one Thom map on sheaf objects

The integral divisor class of the zero section is compatible with reduction modulo the
uniformizer.  The finite-fibre calculation identifies its reduction with compactly supported
cohomology of the affine line, and derived completeness then makes the natural Thom map
`P(-1)[-2] ⟶ Rπ_! π^* P` invertible on the complexes arising from Weil sheaves.  The
remaining dévissage from sheaf objects to arbitrary bounded complexes is recorded separately.

Source: latest blueprint `thm-pur-rank-one-thom`, Steps 1--4.
(blueprint: lem-pur-rank-one-native-sheaf-thom)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- The integral reduction and finite-fibre route supplies the Thom transformation
`σ : P(-1)[-2] ⟶ Rπ_! π^* P`, invertible on objects coming from Weil sheaves.  It points in the
direction of the class: no inverse, and no dévissage of a general complex, is used here.

Proof in words.  The integral class construction
(`WeilComplex.exists_rankOneThom_integral_class`) gives a shift-compatible `σ` whose
degree-two homology map on every sheaf object is an isomorphism.  Away from degree two both
endpoints have zero homology (`WeilComplex.rankOneThom_offDegree_zero`), so every homology map
of `σ_P` is an isomorphism, and homology detects isomorphisms in the derived category.
(blueprint: lem-pur-rank-one-native-sheaf-thom)
-/
theorem WeilComplex.exists_rankOneThom_on_toComplex
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (π : Y ⟶ X) (s : Y ⟶ affineLine k₀)
    [π.IsOver (Spec (CommRingCat.of k₀))]
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    ∃ (σ : WeilComplex.tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ) ⟶
        WeilComplex.upperStar π ⋙ WeilComplex.derivedLowerShriek k₀ l π),
      NatTrans.CommShift σ ℤ ∧ ∀ P : WeilSheaf k₀ l X,
        IsIso (σ.app ((WeilSheaf.toComplex (k₀ := k₀) (l := l) (X := X)).obj P)) := by
  obtain ⟨σ, hσ, h₂⟩ := WeilComplex.exists_rankOneThom_integral_class
    (k₀ := k₀) (l := l) π s hπ
  have hσiso : ∀ P : WeilSheaf k₀ l X, IsIso (σ.app (WeilSheaf.toComplex.obj P)) := by
    intro P
    have hm : IsIso ((WeilComplex.objectProperty k₀ l X).ι.map
        (σ.app (WeilSheaf.toComplex.obj P))) := by
      apply (_root_.DerivedCategory.isIso_iff _ _).2
      intro r
      by_cases hr : r = 2
      · subst r
        have h₂P : IsIso ((WeilComplex.homologySheaf (2 : ℤ)).map
            (σ.app (WeilSheaf.toComplex.obj P))) := h₂ P
        exact (WeilSheaf.objectProperty k₀ l X).ι.map_isIso
          ((WeilComplex.homologySheaf (2 : ℤ)).map
            (σ.app (WeilSheaf.toComplex.obj P)))
      · obtain ⟨hs, ht⟩ := WeilComplex.rankOneThom_offDegree_zero
          (k₀ := k₀) (l := l) π s hπ P hr
        have hzero : IsIso ((WeilComplex.homologySheaf r).map
            (σ.app (WeilSheaf.toComplex.obj P))) :=
          ht.isIso hs ((WeilComplex.homologySheaf r).map
            (σ.app (WeilSheaf.toComplex.obj P)))
        exact (WeilSheaf.objectProperty k₀ l X).ι.map_isIso
          ((WeilComplex.homologySheaf r).map
            (σ.app (WeilSheaf.toComplex.obj P)))
    exact @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _
      (WeilComplex.objectProperty k₀ l X).fullyFaithfulι _ _
      (σ.app (WeilSheaf.toComplex.obj P)) hm
  exact ⟨σ, hσ, hσiso⟩

end AlgebraicGeometry
