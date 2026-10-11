/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.GenericFibre

/-!
# The data of the spreading theorem

The structure `AlgebraicGeometry.Scheme.SpreadingDatum` bundles the hypotheses of the spreading
theorem of blueprint `sbc-thm-spreading-finite-etale-galois` ([Stacks 0EZJ]): a qcqs integral
normal scheme `S`, a qcqs smooth morphism `c : C ⟶ S` with geometrically connected fibres and a
section `σ`, a finite group `G` of order invertible on `S`, the generic fibre `j : C_η ⟶ C` and a
Galois cover `Z` of `C_η` with group `G` having a `κ(η)`-rational point over `σ(η)`.

The proof of the spreading theorem shows that the relative normalization
`ν.normalization ⟶ C` of `C` in `ν = Z.π ≫ j : Z.P ⟶ C` is étale. To organise the induction
over the points of `S`, `AlgebraicGeometry.Scheme.SpreadingDatum.EtaleOver D s` says that the
normalization is étale in a neighbourhood of every point lying over `s ∈ S`, and
`AlgebraicGeometry.Scheme.SpreadingDatum.EtaleOverSection D s` that it is so at every point lying
over `σ(s) ∈ C`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (G : Type (u + 1)) [Group G] [Finite G]

/-- The data and hypotheses of the spreading theorem (blueprint
`sbc-thm-spreading-finite-etale-galois`, [Stacks 0EZJ]); see
`AlgebraicGeometry.Scheme.GaloisCover.exists_isPullback_of_genericFibre`. -/
structure SpreadingDatum where
  /-- the base -/
  S : Scheme.{u}
  [compactSpace : CompactSpace S]
  [quasiSeparatedSpace : QuasiSeparatedSpace S]
  [isIntegral : IsIntegral S]
  /-- the base is normal -/
  isIntegrallyClosed_stalk (x : S) : IsIntegrallyClosed (S.presheaf.stalk x)
  /-- the total space of the smooth family -/
  C : Scheme.{u}
  /-- the smooth family -/
  c : C ⟶ S
  [quasiCompact : QuasiCompact c]
  [quasiSeparated : QuasiSeparated c]
  [smooth : Smooth c]
  [geometricallyConnected : GeometricallyConnected c]
  /-- the section -/
  σ : S ⟶ C
  σ_c : σ ≫ c = 𝟙 S
  /-- the order of the group is invertible on the base -/
  isUnit_card : IsUnit (Nat.card G : Γ(S, ⊤))
  /-- the generic fibre -/
  Cη : Scheme.{u}
  /-- the generic fibre lies over the generic point -/
  q : Cη ⟶ Spec S.functionField
  /-- the inclusion of the generic fibre -/
  j : Cη ⟶ C
  isPullback : IsPullback q j S.fromSpecFunctionField c
  /-- the generic point of the section -/
  sη : Spec S.functionField ⟶ Cη
  sη_q : sη ≫ q = 𝟙 _
  sη_j : sη ≫ j = S.fromSpecFunctionField ≫ σ
  /-- the Galois cover of the generic fibre -/
  Z : GaloisCover G Cη
  exists_point : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη

namespace SpreadingDatum

attribute [instance] compactSpace quasiSeparatedSpace isIntegral quasiCompact quasiSeparated
  smooth geometricallyConnected

variable {G} (D : SpreadingDatum G)

instance : QuasiCompact D.j := MorphismProperty.of_isPullback D.isPullback inferInstance

instance : QuasiSeparated D.j := MorphismProperty.of_isPullback D.isPullback inferInstance

instance : IsFinite D.Z.π := D.Z.isFinite

instance : Etale D.Z.π := D.Z.etale

/-- The morphism `Z.P ⟶ C_η ⟶ C` along which `C` is normalized. -/
abbrev ν : D.Z.P ⟶ D.C := D.Z.π ≫ D.j

/-- The relative normalization of `C` in `Z.P` is étale over `C` in a neighbourhood of every
point lying over `s ∈ S`. -/
def EtaleOver (s : D.S) : Prop :=
  ∀ x : D.ν.normalization, D.c (D.ν.fromNormalization x) = s →
    ∃ U : D.ν.normalization.Opens, x ∈ U ∧ Etale (U.ι ≫ D.ν.fromNormalization)

/-- The relative normalization of `C` in `Z.P` is étale over `C` in a neighbourhood of every
point lying over `σ(s) ∈ C`. -/
def EtaleOverSection (s : D.S) : Prop :=
  ∀ x : D.ν.normalization, D.ν.fromNormalization x = D.σ s →
    ∃ U : D.ν.normalization.Opens, x ∈ U ∧ Etale (U.ι ≫ D.ν.fromNormalization)

end SpreadingDatum

/-- A point of an irreducible scheme other than the generic point has positive codimension. -/
lemma coheight_ne_zero_of_ne_genericPoint {X : Scheme.{u}} [IrreducibleSpace X] (s : X)
    (hs : s ≠ genericPoint X) : Order.coheight s ≠ 0 := by
  rw [Ne, Order.coheight_eq_zero, not_isMax_iff]
  refine ⟨genericPoint X, lt_of_le_not_ge ?_ fun h ↦ hs ?_⟩
  · exact Scheme.le_iff_specializes.2 ((genericPoint_spec X).specializes (Set.mem_univ s))
  · exact Inseparable.eq <| (Scheme.le_iff_specializes.1 h).antisymm
      ((genericPoint_spec X).specializes (Set.mem_univ s))

end AlgebraicGeometry.Scheme
