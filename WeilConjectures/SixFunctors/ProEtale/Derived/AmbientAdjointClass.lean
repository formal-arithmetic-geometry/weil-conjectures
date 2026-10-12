/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.CompactSupportCandidate
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension

/-!
# The exceptional adjoint on the bounded comparison class

Let `f : X ⟶ Y` be a morphism admitting a compactification `X ⟶[j] X̄ ⟶[p] Y`, and let `Λ` be a
finite ring. This file collects the statements of blueprint subsection `sk-prop-sf-existence`
about the pro-étale exceptional adjoint relative to the class of bounded below objects of étale
origin:

* the compact-support comparison `Rf_!(c) K ≅ ν_Y^* Rf_!^{ét}(c) G` for a bounded below `K` of
  étale origin with witness `α : ν_X^* G ≅ K`, natural in the witness (blueprint
  `lem-sf-class-compact-support-comparison`).

## Main definitions

- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationWitnessIso`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section CompactSupportComparison

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Blueprint `lem-sf-class-compact-support-comparison`: On the coefficient class the
compact-support functor is computed on the étale site.

Let `c = (X ⟶[j] X̄ ⟶[p] Y)` be a compactification of `f`, let `G` be a bounded below complex of
étale sheaves on `X` and let `K` be a pro-étale complex of étale origin with witness
`α : ν_X^* G ≅ K`. Then the pro-étale compact-support functor `Rf_!(c) = Rp_* j_!` attached to
`c` satisfies `Rf_!(c) K ≅ ν_Y^* (Rf_!^{ét}(c) G)`, where `Rf_!^{ét}(c) = Rp_{ét,*} j^{ét}_!` is
the étale compact-support functor attached to the same compactification. It is the
compact-support comparison `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationComparisonIso`
(the identification of the two extensions by zero, followed by the comparison direct image for
the proper `p`) precomposed with `Rf_!(c) α⁻¹`; it is natural in the witness
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationWitnessIso_naturality`). No
constructibility is used. -/
noncomputable def rightDerivedLowerShriekOfCompactificationWitnessIso (c : Compactification f)
    {G : DerivedCategory (Sheaf X.smallEtaleTopology A)} (hG : DerivedCategory.TStructure.t.plus G)
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (α : D(ν^*(X)[A]).obj G ≅ K) :
    (ProEtale.rightDerivedLowerShriekOfCompactification A c).obj K ≅
      D(ν^*(Y)[A]).obj ((Etale.rightDerivedLowerShriekOfCompactification A c).obj G) :=
  (ProEtale.rightDerivedLowerShriekOfCompactification A c).mapIso α.symm ≪≫
    (rightDerivedLowerShriekOfCompactificationComparisonIso A c).app ⟨G, hG⟩

/-- The compact-support comparison of
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationWitnessIso` is natural in the
witness: for a morphism of witnesses, given by `g : G ⟶ G'` and `k : K ⟶ K'` with
`α ≫ k = ν^* g ≫ α'`, the comparison isomorphisms intertwine `Rf_!(c) k` and
`ν^* Rf_!^{ét}(c) g`. -/
lemma rightDerivedLowerShriekOfCompactificationWitnessIso_naturality (c : Compactification f)
    {G G' : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hG : DerivedCategory.TStructure.t.plus G) (hG' : DerivedCategory.TStructure.t.plus G')
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (α : D(ν^*(X)[A]).obj G ≅ K) (α' : D(ν^*(X)[A]).obj G' ≅ K') (g : G ⟶ G') (k : K ⟶ K')
    (h : α.hom ≫ k = D(ν^*(X)[A]).map g ≫ α'.hom) :
    (ProEtale.rightDerivedLowerShriekOfCompactification A c).map k ≫
        (rightDerivedLowerShriekOfCompactificationWitnessIso A c hG' α').hom =
      (rightDerivedLowerShriekOfCompactificationWitnessIso A c hG α).hom ≫
        D(ν^*(Y)[A]).map ((Etale.rightDerivedLowerShriekOfCompactification A c).map g) := by
  have hn := (rightDerivedLowerShriekOfCompactificationComparisonIso A c).hom.naturality
    (X := ⟨G, hG⟩) (Y := ⟨G', hG'⟩) (ObjectProperty.homMk g)
  have hk : k ≫ α'.inv = α.inv ≫ D(ν^*(X)[A]).map g := by
    rw [Iso.eq_inv_comp, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  dsimp at hn
  simp only [rightDerivedLowerShriekOfCompactificationWitnessIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, hk, Functor.map_comp_assoc]
  exact congrArg _ hn

end CompactSupportComparison

end ProEtale

end AlgebraicGeometry
