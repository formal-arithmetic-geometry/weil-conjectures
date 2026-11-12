/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedBaseChangeMap

/-!
# Proper base change for complete complexes

Let `f : X ⟶ Y` be proper, `g : Y' ⟶ Y` any morphism and `f' : X' ⟶ Y'`, `g' : X' ⟶ X` the
projections of a cartesian square. Let `K` be a derived complete complex of modules over the
completed coefficient ring of an adic coefficient datum `d` (for instance `𝒪_E`), with reductions
`K_n = K ⊗ᴸ A/Iⁿ⁺¹`. This file records blueprint `proposition-proper-base-change-complete-integral`:

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedPullPushIso`: the canonical isomorphism
  `ĝ^* Rf_* K ≅ R lim_n g^* Rf_* K_n` (clause `--2`);
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.pushCompletedPullIso`: the canonical isomorphism
  `Rf'_* ĝ'^* K ≅ R lim_n Rf'_* g'^* K_n` (clause `--3`);
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedExchange_eq`: under these isomorphisms
  the completed base change map is the derived limit of the tower of base change maps
  `g^* Rf_* K_n ⟶ Rf'_* g'^* K_n`;
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.isIso_completedBaseChangeMap`: it is an
  isomorphism `ĝ^* Rf_* K ≅ Rf'_* ĝ'^* K` when each `K_n` is bounded below of étale origin
  (clause `--4`).

The completed pullback `ĝ^*` is by definition `R lim_n g^* K_n`
(`AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedPull`). Clause `--1` (completeness of
`Rf_* K` and the identification of its reductions) is
`AlgebraicGeometry.ProEtale.internal_integral_direct_image_limits`; in the present framework the
identification of the reductions is the tower projection
`AlgebraicGeometry.Scheme.AdicCoefficientDatum.towerProjection`.
-/

@[expose] public noncomputable section

universe t

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

variable (f g) in
/-- Blueprint `proposition-proper-base-change-complete-integral--2`: the canonical isomorphism
`ĝ^* Rf_* K ≅ R lim_n g^* Rf_* K_n`. The completed pullback `ĝ^* Rf_* K` is `R lim_n` of `g^*`
of the reduction tower of `Rf_* K`, and that tower is identified with the tower `Rf_* K_n` of
direct images of the reductions of `K` by the tower projection. -/
def AdicCoefficientDatum.completedPullPushIso (K : d.derived X) :
    (d.completedPull g).obj ((d.push f).obj K) ≅
      (completedRlim Y' (d.completedRing Y')).obj
        ((d.towerPull g).obj ((d.towerPush f).obj ((completedReductionTower X d).obj K))) :=
  (completedRlim Y' (d.completedRing Y')).mapIso
    ((d.towerPull g).mapIso (asIso (d.towerProjection f K)))

variable (g' f') in
/-- Blueprint `proposition-proper-base-change-complete-integral--3`: the canonical isomorphism
`Rf'_* ĝ'^* K ≅ R lim_n Rf'_* g'^* K_n`. The completed pullback `ĝ'^* K` is `R lim_n g'^* K_n`,
and the direct image `Rf'_*` commutes with derived limits of towers
(`AlgebraicGeometry.Scheme.AdicCoefficientDatum.directImageRlimIso`). -/
def AdicCoefficientDatum.pushCompletedPullIso (K : d.derived X) :
    (d.push f').obj ((d.completedPull g').obj K) ≅
      (completedRlim Y' (d.completedRing Y')).obj
        ((d.towerPush f').obj ((d.towerPull g').obj ((completedReductionTower X d).obj K))) :=
  (d.directImageRlimIso f').app ((d.towerPull g').obj ((completedReductionTower X d).obj K))

variable (sq : ChosenCartesianSquare g' f' f g)

/-- Under the isomorphisms `ĝ^* Rf_* K ≅ R lim_n g^* Rf_* K_n` and
`Rf'_* ĝ'^* K ≅ R lim_n Rf'_* g'^* K_n`, the completed base change map is the derived limit of
the tower of base change maps `g^* Rf_* K_n ⟶ Rf'_* g'^* K_n`
(`AlgebraicGeometry.Scheme.AdicCoefficientDatum.towerV'`). -/
lemma AdicCoefficientDatum.completedExchange_eq (K : d.derived X) :
    d.completedExchange sq K = (d.completedPullPushIso f g K).hom ≫
      (completedRlim Y' (d.completedRing Y')).map (d.towerV' sq K) ≫
        (d.pushCompletedPullIso g' f' K).inv :=
  rfl

/-- **Finite-level proper base change for the tower of reductions.** For `f` proper and `K`
whose reductions `K_n` are bounded below of étale origin, the tower of base change maps
`g^* Rf_* K_n ⟶ Rf'_* g'^* K_n` is an isomorphism of derived towers: each of its levels is the
base change map of the finite coefficient ring `A/Iⁿ⁺¹` at `K_n`, an isomorphism by proper base
change for torsion coefficients
(`AlgebraicGeometry.Scheme.AdicCoefficientDatum.finiteExchange_isIso`), and a map of derived
towers which is levelwise an isomorphism is an isomorphism. This is the first step of the proof of
blueprint `proposition-proper-base-change-complete-integral--4`. -/
theorem AdicCoefficientDatum.isIso_towerV' [IsProper f] (K : d.derived X)
    (_W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    IsIso (d.towerV' sq K) := by
  sorry

/-- Blueprint `proposition-proper-base-change-complete-integral--4`: **proper base change for
complete complexes.** For `f` proper, `K` derived complete whose reductions `K_n` are bounded
below of étale origin, the completed base change map `ĝ^* Rf_* K ⟶ Rf'_* ĝ'^* K`, which is the
derived limit of the base change maps `g^* Rf_* K_n ⟶ Rf'_* g'^* K_n` under the isomorphisms of
`AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedExchange_eq`, is an isomorphism. -/
theorem AdicCoefficientDatum.isIso_completedBaseChangeMap [IsProper f] (K : d.derived X)
    (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    IsIso (d.completedBaseChangeMap sq K hK W) := by
  have := d.isIso_towerV' sq K W
  change IsIso (d.completedExchange sq K)
  rw [d.completedExchange_eq sq K]
  infer_instance

end AlgebraicGeometry.Scheme
