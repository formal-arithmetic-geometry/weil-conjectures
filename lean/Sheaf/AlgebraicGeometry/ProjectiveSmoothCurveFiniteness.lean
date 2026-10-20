/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.AlgebraicGeometry.GeometricFiberFinite
import WeilConjectures.ConstructibleSheaf.Noetherian
import Sheaf.Paper.ProjectiveCurveBettiCardinalities
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.AlgebraicGeometry.GeometricStalkComparisonConstant
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Constant-coefficient finiteness for projective smooth curves

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc,
thm-fin-projective-smooth-curve-finiteness
(blueprint: thm-fin-projective-smooth-curve-finiteness).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Proper base change for the constant prime-field sheaf, with coefficients forgotten. -/
private theorem constant_prime_stalk_equiv
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) (s : S) :
    Nonempty
      (↥(((Scheme.pointSmallEtale (S.algClosurePoint s)).sheafFiber
        (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
        (Etale.higherDirectImage (ULift.{u + 1} (ZMod ℓ)) f r
          ((constantSheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))))) ≃
      ↥((Etale.cohomology AddCommGrpCat.{u + 1}
        (Limits.pullback f (S.algClosurePoint s)) (r : ℤ)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((Limits.pullback f (S.algClosurePoint s)).constantZMod ℓ)))) := by
  let Λ := ULift.{u + 1} (ZMod ℓ)
  let A := ModuleCat.{u + 1} Λ
  let M := ModuleCat.of Λ Λ
  let F := (constantSheaf X.smallEtaleTopology A).obj M
  have : Limits.PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : Scheme.IsFiniteSheaf F := by
    constructor
    intro Ω _ _ y
    let e := (Scheme.pointSmallEtale y).sheafFiberConstantSheafIso M
    have : Finite (((Scheme.pointSmallEtale y).sheafFiber (A := A)).obj F) :=
      Finite.of_equiv Λ e.toLinearEquiv.toEquiv.symm
    exact (ModuleCat.isFinitelyGenerated_iff _).2 Module.Finite.of_finite
  let y := S.algClosurePoint s
  let Y := Limits.pullback f y
  let G := (constantSheaf Y.smallEtaleTopology A).obj M
  obtain ⟨e₁, e₂, he⟩ := Etale.geometricFiber_finite_stalk_formula
    Λ f (AlgebraicClosure (S.residueField s)) y F r
  let e := asIso (e₁.inv ≫
    (Sheaf.Γ (Spec (.of (AlgebraicClosure (S.residueField s)))).smallEtaleTopology A).map
      (Etale.baseChangeHomologyMap Λ (IsPullback.of_hasPullback f y) r F) ≫
    e₂.hom)
  let c := (Scheme.upperStarConstantSheafIso A (Limits.pullback.fst f y)).app M
  let d := (Etale.cohomology A Y (r : ℤ)).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso c)
  let U := forget₂ A AddCommGrpCat.{u + 1}
  obtain ⟨forgetIso⟩ := Scheme.nonempty_etaleModuleCohomology_forgetIso Y Λ r
  have : Y.smallEtaleTopology.PreservesSheafification U := by
    apply GrothendieckTopology.instPreservesSheafification
  let cAb := (constantCommuteCompose Y.smallEtaleTopology U).app M
  let HAb := DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    0 ⋙ Etale.cohomology AddCommGrpCat.{u + 1} Y (r : ℤ)
  exact ⟨(U.mapIso (e ≪≫ d) ≪≫ forgetIso.app G ≪≫
    HAb.mapIso cAb).addCommGroupIsoToAddEquiv.toEquiv⟩

/-- Higher direct images of the constant prime field sheaf under a smooth projective
relative curve over a Noetherian scheme are constructible as module sheaves.

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc,
thm-fin-projective-smooth-curve-finiteness
(blueprint: thm-fin-projective-smooth-curve-finiteness).

Proof:
1. Projectivity implies properness (lem-pc-projective-proper). The constant sheaf
with value the prime field is finite over the finite coefficient ring.
2. Proper base change (cor-weil-pbc-geometric-fiber-finite) identifies each geometric
stalk of the degree-r higher direct image with degree-r cohomology of the geometric
fibre with constant prime field coefficients. Pullback preserves constant sheaves.
3. Apply lem-fin-projective-curve-betti-cardinalities: these cohomology groups are
finite and their cardinality level sets are constructible, since the morphism is
smooth projective of relative dimension one and the prime is invertible on the base.
4. Apply fin4-lem-stalk-constructibility-criterion to obtain a finite locally closed
constructible partition on which the abelian sheaf is finite locally constant.
The additive trivializations are prime-field linear: multiplication by a residue
class modulo the prime is repeated addition. This gives module constructibility
in every degree r. -/
theorem isConstructibleEtaleModuleSheaf_higherDirectImage_constant_of_projective_smooth_curve
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S)
    [IsProjective f] [SmoothOfRelativeDimension 1 f]
    (ℓ : ℕ) [Fact ℓ.Prime] (hinv : IsUnit (ℓ : Γ(S, ⊤))) (r : ℕ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
        (r : ℤ)).obj
        ((Etale.rightDerivedLowerStarPlus
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
            0).obj
            ((constantSheaf X.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
              (ModuleCat.of (ULift.{u + 1} (ZMod ℓ)) (ULift.{u + 1} (ZMod ℓ))))))) := by
  let Λ := ULift.{u + 1} (ZMod ℓ)
  let F := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (ModuleCat.of Λ Λ)
  let H := Etale.higherDirectImage Λ f r F
  have hinvres (s : S) : (ℓ : S.residueField s) ≠ 0 := by
    simpa using (hinv.map (S.Γevaluation s).hom).ne_zero
  obtain ⟨b, hb, -, hloci⟩ := projective_curve_betti_cardinalities
    f ℓ (Fact.out : ℓ.Prime) hinvres
  have hcard (s : S) : Cardinal.mk
      (((Scheme.pointSmallEtale (S.algClosurePoint s)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj H) = b r s := by
    obtain ⟨e⟩ := constant_prime_stalk_equiv f ℓ r s
    exact (Cardinal.mk_congr e).trans (hb r s)
  have hfinite (s : S) : Finite
      (((Scheme.pointSmallEtale (S.algClosurePoint s)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj H) :=
    Cardinal.mk_lt_aleph0_iff.mp ((hcard s).symm ▸ Cardinal.natCast_lt_aleph0)
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : Scheme.IsFiniteSheaf H := by
    constructor
    intro Ω _ _ y
    let s := y (IsLocalRing.closedPoint Ω)
    obtain ⟨β, -⟩ := Scheme.exists_geometricStalkComparison_constant
      (Λ := Λ) (S.algClosurePoint s) y (by simp [s])
    have : Finite (((Scheme.pointSmallEtale y).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj H) :=
      @Finite.of_equiv _ _ (hfinite s) (β.app H).toLinearEquiv.toEquiv
    exact (ModuleCat.isFinitelyGenerated_iff _).2 Module.Finite.of_finite
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf H).2
  apply (Scheme.isConstructibleSheaf_iff_isConstructible_card H).2
  intro n _
  have hnat (s : S) : Nat.card
      (((Scheme.pointSmallEtale (S.algClosurePoint s)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj H) = b r s := by
    simpa only [Nat.card, Cardinal.toNat_natCast] using congrArg Cardinal.toNat (hcard s)
  simpa only [hnat] using (hloci r).2 n

end AlgebraicGeometry
