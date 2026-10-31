/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FinitePullbackStrictTowerData.FinitePullbackStrictTowerData

/-! # Normalized Koszul tower comparison interface

Source: Stacks Project, sites-cohomology.tex, Tag 07A4 and sites-modules.tex, Tag 03EL.
(blueprint: lem-a1-balanced-finite-tower-normalized-theta).

The proof is the ordinary pullback/tensor comparison on the two free Koszul
summands, extended over the sheafified total tensor and its direct sums. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent
open WeilConjectures.FinitePullbackStrictTowerData
open WeilConjectures.CompletedPullbackUniverseTransportData
namespace WeilConjectures.BalancedFiniteTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- The normalized pullback of the principal Koszul tower exists naturally.
Source: Stacks 07A4, displayed total-complex pullback comparison.
(blueprint: lem-a1-balanced-finite-tower-normalized-theta).

Proof: the completed structural map preserves the uniformizer: compose it
with each finite projection, use the constant-coefficient pullback comparison,
and then use the uniqueness of the inverse-limit map. The action unitor on
ordinary module pullback identifies each pulled free rank-one Koszul term
with the target free term. Its formula is a tensor b mapped to c(a)b, with
inverse inserting 1. Uniformizer preservation makes these two maps commute
with multiplication by its (n+1)st power, hence with the cone differential.
The two maps also commute with the transition (uniformizer,1).

Compose the ordinary cochain tensor comparison with identity tensor this
Koszul coefficient isomorphism. Ordinary pullback is a left adjoint, so it
preserves the coproduct over p+q=k. Thus these maps and their inverses exist
on the full unbounded total complex. The differential summands have signs
1 and (-1)^p on both sides: no homogeneous factors are interchanged. On
either basis vector the map sends b times the pullback of x tensor e_q to
(b times the pullback of x) tensor e'_q, which is the displayed formula.
Naturality of the tensor comparison and the action unitor gives naturality
in P. Compatibility with the two transition coordinates gives the displayed
level squares for adjacent arrows; functorial composition gives every arrow
in the opposite natural-number category. These arguments include zero
complexes and the empty site by the same coproduct universal properties. -/
theorem normalized_theta_exists :
    ∃ e : ∀ (P : CochainComplex (Modules l E Y) ℤ) (n : ℕᵒᵖ),
        (((koszuls l E Y ⋙ diagramPull l E g).obj P).obj n) ≅
          (((G l E g ⋙ koszuls l E X).obj P).obj n),
      (∀ (P : CochainComplex (Modules l E Y) ℤ) {n m : ℕᵒᵖ} (f : n ⟶ m),
        ((koszuls l E Y ⋙ diagramPull l E g).obj P).map f ≫ (e P m).hom =
          (e P n).hom ≫ ((G l E g ⋙ koszuls l E X).obj P).map f) ∧
      (∀ (P : CochainComplex (Modules l E Y) ℤ) (n : ℕ) (negative : Bool)
        (p k : ℤ) (hp : p + koszulDegree negative = k) (V : Y.ProEt)
        (x : (P.X p).val.obj (op V))
        (b : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
          (op ((Scheme.proEtaleBaseChange g).obj V))),
        (((e P (op n)).hom.f k).val.app
          (op ((Scheme.proEtaleBaseChange g).obj V)))
          (b • generator l E g (((H l E Y P).obj (op n)).X k) V
            (tensorGenerator l E Y P (PrincipalKoszulStrictReplacement.koszul l E Y n)
              p (koszulDegree negative) k hp (op V) x
              ((koszulBasis l E Y n negative).val.app (op V)
                (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
                  (op V))))) =
        tensorGenerator l E X ((G l E g).obj P)
          (PrincipalKoszulStrictReplacement.koszul l E X n)
          p (koszulDegree negative) k hp (op ((Scheme.proEtaleBaseChange g).obj V))
          (b • generator l E g (P.X p) V x)
          ((koszulBasis l E X n negative).val.app
            (op ((Scheme.proEtaleBaseChange g).obj V))
            (1 : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
              (op ((Scheme.proEtaleBaseChange g).obj V))))) ∧
      (∀ {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P') (n : ℕᵒᵖ),
        ((koszuls l E Y ⋙ diagramPull l E g).map f).app n ≫ (e P' n).hom =
          (e P n).hom ≫ ((G l E g ⋙ koszuls l E X).map f).app n) := by sorry

end WeilConjectures.BalancedFiniteTower
