module

public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.AlgebraicGeometry.Scheme
import Sheaf.SixFunctors.SemilinearEvaluationRingSquare

/-! # Section-normalized ordinary semilinear evaluation

Source: Stacks Project, Tag 03D7 (lemma-adjoint-pullback-pushforward-modules);
`SemilinearProperOpenMatePasting`, lines 1798--1911, and the constant-diagram lift.
(blueprint: lem-sf-semilinear-evaluation-ordinary-adjunction)

We retain the existing system operations, evaluation, and inverse mate. The statement
records their section, single-level, constant-diagram, unit, and counit normalizations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory Opposite AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen

/-- Ordinary evaluation followed by the constant diagonal commutes with direct image
by the unique identity on sections. Its inverse mate is invertible, is the constant
lift of the unique unit-normalized single-level comparison, and respects both specified
units and counits. No restriction is placed on the coefficient transitions or systems.

Source: Stacks Project, Tag 03D7; the ordinary evaluation argument in
`SemilinearProperOpenMatePasting`, lines 1798--1911.
(blueprint: lem-sf-semilinear-evaluation-ordinary-adjunction)

Proof: (1) The coefficient equation and the section-normalized level comparison of
lem-sf-semilinear-evaluation-ring-square identify both scalar actions on M_n(H times_Y X).
Lift that comparison by the constant-diagram functor. Both directions are the identity
on sections; sectionwise extensionality proves uniqueness as a natural isomorphism.
(2) Apply lem-pe-constant-left-module-inverse-image at each arbitrary ring C_i. Its
constant-ring isomorphism preserves scalars and commutes with the actual transitions.
Applying abelian inverse image to the system transitions therefore constructs a system
functor A with level i canonically f_i^* e_i. The finite-product lifting of
lem-weil-pbc-adjunction-lifts-group-ring-objects justifies applying inverse image to actions.
(3) The Hom bijections of lem-weil-pbc-ringed-topoi-module-adjunction restrict to compatible
families: naturality of the abelian unit sends the transition equation for a family p_i
to the transition equation for its adjuncts h_i; injectivity gives the converse.
Thus A is left adjoint to system direct image and its unit is the specified level unit.
(4) Compare A with the specified left adjoint P by the explicit unit-counit transposes.
Their composites are identities by injectivity of the respective Hom bijections. Evaluating
the resulting isomorphism at n gives b; its displayed unit equation uniquely determines it.
(5) Lift b by the constant diagonal. At each tower index its unit equation is the level
unit equation; hence the inverse mate bijection def-weil-pbc-adjunction-mate identifies
this lift with evalPullInv. This proves invertibility without inferring it merely from
invertibility of the direct-image square. The actual termwise tower pullback makes the
canonical constant-diagram compositors sectionwise identities, giving the equality below.
(6) Transpose the counit equation. Both sides transpose to D_N, using the unit equation,
naturality, and the triangle identities. Injectivity proves the equation. All steps use
actual transitions and every ordinary system morphism; no flatness, finiteness, or
cartesianness is required. -/
theorem semilinearEvaluationOrdinaryAdjunction
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃ D : push C τ f ⋙ levelTower C τ n Y ≅
        levelTower C τ n X ⋙ StrictTower.towerDirectImage (C n) f,
      (∀ (M : Modules C τ X) (m : ℕ) (H : Y.ProEt),
        HEq (fun x ↦ ((D.hom.app M).app (op m)).val.app (op H) x)
          (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj H)) ↦ x)) ∧
      (∀ (M : Modules C τ X) (m : ℕ) (H : Y.ProEt),
        HEq (fun x ↦ ((D.inv.app M).app (op m)).val.app (op H) x)
          (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj H)) ↦ x)) ∧
      (∀ D' : push C τ f ⋙ levelTower C τ n Y ≅
          levelTower C τ n X ⋙ StrictTower.towerDirectImage (C n) f,
        (∀ (M : Modules C τ X) (m : ℕ) (H : Y.ProEt),
          HEq (fun x ↦ ((D'.hom.app M).app (op m)).val.app (op H) x)
            (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj H)) ↦ x)) → D' = D) ∧
      evalPullInv C τ n f =
        ((mateEquiv (ordinaryAdj C τ f)
          ((proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
            (StrictTower.coefficients (C n) X)
            (StrictTower.constantRingIso (C n) f)).whiskerRight ℕᵒᵖ)).symm
              (TwoSquare.mk _ _ _ _ D.hom)).natTrans ∧
      IsIso (evalPullInv C τ n f) ∧
      (∃! b : SemilinearSections.evaluation (ProEt.topology Y)
          (coefficients C Y) (transition C τ Y) n ⋙ StrictTower.modulePullback (C n) f ≅
        pull C τ f ⋙ SemilinearSections.evaluation (ProEt.topology X)
          (coefficients C X) (transition C τ X) n,
        ∀ M : Modules C τ Y,
          (proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
              (StrictTower.coefficients (C n) X)
              (StrictTower.constantRingIso (C n) f)).unit.app
                ((SemilinearSections.evaluation (ProEt.topology Y)
                  (coefficients C Y) (transition C τ Y) n).obj M) ≫
            (StrictTower.moduleDirectImage (C n) f).map (b.hom.app M) =
          (SemilinearSections.evaluation (ProEt.topology Y)
              (coefficients C Y) (transition C τ Y) n).map
                ((ordinaryAdj C τ f).unit.app M) ≫
            (D.hom.app ((pull C τ f).obj M)).app (op 0)) ∧
      (∀ b : SemilinearSections.evaluation (ProEt.topology Y)
          (coefficients C Y) (transition C τ Y) n ⋙ StrictTower.modulePullback (C n) f ≅
        pull C τ f ⋙ SemilinearSections.evaluation (ProEt.topology X)
          (coefficients C X) (transition C τ X) n,
        (∀ M : Modules C τ Y,
          (proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
              (StrictTower.coefficients (C n) X)
              (StrictTower.constantRingIso (C n) f)).unit.app
                ((SemilinearSections.evaluation (ProEt.topology Y)
                  (coefficients C Y) (transition C τ Y) n).obj M) ≫
            (StrictTower.moduleDirectImage (C n) f).map (b.hom.app M) =
          (SemilinearSections.evaluation (ProEt.topology Y)
              (coefficients C Y) (transition C τ Y) n).map
                ((ordinaryAdj C τ f).unit.app M) ≫
            (D.hom.app ((pull C τ f).obj M)).app (op 0)) →
        ∀ (M : Modules C τ Y) (m : ℕ),
          ((evalPullInv C τ n f).app M).app (op m) = b.hom.app M) ∧
      (∀ M : Modules C τ Y,
        ((proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
            (StrictTower.coefficients (C n) X)
            (StrictTower.constantRingIso (C n) f)).whiskerRight ℕᵒᵖ).unit.app
              ((levelTower C τ n Y).obj M) ≫
          (StrictTower.towerDirectImage (C n) f).map ((evalPullInv C τ n f).app M) =
        (levelTower C τ n Y).map ((ordinaryAdj C τ f).unit.app M) ≫
          D.hom.app ((pull C τ f).obj M)) ∧
      (∀ N : Modules C τ X,
        (evalPullInv C τ n f).app ((push C τ f).obj N) ≫
          (levelTower C τ n X).map ((ordinaryAdj C τ f).counit.app N) =
        (StrictTower.towerPullback (C n) f).map (D.hom.app N) ≫
          ((proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
            (StrictTower.coefficients (C n) X)
            (StrictTower.constantRingIso (C n) f)).whiskerRight ℕᵒᵖ).counit.app
              ((levelTower C τ n X).obj N)) := by
  -- The existing normalized mate proves Steps 2–5; recover its level map at index zero.
  obtain ⟨d, ⟨hd, hi⟩, _⟩ := evaluationPush_existsUnique C τ f n
  let D : push C τ f ⋙ levelTower C τ n Y ≅
      levelTower C τ n X ⋙ StrictTower.towerDirectImage (C n) f :=
    NatIso.ofComponents
      (fun M ↦ NatIso.ofComponents (fun _ ↦ d.app M) (by intros; simp))
      (by
        intro M N a
        apply NatTrans.ext
        funext m
        exact d.hom.naturality a)
  have hchosen : (evalPushOrdinary_existsUnique C τ n f).choose = D.symm := by
    symm
    apply (evalPushOrdinary_existsUnique C τ n f).choose_spec.2
    intro M m H
    exact hi M H
  let a := ordinaryAdj C τ f
  let l := proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
    (StrictTower.coefficients (C n) X) (StrictTower.constantRingIso (C n) f)
  have hm : evalPullInv C τ n f =
      ((mateEquiv a (l.whiskerRight ℕᵒᵖ)).symm
        (TwoSquare.mk _ _ _ _ D.hom)).natTrans := by
    unfold evalPullInv
    rw [hchosen]
    rfl
  have hu (M : Modules C τ Y) :
      (l.whiskerRight ℕᵒᵖ).unit.app ((levelTower C τ n Y).obj M) ≫
        (StrictTower.towerDirectImage (C n) f).map ((evalPullInv C τ n f).app M) =
      (levelTower C τ n Y).map (a.unit.app M) ≫ D.hom.app ((pull C τ f).obj M) := by
    rw [hm]
    exact (unit_mateEquiv_symm a (l.whiskerRight ℕᵒᵖ)
      (TwoSquare.mk _ _ _ _ D.hom) M).symm
  have he : IsIso (evalPullInv C τ n f) := evalPullInv_isIso C τ n f
  let b : SemilinearSections.evaluation (ProEt.topology Y)
      (coefficients C Y) (transition C τ Y) n ⋙ StrictTower.modulePullback (C n) f ≅
      pull C τ f ⋙ SemilinearSections.evaluation (ProEt.topology X)
        (coefficients C X) (transition C τ X) n :=
    Functor.isoWhiskerRight (asIso (evalPullInv C τ n f))
      ((CategoryTheory.evaluation ℕᵒᵖ (StrictTower.Modules (C n) X)).obj (op 0))
  have hb (M : Modules C τ Y) :
      l.unit.app ((SemilinearSections.evaluation (ProEt.topology Y)
        (coefficients C Y) (transition C τ Y) n).obj M) ≫
        (StrictTower.moduleDirectImage (C n) f).map (b.hom.app M) =
      (SemilinearSections.evaluation (ProEt.topology Y)
        (coefficients C Y) (transition C τ Y) n).map (a.unit.app M) ≫
        (D.hom.app ((pull C τ f).obj M)).app (op 0) := by
    exact congrArg (fun t ↦ t.app (op 0)) (hu M)
  have hc (M : Modules C τ Y) (m : ℕ) :
      ((evalPullInv C τ n f).app M).app (op m) = b.hom.app M := by
    have h := ((evalPullInv C τ n f).app M).naturality
      (homOfLE (Nat.zero_le m)).op
    simpa [b] using h.symm
  have unique : ∀ b',
      (∀ M : Modules C τ Y,
        l.unit.app ((SemilinearSections.evaluation (ProEt.topology Y)
          (coefficients C Y) (transition C τ Y) n).obj M) ≫
          (StrictTower.moduleDirectImage (C n) f).map (b'.hom.app M) =
        (SemilinearSections.evaluation (ProEt.topology Y)
          (coefficients C Y) (transition C τ Y) n).map (a.unit.app M) ≫
          (D.hom.app ((pull C τ f).obj M)).app (op 0)) → b' = b := by
    intro b' hb'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (l.homEquiv _ _).injective
    exact ((l.homEquiv_unit _ _ _).trans ((hb' M).trans (hb M).symm)).trans
      (l.homEquiv_unit _ _ _).symm
  refine ⟨D, ?_, ?_, ?_, hm, he, ⟨b, hb, unique⟩, ?_, hu, ?_⟩
  · intro M m H
    exact hd M H
  · intro M m H
    exact hi M H
  · intro D' hD'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext m
    ext H x
    exact congrFun (eq_of_heq
      ((hD' M m.unop H.unop).trans (hd M H.unop).symm)) x
  · intro b' hb' M m
    rw [unique b' hb']
    exact hc M m
  · intro N
    rw [hm]
    exact (mateEquiv_counit_symm a (l.whiskerRight ℕᵒᵖ)
      (TwoSquare.mk _ _ _ _ D.hom) N).symm

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
