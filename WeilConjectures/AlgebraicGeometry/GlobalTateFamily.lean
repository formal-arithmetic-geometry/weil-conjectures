/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerChartData
import all WeilConjectures.AlgebraicGeometry.TowerOperationsGroundFieldRetagging
import WeilConjectures.AlgebraicGeometry.SignedLineScalarTensorTower
import WeilConjectures.AlgebraicGeometry.ScalarExtensionDualTowerCore
import WeilConjectures.CategoryTheory.SystemRingedSequenceSite

/-! # A global normalized Tate-tower family

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
 sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gluing.proof.md,
Local pairs (blueprint: lem-sp-global-tate-family).

The theorem records the simultaneous normalized Tate tower on every scheme where the
prime `l` is invertible.  It uses the concrete constant-scalar quotient construction,
the scalar-extension tower isomorphism, the signed-line normalization data and the
strict sequence-site equivalence.  No assertion about compact support, graph
comparisons, smooth right adjoints, or a map to `k` is part of this statement; the
identification of the finite first lines with the Kummer lines is a property of
the fixed finite lines, not a field of `Twists`, and is not used here.

Proof plan:

1. On each scheme `T` where `l` is a global unit, map the unit through the germ of
   global sections and the residue map: `l` is invertible in every residue field.
2. Every finite first line `spEllTwistOne` has a cover by unit trivializations
   (`ellTwist_cover`: the DVR factorization `l = u * pi^e` identifies the `l`-power
   and uniformizer ideals, so the locally-free finite-line theorem applies).
3. The constant quotient maps satisfy `q_(n+1) ≫ tau_n = q_n`.  The
   scalar-extension tower isomorphism, transported along this equality, is the
   exponent-one comparison `s ⊗ (t ⊗ x) ↦ s tau_n(t) ⊗ x`.
4. The signed-line comparison theorem, applied to `tau_n`, the two first lines, their
   unit covers and this exponent-one isomorphism, gives normalized comparisons for all
   signed powers; its exponent-one component is the one of step 3.
5. For each `r ≥ 0`, the adjacent transitions `spEllTwistTransition` define an inverse
   sequence of abelian presheaves (`Functor.ofOpSequence`); induction on `n ≤ m` shows
   each composite is semilinear over the coefficient maps, giving a strict ring
   system.  The strict sequence-site equivalence turns it into a sequence-site
   module, whose unit-level isomorphisms identify its evaluations with the lines
   and whose transitions are the given adjacent maps.
6. These comparisons, normalizations, towers, level isomorphisms and transitions fill
   the five fields of `SpChartAdmissibility.Twists`; abstraction over the allowed
   schemes gives the simultaneous family.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option synthInstance.maxSize 4096

universe u c v w

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpChartAdmissibility

section Sequence

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{w} C]
  (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{w})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

private def abelianStep
    (M : ∀ n : ℕ, SemilinearSections.Mod.{c, v, w} J (B n))
    (t : ∀ n : ℕ, M (n + 1) ⟶
      (SemilinearSections.res (τ n)).obj (M n)) (n : ℕ) :
    (M (n + 1)).val.presheaf ⟶ (M n).val.presheaf where
  app U := AddCommGrpCat.ofHom
    { toFun := fun x ↦ (t n).val.app U x
      map_zero' := ((t n).val.app U).hom.map_zero
      map_add' := fun x y ↦ ((t n).val.app U).hom.map_add x y }
  naturality := by
    intro U V f
    ext x
    exact PresheafOfModules.naturality_apply (t n).val f x

private abbrev abelianSequence
    (M : ∀ n : ℕ, SemilinearSections.Mod.{c, v, w} J (B n))
    (t : ∀ n : ℕ, M (n + 1) ⟶
      (SemilinearSections.res (τ n)).obj (M n)) :
    ℕᵒᵖ ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
  Functor.ofOpSequence (X := fun n ↦ (M n).val.presheaf) (abelianStep J B τ M t)

private theorem abelianSequence_smul
    (M : ∀ n : ℕ, SemilinearSections.Mod.{c, v, w} J (B n))
    (t : ∀ n : ℕ, M (n + 1) ⟶
      (SemilinearSections.res (τ n)).obj (M n))
    {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ) :
    ∀ (a : (B n).obj.obj U) (x : (M n).val.obj U),
      ((abelianSequence J B τ M t).map (homOfLE h).op).app U (a • x) =
        (SemilinearSections.coefficientMap J B τ h).hom.app U a •
          (show (M m).val.obj U from
            ((abelianSequence J B τ M t).map (homOfLE h).op).app U x) := by
  induction n, h using Nat.le_induction with
  | base =>
    intro a x
    simp [SemilinearSections.coefficientMap]
    rfl
  | succ n h ih =>
    intro a x
    rw [← homOfLE_comp h (Nat.le_succ n), op_comp,
      CategoryTheory.Functor.map_comp]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    simp only [NatTrans.comp_app, AddCommGrpCat.comp_apply]
    have hs : (t n).val.app U (a • x) =
        (τ n).hom.app U a • (show (M n).val.obj U from (t n).val.app U x) :=
      ((t n).val.app U).hom.map_smul a x
    change ((abelianSequence J B τ M t).map (homOfLE h).op).app U
      ((t n).val.app U (a • x)) =
        (SemilinearSections.coefficientMap J B τ (h.trans (Nat.le_succ n))).hom.app U a •
          (show (M m).val.obj U from
            ((abelianSequence J B τ M t).map (homOfLE h).op).app U
              ((t n).val.app U x))
    rw [hs, ih]
    congr 1
    change _ = ((SemilinearSections.rings J B τ).map
      ((homOfLE (Nat.le_succ n)).op ≫ (homOfLE h).op)).hom.app U a
    rw [CategoryTheory.Functor.map_comp]
    exact congrArg (fun f : B (n + 1) ⟶ B n ↦
      (SemilinearSections.coefficientMap J B τ h).hom.app U (f.hom.app U a))
      (Functor.ofOpSequence_map_homOfLE_succ τ n).symm

private def strictOfSequence
    (M : ∀ n : ℕ, SemilinearSections.Mod.{c, v, w} J (B n))
    (t : ∀ n : ℕ, M (n + 1) ⟶
      (SemilinearSections.res (τ n)).obj (M n)) :
    SheafOfModules.StrictRingSystem.{c, v, w}
      (SemilinearSections.rings J B τ) where
  level := M
  transition h :=
    { val := PresheafOfModules.homMk
        ((abelianSequence J B τ M t).map (homOfLE h).op)
        (abelianSequence_smul J B τ M t h) }
  identity n U x := by
    change ((abelianSequence J B τ M t).map (𝟙 (op n))).app U x = x
    rw [CategoryTheory.Functor.map_id]
    rfl
  compose h k U x := by
    change ((abelianSequence J B τ M t).map (homOfLE (h.trans k)).op).app U x = _
    rw [← homOfLE_comp h k, op_comp, CategoryTheory.Functor.map_comp]
    rfl

end Sequence

section SequencePresentation

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{w} C]
  (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{w})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

private theorem evaluationRingMap (n : ℕ) :
    eqToHom (SemilinearSections.evaluation_ring.{c, v, w} J B τ n).symm =
      SheafOfModules.systemSequenceVerticalRingMap
        (SemilinearSections.rings J B τ) n := by
  ext U x
  simp only [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

private def levelIso
    (M : SheafOfModules.StrictRingSystem.{c, v, w}
      (SemilinearSections.rings J B τ)) (n : ℕ) :
    (SemilinearSections.evaluation J B τ n).obj
      ((SheafOfModules.strictSystemSequenceEquivalence
        (SemilinearSections.rings J B τ)).functor.obj M) ≅
        M.level n :=
  (SheafOfModules.pushforwardCongr (evaluationRingMap J B τ n)).app
    ((SheafOfModules.strictSystemSequenceEquivalence
      (SemilinearSections.rings J B τ)).functor.obj M) ≪≫
    (SheafOfModules.strictSystemSequenceUnitLevel
      (SemilinearSections.rings J B τ) M n).symm

set_option maxHeartbeats 2000000 in
-- Identifying the two evaluation presentations entails several sheaf transports.
private theorem sequence_transition
    (M : SheafOfModules.StrictRingSystem.{c, v, w}
      (SemilinearSections.rings J B τ))
    {m n : ℕ} (h : n ≤ m) :
    (SemilinearSections.transition J B τ h).app
      ((SheafOfModules.strictSystemSequenceEquivalence
        (SemilinearSections.rings J B τ)).functor.obj M) ≫
      (SemilinearSections.res (SemilinearSections.coefficientMap J B τ h)).map
          (levelIso J B τ M n).hom =
    (levelIso J B τ M m).hom ≫
        M.transition h := by
  ext U x
  have hh := (SemilinearSections.transition_exists J B τ h).exists.choose_spec
      ((SheafOfModules.strictSystemSequenceEquivalence
        (SemilinearSections.rings J B τ)).functor.obj M) U
  have he := congrFun (eq_of_heq hh) x
  change (levelIso J B τ M n).hom.val.app U _ = _
  refine (congrArg ((levelIso J B τ M n).hom.val.app U) he).trans ?_
  change (M.level n).val.map (𝟙 U)
    ((M.transition h).val.app U ((levelIso J B τ M m).hom.val.app U x)) = _
  rw [PresheafOfModules.map_id]
  rfl

end SequencePresentation

section Realization

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{w} C]
  (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{w})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

private theorem restriction_hom_heq
    {R S : Sheaf J CommRingCat.{w}} {α β : R ⟶ S} (h : α = β)
    {M : SemilinearSections.Mod.{c, v, w} J R}
    {N : SemilinearSections.Mod.{c, v, w} J S}
    (f : M ⟶ (SemilinearSections.res α).obj N)
    (g : M ⟶ (SemilinearSections.res β).obj N)
    (hfg : ∀ (U : Cᵒᵖ) (x : M.val.obj U), f.val.app U x = g.val.app U x) :
    HEq f g := by
  subst β
  apply heq_of_eq
  ext U x
  exact hfg U x

variable (M : ∀ n : ℕ, SemilinearSections.Mod.{c, v, w} J (B n))
  (t : ∀ n : ℕ, M (n + 1) ⟶ (SemilinearSections.res (τ n)).obj (M n))

private def realizedSequence : SemilinearSections.Systems.{c, v, w} J B τ :=
  (SheafOfModules.strictSystemSequenceEquivalence
    (SemilinearSections.rings J B τ)).functor.obj (strictOfSequence J B τ M t)

private def realizedSequenceLevel (n : ℕ) :
    (SemilinearSections.evaluation J B τ n).obj (realizedSequence J B τ M t) ≅ M n :=
  levelIso J B τ (strictOfSequence J B τ M t) n

private theorem realizedSequence_transition (n : ℕ) :
    HEq
      ((SemilinearSections.transition J B τ (Nat.le_succ n)).app
        (realizedSequence J B τ M t) ≫
          (SemilinearSections.res
            (SemilinearSections.coefficientMap J B τ (Nat.le_succ n))).map
              (realizedSequenceLevel J B τ M t n).hom)
      ((realizedSequenceLevel J B τ M t (n + 1)).hom ≫ t n) := by
  refine (heq_of_eq (sequence_transition J B τ
    (strictOfSequence J B τ M t) (Nat.le_succ n))).trans ?_
  apply restriction_hom_heq J
    (Functor.ofOpSequence_map_homOfLE_succ τ n)
  intro U x
  change ((abelianSequence J B τ M t).map
    (homOfLE (Nat.le_succ n)).op).app U _ = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  rfl

end Realization

section ScalarTower

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} {R S V : Sheaf J CommRingCat.{w}}
  (α : R ⟶ S) (β : S ⟶ V) (γ : R ⟶ V) (h : α ≫ β = γ)
  (L : SemilinearSections.Mod.{c, v, w} J R)

private def quotientTowerIso :
    SheafOfModules.changeOfRingsOfUniverses.{v, c, w, w} β
      (SheafOfModules.changeOfRingsOfUniverses.{v, c, w, w} α L) ≅
        SheafOfModules.changeOfRingsOfUniverses.{v, c, w, w} γ L :=
  SheafOfModules.scalarExtensionTowerIso.{c, v, w, w} α β L ≪≫
    eqToIso (congrArg (fun f ↦
      SheafOfModules.changeOfRingsOfUniverses.{v, c, w, w} f L) h)

private theorem quotientTowerIso_pure (U : Cᵒᵖ) (s : V.obj.obj U)
    (t : S.obj.obj U) (x : L.val.obj U) :
    (quotientTowerIso α β γ h L).hom.val.app U
      (SheafOfModules.scalarExtensionSection β
        (SheafOfModules.changeOfRingsOfUniverses.{v, c, w, w} α L) U s
          (SheafOfModules.scalarExtensionSection α L U t x)) =
      SheafOfModules.scalarExtensionSection γ L U (s * β.hom.app U t) x := by
  subst γ
  change (SheafOfModules.scalarExtensionTowerIso.{c, v, w, w} α β L).hom.val.app U _ = _
  exact (congrArg (fun f ↦ f.val.app U
    (SheafOfModules.scalarExtensionSection β
      (SheafOfModules.changeOfRingsOfUniverses.{v, c, w, w} α L) U s
        (SheafOfModules.scalarExtensionSection α L U t x)))
    (SheafOfModules.scalarExtensionTowerIso_hom.{c, v, w, w} α β L)).trans
      (SheafOfModules.scalarExtensionTowerForward_tmul.{c, v, w, w} α β L U s t x)

end ScalarTower

private theorem quotient_comp (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :
    spEllTwistQuotient l E T (n + 1) ≫ SpTowerShriek.tau l E T n =
      spEllTwistQuotient l E T n := by
  unfold spEllTwistQuotient SpTowerShriek.tau spCoefficientCommRings
  simp only [Functor.ofOpSequence_map_homOfLE_succ]
  rw [← Functor.map_comp]
  congr 1

private theorem comparisons_exist (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    [∀ x : T, Invertible (l : T.residueField x)] :
    ∃ B : SpEllTwistComparisons l E T n,
      SpEllTwistComparisonsNormalized l E T n B := by
  classical
  let α := spEllTwistQuotient l E T (n + 1)
  let β := SpTowerShriek.tau l E T n
  let L := purTwistIntegralOne T l E
  have h := quotient_comp l E T n
  let b := quotientTowerIso α β (spEllTwistQuotient l E T n) h L
  obtain ⟨B, hB, _⟩ := SheafOfModules.exists_signedLineComparison.{u + 1, u, u + 1}
    β (spEllTwistOne l E T (n + 1)) (spEllTwistOne l E T n)
    (ellTwist_cover l E T (n + 1)) (ellTwist_cover l E T n) b
  refine ⟨B, ?_, ?_⟩
  · intro U s t x
    rw [hB.2.1]
    exact quotientTowerIso_pure α β (spEllTwistQuotient l E T n) h L U s t x
  · have hb : B 1 = b := Iso.ext hB.2.1
    rw [hb]
    exact hB

-- The characteristic parameters belong to the original statement.
set_option linter.unusedVariables false in
/-- A normalized Tate tower exists simultaneously on every scheme where `l` is invertible.

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
Local pairs (blueprint: lem-sp-global-tate-family).
The proof follows the eight-step plan in the module docstring.  It uses the weakly
étale finite-limit closure, the discrete constant scalar quotient and DVR ideal
comparison, the root-projection finite Kummer comparison, the signed-line tower
normalization, and choice over the fixed universe.  The construction does not assert
compact-support preservation, graph comparisons, smooth right adjoints, or a map to
`k`.
-/
theorem global_tate_family
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (hne : p ≠ l)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] [CharP k p] :
    Nonempty
      (∀ T : Scheme.{u}, IsUnit (l : Γ(T, ⊤)) → Twists l E T) := by
  classical
  refine ⟨fun T hl ↦ ?_⟩
  let : ∀ x : T, Invertible (l : T.residueField x) := fun x ↦
    (show IsUnit (l : T.residueField x) by
      simpa only [map_natCast] using
        hl.map ((T.residue x).hom.comp (T.presheaf.germ ⊤ x trivial).hom)).invertible
  choose B hB using fun n ↦ comparisons_exist l E T n
  let M (r : ℕ) (n : ℕ) := spEllTwistLine l E T n (r : ℤ)
  let t (r : ℕ) (n : ℕ) := spEllTwistTransition l E T n (B n) (r : ℤ)
  exact {
    comparison := B
    normalized := hB
    tower := fun r ↦ realizedSequence (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) (M r) (t r)
    level := fun n r ↦ realizedSequenceLevel (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) (M r) (t r) n
    transition := fun n r ↦ realizedSequence_transition (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) (M r) (t r) n }

end AlgebraicGeometry.ProEtale.SpChartAdmissibility
