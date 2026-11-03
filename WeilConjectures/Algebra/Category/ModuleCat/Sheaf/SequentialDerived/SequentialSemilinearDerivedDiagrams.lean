/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.System.SystemDerivedTransition
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.SequentialSemilinearDerivedRealization
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.SequentialSemilinearDerivedExact
import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation

/-! # Sequential semilinear derived diagrams

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-finite-extension.proof.md, paragraph 4; the general sequential
lemma formulated in the DAG (blueprint: lem-sf-sequential-semilinear-derived-diagrams).

The strict category, componentwise abelian structure, exact evaluations and
localized transitions are the existing `SheafOfModules.StrictRingSystem` API.
Index `n : ℕ` denotes the positive index `n+1`. The functor `B` records the ring
maps and their composites; it imposes no condition on the adjacent ring maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.SequentialDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [siteSmall : EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- A common lower cohomological bound on all evaluations.
Source: the sequential lemma, paragraph 2
(blueprint: lem-sf-sequential-semilinear-derived-diagrams). -/
def HasCommonLowerBound (M : DerivedCategory (StrictRingSystem B)) : Prop :=
  ∃ a : ℤ, ∀ n : ℕ, ((derivedSystemEvaluation B n).obj M).IsGE a

/-- The derived exact restriction along the adjacent coefficient map.
Source: the sequential lemma, paragraph 1
(blueprint: lem-sf-sequential-semilinear-derived-diagrams). -/
abbrev adjacentRestriction (n : ℕ) :=
  (systemRestriction B (Nat.le_succ n)).mapDerivedCategory

/-- The product of the vertex Hom groups, with the standard cohomological shift.
Source: the sequential lemma, definition of P^r
(blueprint: lem-sf-sequential-semilinear-derived-diagrams). -/
abbrev vertexHom (M N : DerivedCategory (StrictRingSystem B)) (r : ℤ) :=
  ∀ n : ℕ, (derivedSystemEvaluation B n).obj M ⟶
    ((derivedSystemEvaluation B n).obj N)⟦r⟧

/-- The product of the adjacent-edge Hom groups. Restriction is applied after shift.
Source: the sequential lemma, definition of Q^r
(blueprint: lem-sf-sequential-semilinear-derived-diagrams). -/
abbrev edgeHom (M N : DerivedCategory (StrictRingSystem B)) (r : ℤ) :=
  ∀ n : ℕ, (derivedSystemEvaluation B (n + 1)).obj M ⟶
    (adjacentRestriction B n).obj (((derivedSystemEvaluation B n).obj N)⟦r⟧)

/-- The shifted transition, transported through the canonical shift comparison.
Source: the sequential lemma, t^N_n[r]
(blueprint: lem-sf-sequential-semilinear-derived-diagrams). -/
def shiftedTransition (N : DerivedCategory (StrictRingSystem B)) (r : ℤ) (n : ℕ) :
    ((derivedSystemEvaluation B (n + 1)).obj N)⟦r⟧ ⟶
      (adjacentRestriction B n).obj (((derivedSystemEvaluation B n).obj N)⟦r⟧) :=
  ((systemDerivedTransition B (Nat.le_succ n)).app N)⟦r⟧' ≫
    ((adjacentRestriction B n).commShiftIso r).inv.app
      ((derivedSystemEvaluation B n).obj N)

/-- The vertex-edge difference V(f_n) t^M_n - t^N_n[r] f_(n+1).
Source: the sequential lemma, displayed definition of d^r
(blueprint: lem-sf-sequential-semilinear-derived-diagrams). -/
def difference (M N : DerivedCategory (StrictRingSystem B)) (r : ℤ)
    (f : vertexHom B M N r) : edgeHom B M N r :=
  fun n ↦ (systemDerivedTransition B (Nat.le_succ n)).app M ≫
      (adjacentRestriction B n).map (f n) -
    f (n + 1) ≫ shiftedTransition B N r n

/-- Evaluation on maps, followed by the canonical identification N = N[0].
Source: the sequential lemma, the arrow labelled (e_n)
(blueprint: lem-sf-sequential-semilinear-derived-diagrams). -/
def evaluateHom (M N : DerivedCategory (StrictRingSystem B)) (f : M ⟶ N) :
    vertexHom B M N 0 :=
  fun n ↦ (derivedSystemEvaluation B n).map f ≫
    (shiftFunctorZero (DerivedCategory (systemLevel B n)) ℤ).inv.app
      ((derivedSystemEvaluation B n).obj N)

/-- The natural contravariant/covariant action on adjacent-edge Hom groups.
Source: the sequential lemma, naturality of its exact sequence
(blueprint: lem-sf-sequential-semilinear-derived-diagrams). -/
def edgeMap {M M' N N' : DerivedCategory (StrictRingSystem B)}
    (f : M' ⟶ M) (g : N ⟶ N') (r : ℤ) (x : edgeHom B M N r) :
    edgeHom B M' N' r :=
  fun n ↦ (derivedSystemEvaluation B (n + 1)).map f ≫ x n ≫
    (adjacentRestriction B n).map (((derivedSystemEvaluation B n).map g)⟦r⟧')

include siteSmall in
/-- Realization, the natural vertex-edge exact sequence, its unique-lift consequence,
and joint conservativity, on the actual ordinary unbounded derived categories.
Source: the general sequential lemma formulated for paragraph 4 of the latest
blueprint lem-coef-integral-finite-extension.proof.md
(blueprint: lem-sf-sequential-semilinear-derived-diagrams).

Proof (the eight reviewed DAG steps):
1. Choose a representative L_1 of K_1. By the right calculus of fractions and
   right-fraction representation (lem-pc-quasi-isomorphisms-multiplicative-system
   and lem-pc-right-fraction-representation), inductively represent the next
   derived arrow by a roof H <- L_(n+1) -> V_n L_n. Its left leg is a
   quasi-isomorphism. Keep the earlier representatives unchanged. Composite
   adjacent chain maps give all longer strict transitions, realizing the family.
2. Use the actual exact coinduction J_n of lem-coef-system-coinduced-adjunction.
   It is zero below n and scalar restriction above n. The two functors
   F(X) = product J_n X_n and F_+(Y) = product J_(n+1) Y_n are exact, since
   they are finite products at each vertex. Their adjoints are the evaluation
   functors to the two product categories.
3. Localize these exact adjunctions by def-weil-exact-derived-adjunction. Use
   lem-sf-derived-discrete-product to identify derived product categories with
   products of derived categories. The induced Hom bijections identify Hom into
   F(X)[r] and F_+(Y)[r] with the vertex and edge products. Termwise exact
   localization commutes with shifts by lem-sf-exact-functor-derived-triangulated.
4. Form 0 -> N -> F((N_n)) -> F_+((V_n N_n)) -> 0. The augmentation consists
   of the actual transitions. At vertex m the defect sends (x_n) to
   (x_n - t_n x_(n+1)). Its kernel is determined by x_m; to lift (y_n), set
   x_m = 0 and recursively x_n = y_n + t_n x_(n+1). This proves degreewise
   exactness, including at the first vertex. These sections need not be system maps.
5. Apply lem-weil-pbc-complex-ses-triangle to obtain a distinguished triangle.
   Its first two functors are exact. Naturality for chain maps descends through
   right roofs, by the two fraction lemmas of Step 1, to naturality on D(T).
6. Under the coinduction transposes, the relation at vertex n+1 is exactly
   V_n(f_n) t^M_n - t^N_n[r] f_(n+1). The diagonal identity transition identifies
   the augmentation with evaluation on Hom. Use the actual ordinary coinduced
   adjunction and its unit-normalized derived adjunction; localized shift
   comparisons introduce no additional sign.
7. Apply lem-weil-pbc-hom-into-triangle-exact to this triangle and its shifts.
   The resulting five-term Hom sequence is the stated sequence. The natural
   triangle and derived adjunctions give naturality in N; precomposition gives
   contravariant naturality in M.
8. If Q^(-1) is zero, exactness identifies Hom(M,N) bijectively with ker d^0.
   Evaluations jointly detect isomorphisms by lem-coef-semilinear-derived-sections;
   alternatively, componentwise cohomology and
   lem-weil-pbc-unbounded-derived-iso-cohomology give this assertion.
No flatness of a coefficient quotient and no exactness of infinite products of
module sheaves is used; the coinduced products are finite at every vertex. -/
theorem sequentialSemilinearDerivedDiagrams :
    (∀ (K : ∀ n : ℕ, DerivedCategory (systemLevel B n))
      (k : ∀ n : ℕ, K (n + 1) ⟶ (adjacentRestriction B n).obj (K n)),
      (∃ a : ℤ, ∀ n : ℕ, (K n).IsGE a) →
      ∃ (M : DerivedCategory (StrictRingSystem B))
        (e : ∀ n : ℕ, (derivedSystemEvaluation B n).obj M ≅ K n),
        ∀ n : ℕ, (systemDerivedTransition B (Nat.le_succ n)).app M ≫
            (adjacentRestriction B n).map (e n).hom =
          (e (n + 1)).hom ≫ k n) ∧
    (∃ δ : ∀ (M N : DerivedCategory (StrictRingSystem B)),
        HasCommonLowerBound B M → HasCommonLowerBound B N →
          edgeHom B M N (-1) →+ (M ⟶ N),
      (∀ (M N : DerivedCategory (StrictRingSystem B))
        (hM : HasCommonLowerBound B M) (hN : HasCommonLowerBound B N),
        Function.Exact (difference B M N (-1)) (δ M N hM hN) ∧
        Function.Exact (δ M N hM hN) (evaluateHom B M N) ∧
        Function.Exact (evaluateHom B M N) (difference B M N 0)) ∧
      (∀ (M M' N N' : DerivedCategory (StrictRingSystem B))
        (hM : HasCommonLowerBound B M) (hM' : HasCommonLowerBound B M')
        (hN : HasCommonLowerBound B N) (hN' : HasCommonLowerBound B N')
        (f : M' ⟶ M) (g : N ⟶ N') (x : edgeHom B M N (-1)),
        δ M' N' hM' hN' (edgeMap B f g (-1) x) = f ≫ δ M N hM hN x ≫ g)) ∧
    (∀ (M N : DerivedCategory (StrictRingSystem B)) (r : ℤ)
      (f g : vertexHom B M N r),
      difference B M N r (f + g) = difference B M N r f + difference B M N r g) ∧
    (∀ (M N : DerivedCategory (StrictRingSystem B)) (f g : M ⟶ N),
      evaluateHom B M N (f + g) = evaluateHom B M N f + evaluateHom B M N g) ∧
    (∀ (M N : DerivedCategory (StrictRingSystem B)),
      HasCommonLowerBound B M → HasCommonLowerBound B N →
      (∀ n : ℕ, Subsingleton ((derivedSystemEvaluation B (n + 1)).obj M ⟶
        (adjacentRestriction B n).obj (((derivedSystemEvaluation B n).obj N)⟦(-1 : ℤ)⟧))) →
      ∀ f : vertexHom B M N 0, difference B M N 0 f = 0 →
        ∃! g : M ⟶ N, evaluateHom B M N g = f) ∧
    (∀ (M N : DerivedCategory (StrictRingSystem B)) (f : M ⟶ N),
      IsIso f ↔ ∀ n : ℕ, IsIso ((derivedSystemEvaluation B n).map f)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sequentialSemilinearDerivedRealization B
  · exact sequentialSemilinearDerivedExact B
  · intro M N r f g
    funext n
    dsimp [difference]
    simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
    abel
  · intro M N f g
    funext n
    dsimp [evaluateHom]
    simp only [Functor.map_add, Preadditive.add_comp]
  · intro M N hM hN hs f hf
    change Helper.HasCommonLowerBound B M at hM
    change Helper.HasCommonLowerBound B N at hN
    change Helper.vertexHom B M N 0 at f
    change Helper.difference B M N 0 f = 0 at hf
    change (∀ n : ℕ, Subsingleton ((derivedSystemEvaluation B (n + 1)).obj M ⟶
      (Helper.adjacentRestriction B n).obj
        (((derivedSystemEvaluation B n).obj N)⟦(-1 : ℤ)⟧))) at hs
    change ∃! g : M ⟶ N, Helper.evaluateHom B M N g = f
    obtain ⟨δ, hex, hnat⟩ := sequentialSemilinearDerivedExact B
    obtain ⟨g, hg⟩ := ((hex M N hM hN).2.2 f).mp hf
    refine ⟨g, hg, ?_⟩
    intro g' hg'
    have hz : Helper.evaluateHom B M N (g - g') = 0 := by
      have he : Helper.evaluateHom B M N (g - g') =
          Helper.evaluateHom B M N g - Helper.evaluateHom B M N g' := by
        funext n
        dsimp [Helper.evaluateHom]
        simp only [Functor.map_sub, Preadditive.sub_comp]
      rw [he, hg, hg', sub_self]
    obtain ⟨x, hx⟩ := ((hex M N hM hN).2.1 (g - g')).mp hz
    have hx0 : x = 0 := by
      funext n
      exact (hs n).eq_zero (x n)
    have hsub : g - g' = 0 := by simpa [hx0] using hx.symm
    exact (sub_eq_zero.mp hsub).symm
  · intro M N f
    exact systemDerivedEvaluation_isIso_iff B f

end SheafOfModules.SequentialDerived
