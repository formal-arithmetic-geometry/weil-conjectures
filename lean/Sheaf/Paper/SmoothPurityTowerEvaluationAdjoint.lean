/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.Paper.SmoothPurityTowerRightExtensionFiniteColimits
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Exact right adjoints of coefficient-tower evaluation

Source: blueprint main-20261015, sec-smooth-purity, sk-lem-sp-tower-levels,
`sk-lem-sp-tower-levels-adjoint.md` and its proof
(blueprint: det-sp-tower-evaluation-adjoint).

Index n means the positive level n+1, as in the recorded tower category. The
right adjoints are specified on strict systems and transported back by the
recorded sectionwise normalized equivalence. All their object, transition and
morphism data are fixed below; no functor is selected from a bare existence claim.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

-- Elaborate with the existing transport to the full coefficient universe.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})

/-- The explicitly normalized right adjoints and their consequences.
Source: blueprint main-20261015, coefficient-tower evaluation adjoint lemma
(blueprint: det-sp-tower-evaluation-adjoint).

Above n the module is restriction of J, and all iterated transitions are the
identity on its underlying sections. Below n it is zero, including the boundary
transition. Morphisms are the prescribed scalar restrictions above n and zero
below n. The product fan and its limiting property express the product without
assuming that products in the varying-coefficient category are computed levelwise. -/
structure SpTowerEvaluationAdjoint (A : SpCoefficientTowersAbelian l E T) where
  /-- The strict presentation of r_(n+1). -/
  right : ∀ n : ℕ,
    systemLevel.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T) n ⥤
      StrictRingSystem.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T)
  /-- At every higher level, the scalar action is exactly quotient restriction. -/
  above : ∀ (n r : ℕ) (h : n ≤ r)
    (J : systemLevel.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T) n),
    ((right n).obj J).level r = (systemRestriction (spCoefficientCommRings l E T) h).obj J
  /-- Every lower level is the zero module sheaf. -/
  below : ∀ (n r : ℕ) (_h : r < n)
    (J : systemLevel.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T) n),
    IsZero (((right n).obj J).level r)
  /-- Above n, every iterated transition is the identity on the underlying sections. -/
  transitionAbove : ∀ (n m r : ℕ) (h : m ≤ r) (_hn : n ≤ m)
    (J : systemLevel.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T) n)
    (U : T.ProEtᵒᵖ),
    HEq (fun x ↦ (((right n).obj J).transition h).val.app U x)
      (fun x : J.val.obj U ↦ x)
  /-- All transitions with target below n are zero, including the boundary. -/
  transitionBelow : ∀ (n m r : ℕ) (h : m ≤ r) (_hm : m < n)
    (J : systemLevel.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T) n),
    ((right n).obj J).transition h = 0
  /-- The functor applies the given linear map at every level at least n. -/
  mapAbove : ∀ (n r : ℕ) (h : n ≤ r)
    {J K : systemLevel.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T) n}
    (f : J ⟶ K),
    HEq (((right n).map f).app r)
      ((systemRestriction (spCoefficientCommRings l E T) h).map f)
  /-- At lower levels its map is zero. -/
  mapBelow : ∀ (n r : ℕ) (_h : r < n)
    {J K : systemLevel.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T) n}
    (f : J ⟶ K), ((right n).map f).app r = 0
  /-- The actual tower functor is right adjoint to the recorded evaluation. -/
  adjunction : ∀ n : ℕ,
    spCoefficientEvaluation l E T A.equivalence n ⊣ right n ⋙ A.equivalence.inverse
  /-- Exactness, stated by preservation of finite limits and colimits. -/
  exact : ∀ n : ℕ, PreservesFiniteLimits (right n ⋙ A.equivalence.inverse) ∧
    PreservesFiniteColimits (right n ⋙ A.equivalence.inverse)
  /-- Each r_n sends injective module sheaves to injective towers. -/
  injectives : ∀ n : ℕ, (right n ⋙ A.equivalence.inverse).PreservesInjectiveObjects
  /-- Every tower embeds in a product of r_n J_n, with J_n injective over C_n.
  The product map has precisely the adjuncts of the levelwise embeddings as components. -/
  embedding : ∀ C : spCoefficientTowers l E T,
    ∃ (J : ∀ n : ℕ,
        systemLevel.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T) n)
      (i : ∀ n : ℕ, (spCoefficientEvaluation l E T A.equivalence n).obj C ⟶ J n),
      (∀ n : ℕ, Injective (J n)) ∧ (∀ n : ℕ, Mono (i n)) ∧
      ∃ P : Fan (fun n : ℕ ↦ (right n ⋙ A.equivalence.inverse).obj (J n)),
        Nonempty (IsLimit P) ∧ ∃ f : C ⟶ P.pt, Mono f ∧
          ∀ n : ℕ, f ≫ P.proj n = ((adjunction n).homEquiv C (J n)) (i n)

private theorem sp_strict_hom_ext
    {M N : StrictRingSystem.{t + 1, t, max u (t + 1)}
      (spCoefficientCommRings l E T)} (f g : M ⟶ N)
    (h : ∀ n : ℕ, f.app n = g.app n) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have he : f = g := funext h
      subst g
      rfl

private theorem sp_evaluation_jointly_faithful (A : SpCoefficientTowersAbelian l E T)
    {M N : spCoefficientTowers l E T} (f g : M ⟶ N)
    (h : ∀ n : ℕ, (spCoefficientEvaluation l E T A.equivalence n).map f =
      (spCoefficientEvaluation l E T A.equivalence n).map g) : f = g := by
  apply A.equivalence.functor.map_injective
  exact sp_strict_hom_ext l E T _ _ h

private theorem sp_embedding_from_adjunctions (A : SpCoefficientTowersAbelian l E T)
    (R : ∀ n : ℕ,
      systemLevel.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T) n ⥤
        spCoefficientTowers l E T)
    (adj : ∀ n : ℕ, spCoefficientEvaluation l E T A.equivalence n ⊣ R n)
    (C : spCoefficientTowers l E T) :
    ∃ (J : ∀ n : ℕ,
        systemLevel.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T) n)
      (i : ∀ n : ℕ, (spCoefficientEvaluation l E T A.equivalence n).obj C ⟶ J n),
      (∀ n : ℕ, Injective (J n)) ∧ (∀ n : ℕ, Mono (i n)) ∧
      ∃ P : Fan (fun n : ℕ ↦ (R n).obj (J n)),
        Nonempty (IsLimit P) ∧ ∃ f : C ⟶ P.pt, Mono f ∧
          ∀ n : ℕ, f ≫ P.proj n = ((adj n).homEquiv C (J n)) (i n) := by
  classical
  let := A.grothendieck
  have levelGroth (n : ℕ) : IsGrothendieckAbelian.{max u (t + 1)}
      (systemLevel.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T) n) := by
    exact SheafOfModules.isGrothendieckAbelianOfUniverses _ _
  let (n : ℕ) := levelGroth n
  let J := fun n : ℕ ↦ Injective.under
    ((spCoefficientEvaluation l E T A.equivalence n).obj C)
  let i := fun n : ℕ ↦ Injective.ι
    ((spCoefficientEvaluation l E T A.equivalence n).obj C)
  let d := fun n : ℕ ↦ (adj n).homEquiv C (J n) (i n)
  refine ⟨J, i, fun _ ↦ inferInstance, fun _ ↦ inferInstance,
    limit.cone (Discrete.functor (fun n : ℕ ↦ (R n).obj (J n))),
    ⟨limit.isLimit _⟩, Pi.lift d, ?_, ?_⟩
  · constructor
    intro X a b hab
    apply sp_evaluation_jointly_faithful l E T A
    intro n
    apply (cancel_mono (i n)).mp
    apply (adj n).homEquiv X (J n) |>.injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
    change a ≫ d n = b ≫ d n
    have hh := congrArg (fun k ↦ k ≫ Pi.π (fun n : ℕ ↦ (R n).obj (J n)) n) hab
    simpa only [Category.assoc, Pi.lift_π] using hh
  · intro n
    exact Pi.lift_π d n

/-- Evaluation of coefficient towers has the stated exact right adjoints, preserving
injectives, and every tower embeds into a product of their injective values.
Source: blueprint main-20261015, `sk-lem-sp-tower-levels-adjoint.md`
(blueprint: det-sp-tower-evaluation-adjoint).

Proof:
1. For J at level n, put its quotient scalar restriction at r >= n, zero at r < n,
and use identity section maps above n and zero maps below. Both scalar actions on
an upper transition factor through R_n, so these are linear over the quotient maps.
Zero targets handle the boundary. Apply f componentwise to obtain the functor;
identities and composition hold levelwise (det-sp-coefficient-towers-abelian).
2. A tower map C -> r_n J is determined by its component C_n -> J: above n this
component is precomposed with C_r -> C_n, and below n it is zero. Conversely these
form a compatible map of towers. The two operations are inverse and commute with
precomposition and postcomposition, giving the adjunction after the normalized
strict-system equivalence.
3. Kernels and cokernels of towers are levelwise. Scalar restriction preserves both:
kernels are sectionwise, and cokernels sheafify the unchanged sectionwise cokernel
(def-weil-sheaf-of-modules-category). The zero functor does too. Hence r_n is exact.
4. Evaluation is exact by det-sp-coefficient-towers-abelian. The right-adjoint
preservation theorem lem-sp-right-adjoint-preserves-injectives gives injectivity.
5. On the small pro-etale site, lem-pur-ringed-site-grothendieck-abelian and
lem-sp-grothendieck-enough-injectives give injective embeddings i_n : C_n -> J_n.
Form P_r as the finite product of restricted J_n for n <= r, with transitions
dropping the last coordinate. Coordinatewise gluing gives module sheaves and
semilinearity gives a tower. Its coordinate projections to r_n J_n exhibit the
product: any family of tower maps has the unique levelwise tuple as its lift.
The adjuncts of i_n induce C -> P; at level r its last coordinate is i_r, so its
kernel vanishes. Levelwise kernels therefore make it a monomorphism of towers.
The first index is zero, hence exponent one; no boundary at exponent zero is used. -/
theorem sp_tower_evaluation_adjoint (A : SpCoefficientTowersAbelian l E T) :
    Nonempty (SpTowerEvaluationAdjoint l E T A) := by
  obtain ⟨R⟩ := sp_tower_normalized_right_adjoints l E T A
  refine ⟨{ right := R.right
            above := R.above
            below := R.below
            transitionAbove := R.transitionAbove
            transitionBelow := R.transitionBelow
            mapAbove := R.mapAbove
            mapBelow := R.mapBelow
            adjunction := R.adjunction
            exact := ?_
            injectives := ?_
            embedding := ?_ }⟩
  · intro n
    let : PreservesLimits (R.right n ⋙ A.equivalence.inverse) :=
      (R.adjunction n).rightAdjoint_preservesLimits
    exact ⟨inferInstance, sp_tower_right_extension_finite_colimits l E T A R n⟩
  · intro n
    let := A.evaluationLimits n
    exact (R.adjunction n).preservesInjectiveObjects_of_preservesFiniteLimits
  · exact sp_embedding_from_adjunctions l E T A
      (fun n ↦ R.right n ⋙ A.equivalence.inverse) R.adjunction

end AlgebraicGeometry.ProEtale

-- Restore the inherited instance environment.
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
