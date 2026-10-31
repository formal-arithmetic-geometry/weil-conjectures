/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProfiniteActionCoherentPresentation
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite
public import Mathlib.CategoryTheory.Sites.Pretopology
import WeilConjectures.Topology.FiniteQuotientFiberProduct
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Order.CompletePartialOrder

/-! # Finite limits and finite-cover descent for profinite actions

Source: the current blueprint, direct-image stability, paragraph (3), auxiliary
profinite-action infrastructure; Stacks Tags 002O, 08ZY, 0A2P, 08YD and 0AAU
(blueprint: lem-sfb-profinite-action-finite-cover-site).

The small categories and their finite jointly surjective precoverages are the existing
constructions of `Profinite.CondensedAction.CoherentPresentation`. The statement spells
out the limit actions and the matching-family bijections, including empty covers.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace Profinite.CondensedAction.CoherentPresentation

/-- Finite limits are created on underlying profinite spaces, and finite covers admit
unique continuous equivariant descent. Products have diagonal actions and equalizers
have restricted actions, as specified by their coordinate homeomorphisms below.

Source: direct-image stability, paragraph (3), agent-formulated auxiliary infrastructure
(blueprint: lem-sfb-profinite-action-finite-cover-site).

Proof:
1. The universe convention makes `Base` and `Space J` small in u+1. Construct the
   terminal profinite point and pullbacks as closed subspaces of products using
   lem-sfb-finite-quotient-fiber-product; apply
   lem-weil-pbc-finite-limits-from-terminal-pullbacks(1).
2. For any finite underlying limit cone, use lem-sfb-profinite-topological-limits
   with test space J times its vertex. The maps (g,x) to g acting on each coordinate
   induce a unique continuous action. Coordinate uniqueness proves the action laws,
   equivariance of mediating maps and uniqueness of the lifted action. This creates
   finite limits, including the empty diagram.
3. The empty limit is the trivial point. Coordinate equations identify products
   with pairs with diagonal action, and equalizers with the equality subspace with
   restricted action; their projection and inclusion maps give the homeomorphisms.
4. Verify the site axioms of def-weil-pbc-sites-and-cohomology by lifting points:
   isomorphisms are onto, pullback pairs lift points, and composition lifts twice.
   A finite union of finite families is finite. Reindexing is immaterial. The empty
   presieve covers exactly the empty object. These arguments also apply to Base.
5. For a finite cover take the finite disjoint union of its domains. It is compact
   and maps continuously onto its Hausdorff target, hence is quotient by
   lem-sfb-compact-hausdorff-surjection-quotient. Overlap compatibility defines a
   unique descended set map. The quotient criterion proves continuity. This gives
   the displayed matching-family bijection on Base, including the empty target.
6. For equivariant local maps, lift t to x and compute f(g*t)=f_i(g*x)=g*f_i(x).
   Thus the descended map is equivariant. This proves the action-space bijection
   and, by the representable sheaf criterion, subcanonicity on both sites.
7. Trivial parameters retain spaces and maps. The preceding point, product and
   equalizer descriptions show finite-limit preservation, equivalently use
   lem-weil-pbc-finite-limits-from-terminal-pullbacks(2). Joint surjectivity and
   finiteness are unchanged, so all covers, including the empty cover, are preserved.
-/
theorem profiniteAction_finiteCover_site
    (J : Type u) [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    [CompactSpace J] [T2Space J] [TotallyDisconnectedSpace J] :
    HasFiniteLimits (Space J) ∧
    Nonempty (CreatesFiniteLimits (underlying J)) ∧
    Nonempty (IsTerminal ((trivialParameter J).obj
      (AsSmall.up.obj (Profinite.of PUnit.{u + 1})))) ∧
    (∀ X Y : Space J, ∃ p : BinaryFan X Y, Nonempty (IsLimit p) ∧
      ∃ e : (underlying J).obj p.pt ≃ₜ
          ((underlying J).obj X × (underlying J).obj Y),
        (∀ x, e x = ((underlying J).map p.fst x, (underlying J).map p.snd x)) ∧
        (∀ (g : J) (x : (underlying J).obj p.pt),
          e (((AsSmall.down.obj p.pt).obj.ρ g).hom.hom x) =
            (((AsSmall.down.obj X).obj.ρ g).hom.hom (e x).1,
              ((AsSmall.down.obj Y).obj.ρ g).hom.hom (e x).2))) ∧
    (∀ (X Y : Space J) (f h : X ⟶ Y), ∃ p : Fork f h, Nonempty (IsLimit p) ∧
      ∃ e : (underlying J).obj p.pt ≃ₜ
          {x : (underlying J).obj X | (underlying J).map f x = (underlying J).map h x},
        (∀ x, (e x).val = (underlying J).map p.ι x) ∧
        (∀ (g : J) (x : (underlying J).obj p.pt),
          (e (((AsSmall.down.obj p.pt).obj.ρ g).hom.hom x)).val =
            ((AsSmall.down.obj X).obj.ρ g).hom.hom (e x).val)) ∧
    (coverage J).IsSiteForCoverings ∧
    (∃ K : Pretopology (Space J), K.toPrecoverage = coverage J) ∧
    (∀ T : Space J, (⊥ : Presieve T) ∈ coverage J T ↔
      IsEmpty ((underlying J).obj T)) ∧
    (coverage J).toGrothendieck.Subcanonical ∧
    (∀ (T : Space J) (I : Type w) [Finite I] (Tᵢ : I → Space J)
        (a : ∀ i, Tᵢ i ⟶ T), Presieve.ofArrows Tᵢ a ∈ coverage J T →
      ∀ U : Space J,
        Set.BijOn (fun f : T ⟶ U ↦ fun i ↦ a i ≫ f) Set.univ
          {b : ∀ i, Tᵢ i ⟶ U | ∀ i j,
            pullback.fst (a i) (a j) ≫ b i = pullback.snd (a i) (a j) ≫ b j}) ∧
    baseCoverage.{u}.IsSiteForCoverings ∧
    (∃ K : Pretopology Base.{u}, K.toPrecoverage = baseCoverage) ∧
    (∀ T : Base.{u}, (⊥ : Presieve T) ∈ baseCoverage T ↔ IsEmpty (parameter T)) ∧
    baseCoverage.{u}.toGrothendieck.Subcanonical ∧
    (∀ (T : Base.{u}) (I : Type w) [Finite I] (Tᵢ : I → Base.{u})
        (a : ∀ i, Tᵢ i ⟶ T), Presieve.ofArrows Tᵢ a ∈ baseCoverage T →
      ∀ U : Base.{u},
        Set.BijOn (fun f : T ⟶ U ↦ fun i ↦ a i ≫ f) Set.univ
          {b : ∀ i, Tᵢ i ⟶ U | ∀ i j,
            pullback.fst (a i) (a j) ≫ b i = pullback.snd (a i) (a j) ≫ b j}) ∧
    PreservesFiniteLimits (trivialParameter J) ∧
    (∀ (S : Base.{u}) (W : Presieve S), W ∈ baseCoverage S →
      W.map (trivialParameter J) ∈ coverage J ((trivialParameter J).obj S)) := by
  sorry

end Profinite.CondensedAction.CoherentPresentation
