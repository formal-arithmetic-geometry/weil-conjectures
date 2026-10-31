/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1KernelScalarData
import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1KernelSplittingBaseChange
import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1KernelFiniteComparison
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Tower trace base change and the two diagonal scalar identities

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md,
Reduction of the triangle identities and Levelwise check
(blueprint: lem-sp-tower-p1-kernel-scalar-normalization).

The helpers specify the unit/Chern splittings, their inverse-projection traces,
and the actual finite etale composites. Positive level n+1 is indexed by n : Nat.
All equalities before evaluation are in the ordinary derived category of towers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}

variable {p : Presentation l E S hS}

private theorem kernel_degree_zero_detection
    (f g : coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)) ⟶
      coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
    (h : ∀ n : ℕ, (SpTowerShriek.ev l E (ProjectiveLine S) n).map f =
      (SpTowerShriek.ev l E (ProjectiveLine S) n).map g) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun t ↦ (t.val.app (op U.unop.2)) x) (h U.unop.1)

private theorem kernel_degree_zero_lift (k : KernelSplittingData l E p) (a : Bool) :
    ∃! f : coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)) ⟶
      coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)),
      (DerivedCategory.singleFunctor
        (Systems (ProjectiveLine S) (Arings l E (ProjectiveLine S))) 0).map f =
          k.scalar l E a := by
  let F := DerivedCategory.singleFunctor
    (Systems (ProjectiveLine S) (Arings l E (ProjectiveLine S))) 0
  obtain ⟨f, hf⟩ := F.map_surjective (k.scalar l E a)
  exact ⟨f, hf, fun g hg ↦ F.map_injective (hg.trans hf.symm)⟩

private theorem kernel_evaluations_detect (f g :
    unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) ⟶
      unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
    (h : ∀ n : ℕ, (SpTowerShriek.Ev l E (ProjectiveLine S) n).map f =
      (SpTowerShriek.Ev l E (ProjectiveLine S) n).map g) : f = g := by
  let F := DerivedCategory.singleFunctor
    (Systems (ProjectiveLine S) (Arings l E (ProjectiveLine S))) 0
  obtain ⟨f', hf⟩ := F.map_surjective f
  obtain ⟨g', hg⟩ := F.map_surjective g
  suffices heq : f' = g' by rw [← hf, ← hg, heq]
  apply kernel_degree_zero_detection l E
  intro n
  let e := (SpTowerShriek.ev l E (ProjectiveLine S) n).mapDerivedCategorySingleFunctor 0
  apply (DerivedCategory.singleFunctor _ 0).map_injective
  apply (cancel_epi (e.hom.app _)).1
  have heq := congrArg (fun t ↦ t ≫ e.hom.app _) (h n)
  rw [← hf, ← hg] at heq
  have hn := e.hom.naturality f'
  have hm := e.hom.naturality g'
  dsimp only [Functor.comp_map] at hn hm
  change _ = _ at heq
  exact hn.symm.trans (heq.trans hm)

private theorem kernel_inverse_base_change (k : KernelSplittingData l E p) (a : Bool)
    (h : (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).map k.splittingQ.hom ≫
        k.exchange l E a = k.sumComparison l E ≫ (k.splittingProjection a).hom) :
    k.exchange l E a ≫ (k.splittingProjection a).inv =
      (SpTowerShriek.pull l E p.classes.base
        (p.operations.geometry (ProjectiveLine S ↘ S))).map k.splittingQ.inv ≫
          k.sumComparison l E := by
  apply (cancel_epi ((SpTowerShriek.pull l E p.classes.base
    (p.operations.geometry (ProjectiveLine S ↘ S))).map k.splittingQ.hom)).1
  rw [← Category.assoc, h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  erw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

private theorem kernel_sum_comparison_iso (k : KernelSplittingData l E p) :
    IsIso (k.sumComparison l E) := by
  let F := SpTowerShriek.pull l E p.classes.base
    (p.operations.geometry (ProjectiveLine S ↘ S))
  let : F.Additive := inferInstance
  let : PreservesLimitsOfShape (Discrete WalkingPair) F := inferInstance
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryProducts F
  let d := F.mapBiprod ((line l E p.classes.chernS)⟦(2 : ℤ)⟧)
    (unit S (Arings l E S)) ≪≫
      biprod.mapIso (kernelShiftedLine l E k.lineQ) (k.coefficientQ.derivedIso l E)
  have hd : k.sumComparison l E = d.hom := by
    apply biprod.hom_ext <;>
      simp [KernelSplittingData.sumComparison, d] <;> rfl
  rw [hd]
  infer_instance

private theorem kernel_scalar_identity (k : KernelSplittingData l E p)
    (hD : (diagonalImmersion S).ker.IsInvertible)
    (levels : ∀ n : ℕ, k.finiteNormalization l E hD n) (a : Bool) :
    k.scalar l E a = 𝟙 _ := by
  apply kernel_evaluations_detect l E
  intro n
  let : Finite (SpTowerShriek.R l E n) := p.classes.base.finite n
  obtain ⟨c, bP, hc⟩ := levels n
  obtain ⟨hi, _, heq⟩ := hc.composite a
  have : IsIso (c.unitP l E n).comparison := hi
  apply (cancel_epi (c.unitP l E n).comparison).1
  rw [hc.finite_identity a] at heq
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at heq
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact heq

/-- The canonical tower splitting, its inverse and its second projection commute with
both projective-line base-change squares. Both supported diagonal scalar composites
are identities, and every positive-level comparison is the specified ordinary etale
finite composite transported by nu-star. All bases are allowed.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md,
Reduction of the triangle identities and Levelwise check
(blueprint: lem-sp-tower-p1-kernel-scalar-normalization).

Proof: the normalized splitting construction and forward square are isolated in
`towerP1KernelSplittingBaseChange`; finite geometric comparisons and integrals
are isolated in `towerP1KernelFiniteComparison`. The remaining argument is complete.
Preservation of biproducts identifies the sum comparison as an isomorphism.
Cancel the mapped splitting in its forward square to obtain inverse base change;
compose with the second projection and use traceQ to obtain trace base change.
The same square expresses exchange as a composite of isomorphisms.

For either diagonal scalar, the finite WordComparison and finite_identity imply
identity after derived evaluation, by cancellation of the invertible unit-word
comparison. Fullness of singleFunctor at degree zero gives an abelian tower lift;
its faithfulness makes the lift unique. Naturality of exact evaluation's single
comparison and finite-level singleFunctor faithfulness identify all evaluated
abelian components. Equality of module maps is equality on every sequence-site
object (n,U), so equality of all evaluations gives equality of tower maps. Apply
singleFunctor to obtain the two tower scalar identities. The same sectionwise
argument proves the separately asserted detection of abelian coefficient maps.
No faithfulness of evaluation on general derived morphisms is used. -/
theorem towerP1KernelScalarNormalization (S : Scheme.{u}) (hS : IsUnit (l : Γ(S, ⊤)))
    (p : Presentation l E S hS) :
    ∃ k : KernelSplittingData l E p, KernelScalarNormalization l E p k := by
  obtain ⟨k, hsquare, halpha⟩ := towerP1KernelSplittingBaseChange l E S hS p
  obtain ⟨hD, hlevels⟩ := towerP1KernelFiniteComparison l E S hS p k
  have hsum := kernel_sum_comparison_iso l E k
  refine ⟨k, ?_⟩
  refine
    { exchange_iso := ?_
      source_comparison_iso := hsum
      splitting_base_change := hsquare
      inverse_base_change := fun a ↦ kernel_inverse_base_change l E k a (hsquare a)
      trace_base_change := ?_
      alpha_iso := halpha
      scalar_identity := kernel_scalar_identity l E k hD hlevels
      cartier := hD
      levels := hlevels
      degree_zero_lift := kernel_degree_zero_lift l E k
      degree_zero_detection := kernel_degree_zero_detection l E }
  · intro a
    have he : k.exchange l E a =
        (SpTowerShriek.pull l E p.classes.base
          (p.operations.geometry (ProjectiveLine S ↘ S))).map k.splittingQ.inv ≫
            k.sumComparison l E ≫ (k.splittingProjection a).hom := by
      have ht := congrArg (fun t ↦ t ≫ (k.splittingProjection a).hom)
        (kernel_inverse_base_change l E k a (hsquare a))
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using ht
    rw [he]
    infer_instance
  · intro a
    dsimp only [KernelSplittingData.trace]
    rw [← Category.assoc, kernel_inverse_base_change l E k a (hsquare a)]
    rw [Category.assoc, KernelSplittingData.sumComparison]
    erw [biprod.lift_snd]
    rw [← Category.assoc]
    erw [← CategoryTheory.Functor.map_comp]
    rw [k.traceQ]

end AlgebraicGeometry.ProEtale.SpTowerP1

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
