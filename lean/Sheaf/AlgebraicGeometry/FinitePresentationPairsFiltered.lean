/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Comma.Over.Basic
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FinitePresentationRepresentatives
import Sheaf.AlgebraicGeometry.FinitePresentationBiprod
import WeilConjectures.AlgebraicGeometry.ModuleFinitePresentationCokernel
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# The small filtered category of finitely presented pairs over a module sheaf

Source: Stacks Project, Properties, Tag 01PJ,
lemma-directed-colimit-diagram-finite-presentation, choice of pairs and filteredness
(blueprint: lem-weil-pbc-finite-presentation-pairs-filtered).

The category is induced from the over category, so its arrows are precisely all module
maps commuting with the given maps to the target. The diagram and cocone below are explicit
constructions. The representative family is indexed by maps from finite-presentation
representatives, and filteredness follows using biproducts and cokernels.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The category on a set of pairs over `F`, with all commuting triangles as arrows.
Its objects are `I`; an arrow has underlying map `G i ⟶ G j` satisfying
`u ≫ α j = α i`. Identities and composition are the underlying module maps.
Source: Stacks Project, Properties, Tag 01PJ, choice of the pair category
(blueprint: lem-weil-pbc-finite-presentation-pairs-filtered). -/
abbrev ModulePairIndex {X : Scheme.{u}} {I : Type u} {F : X.Modules}
    {G : I → X.Modules} (α : ∀ i : I, G i ⟶ F) :=
  InducedCategory (Over F) (fun i : I ↦ Over.mk (α i))

/-- The diagram sending a pair to its source and a triangle to its underlying module map.
Source: Stacks Project, Properties, Tag 01PJ, the diagram of pairs
(blueprint: lem-weil-pbc-finite-presentation-pairs-filtered). -/
def modulePairDiagram {X : Scheme.{u}} {I : Type u} {F : X.Modules}
    {G : I → X.Modules} (α : ∀ i : I, G i ⟶ F) :
    ModulePairIndex α ⥤ X.Modules :=
  inducedFunctor (fun i : I ↦ Over.mk (α i)) ⋙ Over.forget F

/-- The canonical cocone with vertex `F` and components `α i` on the pair diagram.
Naturality is exactly the commuting-triangle condition defining the arrows.
Source: Stacks Project, Properties, Tag 01PJ, the cocone of pairs
(blueprint: lem-weil-pbc-finite-presentation-pairs-filtered). -/
def modulePairCocone {X : Scheme.{u}} {I : Type u} {F : X.Modules}
    {G : I → X.Modules} (α : ∀ i : I, G i ⟶ F) :
    Cocone (modulePairDiagram α) :=
  (Over.forgetCocone F).whisker (inducedFunctor (fun i : I ↦ Over.mk (α i)))

/-- There is a small filtered family of all finitely presented pairs over a quasi-coherent
module on a quasi-compact quasi-separated scheme, up to isomorphism of pairs.
The functor and cocone specified by the statement are `modulePairDiagram α` and
`modulePairCocone α`; their object, arrow and component assignments are definitional.
Source: Stacks Project, Properties, Tag 01PJ, proof through filteredness
(blueprint: lem-weil-pbc-finite-presentation-pairs-filtered).

Proof:
1. Choose finite-presentation representatives `P j` using
   lem-weil-pbc-module-finite-presentation-representatives. Set `I` to the disjoint union
   of the sets of module maps `P j ⟶ F`. For a pair `(G, ψ)`, choose `e : P j ≅ G`
   and the index `(j, e.hom ≫ ψ)`. This gives the representing equation.
2. The over-category construction gives exactly the displayed Hom sets and module-map
   identities and composition (def-weil-sheaf-of-modules-category). These are small sets.
   The zero module has a rank-zero finite presentation
   (def-weil-pbc-module-finite-type-presentation); representing its map to `F` gives
   nonemptiness.
3. For two indices use `G i ⊞ G j`, finitely presented by
   lem-weil-pbc-module-finite-presentation-direct-sum, and its map to `F` induced by
   the two given maps (def-weil-additive-category). Represent this pair by `G k`.
   The inclusions followed by the inverse representing isomorphism give arrows to `k`.
4. For parallel arrows `a, b`, the cokernel of `a - b` is finitely presented by
   lem-weil-pbc-module-finite-presentation-cokernel. The target map kills `a - b`,
   hence factors through the cokernel (def-weil-sheaf-of-modules-category).
   Represent this pair; the quotient map followed by the inverse representing
   isomorphism is the required arrow equalizing `a` and `b`.
5. These are the three conditions of def-weil-pbc-category-colimit. The induced
   forgetful functor gives the source modules and maps, and the commuting equations
   give the canonical cocone, as constructed above. -/
theorem exists_finitePresentation_pairs_filtered
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (I : Type u) (G : I → X.Modules) (α : ∀ i : I, G i ⟶ F),
      (∀ i : I, (G i).IsFinitePresentation) ∧
      (∀ (H : X.Modules), H.IsFinitePresentation → ∀ ψ : H ⟶ F,
        ∃ (i : I) (e : G i ≅ H), e.hom ≫ ψ = α i) ∧
      IsFiltered (ModulePairIndex α) := by
  classical
  obtain ⟨J, P, hP, hrep⟩ :=
    RingedSpace.exists_finitePresentation_representatives X.toRingedSpace
  let I := Σ j : J, P j ⟶ F
  let G : I → X.Modules := fun i ↦ P i.1
  let α : ∀ i : I, G i ⟶ F := fun i ↦ i.2
  have hG (i : I) : (G i).IsFinitePresentation := hP i.1
  have hpair (H : X.Modules) (hH : H.IsFinitePresentation) (ψ : H ⟶ F) :
      ∃ (i : I) (e : G i ≅ H), e.hom ≫ ψ = α i := by
    obtain ⟨j, ⟨e⟩⟩ := hrep H hH
    exact ⟨⟨j, e.inv ≫ ψ⟩, e.symm, rfl⟩
  refine ⟨I, G, α, hG, hpair, ?_⟩
  let Z : X.Modules := SheafOfModules.free PEmpty.{u + 1}
  let p := SheafOfModules.presentationOfIsCokernelFree
    (0 : SheafOfModules.free PEmpty.{u + 1} ⟶ Z) (𝟙 Z)
    (by simp) (CokernelCofork.IsColimit.ofId _ rfl)
  have : p.IsFinite := ⟨⟨inferInstanceAs (Finite PEmpty.{u + 1})⟩,
    ⟨inferInstanceAs (Finite PEmpty.{u + 1})⟩⟩
  have hZ : Z.IsFinitePresentation := p.isFinitePresentation
  obtain ⟨i₀, _, _⟩ := hpair Z hZ 0
  refine { nonempty := ⟨i₀⟩, cocone_objs := ?_, cocone_maps := ?_ }
  · intro i j
    have := hG i
    have := hG j
    have hB : (G i ⊞ G j).IsFinitePresentation :=
      RingedSpace.isFinitePresentation_biprod X.toRingedSpace (G i) (G j)
    obtain ⟨k, e, he⟩ := hpair (G i ⊞ G j) hB (biprod.desc (α i) (α j))
    refine ⟨k, InducedCategory.homMk (Over.homMk (biprod.inl ≫ e.inv) ?_),
      InducedCategory.homMk (Over.homMk (biprod.inr ≫ e.inv) ?_), trivial⟩
    · change (biprod.inl ≫ e.inv) ≫ α k = α i
      rw [← he]
      simp
    · change (biprod.inr ≫ e.inv) ≫ α k = α j
      rw [← he]
      simp
  · intro i j a b
    have := hG i
    have := hG j
    let d : G i ⟶ G j := a.hom.left - b.hom.left
    have hd : d ≫ α j = 0 := by
      dsimp only [d]
      rw [Preadditive.sub_comp]
      exact sub_eq_zero.mpr ((Over.w a.hom).trans (Over.w b.hom).symm)
    let q : G j ⟶ cokernel d := cokernel.π d
    let β : cokernel d ⟶ F := cokernel.desc d (α j) hd
    have hQ : (cokernel d).IsFinitePresentation :=
      RingedSpace.isFinitePresentation_cokernel_of_both_isFinitePresentation
        X.toRingedSpace d
    obtain ⟨k, e, he⟩ := hpair (cokernel d) hQ β
    have hv : (q ≫ e.inv) ≫ α k = α j := by
      rw [← he]
      simp [q, β]
    refine ⟨k, InducedCategory.homMk (Over.homMk (q ≫ e.inv) hv), ?_⟩
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    change a.hom.left ≫ (q ≫ e.inv) = b.hom.left ≫ (q ≫ e.inv)
    have hq : a.hom.left ≫ q = b.hom.left ≫ q := by
      apply sub_eq_zero.mp
      rw [← Preadditive.sub_comp]
      exact cokernel.condition d
    simpa only [← Category.assoc] using congrArg (fun f ↦ f ≫ e.inv) hq

end AlgebraicGeometry.Scheme.Modules
