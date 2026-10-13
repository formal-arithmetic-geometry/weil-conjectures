/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Sections over graphs extend by zero

Source: Stacks Project, Tag 0F4L, first paragraph of the proof, and Tag 01KT
(blueprint: lem-weil-pbc-etale-graph-section-extension-map).

The sum presheaf is the left Kan extension used by `Etale.etaleLowerShriek` before
sheafification. Its Kan-extension unit is the inclusion of the graph-indexed summand.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Graph geometry, clause 1 of Stacks 0F4L's presheaf construction
(blueprint: lem-weil-pbc-etale-graph-section-extension-map).

Proof: cancellation of étale morphisms gives `Etale φ`. The graph is a section of
`pullback.fst V.hom π`, which is étale by base change and separated since it is finite.
The étale-section-clopen-immersion lemma gives an open and closed immersion. An open
immersion identifies its source with the open subscheme of its image.
-/
theorem etale_graph_clopen
    {X U : Scheme.{u}} (π : U ⟶ X) [IsFinite π] [Etale π]
    (V : X.Etale) (φ : V.left ⟶ U) (h : V.hom = φ ≫ π) :
    let Γ := pullback.lift (𝟙 V.left) φ (by simp [h])
    Etale φ ∧ IsOpenImmersion Γ ∧ IsClosedImmersion Γ ∧
      ∃ O : (pullback V.hom π).Opens,
        (O : Set (pullback V.hom π : Scheme.{u})) = Set.range Γ ∧
          ∃ γ : V.left ≅ O.toScheme, γ.hom ≫ O.ι = Γ := by
  sorry

/-- Extension of graph sections, clauses 2 and 3 of Stacks 0F4L's presheaf construction
(blueprint: lem-weil-pbc-etale-graph-section-extension-map).

Proof: (1) Étale cancellation and base change give the objects and graph morphism.
(2) Finiteness gives separatedness of the projection; the section lemma (01KT) and
étaleness make the graph open and closed. (3) Cover by the graph and its complement.
The sheaf condition, zero sections on the empty scheme, and empty cross intersections
identify sections with the product of the two components. (4) Restriction maps and
sheaf morphisms are Λ-linear. (5) The inverse of this product decomposition on `(s,0)`
is the unique linear extension. (6) Graphs pull back to graphs, by the universal
property of the fibre product and factorization through open subschemes.
(7) Uniqueness makes extension commute with restriction. (8) Sum the extensions on
the finitely supported summands to obtain the presheaf morphism. (9) Commutation of
sheaf morphisms with both component restrictions gives naturality in the sheaf.

Dependency route: step 1 uses `lem-weil-pbc-etale-base-change-finite-limits`,
`lem-weil-pbc-etale-composition-cancellation`, and `def-pc-fibre-product`.
Step 2 uses `lem-weil-pbc-finite-morphism-permanence`, `def-weil-finite-integral-morphism`,
`lem-weil-pbc-affine-morphism-permanence`, and `lem-weil-pbc-etale-section-clopen-immersion`.
Step 3 uses `def-weil-pbc-etale-site`, `def-weil-pbc-abelian-etale-sheaves`, and
`lem-weil-pbc-open-immersion-monomorphism`. Step 4 uses `def-weil-pbc-constant-sheaf`,
`def-weil-pbc-sheafification`, and `def-weil-sheaf-of-modules-category`.
Step 5 is elementary linear algebra. Step 6 additionally uses
`lem-weil-pbc-morphism-factors-through-open-subscheme`. Steps 7 and 9 use uniqueness;
step 8 uses `def-weil-pbc-etale-sum-extension` and `def-weil-pbc-direct-image`.
-/
theorem etale_graph_section_extension_map
    {X U : Scheme.{u}} (π : U ⟶ X) [IsFinite π] [Etale π]
    (Λ : Type (u + 1)) [CommRing Λ] :
    let L := MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : Etale π)
    let B := MorphismProperty.Over.pullback @Etale ⊤ π
    let P := sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙ L.op.lan
    let D := Etale.lowerStar (ModuleCat.{u + 1} Λ) π ⋙
      sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    ∃ c : P ⟶ D,
      ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (W : U.Etale),
        let γ : W ⟶ B.obj (L.obj W) :=
          (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ π inferInstance trivial).unit.app W
        let e : M.obj.obj (op W) ⟶ M.obj.obj (op (B.obj (L.obj W))) :=
          (L.op.lanUnit.app M.obj).app (op W) ≫ (c.app M).app (op (L.obj W))
        ∀ (s : M.obj.obj (op W)) (t : M.obj.obj (op (B.obj (L.obj W)))),
          (M.obj.map γ.op t = s ∧
            ∀ (T : U.Etale) (j : T ⟶ B.obj (L.obj W)),
              IsOpenImmersion j.left →
              Set.range j.left = (Set.range γ.left)ᶜ → M.obj.map j.op t = 0) ↔
          t = e s := by
  sorry

/-- The inverse image of a graph is the graph of the restricted morphism, the key
compatibility in Stacks 0F4L's presheaf construction
(blueprint: lem-weil-pbc-etale-graph-section-extension-map).

Proof: the fibre-product identities show the restricted graph maps into the old graph.
Conversely, factor the inverse-image open subscheme through the old graph image;
its second component is φ composed with its first component. Pullback uniqueness
then identifies it with the restricted graph. This is step 6 of the node's proof.
-/
theorem etale_graph_preimage
    {X U : Scheme.{u}} (π : U ⟶ X) [IsFinite π] [Etale π]
    (V V' : X.Etale) (a : V' ⟶ V) (φ : V.left ⟶ U) (h : V.hom = φ ≫ π) :
    let Γ := pullback.lift (𝟙 V.left) φ (by simp [h])
    let Γ' := pullback.lift (𝟙 V'.left) (a.left ≫ φ)
      (by simp only [Category.id_comp, Category.assoc, ← h, MorphismProperty.Over.w])
    let aU := (MorphismProperty.Over.pullback @Etale ⊤ π).map a
    aU.left ⁻¹' Set.range Γ = Set.range Γ' := by
  sorry

end AlgebraicGeometry
