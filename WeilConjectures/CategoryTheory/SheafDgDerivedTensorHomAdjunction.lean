/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SheafDgBimoduleModels
import Mathlib.CategoryTheory.Localization.Adjunction

/-! # Derived tensor-Hom adjunction for sheaf dg bimodules

Source: Stacks Project, `sdga.tex`, Tags 0FRS, 0FTN and 0FTQ, in the case where
both ordinary functors preserve quasi-isomorphisms
(blueprint: lem-sf-dg-derived-tensor-hom-adjunction).

We use the fixed localization of right dg module sheaves, equivalently the
localization of their homotopy category, as specified by `RingedSiteDg.Derived`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}}

/-- Tensor-Hom adjunction after localization, with the ordinary currying, unit and
counit fixed. The two model arguments identify the ordinary constructions by universal
properties, rather than postulating adjoints. The two preservation assumptions are
exactly preservation of isomorphisms on all underlying cohomology sheaves.

Source: Stacks `sdga.tex`, Tags 0FRS, 0FTN and 0FTQ; localization formulas as in
Mathlib `CategoryTheory/Localization/Adjunction.lean`
(blueprint: lem-sf-dg-derived-tensor-hom-adjunction).

Proof:
1. Apply lem-sf-dg-ordinary-tensor-hom: the balanced tensor and universal evaluation
identify currying with v |-> (m |-> (n |-> v(m tensor n))). Its inverse is evaluation.
The differential is the commutator differential, so these maps are chain maps and
respect degree-minus-one boundaries. Taking H^0 yields the ordinary adjunction on
homotopy classes, and already yields the chain-map adjunction `adj` below. Its unit
is m |-> (n |-> m tensor n), and its counit is f tensor n |-> f(n).
2. Use lem-sfb-sheaf-dg-homotopy-system to identify homotopies, cohomology sheaves and
quasi-isomorphisms. The fixed localization `Q` of chain maps agrees with localization
of K(A): the cylinder quasi-isomorphisms identify homotopic maps. There is no bound
on complexes and no commutativity condition on A or B.
3. Both preservation assumptions let the localization universal property
(lem-weil-pbc-localization-universal-property) construct `F'`, `G'` and the natural
factorization isomorphisms `t`, `h`. Apply lem-sfb-adjunction-localization to `adj`
with these comparisons to obtain `adj'`.
4. The component formulas for localized adjunctions are precisely `unit` and `counit`
below. Substitute the unit formula in the transpose formula and use naturality of
`h` to get the displayed Hom compatibility on every chain map. The Hom bijection
on arbitrary derived arrows is determined by this equation and naturality: represent
an arrow by a fraction, use the inverse of the localized quasi-isomorphism, and
apply the chain-map equation to the numerator. The two triangle identities give
inverse Hom bijections. Thus all the Hom, unit and counit normalizations hold.
-/
theorem sheaf_dg_derived_tensor_hom_adjunction
    (A B : Algebra O) (N : Bimod A B)
    (F : Module A ⥤ Module B) (G : Module B ⥤ Module A)
    (tensor : SheafBalancedTensorModel N F) (hom : SheafBimoduleHomModel N G)
    (tensor_preserves : ∀ (M M' : Module A) (f : M ⟶ M'),
      quasiIsomorphisms A f → quasiIsomorphisms B (F.map f))
    (hom_preserves : ∀ (L L' : Module B) (f : L ⟶ L'),
      quasiIsomorphisms B f → quasiIsomorphisms A (G.map f)) :
    ∃ adj : F ⊣ G, IsSheafBimoduleCurrying N tensor hom adj ∧
      ∃ (F' : Derived A ⥤ Derived B) (G' : Derived B ⥤ Derived A)
        (t : Q A ⋙ F' ≅ F ⋙ Q B) (h : Q B ⋙ G' ≅ G ⋙ Q A) (adj' : F' ⊣ G'),
        (∀ (M : Module A) (L : Module B) (f : F.obj M ⟶ L),
          adj'.homEquiv ((Q A).obj M) ((Q B).obj L)
              (t.hom.app M ≫ (Q B).map f) =
            (Q A).map (adj.homEquiv M L f) ≫ h.inv.app L) ∧
        (∀ M : Module A,
          adj'.unit.app ((Q A).obj M) =
            (Q A).map (adj.unit.app M) ≫ h.inv.app (F.obj M) ≫
              G'.map (t.inv.app M)) ∧
        (∀ L : Module B,
          adj'.counit.app ((Q B).obj L) =
            F'.map (h.hom.app L) ≫ t.hom.app (G.obj L) ≫
              (Q B).map (adj.counit.app L)) := by
  sorry

end CategoryTheory.RingedSiteDg
