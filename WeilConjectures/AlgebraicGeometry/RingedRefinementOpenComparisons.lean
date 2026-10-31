/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedRefinementConstruction
public import WeilConjectures.AlgebraicGeometry.CanonicalRingedRefinementSquare
import WeilConjectures.AlgebraicGeometry.RingedRefinementOpenComparisonData
import WeilConjectures.AlgebraicGeometry.RingedRefinementOpenCompatibility

/-!
# Normalized open comparisons for ringed refinement

This is the first independent component of the arbitrary-ring clopen refinement
construction.  It constructs the open base-change and clopen projection data and
checks the coefficient square before the residual coherence and shift laws.
Source: coefficient supplement Steps 1--6 (Stacks 03DI, 07A6, 0F7B).
(blueprint: new-ringed-refinement-open-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.RingedRefinement

attribute [local irreducible] Calculus.openAdjunction Calculus.shriek
  AlgebraicGeometry.Scheme.ProjectionRestriction.Operation.left
  Spatial.square Spatial.openFactor Spatial.sectionPull


private theorem scalar_h_of_factors {m : Mode} {T : Scheme.{u}}
    {c : Coefficients m T} {o : Calculus c} {p : Spatial o}
    (sc : ScalarComparisons o) (e : OpenComparisons p)
    {X Y Z : Over T} {u : Y ⟶ Z} {j₁ : X ⟶ Y} {j₂ : X ⟶ Z}
    [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    (d : Shape u j₁ j₂) {A B : Rings m T} (a : A ⟶ B) (M : category c X A)
    (hbeta :
      (sc.pull u a).hom.app ((o.shriek j₂ A).obj M) ≫
          (o.scalar Y a).T.map ((e.beta d.b d.q u j₂ d.pullback A).hom.app M) ≫
          (sc.delta d.b a).hom.app ((o.operation d.q A).left.obj M) ≫
          (o.shriek d.b B).map ((sc.pull d.q a).inv.app M) =
        (o.operation u B).left.map ((sc.delta j₂ a).hom.app M) ≫
          (e.beta d.b d.q u j₂ d.pullback B).hom.app ((o.scalar X a).T.obj M))
    (hpi : ∀ N : category c d.V A,
      (o.scalar d.V a).T.map ((e.pi d.s d.clopen A).app N) ≫
          (sc.delta d.s a).hom.app ((o.operation d.s A).left.obj N) =
        (e.pi d.s d.clopen B).app ((o.scalar d.V a).T.obj N) ≫
          (o.shriek d.s B).map ((sc.pull d.s a).hom.app N))
    (hsection :
      (sc.pull d.s a).inv.app ((o.operation d.q A).left.obj M) ≫
          (o.operation d.s B).left.map ((sc.pull d.q a).inv.app M) ≫
          (p.sectionPull d B).hom.app ((o.scalar X a).T.obj M) =
        (o.scalar X a).T.map ((p.sectionPull d A).hom.app M))
    (hopen : ∀ N : category c X A,
      (o.scalar Y a).T.map ((p.openFactor d.s d.b j₁ d.openFactor A).hom.app N) ≫
          (sc.delta j₁ a).hom.app N =
        (sc.delta d.b a).hom.app ((o.shriek d.s A).obj N) ≫
          (o.shriek d.b B).map ((sc.delta d.s a).hom.app N) ≫
          (p.openFactor d.s d.b j₁ d.openFactor B).hom.app ((o.scalar X a).T.obj N)) :
    (sc.pull u a).hom.app ((o.shriek j₂ A).obj M) ≫
        (o.scalar Y a).T.map (e.h d A M) ≫ (sc.delta j₁ a).hom.app M =
      (o.operation u B).left.map ((sc.delta j₂ a).hom.app M) ≫
        e.h d B ((o.scalar X a).T.obj M) := by
  have hs :
      (sc.pull d.s a).hom.app ((o.operation d.q A).left.obj M) ≫
          (o.scalar X a).T.map ((p.sectionPull d A).hom.app M) =
        (o.operation d.s B).left.map ((sc.pull d.q a).inv.app M) ≫
          (p.sectionPull d B).hom.app ((o.scalar X a).T.obj M) := by
    rw [← hsection, Iso.hom_inv_id_app_assoc]
  have hb₁ := (sc.delta d.b a).hom.naturality
    ((o.shriek d.s A).map ((p.sectionPull d A).hom.app M))
  have hb₂ := (sc.delta d.b a).hom.naturality
    ((e.pi d.s d.clopen A).app ((o.operation d.q A).left.obj M))
  have hsn := (sc.delta d.s a).hom.naturality ((p.sectionPull d A).hom.app M)
  have hpn := (e.pi d.s d.clopen B).naturality ((sc.pull d.q a).inv.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map,
    Functor.id_obj] at hb₁ hb₂ hsn hpn
  have hi :
      (o.scalar d.V a).T.map
          ((e.pi d.s d.clopen A).app ((o.operation d.q A).left.obj M)) ≫
          (o.scalar d.V a).T.map
            ((o.shriek d.s A).map ((p.sectionPull d A).hom.app M)) ≫
          (sc.delta d.s a).hom.app M =
        (sc.pull d.q a).inv.app M ≫
          (e.pi d.s d.clopen B).app
            ((o.operation d.q B).left.obj ((o.scalar X a).T.obj M)) ≫
          (o.shriek d.s B).map
            ((p.sectionPull d B).hom.app ((o.scalar X a).T.obj M)) := by
    rw [hsn, ← Category.assoc, hpi]
    simp only [Category.assoc]
    rw [← (o.shriek d.s B).map_comp, hs, (o.shriek d.s B).map_comp]
    rw [← reassoc_of% hpn]
  simp only [OpenComparisons.h, Functor.map_comp, Category.assoc]
  rw [hopen]
  rw [reassoc_of% hb₁, reassoc_of% hb₂]
  rw [← (o.shriek d.b B).map_comp_assoc,
    ← (o.shriek d.b B).map_comp_assoc]
  rw [← Category.assoc] at hi
  rw [hi]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hbeta]


/-- The normalized open comparison package and its scalar compatibility.
Source: coefficient supplement Steps 1--6; arbitrary ordinary and vertical ringed sites.
(blueprint: new-ringed-refinement-open-comparisons).
Proof: take the normalized open-comparison object `e` of
`ringedRefinementOpenComparisonData`.  For a Shape `d`, a coefficient map `a` and an
input `M`, `ringedRefinementOpenFactorCompatibility` gives the scalar equations of the
four factors of `h` (beta, clopen projection, section retraction, open composition).
Expand `h` as beta followed by the open extensions of the projection, of the section
retraction and the open-composition iso; move the scalar comparisons across each
factor by these equations and by naturality of `delta` and of the projection
(`scalar_h_of_factors`).  The remaining word is `h` at `B`, which is `HCompatible`.
The scalar composition data `ac` is not needed.
-/
theorem ringedRefinementOpenComparisons {m : Mode} {T : Scheme.{u}}
    {c : Coefficients m T} (o : Calculus c) (p : Spatial o)
    (sc : ScalarComparisons o) (ac : ScalarComposition o) :
    ∃ e : OpenComparisons p, HCompatible sc e := by
  have _hac := ac
  obtain ⟨e⟩ := ringedRefinementOpenComparisonData o p
  refine ⟨e, ?_⟩
  intro X Y Z u j₁ j₂ _ _ _ _ _ h d A B a M
  obtain ⟨hb, hp, hs, ho⟩ := ringedRefinementOpenFactorCompatibility o p sc e d a M
  exact scalar_h_of_factors sc e d a M hb hp hs ho

end SheafOfModules.RingedRefinement
