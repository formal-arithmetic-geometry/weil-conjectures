/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedRefinement.RingedRefinementData
import WeilConjectures.CategoryTheory.AdjunctionRefinementTranspose
import WeilConjectures.CategoryTheory.NormalizedIdentityMate
/-! Proper/open normalization from an intrinsic alpha equation.
(blueprint: new-lem-pur-ringed-refinement-finite-normalization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u k
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization
namespace SheafOfModules.RingedRefinement
-- Combine the two abstract categorical calculations before specializing them.
-- This keeps the derived-category instance arguments fixed by the final goal.
private theorem normalized_transport
    {C A D A' D' : Type k}
    [Category.{k} C] [Category.{k} A] [Category.{k} D]
    [Category.{k} A'] [Category.{k} D']
    {F G : C ⥤ C} {L : A ⥤ D} {R : D ⥤ A}
    {L' : A' ⥤ D'} {R' : D' ⥤ A'}
    (V : A ⥤ A') (W : D ⥤ D')
    (i : F ⊣ G) (a : L ⊣ R) (b : L' ⊣ R') (J₂ : C ⥤ A) (J₁ : C ⥤ D)
    (α : J₂ ⋙ L ⟶ F ⋙ J₁) (γ : G ⋙ J₂ ⟶ J₁ ⋙ R)
    (g : F ≅ 𝟭 C) (rho : G ≅ 𝟭 C)
    (hn : rho.inv = conjugateEquiv Adjunction.id i g.hom)
    (hγ : γ = mateEquiv i a α)
    (l : L ⋙ W ≅ V ⋙ L') (r : R ⋙ V ≅ W ⋙ R')
    (hu : ∀ N : A, V.map (a.unit.app N) ≫ r.hom.app (L.obj N) ≫
      R'.map (l.hom.app N) = b.unit.app (V.obj N))
    (M : C) {M' : A'} {N' : D'}
    (s : V.obj (J₂.obj M) ⟶ M') (t : W.obj (J₁.obj M) ⟶ N')
    (h : L'.obj M' ⟶ N') (β : M' ⟶ R'.obj N')
    (hβ : b.homEquiv _ _ h = β)
    (hf : W.map (α.app M ≫ J₁.map (g.hom.app M : F.obj M ⟶ M)) ≫ t =
      l.hom.app (J₂.obj M) ≫ L'.map s ≫ h) :
    V.map (J₂.map (rho.inv.app M) ≫ γ.app M) ≫
        r.hom.app (J₁.obj M) ≫ R'.map t = s ≫ β := by
  subst γ
  have ht := CategoryTheory.adjunctionRefinementTranspose
    (M := J₂.obj M) (N := J₁.obj M) a b V W l r hu
    (α.app M ≫ J₁.map (g.hom.app M : F.obj M ⟶ M)) s t h hf
  have hm := CategoryTheory.mateEquiv_identity_refinement a i J₂ J₁ α g rho hn M
  have hx := congrArg
    (fun f ↦ V.map f ≫ r.hom.app (J₁.obj M) ≫ R'.map t) hm
  exact hx.symm.trans (ht.trans (congrArg (fun f ↦ s ≫ f) hβ))

attribute [local irreducible] ProEtale.StrictTower.G ProEtale.StrictTower.R
  ProEtale.StrictTower.J ProEtale.StrictTower.adj ProEtale.StrictTower.gId
  ProEtale.StrictTower.alpha FiniteRealization.derived

/-- Transport of the intrinsic alpha equation gives finite refinement normalization.
Source: coefficient supplement Step 10; Stacks 07A6 and 0B65.
Proof: the comparison adjunction's unit equation allows transport of the alpha
transpose. Identity normalization identifies its strict side with gamma preceded
by the inverse identity comparison; the package refinement adjunct identifies its
other side with the specified refinement map.
(blueprint: new-lem-pur-ringed-refinement-finite-normalization). -/
theorem finiteNormalization_of_comparison {T : Scheme.{u}} (P : Package .systems T)
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (e : ∀ W : Over T, FiniteRealization P B W) (k : FiniteComparison P B e)
    (ha : ∀ {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
      [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
      [QuasiCompact j₁.left] [QuasiCompact j₂.left] (h : j₁ ≫ u = j₂)
      (d : Shape u j₁ j₂) (M : ProEtale.StrictTower.Derived.{u} B X.left),
      (e Y).derived.map
          ((ProEtale.StrictTower.alpha.{u} B j₁.left (𝟙 X.left) u.left j₂.left
            ((congrArg (fun f ↦ f.left) h).trans (Category.id_comp j₂.left).symm)).app M ≫
            (ProEtale.StrictTower.J.{u} B j₁.left).map
              ((ProEtale.StrictTower.gId.{u} B X.left).hom.app M :
                (ProEtale.StrictTower.G.{u} B (𝟙 X.left)).obj M ⟶ M)) ≫
          (k.shriekIso j₁).hom.app M =
        (k.pull u).hom.app ((ProEtale.StrictTower.J.{u} B j₂.left).obj M) ≫
          (P.operations.operation u (finiteRing B T)).left.map
            ((k.shriekIso j₂).hom.app M) ≫
          P.opens.h d (finiteRing B T) ((e X).derived.obj M)) :
    FiniteNormalization P B e k := by
  intro X Y Z u j₁ j₂ _ _ _ _ _ h d M
  -- Infer the categories from the normalization goal before filling the adjunction data.
  apply normalized_transport
  case i => exact ProEtale.StrictTower.adj.{u} B (𝟙 X.left)
  case a => exact ProEtale.StrictTower.adj.{u} B u.left
  case b => exact (P.operations.operation u (finiteRing B T)).derivedAdjunction
  case α =>
    exact ProEtale.StrictTower.alpha.{u} B j₁.left (𝟙 X.left) u.left j₂.left
      ((congrArg (fun f ↦ f.left) h).trans (Category.id_comp j₂.left).symm)
  case g => exact ProEtale.StrictTower.gId.{u} B X.left
  case l => exact k.pull u
  case h => exact P.opens.h d (finiteRing B T) ((e X).derived.obj M)
  case hn => rfl
  case hγ => rfl
  case hu =>
    have hu := (k.adjunction u).unit
    rw [k.adjunction_pull u, k.adjunction_push u] at hu
    exact hu
  case hβ =>
    exact P.refinements.adjunct u j₁ j₂ h d (finiteRing B T) ((e X).derived.obj M)
  case hf => exact ha u j₁ j₂ h d M
end SheafOfModules.RingedRefinement
