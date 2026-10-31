/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! Signed-total assembly of a normalized ordinary tensor comparison.

Source: Stacks, Homology, Tags 0A5J and 012Z. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.tensorObjIsoSheafification

namespace TotalAssembly
universe a b x y

private theorem tensorHasMapBifunctor
    {D : Type a} [Category.{x} D] [Preadditive D] [MonoidalCategory D]
    [MonoidalPreadditive D] [HasCoproducts.{0} D]
    (P Q : CochainComplex D ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor D) (.up ℤ) := by
  infer_instance

attribute [local instance 20000] tensorHasMapBifunctor

section GenericTotal
variable {D : Type a} [Category.{x} D] [Preadditive D] [MonoidalCategory D]
  {E : Type b} [Category.{y} E] [Preadditive E] [MonoidalCategory E]
  [MonoidalPreadditive D] [MonoidalPreadditive E]
  [HasCoproducts.{0} D] [HasCoproducts.{0} E]
  (L : D ⥤ E) [L.Additive] [PreservesColimitsOfSize.{0, 0} L]
  (e : ∀ X Y : D, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)
  (he : ∀ {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y'),
    L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))

private theorem tensorMap_factor
    {P P' Q Q' : CochainComplex D ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    HomologicalComplex.mapBifunctorMap f (𝟙 Q) (curriedTensor D) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 P') g (curriedTensor D) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap f g (curriedTensor D) (.up ℤ) := by
  simp [HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]

include he in
private def tensorRestrictionNatTrans : (Functor.postcompose₂.obj L).obj (curriedTensor D) ⟶
    (((Functor.whiskeringLeft₂ E).obj L).obj L).obj (curriedTensor E) :=
  { app := fun X ↦
      { app := fun Y ↦ (e X Y).hom
        naturality := by
          intro Y Y' g
          change L.map (X ◁ g) ≫ (e X Y').hom =
            (e X Y).hom ≫ (L.obj X ◁ L.map g)
          simpa only [id_tensorHom, L.map_id] using he (𝟙 X) g }
    naturality := by
      intro X X' f
      ext Y
      change L.map (f ▷ Y) ≫ (e X' Y).hom =
        (e X Y).hom ≫ (L.map f ▷ L.obj Y)
      simpa only [tensorHom_id, L.map_id] using he f (𝟙 Y) }

include he in
omit [Preadditive D] [Preadditive E] [MonoidalPreadditive D] [MonoidalPreadditive E]
  [HasCoproducts.{0} D] [HasCoproducts.{0} E]
  [L.Additive] [PreservesColimitsOfSize.{0, 0} L] in
private theorem tensorRestrictionNatTrans_isIso (X Y : D) :
    IsIso (((tensorRestrictionNatTrans L e he).app X).app Y) :=
  (e X Y).isIso_hom

include he in
private theorem tensorTotalRestriction :
    ∃ γ : Functor.uncurry.obj ((curriedTensor D).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ L.mapHomologicalComplex (.up ℤ) ≅
      ((L.mapHomologicalComplex (.up ℤ)).prod (L.mapHomologicalComplex (.up ℤ))) ⋙
        Functor.uncurry.obj ((curriedTensor E).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ)),
      ∀ (P Q : CochainComplex D ℤ) (p q n : ℤ) (h : p + q = n),
        L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor D) p q n h) ≫
            (γ.hom.app (P, Q)).f n =
          (e (P.X p) (Q.X q)).hom ≫
            CochainComplex.ιMapBifunctor
              ((L.mapHomologicalComplex (.up ℤ)).obj P)
              ((L.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor E) p q n h := by
  let τ := tensorRestrictionNatTrans L e he
  let (X Y : D) : IsIso ((τ.app X).app Y) :=
    tensorRestrictionNatTrans_isIso L e he X Y
  have hIso (P Q : CochainComplex D ℤ) :
      IsIso (HomologicalComplex.mapBifunctorComparison
        (c₁ := .up ℤ) (c₂ := .up ℤ) τ (.up ℤ) P Q) := by
    apply HomologicalComplex.instIsIsoMapBifunctorComparisonOfAppFunctor
  let γ : Functor.uncurry.obj ((curriedTensor D).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ L.mapHomologicalComplex (.up ℤ) ≅
      ((L.mapHomologicalComplex (.up ℤ)).prod (L.mapHomologicalComplex (.up ℤ))) ⋙
        Functor.uncurry.obj ((curriedTensor E).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ)) :=
    NatIso.ofComponents
      (fun Z ↦ @asIso _ _ _ _
        (HomologicalComplex.mapBifunctorComparison
          (c₁ := .up ℤ) (c₂ := .up ℤ) τ (.up ℤ) Z.1 Z.2) (hIso Z.1 Z.2)) (by
        intro Z Z' f
        simp only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
          Functor.map₂HomologicalComplex, asIso_hom, tensorMap_factor]
        exact HomologicalComplex.mapBifunctorComparison_naturality
          (c₁ := .up ℤ) (c₂ := .up ℤ) τ (.up ℤ) f.1 f.2)
  refine ⟨γ, ?_⟩
  intro P Q p q n h
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
    Functor.map₂HomologicalComplex]
  dsimp only [γ, NatIso.ofComponents_hom_app, asIso_hom,
    HomologicalComplex.mapBifunctorComparison_f, CochainComplex.ιMapBifunctor]
  -- The inferred cochain shapes use definitionally equal integer addition instances.
  convert HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (c₁ := .up ℤ) (c₂ := .up ℤ) τ (.up ℤ) P Q p q n h using 1
  rfl

end GenericTotal

end TotalAssembly

private theorem finite_tensor_pure_of_summands
    {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i)
    (c : ∀ M N : FiniteModules A X,
        e.equivalence.functor.obj (M ⊗ N) ≅
          ((tensor R).obj (e.equivalence.functor.obj M)).obj (e.equivalence.functor.obj N))
    (hp : ∀ M N W x y, (c M N).hom.val.app W
          ((e.underlying.inv.app (M ⊗ N)).hom.app W
            (finitePure M N W x y)) =
        pure R (e.equivalence.functor.obj M) (e.equivalence.functor.obj N) W
          ((e.underlying.inv.app M).hom.app W x)
          ((e.underlying.inv.app N).hom.app W y))
    (s : FiniteTensorTotal e)
    (hs : ∀ (P Q : CochainComplex (FiniteModules A X) ℤ)
        (p q n : ℤ) (hn : p + q = n),
      e.equivalence.functor.map (HomologicalComplex.ιMapBifunctor P Q
          (curriedTensor (FiniteModules A X)) (.up ℤ) p q n hn) ≫ (s P Q).hom.f n =
        (c (P.X p) (Q.X q)).hom ≫ HomologicalComplex.ιMapBifunctor
          ((finiteComplexRealization e).obj P) ((finiteComplexRealization e).obj Q)
          (tensor R) (.up ℤ) p q n hn) :
    finiteTensorPure e s := by
  let F := e.equivalence.functor
  intro P Q p q n hn W x y
  let j := HomologicalComplex.ιMapBifunctor P Q
    (curriedTensor (FiniteModules A X)) (.up ℤ) p q n hn
  have hu := ConcreteCategory.congr_hom (congr_app
    (congrArg (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).map
      (e.underlying.inv.naturality j)) W) (finitePure (P.X p) (Q.X q) W x y)
  have hh := congrArg (fun f ↦ f.val.app W
    ((e.underlying.inv.app _).hom.app W (finitePure (P.X p) (Q.X q) W x y)))
      (hs P Q p q n hn)
  change ((s P Q).hom.f n).val.app W
    ((e.underlying.inv.app
        ((HomologicalComplex.mapBifunctor P Q
          (curriedTensor (FiniteModules A X)) (.up ℤ)).X n)).hom.app W
      (j.hom.app W (finitePure (P.X p) (Q.X q) W x y))) = _
  change (e.underlying.inv.app
        ((HomologicalComplex.mapBifunctor P Q
          (curriedTensor (FiniteModules A X)) (.up ℤ)).X n)).hom.app W
      (j.hom.app W (finitePure (P.X p) (Q.X q) W x y)) =
    (F.map j).val.app W ((e.underlying.inv.app _).hom.app W
      (finitePure (P.X p) (Q.X q) W x y)) at hu
  rw [hu]
  exact hh.trans (congrArg
    ((HomologicalComplex.ιMapBifunctor
      ((finiteComplexRealization e).obj P) ((finiteComplexRealization e).obj Q)
      (tensor R) (.up ℤ) p q n hn).val.app W) (hp _ _ W x y))

/-- A natural ordinary tensor comparison induces the normalized signed-total comparison.

Source: Stacks, Homology, Tags 0A5J and 012Z (tensor double complex and signed total).
(blueprint: lem-sf-finite-tensor-total-comparison-helper).

Proof: apply the generic tensor-total restriction theorem to the additive
realization equivalence, which preserves the total-degree coproducts, and the
supplied natural ordinary tensor isomorphisms. That theorem applies the
bifunctor comparison to the natural tensor map; additivity respects the signed
differentials, and preservation of coproducts makes the comparison invertible.
Its coprojection equation says that F of every source summand injection,
followed by the degree comparison, is the ordinary comparison followed by the
target injection. Evaluate this identity on the inverse underlying image of a
fixed pure pair. Naturality of the underlying inverse moves it across the
source injection, and the ordinary pure-pair equation gives exactly the required
finiteTensorPure equation. This works in every degree for arbitrary unbounded
complexes, including zero complexes, without any flatness assumption. -/
theorem finite_tensor_total_of_ordinary
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj)
    [Presheaf.IsLocallySurjective (ProEt.topology X) i]
    (e : FiniteRealization A X R i)
    (c : ∀ M N : FiniteModules A X,
        e.equivalence.functor.obj (M ⊗ N) ≅
          ((tensor R).obj (e.equivalence.functor.obj M)).obj (e.equivalence.functor.obj N))
    (hc : ∀ M M' N N' (f : M ⟶ M') (g : N ⟶ N'),
        e.equivalence.functor.map (f ⊗ₘ g) ≫
            (c M' N').hom = (c M N).hom ≫
              (e.equivalence.functor.map f ⊗ₘ e.equivalence.functor.map g))
    (hp : ∀ M N W x y, (c M N).hom.val.app W
          ((e.underlying.inv.app (M ⊗ N)).hom.app W
            (finitePure M N W x y)) =
        pure R (e.equivalence.functor.obj M) (e.equivalence.functor.obj N) W
          ((e.underlying.inv.app M).hom.app W x)
          ((e.underlying.inv.app N).hom.app W y)) :
    ∃ s : Functor.uncurry.obj
        ((curriedTensor (FiniteModules A X)).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ finiteComplexRealization e ≅
      ((finiteComplexRealization e).prod (finiteComplexRealization e)) ⋙ total R,
      finiteTensorPure e (fun P Q ↦ s.app (P, Q)) := by
  let F := e.equivalence.functor
  let : MonoidalPreadditive (Mod R) := SheafOfModules.cochainModulesPreadditive R
  obtain ⟨s, hs⟩ := TotalAssembly.tensorTotalRestriction F c (by
    intro M M' N N' f g
    exact hc M M' N N' f g)
  refine ⟨s, ?_⟩
  exact finite_tensor_pure_of_summands e c hp (fun P Q ↦ s.app (P, Q)) hs

end SheafOfModules.OpenTensorNormalization
