/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import Sheaf.Algebra.Homology.StalkTensorComplexDegrees
import Sheaf.Algebra.Homology.StalkTensorComplexDifferential
import Mathlib.Topology.Sheaves.Abelian

/-!
# Stalks commute with total tensor complexes

Source: Stacks Project, Cohomology, Lemma 06YB, tensor-stalk identification
(blueprint: lem-pc-stalk-tensor-complex).
-/

@[expose] public section

universe u₁

open CategoryTheory MonoidalCategory TopologicalSpace AlgebraicGeometry

namespace CochainComplex

variable (X : RingedSpace.{u₁}) (x : X)

set_option hygiene false in
local notation "O" => (sheafCompose (Opens.grothendieckTopology (X : Type u₁))
  (forget₂ CommRingCat.{u₁} RingCat.{u₁})).obj X.sheaf
set_option hygiene false in
local notation "S" => (RingedSpace.moduleStalkFunctor X x).mapHomologicalComplex (.up ℤ)

noncomputable local instance : MonoidalCategory (SheafOfModules.{u₁} O) :=
  SheafOfModules.monoidalCategory X.sheaf

private instance stalk_additive : (RingedSpace.moduleStalkFunctor X x).Additive where
  map_add := by
    intro M N f g
    ext m
    change (TopCat.Presheaf.stalkFunctor Ab x).map
      ((PresheafOfModules.toPresheaf _).map (f + g).val) m = _
    change (TopCat.Presheaf.stalkFunctor Ab x).map
      ((PresheafOfModules.toPresheaf _).map (f.val + g.val)) m = _
    rw [Functor.map_add, Functor.map_add]
    rfl

-- Elaborating the two total tensor constructions and their coproduct instances needs
-- more than the default heartbeat budget; the file still compiles within 60 seconds.
set_option maxHeartbeats 1500000 in
-- Elaborating both total tensor coproducts exceeds the default heartbeat budget.
/-- (blueprint: lem-pc-stalk-tensor-complex) Stacks Project, Cohomology, Lemma 06YB:
there is an isomorphism from the stalk of the total tensor complex to the total tensor
complex of the stalks, natural in both complexes. Both total complexes use direct sums
in degree `n` over `p + q = n` and differential `d_F ⊗ 1 + (-1)^p 1 ⊗ d_K`.

Proof:
1. By `def-pc-tensor-complex-sheaves`, the degree `n` term is the direct sum of `F^p ⊗ K^q`.
   Apply `lem-pc-stalk-direct-sums` to move the stalk through this direct sum.
2. Apply `lem-pc-ringed-space-module-stalk-tensor` to each summand. Its natural comparison
   identifies the summands with `F_x^p ⊗ K_x^q`, giving the degreewise isomorphisms.
3. Naturality of the module comparison carries the differentials on the two factors to
   their stalk maps. Additivity preserves the sign `(-1)^p`. Thus the maps commute with
   the total differential and form isomorphisms of complexes. The same naturality on each
   summand gives the asserted square for every pair of morphisms of complexes. -/
theorem exists_stalk_tensor_complex_iso :
    ∃ e : ∀ (F K : CochainComplex (SheafOfModules.{u₁} O) ℤ),
      (S).obj (mapBifunctor F K (curriedTensor _)) ≅
        mapBifunctor ((S).obj F) ((S).obj K) (curriedTensor _),
      ∀ (F K F' K' : CochainComplex (SheafOfModules.{u₁} O) ℤ)
        (f : F ⟶ F') (g : K ⟶ K'),
        (S).map (HomologicalComplex.mapBifunctorMap f g (curriedTensor _) (.up ℤ)) ≫
            (e F' K').hom =
          (e F K).hom ≫ HomologicalComplex.mapBifunctorMap
            ((S).map f) ((S).map g) (curriedTensor _) (.up ℤ) := by
  obtain ⟨φ, _, hφ⟩ := SheafOfModules.stalkTensorIso X x
  obtain ⟨e, he⟩ := exists_stalk_tensor_degree_iso X x φ
  let := stalk_additive X x
  let T := RingedSpace.moduleStalkFunctor X x
  have h_ext (F K : CochainComplex (SheafOfModules.{u₁} O) ℤ) (n : ℤ)
      (M : ModuleCat.{u₁} (X.presheaf.stalk x))
      (a b : ((S).obj (mapBifunctor F K (curriedTensor _))).X n ⟶ M)
      (h : ∀ p q (hpq : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (p, q) = n),
        T.map (HomologicalComplex.ιMapBifunctor F K (curriedTensor _) (.up ℤ)
          p q n hpq) ≫ a = T.map (HomologicalComplex.ιMapBifunctor F K
            (curriedTensor _) (.up ℤ) p q n hpq) ≫ b) : a = b := by
    apply (cancel_epi (e F K n).inv).1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    apply (cancel_epi (φ (F.X p) (K.X q)).hom).1
    simp only [← Category.assoc]
    rw [← he F K p q n hpq]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h p q hpq
  have hd (F K : CochainComplex (SheafOfModules.{u₁} O) ℤ) (n m : ℤ) :
      (e F K n).hom ≫ (mapBifunctor ((S).obj F) ((S).obj K) (curriedTensor _)).d n m =
      ((S).obj (mapBifunctor F K (curriedTensor _))).d n m ≫ (e F K m).hom := by
    exact stalk_tensor_degree_differential X x φ hφ e he F K n m
  let E (F K : CochainComplex (SheafOfModules.{u₁} O) ℤ) :=
    HomologicalComplex.Hom.isoOfComponents (e F K) (fun n m _ ↦ hd F K n m)
  refine ⟨E, ?_⟩
  intro F K F' K' f g
  apply HomologicalComplex.Hom.ext
  funext n
  change T.map ((HomologicalComplex.mapBifunctorMap f g (curriedTensor _) (.up ℤ)).f n) ≫
      (e F' K' n).hom = (e F K n).hom ≫
        (HomologicalComplex.mapBifunctorMap ((S).map f) ((S).map g)
          (curriedTensor _) (.up ℤ)).f n
  apply h_ext F K n
  intro p q hpq
  have hi := he F K p q n hpq
  have hi' := he F' K' p q n hpq
  calc
    _ = T.map ((f.f p ⊗ₘ g.f q) ≫ HomologicalComplex.ιMapBifunctor F' K'
        (curriedTensor _) (.up ℤ) p q n hpq) ≫ (e F' K' n).hom := by
      rw [← Functor.map_comp_assoc, HomologicalComplex.ι_mapBifunctorMap]
      rfl
    _ = T.map (f.f p ⊗ₘ g.f q) ≫ (φ (F'.X p) (K'.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor ((S).obj F') ((S).obj K')
          (curriedTensor _) (.up ℤ) p q n hpq := by
      rw [Functor.map_comp, Category.assoc, hi']
    _ = (φ (F.X p) (K.X q)).hom ≫ (T.map (f.f p) ⊗ₘ T.map (g.f q)) ≫
        HomologicalComplex.ιMapBifunctor ((S).obj F') ((S).obj K')
          (curriedTensor _) (.up ℤ) p q n hpq := by
      rw [← Category.assoc, hφ, Category.assoc]
    _ = _ := by
      rw [← Category.assoc _ (e F K n).hom, hi, Category.assoc,
        HomologicalComplex.ι_mapBifunctorMap]
      simp only [tensorHom_def, Category.assoc]
      rfl

end CochainComplex
