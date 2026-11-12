/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MixedGlobalHomAdjunctionIso
import WeilConjectures.AlgebraicGeometry.MixedTensorPairingBaseChange
import all WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso

/-! # Internal Hom exchange with the canonical base-change mate
Source: Stacks Project, duality.tex, Tag 0AA8, lemma-more-base-change,
final comparison diagrams; cohomology.tex, Tag 08I3.
(blueprint: lem-sc-mixed-internal-hom-base-change-exchange).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

private theorem tensorPairing_naturality {S T : Scheme.{u}} (h : T ⟶ S)
    {A A' B B' : schemeDerivedCategory T} (a : A ⟶ A') (b : B ⟶ B') :
    ((schemeDerivedDirectImage h).map a ⊗ₘ (schemeDerivedDirectImage h).map b) ≫
      mixedDirectImageTensorPairing h A' B' =
    mixedDirectImageTensorPairing h A B ≫
      (schemeDerivedDirectImage h).map (a ⊗ₘ b) := by
  let adj := schemeHomPullbackAdjunction h
  let τ := mixedHomTensorPullbackIso h
  dsimp only [mixedDirectImageTensorPairing]
  erw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  congr 1
  have ht := τ.hom.naturality
    (X := ((schemeDerivedDirectImage h).obj A, (schemeDerivedDirectImage h).obj B))
    (Y := ((schemeDerivedDirectImage h).obj A', (schemeDerivedDirectImage h).obj B'))
    ((schemeDerivedDirectImage h).map a, (schemeDerivedDirectImage h).map b)
  dsimp only [Functor.comp_map, Functor.prod_map, tensor] at ht
  erw [← Category.assoc, ht, Category.assoc,
    tensorHom_comp_tensorHom]
  erw [Category.assoc, tensorHom_comp_tensorHom]
  erw [adj.counit.naturality a, adj.counit.naturality b]
  rfl

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem map_pair_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B C' : C} (a : A ⟶ B) (b : B ⟶ C') :
    F.map a ≫ F.map b = F.map (a ≫ b) := (F.map_comp a b).symm

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem tensor_evaluation_interchange
    {D : Type*} [Category D] [MonoidalCategory D] {W A B C V Q : D}
    (k : W ⟶ A ⊗ B) (a : A ⟶ C) (b : B ⟶ V) (v : C ⊗ V ⟶ Q) :
    k ≫ (𝟙 A ⊗ₘ b) ≫ (a ⊗ₘ 𝟙 V) ≫ v = (k ≫ (a ⊗ₘ b)) ≫ v := by
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    Category.comp_id]

set_option maxHeartbeats 800000 in
set_option profiler true in
-- Evaluation crosses the two definitionally equal presentations of scheme module sheaves.
private theorem directImage_evaluation {S T : Scheme.{u}} (h : T ⟶ S)
    (P Q : schemeDerivedCategory T) :
    schemeDerivedTensorHomEquiv S _ _ _
      ((mixedHomDirectImageComparison h).app (op P, Q)) =
    mixedDirectImageTensorPairing h
      ((derivedInternalHom (Opens.grothendieckTopology T) T.sheaf).obj (op P, Q)) P ≫
      (schemeDerivedDirectImage h).map
        (schemeDerivedTensorHomEquiv T _ P Q (𝟙 _)) := by
  let H : (schemeDerivedCategory T)ᵒᵖ × schemeDerivedCategory T ⥤
      schemeDerivedCategory T := derivedInternalHom (Opens.grothendieckTopology T) T.sheaf
  let adj := schemeHomPullbackAdjunction h
  let E : schemeDerivedCategory T := H.obj (op P, Q)
  have hc := (Classical.choose_spec (exists_schemeHomDirectImageComparison h))
    P Q ((schemeDerivedDirectImage h).obj E) (𝟙 _)
  simp only [Category.id_comp] at hc
  dsimp only [mixedHomDirectImageComparison]
  erw [hc]
  have he := schemeHomTensorHom_naturality T
    E ((derivedPullback h).obj
    ((schemeDerivedDirectImage h).obj E)) P P Q Q (adj.counit.app E)
    (𝟙 P) (𝟙 Q) (𝟙 E)
  have hid : H.map ((𝟙 P).op, 𝟙 Q) = 𝟙 (H.obj (op P, Q)) := H.map_id (op P, Q)
  erw [hid] at he
  erw [Category.comp_id, Category.comp_id] at he
  have hi : (adj.homEquiv _ E).symm (𝟙 _) = adj.counit.app E := by
    erw [Adjunction.homEquiv_counit]
    simp
  erw [Category.comp_id] at he
  erw [hi, he]
  dsimp only [mixedDirectImageTensorPairing]
  erw [← adj.homEquiv_naturality_right]
  congr 1
  exact tensor_evaluation_interchange
    ((mixedHomTensorPullbackIso h).hom.app
      ((schemeDerivedDirectImage h).obj E, (schemeDerivedDirectImage h).obj P))
    (adj.counit.app E) (adj.counit.app P)
    (schemeDerivedTensorHomEquiv T E P Q (𝟙 E))

private theorem evaluation_formula (S : Scheme.{u})
    (A P Q : schemeDerivedCategory S)
    (z : A ⟶ (derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q)) :
    schemeDerivedTensorHomEquiv S A P Q z =
      (z ⊗ₘ 𝟙 P) ≫ schemeDerivedTensorHomEquiv S _ P Q (𝟙 _) := by
  have hn := schemeHomTensorHom_naturality S
    _ A P P Q Q z (𝟙 P) (𝟙 Q) (𝟙 _)
  have hid : (derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).map
      (X := (op P, Q)) (Y := (op P, Q)) ((𝟙 P).op, 𝟙 Q) = 𝟙 _ :=
    (derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).map_id (op P, Q)
  erw [hid] at hn
  simpa only [Category.comp_id] using hn

set_option maxHeartbeats 1200000 in
set_option profiler true in
-- Tensor-Hom naturality crosses scheme and ringed-space presentations.
/-- The exchange identity before applying global sections.
Here `p` is the pullback of evaluation transposed by the fixed tensor-Hom bijection.
Source: Stacks Project, duality.tex, Tag 0AA8, lemma-more-base-change,
final comparison diagrams; cohomology.tex, Tag 08I3.
(blueprint: lem-sc-mixed-internal-hom-base-change-exchange).

Proof: transpose both sides by the tensor-Hom bijection on Y'. Naturality in the
first Hom input replaces precomposition by beta_M with tensoring by beta_M;
naturality in the second input replaces postcomposition by beta_N with beta_N.
Use the evaluation-mate equation for the direct-image comparisons, and the
construction of p as pulled-back evaluation. Transpose beta under the f'
adjunction: it is the pullback-composition comparison followed by the pullback
of the f counit. Naturality of that counit and the f' triangle identity cancel
the unit-counit pairs. The remaining tensor comparisons agree: on K-flat
representatives both are the ordinary tensor-pullback comparison along the
commutative square, and uniqueness of the left-derived comparison extends
this equality to all objects. Thus both transposed composites agree, and
injectivity of the tensor-Hom bijection gives the equation. -/
theorem mixedInternalHom_baseChange_exchange
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (M N : schemeDerivedCategory X) :
  let p := fun {S T : Scheme.{u}} (h : T ⟶ S) (P Q : schemeDerivedCategory S) ↦
    ((schemeDerivedTensorHomEquiv T)
      ((derivedPullback h).obj
        ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q)))
      ((derivedPullback h).obj P) ((derivedPullback h).obj Q)).symm
        ((mixedHomTensorPullbackIso h).inv.app
          ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q), P) ≫
          (derivedPullback h).map
            ((schemeDerivedTensorHomEquiv S)
              ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q))
              P Q (𝟙 _)))
  let H := fun Z : Scheme.{u} ↦ derivedInternalHom (Opens.grothendieckTopology Z) Z.sheaf
  let c := fun {S T : Scheme.{u}} (h : T ⟶ S) ↦
    mixedHomDirectImageComparison h
  schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition ((H X).obj (op M, N)) ≫
    (schemeDerivedDirectImage (pullback.snd f g)).map (p (pullback.fst f g) M N) ≫
    (c (pullback.snd f g)).app
      (op ((derivedPullback (pullback.fst f g)).obj M),
        (derivedPullback (pullback.fst f g)).obj N) ≫
    (H Y').map
      (X := (op ((schemeDerivedDirectImage (pullback.snd f g)).obj
        ((derivedPullback (pullback.fst f g)).obj M)),
        (schemeDerivedDirectImage (pullback.snd f g)).obj
          ((derivedPullback (pullback.fst f g)).obj N)))
      (Y := (op ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj M)),
        (schemeDerivedDirectImage (pullback.snd f g)).obj
          ((derivedPullback (pullback.fst f g)).obj N)))
      ((schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition M).op, 𝟙 _) =
    (derivedPullback g).map ((c f).app (op M, N)) ≫
      p g ((schemeDerivedDirectImage f).obj M) ((schemeDerivedDirectImage f).obj N) ≫
      (H Y').map
        ((𝟙 _).op, schemeDerivedBaseChangeMap f (pullback.snd f g) g
          (pullback.fst f g) pullback.condition N) := by
  let p := fun {S T : Scheme.{u}} (h : T ⟶ S) (P Q : schemeDerivedCategory S) ↦
    ((schemeDerivedTensorHomEquiv T)
      ((derivedPullback h).obj
        ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q)))
      ((derivedPullback h).obj P) ((derivedPullback h).obj Q)).symm
        ((mixedHomTensorPullbackIso h).inv.app
          ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q), P) ≫
          (derivedPullback h).map
            ((schemeDerivedTensorHomEquiv S)
              ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q))
              P Q (𝟙 _)))
  let H (Z : Scheme.{u}) : (schemeDerivedCategory Z)ᵒᵖ × schemeDerivedCategory Z ⥤
      schemeDerivedCategory Z := derivedInternalHom (Opens.grothendieckTopology Z) Z.sheaf
  let c := fun {S T : Scheme.{u}} (h : T ⟶ S) ↦
    mixedHomDirectImageComparison h
  let R := schemeDerivedDirectImage f
  let R' := schemeDerivedDirectImage (pullback.snd f g)
  let L := derivedPullback g
  let L' := derivedPullback (pullback.fst f g)
  let E : schemeDerivedCategory X := (H X).obj (op M, N)
  let E' : schemeDerivedCategory (pullback f g) := (H (pullback f g)).obj (op (L'.obj M), L'.obj N)
  let β := fun Z ↦ schemeDerivedBaseChangeMap f (pullback.snd f g) g
    (pullback.fst f g) pullback.condition Z
  let a : L'.obj E ⟶ E' := p (pullback.fst f g) M N
  let b : L.obj ((H Y).obj (op (R.obj M), R.obj N)) ⟶
      (H Y').obj (op (L.obj (R.obj M)), L.obj (R.obj N)) := p g (R.obj M) (R.obj N)
  let z : L.obj (R.obj E) ⟶ (H Y').obj
      (op (R'.obj (L'.obj M)), R'.obj (L'.obj N)) :=
    β E ≫ R'.map a ≫ (c (pullback.snd f g)).app (op (L'.obj M), L'.obj N)
  let t : R.obj E ⟶ (H Y).obj (op (R.obj M), R.obj N) := (c f).app (op M, N)
  suffices hex : z ≫ (H Y').map (X := (op (R'.obj (L'.obj M)), R'.obj (L'.obj N)))
      (Y := (op (L.obj (R.obj M)), R'.obj (L'.obj N))) ((β M).op, 𝟙 _) =
    L.map t ≫ b ≫ (H Y').map ((𝟙 _).op, β N) by
      simpa only [z, t, a, b, R, R', L, L', E, β, Category.assoc] using hex
  apply (schemeDerivedTensorHomEquiv Y' _ _ _).injective
  have hl := schemeHomTensorHom_naturality Y'
    (R'.obj E') (L.obj (R.obj E)) (R'.obj (L'.obj M)) (L.obj (R.obj M))
    (R'.obj (L'.obj N)) (R'.obj (L'.obj N)) (β E ≫ R'.map a) (β M) (𝟙 _)
    ((c (pullback.snd f g)).app (op (L'.obj M), L'.obj N))
  simp only [Category.comp_id] at hl
  have hr := schemeHomTensorHom_naturality Y'
    _ _ _ _ _ _ (L.map t) (𝟙 _) (β N) b
  have hc' := directImage_evaluation (pullback.snd f g) (L'.obj M) (L'.obj N)
  have hc := directImage_evaluation f M N
  simp only [z, Category.assoc] at hl ⊢
  erw [hl, hr, hc']
  have hp' := evaluation_formula (pullback f g) _ _ _ a
  have hpt := evaluation_formula Y _ _ _ t
  have ha : schemeDerivedTensorHomEquiv (pullback f g) _ _ _ a =
      (mixedHomTensorPullbackIso (pullback.fst f g)).inv.app (E, M) ≫
        L'.map (schemeDerivedTensorHomEquiv X E M N (𝟙 E)) := by
    exact (schemeDerivedTensorHomEquiv (pullback f g) _ _ _).apply_symm_apply _
  have hb : schemeDerivedTensorHomEquiv Y' _ _ _ b =
      (mixedHomTensorPullbackIso g).inv.app
        ((H Y).obj (op (R.obj M), R.obj N), R.obj M) ≫
        L.map (schemeDerivedTensorHomEquiv Y _ _ _ (𝟙 _)) := by
    exact (schemeDerivedTensorHomEquiv Y' _ _ _).apply_symm_apply _
  erw [hb]
  have hq := tensorPairing_naturality (pullback.snd f g) a (𝟙 (L'.obj M))
  have ht := (mixedHomTensorPullbackIso g).inv.naturality
    (X := (R.obj E, R.obj M))
    (Y := ((H Y).obj (op (R.obj M), R.obj N), R.obj M)) (t, 𝟙 _)
  dsimp only [Functor.comp_map, Functor.prod_map, tensor] at ht
  erw [CategoryTheory.Functor.map_id] at hq ht
  have hsplit : ((β E ≫ R'.map a) ⊗ₘ β M) =
      (β E ⊗ₘ β M) ≫ (R'.map a ⊗ₘ 𝟙 _) := by
    erw [tensorHom_comp_tensorHom, Category.comp_id]
  erw [hsplit]
  simp only [Category.assoc]
  erw [reassoc_of% hq, ← R'.map_comp, ← hp', ha]
  erw [reassoc_of% ht]
  have hm := map_pair_comp L (t ⊗ₘ 𝟙 (R.obj M))
    (schemeDerivedTensorHomEquiv Y ((H Y).obj (op (R.obj M), R.obj N))
      (R.obj M) (R.obj N) (𝟙 _))
  have hm' := congrArg (fun k ↦
    (mixedHomTensorPullbackIso g).inv.app (R.obj E, R.obj M) ≫ k ≫ β N) hm
  have heval : (t ⊗ₘ 𝟙 (R.obj M)) ≫
      schemeDerivedTensorHomEquiv Y ((H Y).obj (op (R.obj M), R.obj N))
        (R.obj M) (R.obj N) (𝟙 _) =
      mixedDirectImageTensorPairing f E M ≫
        R.map (schemeDerivedTensorHomEquiv X E M N (𝟙 E)) := hpt.symm.trans hc
  have hm'' := congrArg (fun k ↦
    (mixedHomTensorPullbackIso g).inv.app (R.obj E, R.obj M) ≫ L.map k ≫ β N) heval
  have hright := Eq.trans hm' hm''
  simp only [Category.assoc] at hright
  apply Eq.trans _ hright.symm
  exact mixedTensorPairing_baseChange f g E M N
    (schemeDerivedTensorHomEquiv X E M N (𝟙 E))

end AlgebraicGeometry
