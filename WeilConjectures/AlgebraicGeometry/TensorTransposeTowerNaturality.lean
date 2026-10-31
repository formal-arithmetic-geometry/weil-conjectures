/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerTensorTransposeWords
import WeilConjectures.AlgebraicGeometry.RouteTensorProjectionFactorwiseNaturality

/-! # Naturality of the actual tower projection/counit map and its transpose

Source: latest blueprint, tower-geometric gamma proof (2), factorwise naturality.
(blueprint: lem-sp-tensor-transpose-tower-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTensorTranspose

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  {X Z Y : Scheme.{u}}
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
  (hF : ∀ M : SpTowerCalculus.C l E b q X,
    spConstructibleTorTowers l E Y (q.abelian Y)
      ((SpTowerCalculus.F l E b o q (SpTowerGamma.factorization j p)).obj M.obj))
  (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
  (adj : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ G)
  (lv : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization j p) hF G adj)
  (hU : spConstructibleTorTowers l E Y (q.abelian Y)
    (SpTowerGamma.originalUnit l E b q Y))
  (tx : SpTowerP1.TensorData l E b X) (ty : SpTowerP1.TensorData l E b Y)

variable (hQ : ∀ K : SpTowerCalculus.C l E b q Y,
    spConstructibleTorTowers l E X (q.abelian X)
      ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj
        ((SpTowerGamma.tensorSource l E b o q (j ≫ p) ((SpTowerGamma.exceptional l E b q G).obj
          ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩)).obj K)))
  (hpf : ∀ K : SpTowerCalculus.C l E b q Y,
    IsIso (SpTowerShriek.projection l E b o (SpTowerGamma.factorization j p)
      ((SpTowerGamma.exceptional l E b q G).obj ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩)
        ((SpTowerGamma.realization l E b q Y).obj K)))

-- The existing hypotheses are retained for compatibility with all callers.
set_option linter.unusedSectionVars false in
/-- Naturality of the specified inverse-projection/counit map and its actual
adjunction transpose, before evaluating any tower.
Source: latest blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gamma.proof.md, paragraph (2), factorwise naturality.
(blueprint: lem-sp-tensor-transpose-tower-naturality).

Proof:
1. The proper projection is the adjoint transpose of tensorPullback followed by
counit tensor identity. Naturality of the tensor comparison and the counit,
followed by homEquiv_naturality_left and homEquiv_naturality_right, proves its
naturality in both inputs. The open projection inverse is fixed by openTensor_mate;
the same calculation with the open unit proves its naturality. Compose these
squares with the natural pullback-composition isomorphism. Thus, for the fixed
coefficient omega and an input map v, the compactification projection satisfies
PF_K followed by F(1 tensor pull(v)) = (1 tensor v) followed by PF_L.
2. Multiply this equation by the assumed inverses on both sides. Move v across
both tensor symmetries using braiding naturality. Tensor bifunctoriality moves v
past identity tensor the fixed counit, and the scalar right-unitor is natural.
The result is the asserted naturality equation for projectionCounit.
3. Lift the tensor source along inverse realization, using the supplied membership
proofs. In the original full subcategory its arrow is homMk of inverse.map of the
tensor-source map. Naturality of supportRealization and the realization counit,
Step 2 and full faithfulness of realization show that originalComposite is natural
for these arrows. Apply homEquiv_naturality_left_square to this square for the
actual compact-support adjunction. Map the resulting equation by realization and
precompose with its inverse counit. Naturality of this inverse counit gives the
asserted tensorMate equation. All maps are actual tower maps; derived evaluation
is never used to detect equality. Zero objects and zero input maps cause no change
in these equations, and no orientation or smoothness hypothesis is required.
-/
theorem tensor_transpose_tower_naturality :
    (∀ (K L : SpTowerCalculus.C l E b q Y) (v : K ⟶ L),
      (SpTowerShriek.F l E b o (SpTowerGamma.factorization j p)).map ((SpTowerGamma.tensorSource l
        E b o q (j ≫ p) ((SpTowerGamma.exceptional l E b q G).obj ⟨SpTowerGamma.originalUnit l E b q
        Y, hU⟩)).map v) ≫
          SpTowerGamma.projectionCounit l E b o q (SpTowerGamma.factorization j p) tx ty hF G adj hU
            L (hpf L) =
        SpTowerGamma.projectionCounit l E b o q (SpTowerGamma.factorization j p) tx ty hF G adj hU K
          (hpf K) ≫
          (SpTowerGamma.realization l E b q Y).map v) ∧
    (∀ (K L : SpTowerCalculus.C l E b q Y) (v : K ⟶ L),
      (SpTowerGamma.tensorSource l E b o q (j ≫ p) ((SpTowerGamma.exceptional l E b q G).obj
        ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩)).map v ≫
          SpTowerGamma.tensorMate l E b o q (SpTowerGamma.factorization j p) tx ty hF G adj hU L (hQ
            L) (hpf L) =
        SpTowerGamma.tensorMate l E b o q (SpTowerGamma.factorization j p) tx ty hF G adj hU K (hQ
          K) (hpf K) ≫
          (SpTowerGamma.exceptional l E b q G).map v) := by
  classical
  let inst := (b.calculus X).closed.monoidal
  let inst := (b.calculus Y).closed.monoidal
  let inst := tx.symmetry l E
  let inst := ty.symmetry l E
  let c := SpTowerGamma.factorization j p
  let F := SpTowerShriek.F l E b o c
  let P := SpTowerShriek.pull l E b (o.geometry (j ≫ p))
  let r := SpTowerGamma.realization l E b q Y
  let W := (SpTowerGamma.exceptional l E b q G).obj
    ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩
  let T := SpTowerGamma.tensorSource l E b o q (j ≫ p) W
  let a := SpTowerGamma.projectionCounit l E b o q c tx ty hF G adj hU
  have ha : ∀ (K L : SpTowerCalculus.C l E b q Y) (v : K ⟶ L),
      F.map (T.map v) ≫ a L (hpf L) = a K (hpf K) ≫ r.map v := by
    intro K L v
    let inst := hpf K
    let inst := hpf L
    have hp := SpTowerShriek.projection_factorwise_naturality l E b o c
      (𝟙 W) (r.map v)
    change (F.map (𝟙 W) ⊗ₘ r.map v) ≫
        SpTowerShriek.projection l E b o c W (r.obj L) =
      SpTowerShriek.projection l E b o c W (r.obj K) ≫
        F.map (𝟙 W ⊗ₘ P.map (r.map v)) at hp
    rw [F.map_id W] at hp
    have hi : F.map (𝟙 W ⊗ₘ P.map (r.map v)) ≫
        inv (SpTowerShriek.projection l E b o c W (r.obj L)) =
        inv (SpTowerShriek.projection l E b o c W (r.obj K)) ≫
          (𝟙 (F.obj W) ⊗ₘ r.map v) := by
      rw [IsIso.comp_inv_eq, Category.assoc, eq_comm, IsIso.inv_comp_eq]
      exact hp
    have hx := BraidedCategory.braiding_naturality (P.map (r.map v)) (𝟙 W)
    have hy := BraidedCategory.braiding_naturality (𝟙 (F.obj W)) (r.map v)
    have hu : (r.map v ⊗ₘ 𝟙 (SpTowerGamma.unit l E Y)) ≫
          (ty.rightUnit l E (r.obj L)).hom =
        (ty.rightUnit l E (r.obj K)).hom ≫ r.map v := by
      dsimp only [SpTowerP1.TensorData.rightUnit, Iso.trans_hom, Functor.mapIso_hom,
        Iso.prod_hom, Iso.refl_hom, Iso.symm_hom]
      simp only [Category.assoc]
      change (r.map v ⊗ₘ 𝟙 _) ≫ (𝟙 _ ⊗ₘ ty.unitIso.inv) ≫
          (ρ_ (r.obj L)).hom =
        (𝟙 _ ⊗ₘ ty.unitIso.inv) ≫
          (ρ_ (r.obj K)).hom ≫ r.map v
      rw [← MonoidalCategory.rightUnitor_naturality]
      simp only [← MonoidalCategory.tensorHom_id, ← Category.assoc,
        MonoidalCategory.tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id]
    let eps := SpTowerGamma.counit l E b o q c hF G adj
      ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩ ≫
      (SpTowerCalculus.realization l E b Y (q.abelian Y)).counitIso.hom.app
        (SpTowerGamma.unit l E Y)
    have he : (r.map v ⊗ₘ 𝟙 (F.obj W)) ≫ (𝟙 _ ⊗ₘ eps) =
        (𝟙 _ ⊗ₘ eps) ≫ (r.map v ⊗ₘ 𝟙 _) := by
      simp only [MonoidalCategory.tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id]
    dsimp only [a, SpTowerGamma.projectionCounit]
    simp only [Category.assoc]
    change F.map (P.map (r.map v) ⊗ₘ 𝟙 W) ≫
        F.map (β_ (P.obj (r.obj L)) W).hom ≫
        inv (SpTowerShriek.projection l E b o c W (r.obj L)) ≫
        (β_ (F.obj W) (r.obj L)).hom ≫
        (𝟙 (r.obj L) ⊗ₘ eps) ≫ (ty.rightUnit l E (r.obj L)).hom =
      F.map (β_ (P.obj (r.obj K)) W).hom ≫
        inv (SpTowerShriek.projection l E b o c W (r.obj K)) ≫
        (β_ (F.obj W) (r.obj K)).hom ≫
        (𝟙 (r.obj K) ⊗ₘ eps) ≫ (ty.rightUnit l E (r.obj K)).hom ≫ r.map v
    rw [← F.map_comp_assoc, hx, F.map_comp, Category.assoc,
      reassoc_of% hi, reassoc_of% hy, reassoc_of% he, hu]
  refine ⟨ha, ?_⟩
  intro K L v
  let eX := SpTowerCalculus.realization l E b X (q.abelian X)
  let eY := SpTowerCalculus.realization l E b Y (q.abelian Y)
  let s := SpCoordinateAdjunction.supportRealization l E b o q c
  let H := SpTowerGluing.support l E b o q c hF
  let Q (N : SpTowerCalculus.C l E b q Y) :=
    originalSource l E b o q j p G hU N (hQ N)
  let u : Q K ⟶ Q L := ObjectProperty.homMk (eX.inverse.map (T.map v))
  let A (N : SpTowerCalculus.C l E b q Y) :=
    originalComposite l E b o q j p hF G adj hU tx ty N (hQ N) (hpf N)
  have hA : H.map u ≫ A L = A K ≫ v := by
    apply ObjectProperty.hom_ext
    apply eY.functor.map_injective
    change eY.functor.map ((SpTowerCalculus.F l E b o q c).map u.hom ≫
        (A L).hom) = eY.functor.map ((A K).hom ≫ v.hom)
    simp only [Functor.map_comp]
    dsimp only [A, originalComposite, ObjectProperty.homMk_hom]
    rw [Functor.map_preimage, Functor.map_preimage]
    change eY.functor.map ((SpTowerCalculus.F l E b o q c).map u.hom) ≫
        s.hom.app (Q L).obj ≫ F.map (eX.counitIso.hom.app (T.obj L)) ≫ a L (hpf L) =
      (s.hom.app (Q K).obj ≫ F.map (eX.counitIso.hom.app (T.obj K)) ≫
        a K (hpf K)) ≫ r.map v
    have hs := s.hom.naturality u.hom
    change eY.functor.map ((SpTowerCalculus.F l E b o q c).map u.hom) ≫
        s.hom.app (Q L).obj =
      s.hom.app (Q K).obj ≫ F.map (eX.functor.map u.hom) at hs
    erw [reassoc_of% hs, ← F.map_comp_assoc]
    have hd := eX.counitIso.hom.naturality (T.map v)
    change eX.functor.map u.hom ≫ eX.counitIso.hom.app (T.obj L) =
      eX.counitIso.hom.app (T.obj K) ≫ T.map v at hd
    erw [hd, F.map_comp]
    simpa only [Category.assoc] using
      congrArg (fun z ↦ s.hom.app (Q K).obj ≫
        F.map (eX.counitIso.hom.app (T.obj K)) ≫ z) (ha K L v)
  have hm := adj.homEquiv_naturality_left_square u (A L) (A K) v hA
  have hm' := congrArg (fun f ↦ eX.functor.map f.hom) hm
  change eX.functor.map (u.hom ≫ ((adj.homEquiv (Q L) L) (A L)).hom) =
    eX.functor.map (((adj.homEquiv (Q K) K) (A K)).hom ≫ (G.map v).hom) at hm'
  simp only [Functor.map_comp] at hm'
  change T.map v ≫ eX.counitIso.inv.app (T.obj L) ≫
      eX.functor.map (((adj.homEquiv (Q L) L) (A L)).hom) =
    (eX.counitIso.inv.app (T.obj K) ≫
      eX.functor.map (((adj.homEquiv (Q K) K) (A K)).hom)) ≫
        eX.functor.map (G.map v).hom
  have hd := eX.counitIso.inv.naturality (T.map v)
  dsimp only [Functor.comp_map, Functor.id_map] at hd
  erw [reassoc_of% hd, hm']
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.ProEtale.SpTensorTranspose

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
