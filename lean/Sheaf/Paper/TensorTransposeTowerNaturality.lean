/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.TowerTensorTransposeWords

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
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures

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
          (SpTowerGamma.exceptional l E b q G).map v) := by sorry

end AlgebraicGeometry.ProEtale.SpTensorTranspose

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
