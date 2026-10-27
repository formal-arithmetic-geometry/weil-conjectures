/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.Paper.FinitePullbackTensorConstruction

/-! # Associativity on flat K-flat pullback tensor representatives

Source: Stacks Project, Tags 07A4, 06YS and 03EL.
(blueprint: lem-pur-finite-pullback-tensor-associativity-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] Scheme.residueField finiteIntrinsicClosed
  finiteIntrinsicTensorModels finitePullbackTensorConstruction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Associativity for the canonical comparison on localized flat K-flat triples.
Source: Stacks 07A4, lemma-pullback-tensor-product, its total-tensor construction;
06YS and 07A2 for the flat K-flat total-tensor representatives.
(blueprint: lem-pur-finite-pullback-tensor-associativity-representatives).
Proof: total tensors of flat K-flat complexes are again flat K-flat. Apply the
representative normalization square to (A,B), (B,C) and their total tensors.
On each tridegree summand, ordinary pullback tensor comparison sends the
pullback of (x tensor y) tensor z to f*x tensor (f*y tensor f*z) along both
routes. The ordinary associator only changes parentheses, so this equality
has no extra Koszul sign. It respects the signed total differential.
Tensor generators, sheafification and the total coproduct injections determine
the chain maps. Apply the derived quotient to their equality and insert the
specified finite tensor-model comparisons and unit-normalized realization.
The representative associators and the natural comparison isomorphisms cancel
the intermediate conjugations, giving precisely the displayed equation.
This calculation only treats the displayed flat K-flat triples. -/
theorem finitePullbackTensor_associativity_representatives {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (A B C : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (hA : proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n) A)
    (hB : proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n) B)
    (hC : proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n) C) :
    let M := DerivedCategory.Q.obj A
    let N := DerivedCategory.Q.obj B
    let P := DerivedCategory.Q.obj C
    (finiteDerivedPullback l E n f).map
      ((finiteIntrinsicClosed l E Y n).monoidal.associator M N P).hom ≫
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY) M
        ((finiteIntrinsicDerivedTensor l E Y n).obj (N,P))).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (𝟙 _) ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY) N P).hom) =
    ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY)
      ((finiteIntrinsicDerivedTensor l E Y n).obj (M,N)) P).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY) M N).hom (𝟙 _)) ≫
      ((finiteIntrinsicClosed l E X n).monoidal.associator
        ((finiteDerivedPullback l E n f).obj M)
        ((finiteDerivedPullback l E n f).obj N)
        ((finiteDerivedPullback l E n f).obj P)).hom := by
  sorry

end WeilConjectures
