/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FieldCoefficientTensorHypotheses

/-! # Tensor product of strict Weil complexes

Source: literature/blueprint/latest/blueprint/sec-purity-real-sheaves/sk-r-real-linear/
lem-wf-tensor-weil.md, order 3982, and its companion proof, steps 1–6
(blueprint: lem-wf-tensor-weil).

The strict-pair category is the landed category over the geometric fibre and the
specified geometric Frobenius. Exactness is asserted on the underlying derived category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures

private def tensorStrictPairs
    {C : Type*} [Category C] (P : C ⥤ C) (T : C × C ⥤ C)
    (δ : ∀ K L, P.obj (T.obj (K, L)) ≅ T.obj (P.obj K, P.obj L))
    (hδ : ∀ {K L K' L'} (f : K ⟶ K') (g : L ⟶ L'),
      P.map (T.map (Prod.mkHom f g)) ≫ (δ K' L').hom =
        (δ K L).hom ≫ T.map (Prod.mkHom (P.map f) (P.map g)))
    (Q : ObjectProperty C)
    (hQ : ∀ K L, Q K → Q L → Q (T.obj (K, L))) :
    ObjectProperty.FullSubcategory (fun K : Endofunctor.IsoAlgebra P ↦ Q K.carrier) ×
      ObjectProperty.FullSubcategory (fun K : Endofunctor.IsoAlgebra P ↦ Q K.carrier) ⥤
        ObjectProperty.FullSubcategory (fun K : Endofunctor.IsoAlgebra P ↦ Q K.carrier) where
  obj KL := ⟨Endofunctor.IsoAlgebra.mk (T.obj (KL.1.obj.carrier, KL.2.obj.carrier))
    (δ KL.1.obj.carrier KL.2.obj.carrier ≪≫
      T.mapIso (Iso.prod KL.1.obj.str KL.2.obj.str)),
    hQ _ _ KL.1.property KL.2.property⟩
  map {KL MN} fg := ObjectProperty.homMk (ObjectProperty.homMk
    { f := T.map (Prod.mkHom fg.1.hom.hom.f fg.2.hom.hom.f)
      h := by
        change P.map (T.map (Prod.mkHom fg.1.hom.hom.f fg.2.hom.hom.f)) ≫
            ((δ MN.1.obj.carrier MN.2.obj.carrier).hom ≫
              T.map (Prod.mkHom MN.1.obj.str.hom MN.2.obj.str.hom)) =
          ((δ KL.1.obj.carrier KL.2.obj.carrier).hom ≫
              T.map (Prod.mkHom KL.1.obj.str.hom KL.2.obj.str.hom)) ≫
            T.map (Prod.mkHom fg.1.hom.hom.f fg.2.hom.hom.f)
        rw [← Category.assoc, hδ, Category.assoc, ← T.map_comp,
          Category.assoc, ← T.map_comp]
        congr 2
        exact Prod.ext fg.1.hom.hom.h fg.2.hom.hom.h })
  map_id KL := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Endofunctor.Algebra.ext
    exact T.map_id _
  map_comp fg gh := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Endofunctor.Algebra.ext
    exact T.map_comp (Prod.mkHom fg.1.hom.hom.f fg.2.hom.hom.f)
      (Prod.mkHom gh.1.hom.hom.f gh.2.hom.hom.f)

/-- The tensor bifunctor on strict bounded constructible Weil complexes, with its
specified underlying objects, arrows and Frobenius, and exactness in each variable: for every
`K ∈ D^b_c(X, Λ)`, tensoring with `K` on either side is a triangulated functor of the
ambient derived category (so it restricts to `D^b_c(X, Λ)` by the tensor closure).
Source: latest blueprint, sec-purity-real-sheaves/sk-r-real-linear/lem-wf-tensor-weil.md,
order 3982, displayed tensor formula and final sentence (blueprint: lem-wf-tensor-weil). -/
structure WfTensorWeilData
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (c : WeilCoefficient ell) where
  tensor : strictWeilComplexCategory D ell hell X₀ c ×
    strictWeilComplexCategory D ell hell X₀ c ⥤ strictWeilComplexCategory D ell hell X₀ c
  carrier : ∀ K L : strictWeilComplexCategory D ell hell X₀ c,
    (tensor.obj (K, L)).obj.carrier =
      (wfCondensedTensor (WeilCoefficient.ab c) (D.geometricFiber X₀).left).obj
        (K.obj.carrier, L.obj.carrier)
  frobenius : ∀ K L : strictWeilComplexCategory D ell hell X₀ c,
    HEq (tensor.obj (K, L)).obj.str
      (wfCondensedGeometricTensorFrobenius (WeilCoefficient.ab c) D X₀ K.obj L.obj)
  map : ∀ (K K' L L' : strictWeilComplexCategory D ell hell X₀ c)
      (f : K ⟶ K') (g : L ⟶ L'),
    HEq (tensor.map (Prod.mkHom f g)).hom.hom.f
      ((wfCondensedTensor (WeilCoefficient.ab c) (D.geometricFiber X₀).left).map
        (Prod.mkHom f.hom.hom.f g.hom.hom.f))
  exact_left : ∀ K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (D.geometricFiber X₀).left) Ab.{u + 1})
        (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber X₀).left)),
    boundedConstructible (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber X₀).left)
      K →
    ∃ s : ((CondensedRing.derivedTensor (WeilCoefficient.ab c)
      (D.geometricFiber X₀).left).obj K).CommShift ℤ,
      (fun [_sInst : ((CondensedRing.derivedTensor (WeilCoefficient.ab c)
        (D.geometricFiber X₀).left).obj K).CommShift ℤ] ↦
          ((CondensedRing.derivedTensor (WeilCoefficient.ab c)
            (D.geometricFiber X₀).left).obj K).IsTriangulated) (_sInst := s)
  exact_right : ∀ L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (D.geometricFiber X₀).left) Ab.{u + 1})
        (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber X₀).left)),
    boundedConstructible (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber X₀).left)
      L →
    ∃ s : ((CondensedRing.derivedTensor (WeilCoefficient.ab c)
      (D.geometricFiber X₀).left).flip.obj L).CommShift ℤ,
      (fun [_sInst : ((CondensedRing.derivedTensor (WeilCoefficient.ab c)
        (D.geometricFiber X₀).left).flip.obj L).CommShift ℤ] ↦
          ((CondensedRing.derivedTensor (WeilCoefficient.ab c)
            (D.geometricFiber X₀).left).flip.obj L).IsTriangulated) (_sInst := s)

/-- The specified derived tensor defines a bifunctor on strict Weil complexes over
`E̲` or `ℚ̲̄_ℓ`, lying over the exact derived tensor on bounded constructible complexes.
Source: latest blueprint, part-weights-riemann-hypothesis/sec-weights-deligne-theorem/
sec-wdef-weights/sk-r-real-linear/lem-wf-tensor-weil.md,
order 3982, entire statement, and companion proof (blueprint: lem-wf-tensor-weil).

Proof (the node's six steps):
1. Work with the recorded condensed coefficients on `X = X₀ × k`, strict pairs for
   geometric Frobenius, and the Layer B relative derived tensor computed by K-flat models.
2. Finite type survives base change, so X is Noetherian.
3. The existing native theorem `CondensedRing.boundedConstructible_tensorObj` proves
   tensor closure on every scheme with Noetherian underlying space. Its coefficient
   hypotheses hold for both E and Qbar. It includes empty and nonseparated schemes.
4. The existing K-flat-derived shift and triangulated functor instances give exactness
   in both variables on the ambient derived category, hence the exactness fields here.
5. Compose the natural pullback/tensor isomorphism with the tensor of the two supplied
   Weil isomorphisms. Its inverse is the tensor of their inverses followed by the inverse
   comparison. This is exactly `wfCondensedGeometricTensorFrobenius`, with no cocycle datum.
6. Naturality of the comparison and the two intertwining equations show that T(f,g)
   intertwines these structures. Identity and composition are inherited from T, since
   equality of strict-pair arrows is equality of their underlying arrows. Thus objects,
   Frobenius and maps have precisely the specified formulas. -/
theorem wf_tensor_weil_strict
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (c : WeilCoefficient ell) :
    Nonempty (WfTensorWeilData D ell hell X₀ c) := by
  let X := D.geometricFiber X₀
  have : LocallyOfFiniteType X.hom := by
    dsimp [X, FiniteFieldDatum.geometricFiber]
    infer_instance
  have : QuasiCompact X.hom := by
    dsimp [X, FiniteFieldDatum.geometricFiber]
    infer_instance
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  let Λ := WeilCoefficient.ab.{u} c
  let T := wfCondensedTensor Λ X.left
  let P := wfCondensedFrobenius Λ (D.geometricFrobenius X₀).hom
  let Q := boundedConstructible (condensedRingObj Λ X.left)
  have hQ : ∀ K L, Q K → Q L → Q (T.obj (K, L)) := by
    cases c with
    | finite E =>
      exact fun K L hK hL ↦ CondensedRing.boundedConstructible_tensorObj
        (CondensedRing.tensorHypotheses_continuousMapRingObj ell E).lisseTensorHypotheses hK hL
    | qbar =>
      exact fun K L hK hL ↦ CondensedRing.boundedConstructible_tensorObj
        (CondensedRing.tensorHypotheses_padicAlgClRingObj ell).lisseTensorHypotheses hK hL
  refine ⟨{
    tensor := tensorStrictPairs P T
      (wfCondensedTensorPullback Λ (D.geometricFrobenius X₀).hom)
      (fun f g ↦ wfCondensedTensorPullback_naturality Λ _ f g) Q hQ
    carrier := fun _ _ ↦ rfl
    frobenius := ?_
    map := fun _ _ _ _ _ _ ↦ HEq.rfl
    exact_left := ?_
    exact_right := ?_ }⟩
  · intro K L
    apply heq_of_eq
    exact Endofunctor.IsoAlgebra.mk_str _ _
  · intro K _
    refine ⟨inferInstanceAs (((MonoidalCategory.curriedTensor _).obj K).CommShift ℤ), ?_⟩
    exact inferInstanceAs (((MonoidalCategory.curriedTensor _).obj K).IsTriangulated)
  · intro L _
    refine ⟨inferInstanceAs (((MonoidalCategory.curriedTensor _).flip.obj L).CommShift ℤ), ?_⟩
    exact inferInstanceAs (((MonoidalCategory.curriedTensor _).flip.obj L).IsTriangulated)

end WeilConjectures
