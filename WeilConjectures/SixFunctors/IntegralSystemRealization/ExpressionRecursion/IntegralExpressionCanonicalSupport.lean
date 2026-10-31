/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.ExpressionRecursion.IntegralExpressionTransposeIsIso
import WeilConjectures.SixFunctors.IntegralSystemRealization.ExpressionRecursion.IntegralExpressionCanonicalEquations

/-! # Direct compactification agreement of the canonical comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField
  WeilConjectures.integralDerivedPullback WeilConjectures.integralCompletedTensor
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization.ExpressionRecursion
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem inverseOrZero_eq_inv {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y : C} (f : X ⟶ Y) [IsIso f] : GeneratorReduction.inverseOrZero f = inv f := by
  simp only [GeneratorReduction.inverseOrZero, dif_pos (inferInstance : IsIso f)]

private theorem unaryA_reduction (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (d : Primitives l E D o) (rec : Reconstruction l E D)
    {U V : Over (Spec (.of D.k))} (a : Unary _ U V)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (K : (basicUnaryDomain l E U.left V.left (a.system l E o)).FullSubcategory)
    (h : basicUnaryDomain l E U.left V.left (a.system l E o)
      ((coefficientSequenceLimit l E U.left).obj ((calculus l E U.left).reduction.obj K.obj))) :
    unaryA l E d a ((calculus l E U.left).reduction.obj K.obj) h ≫
      (a.integral l E).map
        (GeneratorReduction.inverseOrZero ((calculus l E U.left).adjunction.unit.app K.obj)) =
      (d.unary a).hom.app K := by
  have := rec.unit U K.obj K.property.1
  have := rec.counit U ((calculus l E U.left).reduction.obj K.obj) K.property.2.1
  have hi : inv ((coefficientSequenceLimit l E V.left).map
      ((a.system l E o).map ((calculus l E U.left).adjunction.counit.app
        ((calculus l E U.left).reduction.obj K.obj)))) =
      (coefficientSequenceLimit l E V.left).map ((a.system l E o).map
        ((calculus l E U.left).reduction.map
          ((calculus l E U.left).adjunction.unit.app K.obj))) := by
    apply IsIso.inv_eq_of_inv_hom_id
    erw [← Functor.map_comp, ← Functor.map_comp,
      (calculus l E U.left).adjunction.left_triangle_components,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    simp only [CategoryTheory.Functor.id_obj]
  have hn := (d.unary a).hom.naturality
    (ObjectProperty.homMk ((calculus l E U.left).adjunction.unit.app K.obj) :
      K ⟶ ⟨_, h⟩)
  change (coefficientSequenceLimit l E V.left).map ((a.system l E o).map
      ((calculus l E U.left).reduction.map ((calculus l E U.left).adjunction.unit.app K.obj))) ≫
      (d.unary a).hom.app ⟨_, h⟩ =
    (d.unary a).hom.app K ≫ (a.integral l E).map
      ((calculus l E U.left).adjunction.unit.app K.obj) at hn
  simp only [unaryA, inverseOrZero_eq_inv]
  erw [hi, hn, Category.assoc, ← Functor.map_comp,
    IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

private theorem properA (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (d : Primitives l E D o) (rec : Reconstruction l E D)
    {U V : Over (Spec (.of D.k))} (p : U ⟶ V) (hp : IsProper p.left)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (M : System l E U.left) (hM : Good l E U.left M)
    (h : basicUnaryDomain l E U.left V.left (Operations.push l E o p.left)
      ((coefficientSequenceLimit l E U.left).obj M)) :
    unaryA l E d (.push p hp) M h = (d.model.push l E p.left).hom.app M := by
  have := rec.counit U M hM
  have := rec.unit U _ (rec.limit U M hM)
  have hu : (coefficientSequenceLimit l E U.left).map
      ((calculus l E U.left).adjunction.counit.app M) =
      inv ((calculus l E U.left).adjunction.unit.app
        ((coefficientSequenceLimit l E U.left).obj M)) :=
    IsIso.eq_inv_of_hom_inv_id ((calculus l E U.left).adjunction.right_triangle_components M)
  have hn := (d.model.push l E p.left).hom.naturality
    ((calculus l E U.left).adjunction.counit.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  erw [unaryA, d.unary_spec]
  change GeneratorReduction.inverseOrZero
      ((coefficientSequenceLimit l E V.left).map
        ((Operations.push l E o p.left).map ((calculus l E U.left).adjunction.counit.app M))) ≫
      ((d.model.push l E p.left).hom.app
          ((calculus l E U.left).reduction.obj ((coefficientSequenceLimit l E U.left).obj M)) ≫
        (ringedPush l E p.left).map (GeneratorReduction.inverseOrZero
          ((calculus l E U.left).adjunction.unit.app
            ((coefficientSequenceLimit l E U.left).obj M)))) = _
  simp only [inverseOrZero_eq_inv]
  erw [← hu, ← hn, IsIso.inv_hom_id_assoc]

/-- Agreement with the prescribed direct comparison for the one-variable
compactification expression. This only identifies that single open/proper branch.
Source: fix-prop-coherence.proof.md, coefficient-comparison sentence; extracted
expression-recursion proof, steps 8--11
(blueprint: lem-sf-integral-expression-canonical-support).

Proof: apply canonicalComparisons_equations to supportExpression f cf and its
variable child. The leaf factor is the inverse actual unit. Expand the two unaryA
maps. Naturality of the open primitive comparison moves the leaf inverse through
the open step. The adjunction triangle identity cancels its unit and counit,
leaving exactly L(model.openReduction) followed by the inverse unit at j_! K,
as pinned by unary_spec. At proper image, naturality of model.push moves the open
comparison through the proper comparison and cancels the inverse reconstruction
unit against the transported counit. Thus the recursive hom component is
model.push.hom at J_j(R K), followed by ringedPush.map of that open composite.
The finite-type geometric hypotheses and Reconstruction give invertible units and
counits at every cancellation. Compose with the recorded integral compact-support
realization. DirectComparisons.normalization identifies exactly this composite
with dc.comparison.hom, proving SupportAgreement. No equality is inferred merely
from finite evaluations; the normalization is already an equality of actual
whole-system comparison components. DirectProjection is additional compatible
data and need not be invoked again in this identification. -/
theorem canonicalComparisons_support (D : FiniteFieldDatum.{u})
    (o : Operations l E) (d : Primitives l E D o) (rec : Reconstruction l E D)
    (dc : DirectComparisons l E D o d.model) :
    SupportAgreement l E d dc (canonicalComparisons l E D o d rec) := by
  intro U V f _ _ _ _ _ _ _ hl cf g K
  have : LocallyOfFiniteType V.hom := g.1
  have : QuasiCompact V.hom := g.2.1
  have : LocallyOfFiniteType U.hom := g.2.2.2.2.2.1
  have : QuasiCompact U.hom := g.2.2.2.2.2.2.1
  let Z : Over (Spec (.of D.k)) := Over.mk (cf.g ≫ V.hom)
  let j : U ⟶ Z := Over.homMk cf.i
    ((Category.assoc cf.i cf.g V.hom).symm.trans
      ((congrArg (fun z ↦ z ≫ V.hom) cf.comm.symm).trans f.w))
  let p : Z ⟶ V := Over.homMk cf.g rfl
  let aj : Unary _ U Z := .shriek j (inferInstance : IsOpenImmersion cf.i)
    (compactOpenQuasiCompact cf g.2.2.2.2.1)
  let : LocallyOfFiniteType Z.hom := inferInstanceAs
    (LocallyOfFiniteType (cf.g ≫ V.hom))
  let : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (cf.g ≫ V.hom))
  have he := canonicalComparisons_equations l E D o d rec (supportExpression f cf) g
    (supportInput l E o f cf K)
  simp only [supportExpression, Equations] at he
  obtain ⟨hj, hp, he, hv⟩ := he
  have hjK : basicUnaryDomain l E U.left cf.Z (aj.system l E o) K.obj :=
    ⟨K.property.1.1, K.property.1.2.1, K.property.2⟩
  have hproper := properA l E D o d rec p (inferInstance : IsProper cf.g)
    ((Operations.shriek l E o cf.i).obj ((calculus l E U.left).reduction.obj K.obj))
    K.property.2 hp
  have hopen := unaryA_reduction l E D o d rec aj ⟨K.obj, hjK⟩ hj
  erw [he]
  erw [hv, hproper, hopen]
  erw [d.unary_spec]
  dsimp only [aj, j, p, Z, Unary.primitiveHom, Over.Hom.left, Over.homMk,
    CostructuredArrow.homMk, Over.left, Over.mk, CostructuredArrow.mk]
  erw [dc.normalization f hl cf K]; simp only [Category.assoc]


end WeilConjectures.IntegralSystemRealization.ExpressionRecursion
