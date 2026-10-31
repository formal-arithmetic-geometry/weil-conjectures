/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.SystemProjectionFormula.SystemProjectionFormulaMaps
import WeilConjectures.AlgebraicGeometry.CompactCompositionProjection.TriangleProjectionCompositorContraction

/-! # Projection composition on a compatible triangle

Source: Stacks 0F7B, 0F7J and 0B56; the strict-system projection calculation.
(blueprint: lem-pur-system-projection-triangle-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOfSpec false
set_option genInjectivity false

set_option Elab.async false

universe u g h v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.SystemProjectionFormula

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian

attribute [local irreducible] WeilConjectures.pullbackTensorCalculus
  WeilConjectures.pullbackTensorSequenceDerived HasDerivedCategory.standard
  Functor.leftAdjoint Functor.mapDerivedCategory DerivedCategory CoefficientClosedStructure.tensor

attribute [local implicit_reducible] coefficientSequenceHasDerived SemilinearSections.moduleAbelian
  ProEtale.CompactCompositionProjection.realizedSystems
  ProEtale.CompactCompositionProjection.realizedTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem tensor_map_comp_right {C : Type*} [Category* C]
    (T : C × C ⥤ C) (M : C) {A B R : C} (f : A ⟶ B) (g : B ⟶ R) :
    T.map (Prod.mkHom (𝟙 M) (f ≫ g)) =
      T.map (Prod.mkHom (𝟙 M) f) ≫ T.map (Prod.mkHom (𝟙 M) g) := by
  exact ((Functor.curryObj T).obj M).map_comp f g

private def properComponent (o : Operations l E) {A B : Scheme.{u}} (f : A ⟶ B)
    (K : System l E A) (L : System l E B) :
    (calculus l E B).systemClosed.tensor.obj ((Operations.push l E o f).obj K, L) ⟶
      (Operations.push l E o f).obj
        ((calculus l E A).systemClosed.tensor.obj (K, (pull l E f).obj L)) :=
  ((properProjection l E o f).app K).app L

private def openComponent (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {A B : Scheme.{u}} (j : A ⟶ B) [IsOpenImmersion j]
    (K : System l E A) (L : System l E B) :
    (calculus l E B).systemClosed.tensor.obj ((Operations.shriek l E o j).obj K, L) ⟶
      (Operations.shriek l E o j).obj
        ((calculus l E A).systemClosed.tensor.obj (K, (pull l E j).obj L)) :=
  (a.projection j).hom.app (K, L)

private theorem projection_component_eq (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {A B : Scheme.{u}} {f : A ⟶ B}
    (d : Compactification f) (K : System l E A) (L : System l E B) :
    projection l E o c a d K L =
      properComponent l E o d.g ((Operations.shriek l E o d.i).obj K) L ≫
        (Operations.push l E o d.g).map
          (openComponent l E o c a d.i K ((pull l E d.g).obj L) ≫
            (Operations.shriek l E o d.i).map ((calculus l E A).systemClosed.tensor.map
              (Prod.mkHom (𝟙 K) ((c.pullComp d.i d.g).inv.app L ≫
                eqToHom (congrArg (fun h : A ⟶ B ↦ (pull l E h).obj L) d.comm.symm))))) := by
  rfl

private def rawProjection (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {A V B : Scheme.{u}}
    (j : A ⟶ V) [IsOpenImmersion j] (q : V ⟶ B)
    (K : System l E A) (L : System l E B) :
    (calculus l E B).systemClosed.tensor.obj
        ((Operations.push l E o q).obj ((Operations.shriek l E o j).obj K), L) ⟶
      (Operations.push l E o q).obj ((Operations.shriek l E o j).obj
        ((calculus l E A).systemClosed.tensor.obj (K, (pull l E (j ≫ q)).obj L))) :=
  properComponent l E o q ((Operations.shriek l E o j).obj K) L ≫
    (Operations.push l E o q).map
      (openComponent l E o c a j K ((pull l E q).obj L) ≫
        (Operations.shriek l E o j).map ((calculus l E A).systemClosed.tensor.map
          (Prod.mkHom (𝟙 K) ((c.pullComp j q).inv.app L))))

private theorem projection_transport (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {A B : Scheme.{u}} {f : A ⟶ B}
    (d : Compactification f) (K : System l E A) (L : System l E B) :
    projection l E o c a d K L = rawProjection l E o c a d.i d.g K L ≫
      (Operations.push l E o d.g).map ((Operations.shriek l E o d.i).map
        ((calculus l E A).systemClosed.tensor.map (Prod.mkHom (𝟙 K)
          (eqToHom (congrArg (fun h : A ⟶ B ↦ (pull l E h).obj L) d.comm.symm))))) := by
  rw [projection_component_eq]
  dsimp only [rawProjection]
  simp -implicitDefEqProofs only [tensor_map_comp_right, Functor.map_comp, Category.assoc]

attribute [local irreducible] properProjection compactificationProjection projection rawProjection

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (o : Operations l E) (z : Realizations l E D o)
  {X Y Z : Scheme.{u}}
  [overX : X.Over (Spec (.of D.k))] [overY : Y.Over (Spec (.of D.k))]
  [overZ : Z.Over (Spec (.of D.k))]
  [sepX : IsSeparated (X ↘ Spec (.of D.k))] [sepY : IsSeparated (Y ↘ Spec (.of D.k))]
  [sepZ : IsSeparated (Z ↘ Spec (.of D.k))]
  [ftX : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [qcX : QuasiCompact (X ↘ Spec (.of D.k))]
  [ftY : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [qcY : QuasiCompact (Y ↘ Spec (.of D.k))]
  [ftZ : LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
  [qcZ : QuasiCompact (Z ↘ Spec (.of D.k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [overF : f.IsOver (Spec (.of D.k))] [overG : g.IsOver (Spec (.of D.k))]
  [sepF : IsSeparated f] [ftF : LocallyOfFiniteType f] [QuasiCompact f]
  [sepG : IsSeparated g] [ftG : LocallyOfFiniteType g] [QuasiCompact g]

-- Keep the original separatedness binders, although the component calculation does not use them.
set_option linter.unusedSectionVars false in
include D hl overX overY overZ sepX sepY sepZ ftX qcX ftY qcY ftZ qcZ
  overF overG sepF sepG ftF ftG in
end Geometry
end WeilConjectures.SystemProjectionFormula
