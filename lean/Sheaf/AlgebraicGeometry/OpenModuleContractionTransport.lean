/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryEvaluationData
public import Sheaf.Paper.DerivedHomMayerVietoris
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Transport of a module contraction on an open subscheme

Source: Stacks Project, Tags 08DL, 08DQ and 03EO; the sectionwise
open-site reindexing construction of `Scheme.Modules.overEquiv`.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

/-- Open-site transport of contraction by an arbitrary module-valued dual input.
Source: Stacks Project, Tags 08DL and 08DQ (restriction and evaluation),
and Tag 03EO (tensor-Hom adjunction).
(blueprint: lem-pc-open-module-contraction-transport).

Proof: compare e with sectionwise internal-Hom reindexing. Its quotient is
an internal-Hom automorphism natural in both variables. On global morphisms,
its value on identities gives endomorphisms z with alpha(f)=z_B f=f z_A.
For each open V, use the extension by zero of O_V and its map to O, which is
identity on V. Its endomorphism is multiplication by the restriction of
z_O(1). Every local section is represented by a map from this extension by
zero, so every z_A is multiplication by the same scalar t. Apply the same
argument to the adjoint map from the extension by zero of A restricted to V
to obtain alpha(phi)=t phi for local Hom sections. The scalar is invertible
because alpha on Hom(O,O) is invertible. The normalized tensorator is the
canonical reindexing tensorator: test local pure tensors with the two maps
from the extension by zero of O_V, reduce by naturality to the unit-unit
component, and use the unit coherence law and hunit. Local sums of pure
tensors determine maps from the sheaf tensor product. On a local tensor
b tensor w the two curried maps send x to k(t * v(h(w))(x) • b); linearity
allows t to move between the two factors. Symmetry and associativity place
these factors in the displayed order. Substitute hv and hk in this equation.
The output map k is handled by
naturality in the target, and the input h by tensor-Hom naturality.
Thus the maps agree on local tensors, hence on their sheafification.
The argument includes zero modules, empty opens and the zero ring. -/
theorem openModule_contraction_transport (X : Scheme.{u}) (U : X.Opens) :
    let L := Equivalence.functor
      (C := localEvaluationModules X U)
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    ∀ (e : ∀ A B : localEvaluationModules X U,
      L.obj (SheafOfModules.homObj (R := X.sheaf.over U) A B) ≅
        SheafOfModules.homObj (R := U.toScheme.sheaf) (L.obj A) (L.obj B))
    (he : ∀ (A A' B B' : localEvaluationModules X U) (f : A' ⟶ A) (g : B ⟶ B'),
      L.map (SheafOfModules.homObjMap (R := X.sheaf.over U) f g) ≫ (e A' B').hom =
        (e A B).hom ≫
          SheafOfModules.homObjMap (R := U.toScheme.sheaf) (L.map f) (L.map g))
    (m : L.CoreMonoidal)
    (hunit : m.εIso = Scheme.Modules.overEquivFunctorObjUnitIso U)
    (hsymm : ∀ A B : localEvaluationModules X U,
      L.map (β_ A B).hom ≫ (m.μIso B A).inv =
        (m.μIso A B).inv ≫ (β_ (L.obj A) (L.obj B)).hom)
    (A B V B' : localEvaluationModules X U)
    (W : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (h : W ⟶ L.obj V)
    (v : V ⟶ SheafOfModules.homObj (R := X.sheaf.over U) A
      (𝟙_ (localEvaluationModules X U))) (k : B ⟶ B')
    (v' : W ⟶ SheafOfModules.homObj (R := U.toScheme.sheaf) (L.obj A)
      (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))))
    (k' : L.obj B ⟶ L.obj B')
    (hv : h ≫ L.map v ≫ (e A (𝟙_ (localEvaluationModules X U))).hom ≫
      SheafOfModules.homObjMap (R := U.toScheme.sheaf) (𝟙 (L.obj A))
        (Scheme.Modules.overEquivFunctorObjUnitIso U).inv = v')
    (hk : L.map k = k'),
    (𝟙 (L.obj B) ⊗ₘ h) ≫ (m.μIso B V).hom ≫
      L.map (SheafOfModules.tensorHomEquiv (R := X.sheaf.over U) A _ _
        ((β_ A (B ⊗ V)).hom ≫ (α_ B V A).hom ≫
          B ◁ ((β_ V A).hom ≫
            (SheafOfModules.tensorHomEquiv (R := X.sheaf.over U) A V
              (𝟙_ (localEvaluationModules X U))).symm v) ≫ (ρ_ B).hom ≫ k)) ≫
        (e A B').hom =
      SheafOfModules.tensorHomEquiv (R := U.toScheme.sheaf) (L.obj A) _ _
        ((β_ (L.obj A) (L.obj B ⊗ W)).hom ≫ (α_ (L.obj B) W (L.obj A)).hom ≫
          L.obj B ◁ ((β_ W (L.obj A)).hom ≫
            (SheafOfModules.tensorHomEquiv (R := U.toScheme.sheaf) (L.obj A) W
              (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))).symm
                v') ≫
          (ρ_ (L.obj B)).hom ≫ k') := by sorry

end AlgebraicGeometry
