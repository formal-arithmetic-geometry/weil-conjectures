/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSheafConstruction
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.AlternatingCechTotalComplex

/-! # Global sections of the increasing-tuple sheaf complex

Source: Stacks Project, Tag 01FM, signed faces and intersection sections.
(blueprint: lem-pc-s3-alternating-cech-sheaf-affine-sections).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Taking global sections after pushforward recovers the section complex, with scalars
restricted along the base morphism. Source: Stacks Project, Tags 01FM and 02KG.
(blueprint: lem-pc-s3-alternating-cech-sheaf-affine-sections).

Proof: The intersection presheaf V ↦ G(V ∩ W) is already a sheaf: it is the direct
image from the over site of W. Its sheafification unit is therefore an isomorphism.
Module sheafification is additive and preserves finite biproducts, hence finite
products. The forgetful functor and evaluation preserve products. Therefore the
degree-p global sections of the sheafified product are the product of G(W_t).
At the top open, top ∩ W_t = W_t.
Pushforward sections at the top are sections on X, and restriction of scalars is
along A → Γ(X,O_X), the composite of ΓSpecIso.inv and f.appTop. These identifications
commute with each face restriction since they are the sheafification unit followed
by restriction along top ∩ W_t = W_t. Additivity then identifies the finite signed
sums defining both differentials. Thus the degree comparisons form a complex
isomorphism. In negative degrees both extended complexes are zero, and the unique
maps give the comparison there. The empty family and empty tuple types contribute
zero modules, and require no covering or affineness hypothesis. -/
theorem alternatingCechSheafComplex_affineSections
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) :
    letI : (moduleSpecΓFunctor (R := A)).Additive := ⟨by intros; rfl⟩
    Nonempty (((moduleSpecΓFunctor (R := A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)) ≅
      ((ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom)).mapHomologicalComplex
         (ComplexShape.up ℤ)).obj
        ((alternatingCechComplex U G.presheafModuleCat).extend
          ComplexShape.embeddingUpNat)) := by sorry

end AlgebraicGeometry
