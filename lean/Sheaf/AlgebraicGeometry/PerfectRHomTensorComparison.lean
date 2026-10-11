/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction
public import Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! # Perfect RHom tensor comparison

Source: Stacks Project, Cohomology, Tags 08DQ, 0FPC and 0GM7
(blueprint: lem-pc-perfect-rhom-tensor-comparison).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The dual of a perfect complex is perfect, with evaluation, coevaluation, biduality,
base change, and the tensor--internal-Hom comparison.
Source: Stacks Project, Cohomology, Tags 08DQ, 0FPC and 0GM7
(blueprint: lem-pc-perfect-rhom-tensor-comparison).

Proof: choose a strictly perfect local representative of `K`. By
lem-sc-derived-internal-hom-restrict-open and lem-pc-rhom-strict-perfect-hom,
the dual and RHom are represented locally by ordinary Hom complexes. Their dual terms
are finite projective and quasi-coherent. By lem-pc-bounded-above-flat-kflat they compute
the derived tensor. The tensor--Hom comparison is a termwise isomorphism for finite
free modules and their direct summands. Check invertibility locally on cohomology
sheaves; no morphisms need gluing. Apply lem-pc-dualizable-evaluation-criterion to the
comparison (valid for all
objects of D(O_X) by the same local calculation). Its coevaluation is the inverse
image of the identity, and its triangle identities give the exact pairing. The bidual and
base-change maps are the maps corresponding under the tensor--internal-Hom bijections
`adj`, `adj'` (on `X`) and `adjT` (on `T`) of lem-sc-derived-internal-hom-adjunction,
tied by their naturality equations as in `scheme_derivedInternalHom_adjunction`
(`adj'` is its symmetric form, the symmetry followed by `adj`); the base-change map uses
the tensor and unit isomorphisms of a canonical monoidal model of `Lg^*`
(`IsDerivedPullbackMonoidalModel`, the descent of `derivedPullback_tensorProduct`).
Any two such bijections, or two such models, change these maps only by isomorphisms,
so the invertibility assertions do not depend on the choices.
For base change restrict to affine opens in inverse images of
the cover;
lem-pc-flat-complex-derived-pullback computes both duals by termwise pullback. The
comparison is pullback of finite-projective duals, an isomorphism on finite free
modules and direct summands. Check invertibility locally on cohomology sheaves. -/
theorem perfect_rhom_tensor_comparison
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K M : schemeDerivedQCohCategory X)
    (hK : Scheme.IsPerfect X K.obj)
    (adj : ∀ A B C : schemeDerivedCategory X,
      (A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op B, C)) ≃ (A ⊗ B ⟶ C))
    (hadj : ∀ (A A' B B' C C' : schemeDerivedCategory X)
      (a : A' ⟶ A) (b : B' ⟶ B) (c : C ⟶ C')
      (f : A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op B, C)),
      adj A' B' C' (a ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.op, c)) =
        (a ⊗ₘ b) ≫ adj A B C f ≫ c)
    (adj' : ∀ A B C : schemeDerivedCategory X,
      (A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op B, C)) ≃ (B ⊗ A ⟶ C))
    (hadj' : ∀ (A A' B B' C C' : schemeDerivedCategory X)
      (a : A' ⟶ A) (b : B' ⟶ B) (c : C ⟶ C')
      (f : A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op B, C)),
      adj' A' B' C' (a ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.op, c)) =
        (b ⊗ₘ a) ≫ adj' A B C f ≫ c) :
    ∃ (Kdual : schemeDerivedQCohCategory X)
      (hdual : Kdual.obj =
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op K.obj, 𝟙_ (schemeDerivedCategory X)))
      (ev : Kdual.obj ⊗ K.obj ⟶ 𝟙_ (schemeDerivedCategory X)),
      ev = adj Kdual.obj K.obj (𝟙_ (schemeDerivedCategory X)) (eqToHom hdual) ∧
      Scheme.IsPerfect X Kdual.obj ∧
      ∃ comparison : ∀ N : schemeDerivedQCohCategory X, N.obj ⊗ Kdual.obj ⟶
          (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
            X.toRingedSpace.sheaf).obj (op K.obj, N.obj),
        (∀ N, adj (N.obj ⊗ Kdual.obj) K.obj N.obj (comparison N) =
            (α_ N.obj Kdual.obj K.obj).hom ≫ N.obj ◁ ev ≫ (ρ_ N.obj).hom) ∧
        IsIso (comparison M) ∧ IsIso (comparison K) ∧
        ∃ bidual : K.obj ⟶
            (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
              X.toRingedSpace.sheaf).obj (op Kdual.obj, 𝟙_ (schemeDerivedCategory X)),
          adj' K.obj Kdual.obj (𝟙_ (schemeDerivedCategory X)) bidual = ev ∧
          IsIso bidual ∧
          ∃ η : 𝟙_ (schemeDerivedCategory X) ⟶ K.obj ⊗ Kdual.obj,
            adj (𝟙_ (schemeDerivedCategory X)) K.obj K.obj
                (η ≫ comparison K) = (λ_ K.obj).hom ∧
            (∀ z : 𝟙_ (schemeDerivedCategory X) ⟶ K.obj ⊗ Kdual.obj,
              adj (𝟙_ (schemeDerivedCategory X)) K.obj K.obj
                  (z ≫ comparison K) = (λ_ K.obj).hom → z = η) ∧
            (∃ p : ExactPairing K.obj Kdual.obj,
              p.evaluation' = ev ∧ p.coevaluation' = η) ∧
            ∀ (T : Scheme.{u}) (g : T ⟶ X)
              [HasDerivedCategory.{w}
                (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
              (adjT : ∀ A B C : schemeDerivedCategory T,
                (A ⟶ (derivedInternalHom (Opens.grothendieckTopology T.toRingedSpace)
                  T.toRingedSpace.sheaf).obj (op B, C)) ≃ (A ⊗ B ⟶ C)),
              (∀ (A A' B B' C C' : schemeDerivedCategory T)
                (a : A' ⟶ A) (b : B' ⟶ B) (c : C ⟶ C')
                (f : A ⟶ (derivedInternalHom (Opens.grothendieckTopology T.toRingedSpace)
                  T.toRingedSpace.sheaf).obj (op B, C)),
                adjT A' B' C' (a ≫ f ≫
                  (derivedInternalHom (Opens.grothendieckTopology T.toRingedSpace)
                    T.toRingedSpace.sheaf).map (b.op, c)) =
                  (a ⊗ₘ b) ≫ adjT A B C f ≫ c) →
              ∀ m : (derivedPullback g).CoreMonoidal,
              IsDerivedPullbackMonoidalModel g m →
              ∃ bc : (derivedPullback g).obj Kdual.obj ⟶
                  (derivedInternalHom (Opens.grothendieckTopology T.toRingedSpace)
                    T.toRingedSpace.sheaf).obj
                    (op ((derivedPullback g).obj K.obj), 𝟙_ (schemeDerivedCategory T)),
                adjT ((derivedPullback g).obj Kdual.obj) ((derivedPullback g).obj K.obj)
                  (𝟙_ (schemeDerivedCategory T)) bc =
                    (m.μIso Kdual.obj K.obj).hom ≫ (derivedPullback g).map ev ≫
                      m.εIso.inv ∧
                IsIso bc := by
  sorry

end AlgebraicGeometry
