/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.RingTheory.FaithfullyFlat.Amitsur
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.EtaleTensorSections
import Sheaf.AlgebraicGeometry.TensorPullback

/-! # Degreewise affine singleton tensor comparison
Source: Stacks Project, Tag 03P2, affine tensor-product calculation.
(blueprint: new-etale-affine-singleton-tensor-degree-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- The singleton tensor-section Čech complex, before identifying its terms. -/
abbrev singletonTensorCech (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) :=
  (cechComplexFunctor fun _ : Fin 1 ↦ Over.mk g).obj
    ((Over.forget U).op ⋙
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf F)).obj)

/-- Forget scalars and lift the affine Amitsur complex. -/
abbrev singletonTensorAmitsur (X : Scheme.{u}) (F : X.Modules)
    (U W : X.Etale) (g : W ⟶ U) :=
  letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  (((forget₂ (ModuleCat.{u} Γ(U.left, ⊤)) AddCommGrpCat.{u}) ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (.up ℕ)).obj
      (Algebra.TensorProduct.amitsurComplex Γ(U.left, ⊤) Γ(W.left, ⊤)
        Γ((Modules.tensorPullback U.hom).obj F, ⊤))

/-- The cosimplicial object underlying the singleton tensor-section Čech complex. -/
abbrev singletonTensorCechCosimplicial (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] (U W : X.Etale) (g : W ⟶ U) :=
  (FormalCoproduct.cosimplicialObjectFunctor
    (FormalCoproduct.mk _ (fun _ : Fin 1 ↦ Over.mk g)).cech).obj
      ((Over.forget U).op ⋙
        ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (Modules.etaleTensorSectionsSheaf F)).obj)

/-- The coefficient-forgetting and universe-lifting functor used by the comparison. -/
abbrev singletonTensorForget (U : Scheme.{u}) :=
  (forget₂ (ModuleCat.{u} Γ(U, ⊤)) AddCommGrpCat.{u}) ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- The pure-tensor equation fixes the degree comparison uniquely: evaluate the singleton
product, multiply the pulled-back functions, and pull back the coefficient section.
This predicate mentions no differential or coface. -/
def IsSingletonTensorDegreeComparison (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] (U W : X.Etale) (g : W ⟶ U) (n : ℕ)
    (e : (singletonTensorAmitsur X F U W g).X n ≅
      (singletonTensorCech X F U W g).X n) : Prop :=
  letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  let P := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
  ∀ (m : Γ((Modules.tensorPullback U.hom).obj F, ⊤))
    (b : Fin (n + 1) → Γ(W.left, ⊤)),
    ((Pi.π (fun _ : Fin (n + 1) → Fin 1 ↦
      AddCommGrpCat.of (ULift.{u + 1} Γ((Modules.tensorPullback P.left.hom).obj F, ⊤)))
      (fun _ ↦ 0))
        (e.hom (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b)))).down =
      (∏ k : Fin (n + 1), (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left.appTop
        (b k)) • Modules.etaleTensorSectionsRestriction F P.hom m

/-- Affine pullback sections give canonical degree isomorphisms, with their pure-tensor
normalization, without asserting compatibility between different degrees.
Source: Stacks Project, Tag 03P2, affine-case identification before exactness;
Tags 01I9 and 01IA for the affine fibre-product and module calculations.
(blueprint: new-etale-affine-singleton-tensor-degree-comparison)

Proof: write A = Γ(U,O), B = Γ(W,O), M = Γ(U,U*F). Compare tensor pullback with
Mathlib pullback using their adjunctions to the same pushforward. This transports
quasi-coherence of U*F. The product of n+1 copies of W over U is affine, and its
functions are the indexed tensor product of n+1 copies of B over A, with the
k-th projection inducing the k-th tensor inclusion. Apply the affine pullback
sections formula to this product over U. Normalize composite pullback by its
unit equation; on m tensor the pure tensor b the resulting section is the product
of the pulled-back b(k) times the restriction of m. The outer product is indexed
by functions to Fin 1, so evaluation at its unique index is an isomorphism.
Apply ULift and invert this evaluation to obtain e. Tensor generators prove the
stated normalization and also make e unique. For an empty W the section groups
and tensors are zero; for n=0 this is the ordinary affine sections formula. -/
theorem exists_singletonTensorDegreeComparison
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (hU : IsAffine U.left) (hW : IsAffine W.left) :
    ∃ e : ∀ n : ℕ, (singletonTensorAmitsur X F U W g).X n ≅
      (singletonTensorCech X F U W g).X n,
      ∀ n, IsSingletonTensorDegreeComparison X F U W g n (e n) := by sorry

end
end AlgebraicGeometry.Scheme
