/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Limits.Opposites

import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Galois limits and the faces of the separable-closure Cech nerve

Source: Stacks, fields.tex Tag 0BU2, algebra.tex Tag 00DD, limits.tex Tag 01YW;
blueprint latest, det-thm-sf-ctf-stability-direct-images, paragraph (3), expanded
by the cumulative-vertex calculation in the DAG.
(blueprint: lem-sfb-galois-limit-nerve-faces).

The finite-stage diagram, its colimit cocone, and the comparison isomorphisms are
existentially specified with their canonical normalization. No arbitrary map is
assumed in place of a canonical construction. The arbitrary simplex-map formula
includes every face and degeneracy, with its action on the initial vertex.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct Simplicial

namespace AlgebraicGeometry.ProEtale

/-- Finite Galois coordinates pass to locally constant functions and to the actual
scheme Cech nerve, with the twisted first face.

Source: Stacks Tags 0BU2, 00DD, 01YW, and the explicit cumulative-vertex substitution
in blueprint latest, det-thm-sf-ctf-stability-direct-images, paragraph (3).
(blueprint: lem-sfb-galois-limit-nerve-faces).

Proof: (1) A separable closure is Galois. Finite Galois intermediate fields are a
nonempty directed set, their union is the closure, and restriction identifies its
Krull group with their inverse limit (lem-weil-pbc-separable-closure-exists-galois,
lem-exc-galois-krull-finite-limit, lem-weil-pbc-finite-set-in-finite-galois-subextension,
lem-weil-pbc-normal-subextension-automorphism-extends). The same holds for each
finite power, including the singleton zeroth power.
(2) Tensor products commute with this union: evaluate a compatible cocone on a
single tensor slot at a finite stage containing its entry. A common upper stage
makes this independent of the choice, and tensor universality gives existence
and uniqueness. Transport by theta (lem-weil-pbc-algebra-tensor-pushout-universal-property).
(3) Every locally constant function factors through a finite stage by
lem-weil-pbc-profinite-limit-function-factorization. Surjective restriction maps
prove injectivity after a common refinement. This proves the colimit universal
property and also factorization of maps to every finite discrete set.
(4) Apply Spec, the affine tensor/pullback formula, and the finite coproduct formula
(lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-spec-small-colimit-limit,
lem-weil-pbc-finite-affine-coproduct-spectrum). Cofinality of these partitions
identifies this limit with def-sfb-profinite-test-objects, preserving vertex zero.
(5) Evaluate a tensor supported in slot j: its coordinate is the cumulative product
of the first j increments. Composition with any ring-valued base point gives the
stated vertex, with the order reversed by Spec on scheme maps.
(6) Deleting vertex zero applies the first increment to the remaining value;
deleting an interior vertex multiplies adjacent increments; deleting the last
vertex drops the last increment. All are equalities of ring maps by tensor
universality. The twisted value is locally constant: enlarge the finite stage to
contain the finite range of the function.
(7) Repeating a vertex inserts the identity increment. The general simplex formula
selects cumulative vertices and divides successive selections on the left.
(8) On a triple the edges have labels (x,g), (xg,h), (x,gh). Composition of the
later-to-earlier identifications is epsilon02 = epsilon01 after epsilon12.
For structure-ring coefficients its equation is c(gh)=c(g)*g(c(h)); constant
coefficients give c(gh)=c(g)*c(h), as recorded separately below. -/
theorem galois_limit_nerve_faces
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    (θ : ∀ (E : FiniteGaloisIntermediateField k Ω) (q : ℕ),
      (Ω ⊗[k] (⨂[k] _ : Fin q, E)) ≃ₐ[Ω] ((Fin q → (E ≃ₐ[k] E)) → Ω))
    (hθ : ∀ (E : FiniteGaloisIntermediateField k Ω) (q : ℕ)
      (a₀ : Ω) (a : Fin q → E) (g : Fin q → (E ≃ₐ[k] E)),
      θ E q (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a) g =
        a₀ * ∏ j : Fin q, (((List.ofFn g).take (j.val + 1)).prod (a j) : Ω))
    (hθcompat : ∀ (E F : FiniteGaloisIntermediateField k Ω) (h : E ≤ F)
      (q : ℕ) (a₀ : Ω) (a : Fin q → E) (g : Fin q → (F ≃ₐ[k] F)),
      θ F q (a₀ ⊗ₜ[k] PiTensorProduct.tprod k
          (fun j ↦ (⟨(a j : Ω), h (a j).property⟩ : F))) g =
        θ E q (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a)
          (fun j ↦ finGaloisGroupMap (homOfLE h).op (g j))) :
    ∃ e : ∀ q : ℕ, (Ω ⊗[k] (⨂[k] _ : Fin q, Ω)) ≃ₐ[Ω]
        LocallyConstant (Fin q → (Ω ≃ₐ[k] Ω)) Ω,
      (∀ (q : ℕ) (a₀ : Ω) (a : Fin q → Ω) (g : Fin q → (Ω ≃ₐ[k] Ω)),
        e q (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a) g =
          a₀ * ∏ j : Fin q, ((List.ofFn g).take (j.val + 1)).prod (a j)) ∧
      (∀ q : ℕ,
        ∃ (D : FiniteGaloisIntermediateField k Ω ⥤ CommAlgCat.{u} Ω)
          (o : ∀ E : FiniteGaloisIntermediateField k Ω,
            D.obj E ≅ CommAlgCat.of Ω ((Fin q → (E ≃ₐ[k] E)) → Ω))
          (ι : D ⟶ (Functor.const _).obj
            (CommAlgCat.of Ω (LocallyConstant (Fin q → (Ω ≃ₐ[k] Ω)) Ω))),
          (∀ (E F : FiniteGaloisIntermediateField k Ω) (h : E ≤ F)
            (f : (Fin q → (E ≃ₐ[k] E)) → Ω) (g : Fin q → (F ≃ₐ[k] F)),
            ((o F).hom.hom ((D.map (homOfLE h)).hom ((o E).inv.hom f))) g =
              f (fun j ↦ finGaloisGroupMap (homOfLE h).op (g j))) ∧
          (∀ (E : FiniteGaloisIntermediateField k Ω)
            (f : (Fin q → (E ≃ₐ[k] E)) → Ω) (g : Fin q → (Ω ≃ₐ[k] Ω)),
            (@id (LocallyConstant (Fin q → (Ω ≃ₐ[k] Ω)) Ω)
              ((ι.app E).hom ((o E).inv.hom f))) g =
              f (fun j ↦ AlgEquiv.restrictNormalHom E (g j))) ∧
          Nonempty (IsColimit (Cocone.mk _ ι)) ∧
          Nonempty (IsLimit (Scheme.Spec.mapCone
            (((forget₂ (CommAlgCat Ω) CommRingCat).mapCocone
              (Cocone.mk _ ι)).op)))) ∧
      (∀ (q : ℕ) (A : Type v) [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
        (f : C((Fin q → (Ω ≃ₐ[k] Ω)), A)),
        ∃ (E : FiniteGaloisIntermediateField k Ω) (fE : (Fin q → (E ≃ₐ[k] E)) → A),
          ∀ g : Fin q → (Ω ≃ₐ[k] Ω),
            f g = fE (fun j ↦ AlgEquiv.restrictNormalHom E (g j))) ∧
      ∃ (r : ∀ q : ℕ,
          (Arrow.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).cechNerve.obj
            (op ⦋q⦌) ≅ Spec (.of (Ω ⊗[k] (⨂[k] _ : Fin q, Ω))))
        (c : ∀ q : ℕ, Spec (.of (LocallyConstant (Fin q → (Ω ≃ₐ[k] Ω)) Ω)) ≅
          ((profiniteToProEtOf (Spec (.of Ω))).obj
            (Profinite.of (Fin q → (Ω ≃ₐ[k] Ω)))).left)
        (s : ∀ q : ℕ,
          (Arrow.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).cechNerve.obj
            (op ⦋q⦌) ≅ ((profiniteToProEtOf (Spec (.of Ω))).obj
              (Profinite.of (Fin q → (Ω ≃ₐ[k] Ω)))).left)
        (F : ∀ (n m : ℕ) (_α : SimplexCategory.mk n ⟶ SimplexCategory.mk m),
          LocallyConstant (Fin n → (Ω ≃ₐ[k] Ω)) Ω →ₐ[k]
            LocallyConstant (Fin m → (Ω ≃ₐ[k] Ω)) Ω),
        (∀ q : ℕ, (c q).inv ≫ Spec.map (CommRingCat.ofHom (e q).toRingHom) ≫
          (r q).inv = (s q).inv) ∧
        (∀ q : ℕ, (c q).hom ≫
          ((profiniteToProEtOf (Spec (.of Ω))).obj
            (Profinite.of (Fin q → (Ω ≃ₐ[k] Ω)))).hom =
              Spec.map (CommRingCat.ofHom LocallyConstant.constRingHom)) ∧
        (∀ q : ℕ, (c q).hom ≫
          pullback.fst
            (toSpecZ ((profiniteToProEt.obj
              (Profinite.of (Fin q → (Ω ≃ₐ[k] Ω)))).left))
            (toSpecZ (Spec (.of Ω))) =
          Spec.map (CommRingCat.ofHom
            (LocallyConstant.mapRingHom (Int.castRingHom Ω)))) ∧
        (∀ q : ℕ, (r q).inv ≫
          WidePullback.π (fun _ : Fin (q + 1) ↦
            Spec.map (CommRingCat.ofHom (algebraMap k Ω))) 0 =
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeft : Ω →ₐ[Ω]
              Ω ⊗[k] (⨂[k] _ : Fin q, Ω)).toRingHom)) ∧
        (∀ (q : ℕ) (j : Fin q), (r q).inv ≫
          WidePullback.π (fun _ : Fin (q + 1) ↦
            Spec.map (CommRingCat.ofHom (algebraMap k Ω))) j.succ =
          Spec.map (CommRingCat.ofHom
            ((Algebra.TensorProduct.includeRight : (⨂[k] _ : Fin q, Ω) →ₐ[k]
              Ω ⊗[k] (⨂[k] _ : Fin q, Ω)).comp
                (PiTensorProduct.singleAlgHom (R := k) j)).toRingHom)) ∧
        (∀ (q : ℕ) (B : Type u) [CommRing B] (x : Ω →+* B)
          (g : Fin q → (Ω ≃ₐ[k] Ω)) (j : Fin (q + 1)),
          Spec.map (CommRingCat.ofHom (x.comp (LocallyConstant.evalRingHom g))) ≫
            (c q).hom ≫ (s q).inv ≫
              WidePullback.π (fun _ : Fin (q + 1) ↦
                Spec.map (CommRingCat.ofHom (algebraMap k Ω))) j =
            Spec.map (CommRingCat.ofHom
              (x.comp (((List.ofFn g).take j.val).prod).toRingHom))) ∧
        (∀ (n m : ℕ) (α : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
          (f : LocallyConstant (Fin n → (Ω ≃ₐ[k] Ω)) Ω)
          (g : Fin m → (Ω ≃ₐ[k] Ω)),
          F n m α f g = ((List.ofFn g).take (α.toOrderHom 0).val).prod
            (f (fun j ↦
              (((List.ofFn g).take (α.toOrderHom j.castSucc).val).prod)⁻¹ *
                ((List.ofFn g).take (α.toOrderHom j.succ).val).prod))) ∧
        (∀ (n m : ℕ) (α : SimplexCategory.mk n ⟶ SimplexCategory.mk m),
          (s m).inv ≫
            (Arrow.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).cechNerve.map α.op ≫
              (s n).hom =
          (c m).inv ≫ Spec.map (CommRingCat.ofHom (F n m α).toRingHom) ≫ (c n).hom) ∧
        (∀ f : LocallyConstant (Fin 1 → (Ω ≃ₐ[k] Ω)) Ω,
          F 1 2 (SimplexCategory.δ (1 : Fin 3)) f =
              F 1 2 (SimplexCategory.δ (2 : Fin 3)) f *
                F 1 2 (SimplexCategory.δ (0 : Fin 3)) f ↔
            ∀ g h : Ω ≃ₐ[k] Ω,
              f (fun _ ↦ g * h) = f (fun _ ↦ g) * g (f (fun _ ↦ h))) := by
  sorry

/-- With trivial action on coefficient values, the pulled-back descent cocycle is
exactly a homomorphism in the order g then h. Coefficients can be any monoid, hence
include invertible matrices and fibre automorphisms.

Source: the triple-overlap calculation in blueprint latest,
det-thm-sf-ctf-stability-direct-images, paragraph (3).
(blueprint: lem-sfb-galois-limit-nerve-faces).
Proof: the selected edges 02, 01, 12 of a triple of increments (g,h) have labels
gh, g, h. The later-to-earlier composite is c(g)*c(h). Equality of locally
constant functions is pointwise equality. The first theorem retains the moved
base vertex and thus gives the twisted version for structure-ring coefficients. -/
theorem galois_limit_nerve_constant_cocycle
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    (A : Type v) [Monoid A] (c : LocallyConstant (Ω ≃ₐ[k] Ω) A) :
    c.comap ⟨(fun p : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) ↦ p.1 * p.2),
        continuous_fst.mul continuous_snd⟩ =
      c.comap ⟨Prod.fst, continuous_fst⟩ * c.comap ⟨Prod.snd, continuous_snd⟩ ↔
        ∀ g h : Ω ≃ₐ[k] Ω, c (g * h) = c g * c h := by
  sorry

end AlgebraicGeometry.ProEtale
