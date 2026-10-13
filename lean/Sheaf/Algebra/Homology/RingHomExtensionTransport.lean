/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap

/-! # Transport of a module Hom comparison to the one-point ring site

Source: Stacks Project, more-algebra.tex, equation-base-change-RHom and
Lemma 0A6A; the one-point-site realization used in the parent statement.
(blueprint: lem-pc-ring-hom-extension-transport)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace CategoryTheory

private theorem point_eq (U : (Discrete PUnit.{u + 1})ᵒᵖ) :
    U = op ⟨PUnit.unit⟩ := by
  rcases U with ⟨⟨⟨⟩⟩⟩
  rfl

private theorem slice_eq (W : (Over (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1}))ᵒᵖ) :
    W = op (Over.mk (𝟙 (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1}))) := by
  rcases W with ⟨⟨⟨⟨⟩⟩, ⟨⟨⟩⟩, f⟩⟩
  rfl

private noncomputable def pointLift {A : Type u} [CommRing A]
    (M N : RingSiteModules A)
    (f : M.val.obj (op ⟨PUnit.unit⟩) →ₗ[A] N.val.obj (op ⟨PUnit.unit⟩)) : M ⟶ N where
  val :=
    { app := fun U ↦ by
        have hU := point_eq U
        subst U
        exact ModuleCat.ofHom f
      naturality := by
        intro U V i
        have hU := point_eq U
        subst U
        have hV := point_eq V
        subst V
        have hi : i = 𝟙 (op (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1})) :=
          Subsingleton.elim _ _
        subst i
        ext x
        simp }

private noncomputable def pointHomEquiv {A : Type u} [CommRing A]
    (M N : RingSiteModules A) :
    (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N).val.obj
      (op ⟨PUnit.unit⟩) ≃ₗ[A]
        (M.val.obj (op ⟨PUnit.unit⟩) →ₗ[A] N.val.obj (op ⟨PUnit.unit⟩)) where
  toFun f := (f.app (op (Over.mk (𝟙 _)))).hom
  invFun f :=
    { app := fun W ↦ by
        rw [slice_eq W]
        exact ModuleCat.ofHom f
      naturality := by
        intro U V i
        have hU := slice_eq U
        subst U
        have hV := slice_eq V
        subst V
        have hi : i = 𝟙 _ := by
          apply Quiver.Hom.unop_inj
          ext
          apply Subsingleton.elim
        subst i
        ext x
        simp
        rfl }
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro W
    rw [slice_eq W]
    rfl
  right_inv f := rfl
  map_add' f g := rfl
  map_smul' a f := by
    ext x
    rfl

private noncomputable def pointExtensionEquiv
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (M : RingSiteModules A) :
    letI := φ.toAlgebra
    B ⊗[A] M.val.obj (op ⟨PUnit.unit⟩) ≃ₗ[B]
      (F.obj M).val.obj (op ⟨PUnit.unit⟩) := by
  letI := φ.toAlgebra
  let T := SheafOfModules.changeOfRingsPresheaf.{u} (ringSiteMap φ) M
  let η := toSheafify ⊥ T.presheaf
  have : IsIso η := isIso_toSheafify ⊥ (Presheaf.isSheaf_bot _)
  let α := (eqToHom (hF M).symm).val.app (op ⟨PUnit.unit⟩)
  have : IsIso α := by
    change IsIso ((SheafOfModules.evaluation _ _).map (eqToHom (hF M).symm))
    infer_instance
  let e : B ⊗[A] M.val.obj (op ⟨PUnit.unit⟩) →ₗ[B]
      (SheafOfModules.changeOfRings (ringSiteMap φ) M).val.obj (op ⟨PUnit.unit⟩) :=
    ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app T).app
      (op ⟨PUnit.unit⟩) |>.hom
  exact (LinearEquiv.ofBijective e
    (ConcreteCategory.bijective_of_isIso (η.app (op ⟨PUnit.unit⟩)))).trans
    (LinearEquiv.ofBijective α.hom (ConcreteCategory.bijective_of_isIso α))

private theorem pointExtensionEquiv_tmul
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (M : RingSiteModules A) (b : B) (x : M.val.obj (op ⟨PUnit.unit⟩)) :
    letI := φ.toAlgebra
    pointExtensionEquiv φ F hF M (b ⊗ₜ[A] x) =
      ringExtensionPure φ F hF M (op ⟨PUnit.unit⟩) b x := by
  rfl

private theorem pointLift_isIso_iff {A : Type u} [CommRing A]
    (M N : RingSiteModules A)
    (f : M.val.obj (op ⟨PUnit.unit⟩) →ₗ[A] N.val.obj (op ⟨PUnit.unit⟩)) :
    IsIso (pointLift M N f) ↔ Function.Bijective f := by
  constructor
  · intro h
    have := h
    exact ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation _ (op ⟨PUnit.unit⟩)).map (pointLift M N f))
  · intro h
    let e := LinearEquiv.ofBijective f h
    refine ⟨⟨pointLift N M e.symm.toLinearMap, ?_, ?_⟩⟩
    · apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      have hU := point_eq U
      subst U
      ext x
      exact e.symm_apply_apply x
    · apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      have hU := point_eq U
      subst U
      ext x
      exact e.apply_symm_apply x

-- The unchanged signature names a nondependent forall hypothesis `hk`.
set_option linter.unusedVariables false in
/-- Transport a normalized ordinary module comparison to the one-point site.
No finite-generation, projectivity, flatness, or invertibility assumption is made.
Invertibility of the transported map is equivalent to bijectivity of the module map.

Source: Stacks Project, more-algebra.tex, equation-base-change-RHom and Lemma 0A6A;
one-point-site realization in step 1 of the parent finite-projective comparison.
(blueprint: lem-pc-ring-hom-extension-transport).

Proof: write * for the unique object of Discrete PUnit. Evaluation at * is an
equivalence between module presheaves for the constant ring A and ordinary A-modules.
Its inverse is the constant module presheaf. More explicitly, the unique arrow
U -> * induces M(*) -> M(U), with inverse induced by * -> U; the presheaf laws
prove the inverse equations. All presheaves are sheaves for the bottom topology.
The internal Hom at * consists of module maps on the slice over *: evaluating
at the identity slice object identifies it with Hom_A(M(*),N(*)). Conversely a
linear map extends to every slice object by conjugating with the two restriction
isomorphisms just described. Naturality follows from the presheaf composition law,
and the two constructions are inverse by naturality at the arrow to the identity.
For scalar extension, its presheaf value at * is B tensor_A M(*). The sheafification
unit is invertible because this presheaf is already a sheaf; its module linearity
makes it a B-linear isomorphism. Transport further along hF(M) to get a B-linear
isomorphism from B tensor_A M(*) to F(M)(*), sending b tensor x to ringExtensionPure.
Apply these identifications to the source F(Hom_A(M,N)) and target
Hom_B(F(M),F(N)), and conjugate k by them. Evaluation's full faithfulness extends
this B-linear map uniquely to a sheaf morphism g. Evaluation reflects isomorphisms;
conjugating by linear equivalences shows that g is invertible exactly when k is
bijective. At *, the asserted formula follows by the two unit identifications,
the identity-slice Hom identification, and hk. At any U, use the unique isomorphism
U -> *: restrictions commute with the sheafification unit, tensor pure sections,
and the internal-Hom evaluation. Thus restriction of the formula at * is the
formula at U, with exactly the given ringExtensionPure expressions. This argument
also applies to zero rings and zero modules and uses no property of k besides
linearity and hk. -/
theorem ringHomExtension_transport
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (M N : RingSiteModules A) :
    letI := φ.toAlgebra
    ∀ (k : B ⊗[A] ((M.val.obj (op ⟨PUnit.unit⟩)) →ₗ[A]
          (N.val.obj (op ⟨PUnit.unit⟩))) →ₗ[B]
        ((B ⊗[A] (M.val.obj (op ⟨PUnit.unit⟩))) →ₗ[B]
          (B ⊗[A] (N.val.obj (op ⟨PUnit.unit⟩)))))
      (hk : ∀ (b c : B)
        (f : M.val.obj (op ⟨PUnit.unit⟩) →ₗ[A] N.val.obj (op ⟨PUnit.unit⟩))
        (x : M.val.obj (op ⟨PUnit.unit⟩)),
        k (b ⊗ₜ[A] f) (c ⊗ₜ[A] x) = (b * c) ⊗ₜ[A] f x),
    ∃ g : F.obj (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N) ⟶
        SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf B) (F.obj M) (F.obj N),
      (IsIso g ↔ Function.Bijective k) ∧ ∀ (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
        (f : (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N).val.obj U)
        (x : M.val.obj U),
        ((g.val.app U (ringExtensionPure φ F hF _ U b f)).app
          (op (Over.mk (𝟙 U.unop)))) (ringExtensionPure φ F hF M U c x) =
        ringExtensionPure φ F hF N U (b * c) ((f.app (op (Over.mk (𝟙 U.unop)))) x) := by
  let := φ.toAlgebra
  intro k hk
  let H := SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N
  let HB := SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf B)
    (F.obj M) (F.obj N)
  let eM := pointExtensionEquiv φ F hF M
  let eN := pointExtensionEquiv φ F hF N
  let eH := pointExtensionEquiv φ F hF H
  let eA := pointHomEquiv M N
  let eB := pointHomEquiv (F.obj M) (F.obj N)
  let eS := eH.symm.trans
    (AlgebraTensorModule.congr (LinearEquiv.refl B B) eA)
  let eT := (LinearEquiv.arrowCongr eM eN).trans eB.symm
  let l := eT.toLinearMap.comp (k.comp eS.toLinearMap)
  refine ⟨pointLift (F.obj H) HB l, ?_, ?_⟩
  · rw [pointLift_isIso_iff]
    change Function.Bijective (eT ∘ k ∘ eS) ↔ Function.Bijective k
    exact (Function.Bijective.of_comp_iff' eT.bijective (k ∘ eS)).trans
      (Function.Bijective.of_comp_iff k eS.bijective)
  · intro U b c f x
    have hU := point_eq U
    subst U
    change (eB (l (ringExtensionPure φ F hF H _ b f)))
      (ringExtensionPure φ F hF M _ c x) = _
    rw [← pointExtensionEquiv_tmul φ F hF H,
      ← pointExtensionEquiv_tmul φ F hF M,
      ← pointExtensionEquiv_tmul φ F hF N]
    change eN (k ((AlgebraTensorModule.congr (LinearEquiv.refl B B) eA)
      (eH.symm (eH (b ⊗ₜ[A] f)))) (eM.symm (eM (c ⊗ₜ[A] x)))) = _
    rw [eH.symm_apply_apply, eM.symm_apply_apply, AlgebraTensorModule.congr_tmul]
    exact congrArg eN (hk b c (eA f) x)

end CategoryTheory
