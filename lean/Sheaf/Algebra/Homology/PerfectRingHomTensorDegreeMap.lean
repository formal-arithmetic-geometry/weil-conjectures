/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2, SHEAF group H3
-/
module

public import Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeCondition
import Mathlib.LinearAlgebra.Contraction
import all Sheaf.Algebra.Homology.PerfectRingDualTermFlat
import all Sheaf.Algebra.Homology.RingHomExtensionDegrees

/-! # Existence of the signed degreewise evaluation map

Source: Stacks Project, More on Algebra, Tags 0A6A and 0ATK.
(blueprint: lem-pc-perfect-ring-hom-tensor-degree-map)
-/

@[expose] public section

-- Avoid competing conversion checks on the chosen constructions.
set_option Elab.async false

universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory TensorProduct
namespace CategoryTheory

-- Conversion needs their interfaces, not the large chosen construction terms.
attribute [local irreducible] homComplexFunctor SheafOfModules.monoidalCategory

private abbrev point : (Discrete PUnit.{u + 1})ᵒᵖ := op ⟨PUnit.unit⟩

set_option backward.isDefEq.respectTransparency false in
private noncomputable def tensorPointEquiv {A : Type u} [CommRing A]
    (M N : RingSiteModules A) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    M.val.obj point ⊗[A] N.val.obj point ≃ₗ[A] (M ⊗ N).val.obj point := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  let T := M.val ⊗ N.val
  let η := toSheafify ⊥ T.presheaf
  have : IsIso η := isIso_toSheafify ⊥ (Presheaf.isSheaf_bot _)
  let α := (SheafOfModules.tensorObjIsoSheafification
    (R := CochainComplex.onePointRingSheaf A) M N).inv.val.app point
  have : IsIso α := by
    change IsIso ((SheafOfModules.evaluation _ _).map
      (SheafOfModules.tensorObjIsoSheafification
        (R := CochainComplex.onePointRingSheaf A) M N).inv)
    infer_instance
  let e : M.val.obj point ⊗[A] N.val.obj point ≃ₗ[A]
      ((PresheafOfModules.sheafification (𝟙 _)).obj T).val.obj point :=
    LinearEquiv.ofBijective
      (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app T).app point).hom
      (ConcreteCategory.bijective_of_isIso (η.app point))
  exact e.trans (LinearEquiv.ofBijective α.hom (ConcreteCategory.bijective_of_isIso α))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def dualEvaluateLinear {A : Type u} [CommRing A]
    (P : CochainComplex (RingSiteModules A) ℤ) (r : ℤ) :
    ((perfectRingDual P).X r).val.obj point →ₗ[A]
      Module.Dual A ((P.X (-r)).val.obj point) := by
  let O := SheafOfModules.unit ((sheafCompose ⊥
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (CochainComplex.onePointRingSheaf A))
  let S := (CochainComplex.singleFunctor (RingSiteModules A) 0).obj O
  let π := (ringHomComplexProjection P S r (-r)).val.app point
  let t : (S.X (-r + r)).val.obj point →ₗ[A] A :=
    ((HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 O (-r + r)
      (by omega)).hom.val.app point).hom
  exact (LinearMap.compRight A t).comp
    ((pointHomEquiv (P.X (-r)) (S.X (-r + r))).toLinearMap.comp π.hom)

set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_block {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (r s n : ℤ) (h : r + s = n) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    ∃ g : (perfectRingDual P).X r ⊗ Q.X s ⟶
        SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A)
          (P.X (-r)) (Q.X (-r + n)),
      ∀ (U : (Discrete PUnit.{u + 1})ᵒᵖ)
        (lam : ((perfectRingDual P).X r).val.obj U) (y : (Q.X s).val.obj U)
        (x : (P.X (-r)).val.obj U),
        ((g.val.app U ((perfectRingTensorSectionMap
          ((perfectRingDual P).X r) (Q.X s)).app U (lam ⊗ₜ[A] y))).app
            (op (Over.mk (𝟙 U.unop)))) x =
        (eqToHom (congrArg Q.X (show s = -r + n by omega))).val.app U
          ((r * s).negOnePow • (perfectRingDualEvaluate P r U lam x • y)) := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  let M := ((perfectRingDual P).X r).val.obj point
  let X := (P.X (-r)).val.obj point
  let Y := (Q.X s).val.obj point
  let e := tensorPointEquiv ((perfectRingDual P).X r) (Q.X s)
  let t : (Q.X s).val.obj point →ₗ[A] (Q.X (-r + n)).val.obj point :=
    ((eqToHom (congrArg Q.X (show s = -r + n by omega))).val.app point).hom
  let k : M ⊗[A] Y →ₗ[A] X →ₗ[A] Y :=
    (dualTensorHom A X Y).comp
      (TensorProduct.map (dualEvaluateLinear P r) (LinearMap.id))
  let l := (pointHomEquiv (P.X (-r)) (Q.X (-r + n))).symm.toLinearMap.comp
    ((LinearMap.compRight A t).comp (((r * s).negOnePow • k).comp e.symm.toLinearMap))
  refine ⟨pointLift _ _ l, ?_⟩
  intro U lam y x
  rcases U with ⟨⟨⟨⟩⟩⟩
  change ((pointHomEquiv (P.X (-r)) (Q.X (-r + n))) (l (e (lam ⊗ₜ[A] y)))) x = _
  simp only [l, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply]
  change t (((r * s).negOnePow • k) (e.symm (e (lam ⊗ₜ[A] y))) x) = _
  rw [e.symm_apply_apply]
  change t ((r * s).negOnePow • (k (lam ⊗ₜ[A] y) x)) = _
  rw [show k (lam ⊗ₜ[A] y) x = perfectRingDualEvaluate P r point lam x • y from rfl]

set_option backward.isDefEq.respectTransparency true in
/-- Signed evaluation defines a map in each degree, without finiteness assumptions.
Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1).
(blueprint: lem-pc-perfect-ring-hom-tensor-degree-map)

Proof: use the product projections of Hom(P,A[0]) to evaluate its degree-r sections
on P^(-r), followed by the degree-zero single-complex identification with A.
Multiplication on Q^s gives an A-bilinear pairing, hence a map from the sectionwise
tensor. This pairing is natural under restriction. By the sheafification adjunction
it descends to the sheaf tensor. For r+s=n, put this signed map in Hom coordinate
p=-r, transporting Q^s to Q^(p+n), and put zero in every other coordinate.
The product universal property gives a map from this tensor summand to Hom degree n.
The coproduct universal property defining the total tensor degree assembles all
summands. Its composites with projections vanish off the diagonal by construction;
on the diagonal its value on pure tensors is precisely the defining signed pairing.
The argument uses no bound, finite generation, or projectivity. Zero modules and the
zero ring are included because the bilinear pairing and both universal properties
still apply. -/
theorem perfectRingHom_tensorDual_degree_map_exists {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    ∃ f : (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X n ⟶
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n,
      PerfectRingHomTensorDegreeCondition P Q n f := by
  classical
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  let H (p : ℤ) := SheafOfModules.homObj
    (R := CochainComplex.onePointRingSheaf A) (P.X p) (Q.X (p + n))
  let hH := (ringHomComplex_isLimit P Q n).some
  choose g hg using fun (r s : ℤ) (h : r + s = n) ↦ evaluation_block P Q r s n h
  let b (r s : ℤ) (h : r + s = n) (p : ℤ) :
      (perfectRingDual P).X r ⊗ Q.X s ⟶ H p :=
    if hp : p = -r then g r s h ≫ eqToHom (congrArg H hp.symm) else 0
  let f : (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X n ⟶
      (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n :=
    HomologicalComplex.mapBifunctorDesc
      (K₁ := perfectRingDual P) (K₂ := Q) (F := curriedTensor _) (c := .up ℤ)
      (fun r s h ↦ Fan.IsLimit.lift hH (b r s h))
  have hf (r s : ℤ) (h : r + s = n) (p : ℤ) :
      CochainComplex.ιMapBifunctor (perfectRingDual P) Q (curriedTensor _)
        r s n h ≫ f ≫ ringHomComplexProjection P Q n p = b r s h p := by
    rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
    exact Fan.IsLimit.fac hH _ p
  refine ⟨f, ?_, ?_⟩
  · intro r s h p hp
    rw [hf]
    exact dif_neg hp
  · intro r s h U lam y x
    rcases U with ⟨⟨⟨⟩⟩⟩
    set_option backward.isDefEq.respectTransparency false in
      change (((CochainComplex.ιMapBifunctor (perfectRingDual P) Q (curriedTensor _)
        r s n h ≫ f ≫ ringHomComplexProjection P Q n (-r)).val.app point
          ((perfectRingTensorSectionMap ((perfectRingDual P).X r) (Q.X s)).app point
            (lam ⊗ₜ[A] y))).app (op (Over.mk (𝟙 point.unop)))) x = _
    rw [hf]
    simpa only [b, dif_pos rfl, eqToHom_refl, Category.comp_id] using hg r s h point lam y x

end CategoryTheory
