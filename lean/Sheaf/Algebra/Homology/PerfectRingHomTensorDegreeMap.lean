/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2, SHEAF group T3
-/
module

public import Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeCondition
import Sheaf.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal

/-! # Existence of the signed degreewise evaluation map

Source: Stacks Project, More on Algebra, Tags 0A6A and 0ATK.
(blueprint: lem-pc-perfect-ring-hom-tensor-degree-map)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory

private abbrev point : (Discrete PUnit.{u + 1})ᵒᵖ := op ⟨PUnit.unit⟩

private noncomputable def pointPreimage {A : Type u} [CommRing A]
    {M N : RingSiteModules A} (f : M.val.obj point ⟶ N.val.obj point) :
    M.val ⟶ N.val where
  app X := by
    obtain rfl : X = point := Subsingleton.elim _ _
    exact f
  naturality {X Y} g := by
    obtain rfl : X = point := Subsingleton.elim _ _
    obtain rfl : Y = point := Subsingleton.elim _ _
    obtain rfl : g = 𝟙 point := Subsingleton.elim _ _
    ext x
    simp only [PresheafOfModules.map_id]
    rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def homPointLift {A : Type u} [CommRing A]
    (M N : RingSiteModules A) :
    (M.val.obj point →ₗ[A] N.val.obj point) →ₗ[A]
      (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N).val.obj
        point where
  toFun f := (PresheafOfModules.restrictOver (CochainComplex.onePointRingSheaf A).obj
    point.unop).map (pointPreimage (ModuleCat.ofHom f))
  map_add' f g := by
    apply PresheafOfModules.hom_ext
    intro W
    rcases W with ⟨⟨⟨⟩⟩, ⟨⟩, f⟩
    obtain rfl : f = 𝟙 point.unop := Subsingleton.elim _ _
    rfl
  map_smul' a f := by
    apply PresheafOfModules.hom_ext
    intro W
    rcases W with ⟨⟨⟨⟩⟩, ⟨⟩, f⟩
    obtain rfl : f = 𝟙 point.unop := Subsingleton.elim _ _
    rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def dualPointPair {A : Type u} [CommRing A]
    (P : CochainComplex (RingSiteModules A) ℤ) (r : ℤ) :
    ((perfectRingDual P).X r).val.obj point →ₗ[A]
      (P.X (-r)).val.obj point →ₗ[A] A := by
  let O := SheafOfModules.unit ((sheafCompose ⊥
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (CochainComplex.onePointRingSheaf A))
  let S := (CochainComplex.singleFunctor (RingSiteModules A) 0).obj O
  let π := ringHomComplexProjection P S r (-r)
  let e := (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 O (-r + r)
    (by omega)).hom.val.app point
  let el : (S.X (-r + r)).val.obj point →ₗ[A] A := e.hom
  let ev : (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A)
      (P.X (-r)) (S.X (-r + r))).val.obj point →ₗ[A]
      (P.X (-r)).val.obj point →ₗ[A] (S.X (-r + r)).val.obj point :=
    PresheafOfModules.homObjEvalId (P.X (-r)).val (S.X (-r + r)).val point.unop
  let pl : ((perfectRingDual P).X r).val.obj point →ₗ[A]
      (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A)
        (P.X (-r)) (S.X (-r + r))).val.obj point := (π.val.app point).hom
  exact (LinearMap.llcomp A _ _ _ el).comp (ev.comp pl)

private lemma dualPointPair_eval {A : Type u} [CommRing A]
    (P : CochainComplex (RingSiteModules A) ℤ) (r : ℤ)
    (lam : ((perfectRingDual P).X r).val.obj point) (x : (P.X (-r)).val.obj point) :
    dualPointPair P r lam x = perfectRingDualEvaluate P r point lam x := rfl

set_option backward.isDefEq.respectTransparency false in
private lemma point_bilinear_natural {A : Type u} [CommRing A]
    (M N H : RingSiteModules A)
    (β : ∀ U : (Discrete PUnit.{u + 1})ᵒᵖ,
      M.val.obj U →ₗ[A] N.val.obj U →ₗ[A] H.val.obj U)
    {U V : (Discrete PUnit.{u + 1})ᵒᵖ} (f : U ⟶ V)
    (x : M.val.obj U) (y : N.val.obj U) :
    β V (M.val.map f x) (N.val.map f y) = H.val.map f (β U x y) := by
  obtain rfl : U = point := Subsingleton.elim _ _
  obtain rfl : V = point := Subsingleton.elim _ _
  obtain rfl : f = 𝟙 point := Subsingleton.elim _ _
  simp only [PresheafOfModules.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem summand_pair_exists {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (r s : ℤ) :
    let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    ∃ e : (perfectRingDual P).X r ⊗ Q.X s ⟶
        SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A)
          (P.X (-r)) (Q.X s),
      ∀ (U : (Discrete PUnit.{u + 1})ᵒᵖ)
        (lam : ((perfectRingDual P).X r).val.obj U) (y : (Q.X s).val.obj U)
        (x : (P.X (-r)).val.obj U),
        ((e.val.app U ((perfectRingTensorSectionMap ((perfectRingDual P).X r)
          (Q.X s)).app U (lam ⊗ₜ[A] y))).app (op (Over.mk (𝟙 U.unop)))) x =
          (r * s).negOnePow • (perfectRingDualEvaluate P r U lam x • y) := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  let M := (perfectRingDual P).X r
  let N := Q.X s
  let H := SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) (P.X (-r)) N
  let β₀ : M.val.obj point →ₗ[A] N.val.obj point →ₗ[A] H.val.obj point :=
    ((LinearMap.llcomp A _ _ _ (homPointLift (P.X (-r)) N)).comp
      (LinearMap.smulRightₗ.comp ((r * s).negOnePow • dualPointPair P r)))
  let β : ∀ U : (Discrete PUnit.{u + 1})ᵒᵖ,
      M.val.obj U →ₗ[A] N.val.obj U →ₗ[A] H.val.obj U := fun U ↦ by
    obtain rfl : U = point := Subsingleton.elim _ _
    exact β₀
  obtain ⟨e, he, _⟩ := SheafOfModules.tensor_bilinear_universal
    (CochainComplex.onePointRingSheaf A) M N H β (point_bilinear_natural M N H β)
  refine ⟨e, ?_⟩
  intro U lam y x
  change (e.val.app U ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
      (M.val ⊗ N.val)).app U (lam ⊗ₜ[A] y)))).app (op (Over.mk (𝟙 U.unop))) x = _
  erw [he]
  obtain rfl : U = point := Subsingleton.elim _ _
  change (β₀ lam y).app (op (Over.mk (𝟙 point.unop))) x = _
  change (((r * s).negOnePow • dualPointPair P r) lam) x • y = _
  simp only [Units.smul_def]
  erw [LinearMap.smul_apply]
  rw [dualPointPair_eval]
  exact smul_assoc _ _ _


private lemma hom_transport_eval {A : Type u} [CommRing A]
    (M : RingSiteModules A) (N : ℤ → RingSiteModules A) (i j : ℤ) (h : i = j)
    (U : (Discrete PUnit.{u + 1})ᵒᵖ)
    (z : (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M (N i)).val.obj U)
    (x : M.val.obj U) :
    (((eqToHom (congrArg (fun q ↦ SheafOfModules.homObj
        (R := CochainComplex.onePointRingSheaf A) M (N q)) h)).val.app U z).app
          (op (Over.mk (𝟙 U.unop)))) x =
      (eqToHom (congrArg N h)).val.app U (z.app (op (Over.mk (𝟙 U.unop))) x) := by
  subst j
  rfl


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
  set_option backward.isDefEq.respectTransparency true in
   classical
   let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
   choose e he using summand_pair_exists P Q
   let T (p : ℤ) := SheafOfModules.homObj
     (R := CochainComplex.onePointRingSheaf A) (P.X p) (Q.X (p + n))
   let Z := (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n
   let π : ∀ p, Z ⟶ T p := ringHomComplexProjection P Q n
   let hπ : IsLimit (Fan.mk Z π) :=
     (homComplex_isLimit P Q n).some
   let c (r s : ℤ) (h : r + s = n) (p : ℤ) :
       (perfectRingDual P).X r ⊗ Q.X s ⟶ T p :=
     if hp : p = -r then
       e r s ≫ eqToHom (congrArg (fun q ↦ SheafOfModules.homObj
         (R := CochainComplex.onePointRingSheaf A) (P.X (-r)) (Q.X q))
         (show s = -r + n by omega)) ≫ eqToHom (congrArg T hp.symm)
     else 0
   let k (r s : ℤ) (h : r + s = n) : (perfectRingDual P).X r ⊗ Q.X s ⟶ Z :=
     Fan.IsLimit.lift hπ (c r s h)
   have hk (r s : ℤ) (h : r + s = n) (p : ℤ) :
       k r s h ≫ π p = c r s h p := Fan.IsLimit.fac hπ _ p
   let f : (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X n ⟶ Z :=
     HomologicalComplex.mapBifunctorDesc (fun r s h ↦ k r s h)
   have hf (r s : ℤ) (h : r + s = n) (p : ℤ) :
       CochainComplex.ιMapBifunctor (perfectRingDual P) Q (curriedTensor _)
         r s n h ≫ f ≫ π p = c r s h p := by
     rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
     exact hk r s h p
   refine ⟨f, ?_, ?_⟩
   · intro r s h p hp
     exact (hf r s h p).trans (dif_neg hp)
   · set_option backward.isDefEq.respectTransparency false in
      intro r s h U lam y x
      change (((CochainComplex.ιMapBifunctor (perfectRingDual P) Q (curriedTensor _)
        r s n h ≫ f ≫ π (-r)).val.app U
          ((perfectRingTensorSectionMap ((perfectRingDual P).X r) (Q.X s)).app U
            (lam ⊗ₜ[A] y))).app (op (Over.mk (𝟙 U.unop)))) x = _
      rw [hf]
      simp only [c, dif_pos rfl, eqToHom_refl, Category.comp_id]
      change (((eqToHom (congrArg (fun q ↦ SheafOfModules.homObj
          (R := CochainComplex.onePointRingSheaf A) (P.X (-r)) (Q.X q))
            (show s = -r + n by omega))).val.app U
          ((e r s).val.app U
            ((perfectRingTensorSectionMap ((perfectRingDual P).X r) (Q.X s)).app U
              (lam ⊗ₜ[A] y)))).app (op (Over.mk (𝟙 U.unop)))) x = _
      rw [hom_transport_eval, he]
      all_goals omega


end CategoryTheory
