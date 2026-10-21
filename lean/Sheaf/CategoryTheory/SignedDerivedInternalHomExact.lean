/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import all Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses

/-! # The normalized exact structure on contravariant derived internal Hom

Source: Stacks Project, sites-cohomology.tex, Tags 0A8X and 08JC.
(blueprint: lem-coef-signed-derived-internal-hom-exact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedHomUniverses CategoryTheory.Pretriangulated.Opposite
attribute [local irreducible] CategoryTheory.homComplexFunctor

/- The checked ordinary stage uses the naive opposite shift on its source and the negative
pullback shift on its target. Thus its parameter m is the original complex shift. The correction
is m(m-1)/2; after setting m=-n for the triangulated opposite this becomes n(n+1)/2. The derived
localization and distinguished-triangle arguments are still the named theorem below. -/
namespace CategoryTheory.RingedHomUniverses
private def negInt : ℤ →+ ℤ := AddMonoidHom.mk' (fun n : ℤ ↦ -n) (by intros; lia)
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{max c v r})
private def ordinaryDual (I : Complex.{c, v, r} J R) :
    OppositeShift (Complex.{c, v, r} J R) ℤ ⥤
      PullbackShift (Complex.{c, v, r} J R) negInt :=
  Prod.sectL _ I ⋙ ordinaryBifunctor.{c, v, r} J R
private def rawSourceIso (I : Complex.{c, v, r} J R) (n : ℤ) :
    shiftFunctor _ n ⋙ ordinaryDual.{c, v, r} J R I ≅
      ordinaryDual.{c, v, r} J R I ⋙ shiftFunctor _ n := by
  let e := (ordinaryLeftShift.{c, v, r} J R n).choose
  refine NatIso.ofComponents (fun X ↦ e.symm.app (X, I)) ?_
  intro X Y f
  change (ordinaryBifunctor.{c, v, r} J R).map
      (Prod.mkHom (((shiftFunctor (Complex.{c, v, r} J R) n).map f.unop).op) (𝟙 I)) ≫
        e.inv.app (Y, I) = e.inv.app (X, I) ≫
          (shiftFunctor (Complex.{c, v, r} J R) (-n)).map
            ((ordinaryBifunctor.{c, v, r} J R).map (Prod.mkHom f (𝟙 I)))
  simpa only [ordinaryDual, negInt, Functor.comp_map, Functor.comp_obj, Functor.op_map,
    Functor.prod_map, Functor.prod_obj, Functor.id_map, Functor.id_obj,
    Prod.sectL_map, Prod.sectL_obj, Iso.app_hom, Iso.symm_hom] using
      e.inv.naturality (Prod.mkHom f (𝟙 I))
private theorem rawSourceIso_formula (I E : Complex.{c, v, r} J R) (n k p q : ℤ)
    (h : p + k = q) :
    (((rawSourceIso.{c, v, r} J R I n).inv.app (op E)).f k) ≫
        homComplexπ.{c, v, max c v r, max c v r} (R := R) (E⟦n⟧) I k p q h =
      (n * k).negOnePow •
        homComplexπ.{c, v, max c v r, max c v r} (R := R) E I (k + -n)
          (p + n) q (by omega) := by
  change (((ordinaryLeftShift.{c, v, r} J R n).choose.hom.app (op E, I)).f k) ≫
      homComplexπ.{c, v, max c v r, max c v r} (R := R) (E⟦n⟧) I k p q h = _
  simpa only [Iso.app_hom] using
    (ordinaryLeftShift.{c, v, r} J R n).choose_spec E I k p q h
private def correctedSourceIso (I : Complex.{c, v, r} J R) (n : ℤ) :
    shiftFunctor _ n ⋙ ordinaryDual.{c, v, r} J R I ≅
      ordinaryDual.{c, v, r} J R I ⋙ shiftFunctor _ n :=
  (n * (n - 1) / 2).negOnePow • rawSourceIso.{c, v, r} J R I n
private theorem units_smul_f (E F : Complex.{c, v, r} J R)
    (u : ℤˣ) (f : E ⟶ F) (k : ℤ) : (u • f).f k = u • f.f k := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp only [one_smul]
  · simp only [Units.neg_smul, one_smul, HomologicalComplex.neg_f_apply]
private theorem correctedSourceIso_formula (I E : Complex.{c, v, r} J R)
    (n k p q : ℤ) (h : p + k = q) :
    (((correctedSourceIso.{c, v, r} J R I n).inv.app (op E)).f k) ≫
        homComplexπ.{c, v, max c v r, max c v r} (R := R) (E⟦n⟧) I k p q h =
      (n * (n - 1) / 2 + n * k).negOnePow •
        homComplexπ.{c, v, max c v r, max c v r} (R := R) E I (k + -n)
          (p + n) q (by omega) := by
  simp only [correctedSourceIso, Preadditive.smul_iso_inv,
    Int.units_inv_eq_self, NatTrans.app_units_zsmul]
  change (((n * (n - 1) / 2).negOnePow •
      ((rawSourceIso.{c, v, r} J R I n).inv.app (op E) :
        (complexHom.{c, v, r} J R E I)⟦-n⟧ ⟶ complexHom.{c, v, r} J R (E⟦n⟧) I)).f k) ≫
          homComplexπ.{c, v, max c v r, max c v r} (R := R) (E⟦n⟧) I k p q h = _
  erw [units_smul_f.{c, v, r} J R, Linear.units_smul_comp, rawSourceIso_formula]
  rw [smul_smul, ← Int.negOnePow_add]
private theorem ordinaryDual_map_formula (I E F : Complex.{c, v, r} J R)
    (f : F ⟶ E) (k p q : ℤ) (h : p + k = q) :
    ((ordinaryDual.{c, v, r} J R I).map f.op).f k ≫
      homComplexπ.{c, v, max c v r, max c v r} (R := R) F I k p q h =
        homComplexπ.{c, v, max c v r, max c v r} (R := R) E I k p q h ≫
          SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R)
            (f.f p) (𝟙 _) := by
  have hh := homComplexFunctor_map_f_π.{c, v, max c v r, max c v r} f (𝟙 I) k p q h
  simpa only [ordinaryDual, Functor.comp_map, Prod.sectL_map,
    Functor.uncurry_obj_map, Prod.sectL_obj, Functor.map_id, NatTrans.id_app, Category.comp_id,
    HomologicalComplex.id_f] using hh
private theorem negativeShift_zero_hom (E : Complex.{c, v, r} J R) :
    (shiftFunctorZero (PullbackShift (Complex.{c, v, r} J R) negInt) ℤ).hom.app E =
      (shiftFunctorZero (Complex.{c, v, r} J R) ℤ).hom.app E := by
  rw [pullbackShiftFunctorZero_hom_app]
  simp only [pullbackShiftIso, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
private theorem sourceProjection_eq (I E : Complex.{c, v, r} J R)
    (k k' p p' q : ℤ) (hk : k = k') (hp : p = p')
    (h : p + k = q) (h' : p' + k' = q) :
    ((complexHom.{c, v, r} J R E I).XIsoOfEq hk).hom ≫
        homComplexπ.{c, v, max c v r, max c v r} (R := R) E I k' p' q h' ≫
          SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R)
            (E.XIsoOfEq hp).hom (𝟙 _) =
      homComplexπ.{c, v, max c v r, max c v r} (R := R) E I k p q h := by
  subst k' p'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    SheafOfModules.homObjMap_id, Category.id_comp, Category.comp_id]
private theorem correctedSourceIso_zero (I : Complex.{c, v, r} J R) :
    correctedSourceIso.{c, v, r} J R I 0 =
      Functor.CommShift.isoZero (ordinaryDual.{c, v, r} J R I) ℤ := by
  apply Iso.ext_inv
  apply NatTrans.ext
  funext E
  apply HomologicalComplex.hom_ext
  intro k
  apply Fan.IsLimit.hom_ext
    (homComplexIsLimit.{c, v, max c v r, max c v r} (E.unop⟦(0 : ℤ)⟧) I k)
  intro p
  rw [Functor.CommShift.isoZero_inv_app]
  dsimp only [Fan.mk_π_app, Fan.proj, HomologicalComplex.comp_f]
  change ((correctedSourceIso.{c, v, r} J R I 0).inv.app E).f k ≫
      homComplexπ.{c, v, max c v r, max c v r} (R := R) (E.unop⟦(0 : ℤ)⟧) I
        k p (p + k) rfl = _
  erw [correctedSourceIso_formula.{c, v, r} J R I E.unop 0 k p (p + k) rfl]
  rw [negativeShift_zero_hom, oppositeShiftFunctorZero_inv_app]
  change _ = (((shiftFunctorZero (Complex.{c, v, r} J R) ℤ).hom.app
      (complexHom.{c, v, r} J R E.unop I)).f k) ≫
        (((ordinaryDual.{c, v, r} J R I).map
          (((shiftFunctorZero (Complex.{c, v, r} J R) ℤ).hom.app E.unop).op)).f k) ≫
            homComplexπ.{c, v, max c v r, max c v r} (R := R)
              (E.unop⟦(0 : ℤ)⟧) I k p (p + k) rfl
  erw [ordinaryDual_map_formula.{c, v, r} J R]
  simp only [CochainComplex.shiftFunctorZero_hom_app_f,
    zero_mul, Int.zero_ediv, zero_add, Int.negOnePow_zero, one_smul, Functor.id_obj]
  exact (sourceProjection_eq.{c, v, r} J R I E.unop (k + -0) k (p + 0) p (p + k)
    (by omega) (by omega) (by omega) rfl).symm
private theorem negativeShift_add_hom (E : Complex.{c, v, r} J R) (a b : ℤ) :
    (shiftFunctorAdd (PullbackShift (Complex.{c, v, r} J R) negInt) a b).hom.app E =
      (shiftFunctorAdd' (Complex.{c, v, r} J R) (-a) (-b) (-(a + b))
        (by omega)).hom.app E := by
  rw [← shiftFunctorAdd'_eq_shiftFunctorAdd]
  rw [pullbackShiftFunctorAdd'_hom_app negInt E a b (a + b) rfl
    (-a) (-b) (-(a + b)) rfl rfl rfl]
  simp only [pullbackShiftIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp]
  erw [Functor.map_id, Category.comp_id]
private theorem correction_add (a b : ℤ) :
    (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + b * (b - 1) / 2 + a * b := by
  have he (n : ℤ) : 2 ∣ n * (n - 1) := by
    have h := Int.two_dvd_mul_add_one (n - 1)
    convert h using 1
    ring
  have ha := Int.ediv_mul_cancel (he a)
  have hb := Int.ediv_mul_cancel (he b)
  have hab := Int.ediv_mul_cancel (he (a + b))
  have h : (a + b) * (a + b - 1) = a * (a - 1) + b * (b - 1) + 2 * (a * b) := by ring
  omega
private theorem correctionSign_add (a b k : ℤ) :
    ((a + b) * (a + b - 1) / 2 + (a + b) * k).negOnePow =
      (b * (b - 1) / 2 + b * k).negOnePow *
        (a * (a - 1) / 2 + a * (k + -b)).negOnePow := by
  rw [← Int.negOnePow_add, Int.negOnePow_eq_iff, correction_add]
  refine ⟨a * b, ?_⟩
  ring
private theorem correctedSourceIso_add (I : Complex.{c, v, r} J R) (a b : ℤ) :
    correctedSourceIso.{c, v, r} J R I (a + b) =
      Functor.CommShift.isoAdd (correctedSourceIso.{c, v, r} J R I a)
        (correctedSourceIso.{c, v, r} J R I b) := by
  apply Iso.ext_inv
  apply NatTrans.ext
  funext E
  apply HomologicalComplex.hom_ext
  intro k
  apply Fan.IsLimit.hom_ext
    (homComplexIsLimit.{c, v, max c v r, max c v r} (E.unop⟦a + b⟧) I k)
  intro p
  rw [Functor.CommShift.isoAdd_inv_app]
  dsimp only [Fan.mk_π_app, Fan.proj, HomologicalComplex.comp_f]
  change ((correctedSourceIso.{c, v, r} J R I (a + b)).inv.app E).f k ≫
      homComplexπ.{c, v, max c v r, max c v r} (R := R) (E.unop⟦a + b⟧) I
        k p (p + k) rfl = _
  erw [correctedSourceIso_formula.{c, v, r} J R I E.unop (a + b) k p (p + k) rfl]
  rw [negativeShift_add_hom, oppositeShiftFunctorAdd_inv_app]
  change _ = (((shiftFunctorAdd' (Complex.{c, v, r} J R) (-a) (-b) (-(a + b))
      (by omega)).hom.app (complexHom.{c, v, r} J R E.unop I)).f k) ≫
        (((shiftFunctor (Complex.{c, v, r} J R) (-b)).map
          ((correctedSourceIso.{c, v, r} J R I a).inv.app E)).f k) ≫
          (((correctedSourceIso.{c, v, r} J R I b).inv.app (op (E.unop⟦a⟧))).f k) ≫
            (((ordinaryDual.{c, v, r} J R I).map
              (((shiftFunctorAdd (Complex.{c, v, r} J R) a b).hom.app E.unop).op)).f k) ≫
                homComplexπ.{c, v, max c v r, max c v r} (R := R) (E.unop⟦a + b⟧) I
                  k p (p + k) rfl
  have hm := ordinaryDual_map_formula.{c, v, r} J R I
    ((E.unop⟦a⟧)⟦b⟧) (E.unop⟦a + b⟧)
    ((shiftFunctorAdd (Complex.{c, v, r} J R) a b).hom.app E.unop) k p (p + k) rfl
  rw [hm]
  have hb := correctedSourceIso_formula.{c, v, r} J R I (E.unop⟦a⟧) b
    k p (p + k) rfl
  rw [reassoc_of% hb]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp]
  rw [CochainComplex.shiftFunctor_map_f']
  have ha := correctedSourceIso_formula.{c, v, r} J R I E.unop a
    (k + -b) (p + b) (p + k) (by omega)
  erw [reassoc_of% ha]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul]
  simp only [CochainComplex.shiftFunctorAdd'_hom_app_f',
    CochainComplex.shiftFunctorAdd_hom_app_f]
  rw [sourceProjection_eq.{c, v, r} J R I E.unop
    (k + -(a + b)) (k + -b + -a) (p + (a + b)) (p + b + a) (p + k)
    (by omega) (by omega) (by omega) (by omega)]
  rw [correctionSign_add]

@[instance_reducible]
private def ordinarySignedCommShift (I : Complex.{c, v, r} J R) :
    (ordinaryDual.{c, v, r} J R I).CommShift ℤ where
  commShiftIso := correctedSourceIso.{c, v, r} J R I
  commShiftIso_zero := correctedSourceIso_zero.{c, v, r} J R I
  commShiftIso_add := correctedSourceIso_add.{c, v, r} J R I
private theorem ordinarySignedCommShift_formula (I E : Complex.{c, v, r} J R)
    (n k p q : ℤ) (h : p + k = q) :
    (((ordinarySignedCommShift.{c, v, r} J R I).commShiftIso n).inv.app (op E)).f k ≫
        homComplexπ.{c, v, max c v r, max c v r} (R := R) (E⟦n⟧) I k p q h =
      (n * (n - 1) / 2 + n * k).negOnePow •
        homComplexπ.{c, v, max c v r, max c v r} (R := R) E I (k + -n)
          (p + n) q (by omega) :=
  correctedSourceIso_formula.{c, v, r} J R I E n k p q h
end CategoryTheory.RingedHomUniverses

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]

/-- Contravariant derived Hom is exact with the coherently normalized signed source shift.
Source: Stacks 08JC (lemma-RHom-triangulated) and 0A8X (Hom-complex differential).
(blueprint: lem-coef-signed-derived-internal-hom-exact).
Proof: Represent M by a K-injective I. The signed source comparison on Hom complexes
multiplies the reindexed degree-q family for E[m] by (-1)^(m*q). For the opposite-category
shift n this uses m=-n. Raw comparisons have the addition discrepancy (-1)^(n*m).
Multiply the degree-n comparison by (-1)^(n*(n+1)/2). The identity
q(n+m)=q(n)+q(m)+n*m cancels that discrepancy and gives zero and addition coherence for
all integers. At n=1 this correction is -1; at n=-1 it is 1. The fixed ordinary-to-derived
augmentation and its uniqueness therefore give exactly the two displayed normalizations.
For a cone of E -> G, ordinary Hom into I is the graded direct sum of Hom(G,I) and
Hom(E,I)[-1]. Its differential is (d*x,d*y+(-1)^(q+1)*f*(x)). The degree-q map
(x,y) -> (x,(-1)^(q+1)*y), in cone-summand order, identifies it with Cone(f*)[-1].
Rotation and the specified opposite triangle sign identify all three arrows. For the connecting
arrow, the minus in the degree-one comparison turns the reversed third arrow into cone inclusion.
Hom into I inverts quasi-isomorphisms, so localize these identities.
Every distinguished derived triangle is isomorphic to a localized cone triangle; transport
along this isomorphism proves exactness. No double dual or bidual evaluation map is used. -/
theorem signedDerivedInternalHom_exact (M : D.{c, v, r, w} J R) :
    let T := Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R
    ∃ S : T.CommShift ℤ,
      (fun [_shiftInst : T.CommShift ℤ] ↦ T.IsTriangulated ∧
        (∀ X : D.{c, v, r, w} J R,
          (T.commShiftIso (1 : ℤ)).hom.app (op X) =
            -(sourceShift.{c, v, r, w} J R X (-1)).inv.app M) ∧
        (∀ X : D.{c, v, r, w} J R,
          (T.commShiftIso (-1 : ℤ)).inv.app (op X) =
            (sourceShift.{c, v, r, w} J R X 1).hom.app M)) (_shiftInst := S) := by
  sorry

end CategoryTheory
