/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.Algebra.Homology.PerfectRingDualTermFlat

/-! # Degreewise signed evaluation interfaces

Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1).
(blueprint: lem-pc-perfect-ring-hom-tensor-degrees)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory

private lemma single_projection_evaluation {A : Type u} [CommRing A]
    (P : CochainComplex (RingSiteModules A) ℤ) (M Z : RingSiteModules A)
    (n p j : ℤ) (h : p + n = j)
    (π : ∀ (q : ℤ) (_h : p + n = q), Z ⟶
      SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) (P.X p)
        (((CochainComplex.singleFunctor (RingSiteModules A) j).obj M).X q))
    (U : (Discrete PUnit.{u + 1})ᵒᵖ) (lam : Z.val.obj U) (x : (P.X p).val.obj U) :
    (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) j M (p + n) h).hom.val.app U
      (((π (p + n) rfl).val.app U lam).app (op (Over.mk (𝟙 U.unop))) x) =
    (HomologicalComplex.singleObjXSelf (.up ℤ) j M).hom.val.app U
      (((π j h).val.app U lam).app (op (Over.mk (𝟙 U.unop))) x) := by
  subst j
  rfl

/-- Evaluate the degree `r` dual at a vector of degree `-r`, using the projection
of the shared Hom complex and the canonical degree-zero single-complex isomorphism.
Source: Stacks, Tag 0A6A (1), chain-level evaluation.
(blueprint: lem-pc-perfect-ring-hom-tensor-degrees) -/
noncomputable def perfectRingDualEvaluate {A : Type u} [CommRing A]
    (P : CochainComplex (RingSiteModules A) ℤ) (r : ℤ)
    (U : (Discrete PUnit.{u + 1})ᵒᵖ)
    (lam : ((perfectRingDual P).X r).val.obj U) (x : (P.X (-r)).val.obj U) : A := by
  let M := SheafOfModules.unit ((sheafCompose ⊥
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (CochainComplex.onePointRingSheaf A))
  let S := (CochainComplex.singleFunctor (RingSiteModules A) 0).obj M
  let π := ringHomComplexProjection P S r (-r)
  let y := ((π.val.app U lam).app (op (Over.mk (𝟙 U.unop)))) x
  exact (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 M (-r + r)
    (by omega)).hom.val.app U y

/-- The canonical map from the sectionwise tensor to the sheaf tensor, formed
from the sheafification unit and its specified tensor comparison.
Source: Stacks, Modules on Sites, Section 03EK.
(blueprint: lem-pc-perfect-ring-hom-tensor-degrees) -/
noncomputable def perfectRingTensorSectionMap {A : Type u} [CommRing A]
    (M N : RingSiteModules A) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    M.val ⊗ N.val ⟶ (M ⊗ N).val := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  exact (PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app (M.val ⊗ N.val) ≫
    (SheafOfModules.tensorObjIsoSheafification
      (R := CochainComplex.onePointRingSheaf A) M N).inv.val

/-- Normalization of evaluation: the `(r,s)` tensor summand contributes only to
Hom coordinate `-r`, with sign `(-1)^(r*s)`. The equation is before sheafification.
Source: Stacks, Tags 0A6A (1), 0ATK (1), expanded finite-projective argument.
(blueprint: lem-pc-perfect-ring-hom-tensor-degrees) -/
def PerfectRingHomTensorDegreeCondition {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    ((CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X n ⟶
      (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n) → Prop := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  intro a
  exact (∀ (r s : ℤ) (h : r + s = n) (p : ℤ), p ≠ -r →
    CochainComplex.ιMapBifunctor (perfectRingDual P) Q (curriedTensor _)
      r s n h ≫ a ≫ ringHomComplexProjection P Q n p = 0) ∧
    (∀ (r s : ℤ) (h : r + s = n) (U : (Discrete PUnit.{u + 1})ᵒᵖ)
      (lam : ((perfectRingDual P).X r).val.obj U) (y : (Q.X s).val.obj U)
      (x : (P.X (-r)).val.obj U),
      ringHomEvaluate P Q n (-r) U
        (a.val.app U ((CochainComplex.ιMapBifunctor (perfectRingDual P) Q
          (curriedTensor _) r s n h).val.app U
            ((perfectRingTensorSectionMap ((perfectRingDual P).X r) (Q.X s)).app U
              (lam ⊗ₜ[A] y)))) x =
        (eqToHom (congrArg Q.X (show s = -r + n by omega))).val.app U
          ((r * s).negOnePow • (perfectRingDualEvaluate P r U lam x • y)))

end CategoryTheory
