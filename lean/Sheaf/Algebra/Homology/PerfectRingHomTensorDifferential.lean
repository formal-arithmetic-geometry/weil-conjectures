/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4, SHEAF group S1
-/
module

public import Sheaf.Algebra.Homology.PerfectRingHomTensorDegrees
import Sheaf.Algebra.Homology.PerfectRingHomTensorPostcomposition
import Sheaf.Algebra.Homology.PerfectRingHomTensorPrecomposition

/-! # Differential compatibility of signed tensor-dual evaluation

Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1), expanded
chain-level calculation in `lem-pc-perfect-ring-hom-tensor-dual-iso`, step 2.
(blueprint: lem-pc-perfect-ring-hom-tensor-differential)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory

private theorem tensorHom_comm_of_components
    {C : Type*} [Category C] [Preadditive C]
    (D Q : CochainComplex C ℤ) (F : C ⥤ C ⥤ C)
    [F.PreservesZeroMorphisms] [∀ M, (F.obj M).PreservesZeroMorphisms]
    [CochainComplex.HasMapBifunctor D Q F]
    (H : CochainComplex C ℤ) (X Y : ℤ → ℤ → C)
    (π : ∀ n p, H.X n ⟶ X n p) (ρ : ∀ n p, H.X n ⟶ Y n p)
    (post : ∀ n p, X n p ⟶ X (n + 1) p)
    (pre : ∀ n p, Y n p ⟶ X (n + 1) p)
    (f : ∀ n, (CochainComplex.mapBifunctor D Q F).X n ⟶ H.X n)
    (hπ : ∀ n, Nonempty (IsLimit (Fan.mk (H.X n) (π n))))
    (hd : ∀ n p, H.d n (n + 1) ≫ π (n + 1) p =
      π n p ≫ post n p - n.negOnePow • (ρ n p ≫ pre n p))
    (hpre : ∀ n r s (h : r + s = n) p,
      HomologicalComplex.mapBifunctor.d₁ D Q F (.up ℤ) r s (n + 1) ≫
          f (n + 1) ≫ π (n + 1) p =
        -n.negOnePow • (CochainComplex.ιMapBifunctor D Q F r s n h ≫
          f n ≫ ρ n p ≫ pre n p))
    (hpost : ∀ n r s (h : r + s = n) p,
      HomologicalComplex.mapBifunctor.d₂ D Q F (.up ℤ) r s (n + 1) ≫
          f (n + 1) ≫ π (n + 1) p =
        CochainComplex.ιMapBifunctor D Q F r s n h ≫ f n ≫ π n p ≫ post n p) :
    ∀ n m, (ComplexShape.up ℤ).Rel n m →
      f n ≫ H.d n m = (CochainComplex.mapBifunctor D Q F).d n m ≫ f m := by
  intro n m hnm
  have hm : n + 1 = m := hnm
  subst m
  apply HomologicalComplex.mapBifunctor.hom_ext (K₁ := D) (K₂ := Q) (F := F)
    (c := ComplexShape.up ℤ)
  intro r s hrs
  apply Fan.IsLimit.hom_ext (Classical.choice (hπ (n + 1)))
  intro p
  simp only [fan_mk_proj, Category.assoc]
  rw [hd n p, HomologicalComplex.mapBifunctor.d_eq D Q F (.up ℤ) n (n + 1)]
  simp only [Preadditive.comp_add, Preadditive.add_comp,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc,
    HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  rw [hpre n r s hrs p, hpost n r s hrs p]
  simp only [Preadditive.comp_sub, Linear.comp_units_smul, Units.neg_smul]
  abel

set_option backward.isDefEq.respectTransparency true in
/-- Any family with the signed evaluation formula commutes with the differentials.
There are no boundedness, projectivity, finiteness, or invertibility assumptions.
Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1), expanded
chain-level calculation in `lem-pc-perfect-ring-hom-tensor-dual-iso`, step 2.
(blueprint: lem-pc-perfect-ring-hom-tensor-differential)

Proof: test equality after every tensor coproduct inclusion and every Hom product
projection. On the bottom-topology one-object site sheafification is invertible and
restriction maps in the unique slice are identities, so equality is detected on pure
tensors lam tensor y and vectors x. For a summand of bidegree (r,s), n=r+s, the tensor
differential has terms d_D(lam) tensor y and (-1)^r lam tensor d_Q(y). Since D is
Hom(P,A[0]), its differential on a functional is -(-1)^r lam composed with d_P.
For the second term the normalization in degree n+1 contributes (-1)^(r*(s+1));
combined with (-1)^r this is (-1)^(r*s), exactly the postcomposition term of the Hom
differential. For the first term the sign is -(-1)^(r+(r+1)*s), which equals
-(-1)^(r+s+r*s), exactly its precomposition term. The postcomposition term is supported
only in Hom coordinate -r and the precomposition term only in coordinate -r-1; all
other coordinates vanish by the off-diagonal condition. Degree transports agree by
proof irrelevance and naturality. Bilinearity extends the equality from pure tensors,
the sheafification adjunction gives equality on each sheaf tensor, and the coproduct
and product universal properties give the asserted equality. No finite-support
argument is used; zero objects, arbitrary unbounded Q, and the zero ring obey the
same equations. -/
theorem perfectRingHom_tensorDual_degree_comm {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    ∀ (f : ∀ n : ℤ,
      (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X n ⟶
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n),
      (∀ n : ℤ, PerfectRingHomTensorDegreeCondition P Q n (f n)) →
      ∀ n m : ℤ, (ComplexShape.up ℤ).Rel n m →
        f n ≫ (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).d n m =
          (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).d n m ≫
            f m := by
  classical
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  intro f hf
  let H := homComplex (R := CochainComplex.onePointRingSheaf A) P Q
  let X := fun n p : ℤ ↦ SheafOfModules.homObj
    (R := CochainComplex.onePointRingSheaf A) (P.X p) (Q.X (p + n))
  let Y := fun n p : ℤ ↦ SheafOfModules.homObj
    (R := CochainComplex.onePointRingSheaf A) (P.X (p + 1)) (Q.X (p + (n + 1)))
  let ρ : ∀ n p : ℤ, H.X n ⟶ Y n p := fun n p ↦
    (homComplex_exists.{u, u, u, u}
      (R := CochainComplex.onePointRingSheaf A)).choose_spec.choose
        P Q n (p + 1) (p + (n + 1)) (by omega)
  apply tensorHom_comm_of_components (perfectRingDual P) Q
    (curriedTensor (RingSiteModules A)) H X Y (ringHomComplexProjection P Q) ρ
    (fun n p ↦ SheafOfModules.homObjMap (R := CochainComplex.onePointRingSheaf A)
      (𝟙 (P.X p)) (Q.d (p + n) (p + (n + 1))))
    (fun n p ↦ SheafOfModules.homObjMap (R := CochainComplex.onePointRingSheaf A)
      (P.d p (p + 1)) (𝟙 (Q.X (p + (n + 1))))) f
  · intro n
    exact (homComplex_exists.{u, u, u, u}
      (R := CochainComplex.onePointRingSheaf A)).choose_spec.choose_spec.1 P Q n
  · intro n p
    exact (homComplex_exists.{u, u, u, u}
      (R := CochainComplex.onePointRingSheaf A)).choose_spec.choose_spec.2.1
        P Q n (n + 1) p (p + (n + 1)) (p + n) (p + 1) rfl rfl rfl (by omega)
  · intro n r s hrs p
    exact perfectRingHom_tensorDual_precomposition P Q n (f n) (f (n + 1))
      (hf n) (hf (n + 1)) r s p hrs
  · intro n r s hrs p
    exact perfectRingHom_tensorDual_postcomposition P Q n (f n) (f (n + 1))
      (hf n) (hf (n + 1)) r s p hrs

end CategoryTheory
