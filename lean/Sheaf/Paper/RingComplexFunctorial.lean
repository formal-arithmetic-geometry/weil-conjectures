/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

import Sheaf.Paper.RingComplexGodementFunctorial
import Sheaf.Paper.RingComplexGodementCech
import Sheaf.Paper.RingComplexCechBaseChange

/-!
# Functorial augmented ring complexes

Source: Stacks Project, algebraization.tex, Tag 099D, lemma-all-rings, clauses (a)-(d)
(blueprint: lem-weil-pbc-ring-complex-functorial).

All complexes use modules on the existing one-object bottom-topology site. Semilinear
chain maps are given on the unique object's sections. Scalar extension of a K-flat
replacement is specified term by term, including its differential and the pure-tensor
normalization of the induced map. This is the total tensor with the target ring in
degree zero. The localization complex is specified by coordinates, including its
differential, rather than by choosing an unspecified complex with the same terms.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators TensorProduct ChangeOfRings

namespace AlgebraicGeometry

/-- Stacks Project, Tag 099D(a)-(d)
(blueprint: lem-weil-pbc-ring-complex-functorial).

Proof:
1. Construct K(A,I) as the mapping fibre of A[0] to global sections of the concrete
   Godement resolution on Spec A minus V(I). The germ augmentation is a chain map,
   so the mapping fibre and its projection contain no postponed data.
2. Apply ringComplex_godement_functorial. Its semilinear maps commute with the
   differentials and augmentations and satisfy the strict identity and composition
   equations, giving the first four clauses.
3. Apply ringComplex_godement_cech. Principal intersections are affine and their
   structure-sheaf sections are the specified localizations. Godement flasqueness
   and affine acyclicity give the augmented comparison through the finite ordered
   Cech double total. Mapping fibres give the final clause, including the signs
   and the projection onto A in degree zero.
4. Given p:P to K(A,I) a K-flat resolution, transport this augmented Cech model to
   P by composing its derived comparison with the inverse of Q(p). Construct E by
   the actual scalar-extension functor, and chi by extending the semilinear maps
   m after p. The extension/restriction adjunction proves its value on 1 tensor x.
   Pure-tensor extensionality proves its chain equation with the stipulated
   changeOfRingsHom differential.
5. Apply ringComplex_cech_baseChange_quasiIso to P and K(B,J). The required
   augmentation equality follows from step 2 and the pure-tensor formula. This
   comparison uses the fraction base-change isomorphism of the bounded flat Cech
   model. Its augmentation determines the induced derived map by the
   local-cohomology coreflection (Stacks, Tags 0A6R and 0ALZ), so that map is
   invertible. K-flatness identifies ordinary scalar extension with derived scalar
   extension. Thus chi is a quasi-isomorphism and Q(chi) is invertible.
6. The term isomorphisms for E are identities by its construction, and the proved
   pure-tensor formula is exactly the last equation in the base-change clause.
   Assemble these data with the first four clauses and the model from step 3.
   Empty lists, zero rings, and zero or repeated generators are included. -/
theorem exists_functorial_ringComplex
    [∀ A : CommRingCat.{u}, HasDerivedCategory.{w} (RingSiteModules A)] :
    ∃ (K : ∀ A : CommRingCat.{u}, {I : Ideal A // I.FG} →
          CochainComplex (RingSiteModules A) ℤ)
      (ε : ∀ (A : CommRingCat.{u}) (I : {I : Ideal A // I.FG}),
        K A I ⟶ (HomologicalComplex.single (RingSiteModules A) (ComplexShape.up ℤ) 0).obj
          (@id (RingSiteModules A)
            (SheafOfModules.unit.{u, u, u} ((sheafCompose ⊥
              (forget₂ CommRingCat.{u} RingCat.{u})).obj
                (CochainComplex.onePointRingSheaf.{u} A)))))
      (m : ∀ (A B : CommRingCat.{u}) (φ : A →+* B)
        (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG}),
        I.val.map φ = J.val → ∀ n : ℤ,
          ((K A I).X n).val.obj (op ⟨PUnit.unit⟩) →ₛₗ[φ]
            ((K B J).X n).val.obj (op ⟨PUnit.unit⟩)),
      (∀ (A B : CommRingCat.{u}) (φ : A →+* B)
        (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
        (h : I.val.map φ = J.val) (n k : ℤ)
        (x : ((K A I).X n).val.obj (op ⟨PUnit.unit⟩)),
        m A B φ I J h k (((K A I).d n k).val.app (op ⟨PUnit.unit⟩) x) =
          ((K B J).d n k).val.app (op ⟨PUnit.unit⟩) (m A B φ I J h n x)) ∧
      (∀ (A B : CommRingCat.{u}) (φ : A →+* B)
        (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
        (h : I.val.map φ = J.val)
        (x : ((K A I).X 0).val.obj (op ⟨PUnit.unit⟩)),
        ((ε B J).f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (SheafOfModules.unit.{u, u, u} ((sheafCompose ⊥
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (CochainComplex.onePointRingSheaf.{u} B)))).hom).val.app (op ⟨PUnit.unit⟩)
          (m A B φ I J h 0 x) =
          φ (((ε A I).f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (SheafOfModules.unit.{u, u, u} ((sheafCompose ⊥
              (forget₂ CommRingCat.{u} RingCat.{u})).obj
                (CochainComplex.onePointRingSheaf.{u} A)))).hom).val.app (op ⟨PUnit.unit⟩) x)) ∧
      (∀ (A : CommRingCat.{u}) (I : {I : Ideal A // I.FG})
        (h : I.val.map (RingHom.id A) = I.val) (n : ℤ)
        (x : ((K A I).X n).val.obj (op ⟨PUnit.unit⟩)),
        m A A (RingHom.id A) I I h n x = x) ∧
      (∀ (A B D : CommRingCat.{u}) (φ : A →+* B) (ψ : B →+* D)
        (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
        (L : {L : Ideal D // L.FG}) (h : I.val.map φ = J.val)
        (h' : J.val.map ψ = L.val) (h'' : I.val.map (ψ.comp φ) = L.val)
        (n : ℤ) (x : ((K A I).X n).val.obj (op ⟨PUnit.unit⟩)),
        m B D ψ J L h' n (m A B φ I J h n x) = m A D (ψ.comp φ) I L h'' n x) ∧
      (∀ (A B : CommRingCat.{u}) (φ : A →+* B)
        (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
        (h : I.val.map φ = J.val) (P : CochainComplex (RingSiteModules A) ℤ)
        (p : P ⟶ K A I), P.IsAcyclicTensorKFlat → QuasiIso p →
        ∃ (E : CochainComplex (RingSiteModules B) ℤ)
          (t : ∀ n : ℤ, E.X n ≅
            SheafOfModules.changeOfRings.{u, u, u} (ringSiteMap.{u} φ) (P.X n)),
          (∀ n k : ℤ, E.d n k ≫ (t k).hom = (t n).hom ≫
            SheafOfModules.changeOfRingsHom.{u, u, u} (ringSiteMap.{u} φ) (P.X n) (P.d n k)) ∧
          ∃ χ : E ⟶ K B J, IsIso (DerivedCategory.Q.map χ) ∧
            ∀ (n : ℤ) (x : (P.X n).val.obj (op ⟨PUnit.unit⟩)),
              (χ.f n).val.app (op ⟨PUnit.unit⟩)
                ((t n).inv.val.app (op ⟨PUnit.unit⟩)
                  ((toSheafify ⊥ (SheafOfModules.changeOfRingsPresheaf
                    (ringSiteMap.{u} φ) (P.X n)).presheaf).app (op ⟨PUnit.unit⟩)
                    ((1 : B) ⊗ₜ[A, φ] x))) =
                m A B φ I J h n ((p.f n).val.app (op ⟨PUnit.unit⟩) x)) ∧
      (∀ (A : CommRingCat.{u}) (I : {I : Ideal A // I.FG}) (r : ℕ)
        (f : Fin r → A), Ideal.span (Set.range f) = I.val →
        ∃ (C : CochainComplex (RingSiteModules A) ℤ)
          (a : C ⟶ (HomologicalComplex.single (RingSiteModules A) (ComplexShape.up ℤ) 0).obj
            (@id (RingSiteModules A)
              (SheafOfModules.unit.{u, u, u} ((sheafCompose ⊥
                (forget₂ CommRingCat.{u} RingCat.{u})).obj
                  (CochainComplex.onePointRingSheaf.{u} A)))))
          (e₀ : (C.X 0).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A] A)
          (e : ∀ q : ℕ, (C.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A]
            ((t : Fin (q + 1) ↪o Fin r) → Localization.Away (∏ i, f (t i))))
          (l : ∀ (q : ℕ) (t : Fin (q + 2) ↪o Fin r) (j : Fin (q + 2)),
            Localization.Away (∏ i, f (t (Fin.succAboveOrderEmb j i))) →ₐ[A]
              Localization.Away (∏ i, f (t i))),
          (∀ n : ℤ, n < 0 → IsZero (C.X n)) ∧
          (∀ (x : (C.X 0).val.obj (op ⟨PUnit.unit⟩)) (t : Fin 1 ↪o Fin r),
            e 0 ((C.d 0 1).val.app (op ⟨PUnit.unit⟩) x) t =
              algebraMap A (Localization.Away (∏ i, f (t i))) (e₀ x)) ∧
          (∀ (q : ℕ) (x : (C.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩))
            (t : Fin (q + 2) ↪o Fin r),
            e (q + 1) ((C.d ((q : ℤ) + 1) ((q : ℤ) + 2)).val.app
              (op ⟨PUnit.unit⟩) x) t =
              ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
                l q t j (e q x ((Fin.succAboveOrderEmb j).trans t))) ∧
          (∀ x : (C.X 0).val.obj (op ⟨PUnit.unit⟩),
            (a.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (SheafOfModules.unit.{u, u, u} ((sheafCompose ⊥
                (forget₂ CommRingCat.{u} RingCat.{u})).obj
                  (CochainComplex.onePointRingSheaf.{u} A)))).hom).val.app
                    (op ⟨PUnit.unit⟩) x = e₀ x) ∧
          ∃ α : DerivedCategory.Q.obj C ≅ DerivedCategory.Q.obj (K A I),
            α.hom ≫ DerivedCategory.Q.map (ε A I) = DerivedCategory.Q.map a) := by
  let K : RingComplexFamily.{u} := fun A I ↦ ringComplexGodement A I.val
  let ε : RingComplexAugmentations K := fun A I ↦ ringComplexGodementAugmentation A I.val
  obtain ⟨m, hm⟩ := ringComplex_godement_functorial.{u}
  have hC (A : CommRingCat.{u}) (I : {I : Ideal A // I.FG}) :
      RingComplexHasCechModel A I.val (K A I) (ε A I) := ringComplex_godement_cech A I
  refine ⟨K, ε, m, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2, ?_, hC⟩
  intro A B φ I J h P p hP hp
  let E := ringComplexExtensionComplex φ P
  let χ := ringComplexExtendAlong φ K m I J h (hm.1 A B φ I J h) P p
  have hCP : RingComplexHasCechModel A I.val P (p ≫ ε A I) :=
    ringComplexHasCechModel_of_quasiIso (ε A I) p hp (hC A I)
  have hχ : QuasiIso χ := by
    apply ringComplex_cech_baseChange_quasiIso A B φ I J h
      P (K B J) (p ≫ ε A I) (ε B J) hCP (hC B J) hP χ
    intro x
    dsimp only [χ]
    rw [ringComplexExtendAlong_one_tmul]
    exact (hm.2.1 A B φ I J h _).trans (by rfl)
  refine ⟨E, fun n ↦ Iso.refl _, ?_, χ, ?_, ?_⟩
  · intro n k
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ χ).2 hχ
  · intro n x
    simp only [Iso.refl_inv, SheafOfModules.id_val, PresheafOfModules.id_app]
    exact ringComplexExtendAlong_one_tmul φ K m I J h (hm.1 A B φ I J h) P p n x

end AlgebraicGeometry
