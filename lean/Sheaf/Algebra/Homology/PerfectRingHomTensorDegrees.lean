/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.Algebra.Homology.PerfectRingDualTermFlat

/-! # Signed evaluation in each total tensor degree

Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1).
(blueprint: lem-pc-perfect-ring-hom-tensor-degrees)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory

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
  let π := (homComplex_exists (R := CochainComplex.onePointRingSheaf A)).choose_spec.choose
    P S r (-r) 0 (by omega)
  let y := ((π.val.app U lam).app (op (Over.mk (𝟙 U.unop)))) x
  exact (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom.val.app U y

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

/-- Signed evaluation is invertible in each degree; no differential compatibility is asserted.
Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1), expanded
finite-projective representative calculation, steps 1 and the finite-support part of step 2
of `lem-pc-perfect-ring-hom-tensor-dual-iso`.
(blueprint: lem-pc-perfect-ring-hom-tensor-degrees)

Proof: on the one-object bottom-topology site the sheafification unit is invertible,
and a localized linear map is determined by its value on the unique object. Projection
identifies the degree-r dual with Hom(P^(-r),A): the single complex is zero in every
other target degree, and a product with only one nonzero factor is that factor.
For a finite free module M, the map from its dual tensor N to Hom(M,N) has inverse
f mapped to the finite sum of e_i^* tensor f(e_i). Both inverse identities follow
from the dual-basis identities. For finite projective M, split a finite generating
surjection A^t onto M. Precomposition with the inclusion and projection restricts the
free comparison and its inverse to the corresponding summands, with the same formula.
Mathlib dualTensorHomEquiv and dualTensorHomEquiv_tmul already provide this
finite-projective module comparison and its formula; reuse them rather than prove
the module calculation again. Apply this to M=P^(-r) and N=Q^s.
For fixed n, bounds on P leave only finitely many
nonzero factors in both the tensor coproduct and Hom product. Reindex r+s=n by p=-r
and identify both with the finite biproduct. The diagonal block is evaluation multiplied
by the unit (-1)^(r*s), so is invertible; take its inverse block by block. The coproduct
inclusions and product projections give exactly the displayed normalization. There is
no use of differentials or of a bound on Q. If the support interval is empty, or P or Q
is zero, the finite biproduct is zero and the same inverse equations apply. The zero
ring and rank-zero projective summands are also covered. -/
theorem perfectRingHom_tensorDual_degree_exists {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hp : ∀ n : ℤ, Module.Projective A ((P.X n).val.obj (op ⟨PUnit.unit⟩)))
    (hf : ∀ n : ℤ, Module.Finite A ((P.X n).val.obj (op ⟨PUnit.unit⟩))) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    ∃ e : (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X n ≅
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n,
      PerfectRingHomTensorDegreeCondition P Q n e.hom := by sorry

end CategoryTheory
