/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Both coefficient shift squares for external chain evaluations

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, Tag 0A90
(lemma-compose), and lemma-RHom-triangulated; the two-variable sign calculation
from steps 8 and 9 of lem-pur-external-rhom-cone-pairing
(blueprint: lem-pur-external-evaluation-two-shift-squares).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.ExternalEvaluation

variable {C : Type u} [Category.{v} C] (S : GrothendieckTopology C)
  (A : Type (max u v)) [CommRing A]

/-- The recorded constant-ring module category, in its commutative presentation.
Source: Stacks 03CY and 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
abbrev Modules := realizationModules S A

/-- Cochain complexes in the recorded module-sheaf category.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
abbrev Complex := CochainComplex (Modules S A) ℤ

/-- Coefficient complexes over the original ring.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
abbrev Coeff (R : Type w) [CommRing R] := CochainComplex (ModuleCat.{w} R) ℤ

/-- Termwise constant realization, using the existing sheafification construction.
Source: Stacks 03CY (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
abbrev constantComplex :=
  (commutativeSiteConstantModuleFunctor S A).mapHomologicalComplex (.up ℤ)

/-- Forget scalars on a coefficient complex; no component or differential is changed.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
abbrev underlying (R : Type w) [CommRing R] :=
  (forget₂ (ModuleCat.{w} R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)

/-- A constant local section is the image of the module-sheafification unit.
Source: Stacks 03CY (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def constantSection (Q : ModuleCat.{max u v} A) (W : Cᵒᵖ) (x : Q) :
    ((commutativeSiteConstantModuleFunctor S A).obj Q).val.obj W :=
  (toSheafify S ((siteConstantModulePresheafGeneral (C := C) A).obj Q).presheaf).app W x

/-- A local pure tensor in the existing sheaf tensor, via its sheafification comparison.
Source: Stacks 03EK (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def tensorSection (P Q : Modules S A) (W : Cᵒᵖ) (x : P.val.obj W) (y : Q.val.obj W) :
    (P ⊗ Q).val.obj W :=
  ((SheafOfModules.tensorObjIsoSheafification (R := realizationRing S A) P Q).inv.val.app W)
    ((((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
      (P.val ⊗ Q.val)).app W) (TensorProduct.tmul _ x y))

/-- The recorded direct-sum total tensor, with the usual signed differential.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
abbrev tensorComplex (P Q : Complex S A) :=
  CochainComplex.mapBifunctor P Q (curriedTensor (Modules S A))

/-- Include a local pure tensor in its direct-sum total-complex summand.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def tensorComplexSection (P Q : Complex S A) (r s n : ℤ) (h : r + s = n)
    (W : Cᵒᵖ) (x : (P.X r).val.obj W) (y : (Q.X s).val.obj W) :
    ((tensorComplex S A P Q).X n).val.obj W :=
  ((CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules S A)) r s n h).val.app W)
    (tensorSection S A (P.X r) (Q.X s) W x y)

/-- Include a coefficient pure tensor in the direct-sum total tensor.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def coefficientTensor (R : Type w) [CommRing R] (U V : Coeff R) (r s : ℤ)
    (w : U.X r) (z : V.X s) :
    (U ⊗ V).X (r + s) :=
  (HomologicalComplex.ιTensorObj U V r s (r + s) rfl).hom (TensorProduct.tmul R w z)

/-- Evaluate an ordinary chain map on a coefficient and a homogeneous local section.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def evaluate (U : Coeff A) (E N : Complex S A)
    (f : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N) (r q : ℤ) (W : Cᵒᵖ)
    (w : U.X r) (e : (E.X q).val.obj W) : (N.X (r + q)).val.obj W :=
  ((f.f (r + q)).val.app W)
    (tensorComplexSection S A ((constantComplex S A).obj U) E r q (r + q) rfl W
      (constantSection S A (U.X r) W w) e)

/-- The unsigned external evaluation, transported only along equality of total degrees.
Source: Stacks 0A90 (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def unsignedEvaluation (U V : Coeff A) (E H N M J : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (v : tensorComplex S A ((constantComplex S A).obj V) H ⟶ M)
    (i : tensorComplex S A N M ⟶ J) (r s q t k : ℤ)
    (hk : (r + q) + (s + t) = k) (W : Cᵒᵖ) (w : U.X r) (z : V.X s)
    (e : (E.X q).val.obj W) (h : (H.X t).val.obj W) : (J.X k).val.obj W :=
  ((J.XIsoOfEq hk).hom.val.app W)
    (((i.f ((r + q) + (s + t))).val.app W)
      (tensorComplexSection S A N M (r + q) (s + t) ((r + q) + (s + t)) rfl W
        (evaluate S A U E N u r q W w e) (evaluate S A V H M v s t W z h)))

/-- Scalar linearity for a map to global Hom, expressed on all local components.
This equips the additive global Hom presentation with exactly its original A-linearity;
the scalar is sent to the constant ring sheaf by the prescribed sheafification unit.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def IsLinearHomMap (T : Coeff A) (B J : Complex S A)
    (p : (underlying A).obj T ⟶ CochainComplex.HomComplex B J) : Prop :=
  ∀ (n : ℤ) (a : A) (x : T.X n) (j k : ℤ) (hjk : j + n = k)
    (W : Cᵒᵖ) (y : (B.X j).val.obj W),
    (((((p.f n) (a • x)).v j k hjk).val.app W) y) =
      ((realizationRingUnit S A).app W a) •
        (((((p.f n) x).v j k hjk).val.app W) y)

/-- The displayed signed pairing on all homogeneous local pure tensors.
The global Hom complex is Mathlib's product of sheaf morphisms; forgetting scalars on
its source does not change a component. The formula fixes the pairing on generators.
Source: Stacks 0A8X and 0A90
(blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def IsExternalPairing (U V : Coeff A) (E H N M J : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (v : tensorComplex S A ((constantComplex S A).obj V) H ⟶ M)
    (i : tensorComplex S A N M ⟶ J)
    (p : (underlying A).obj (U ⊗ V) ⟶
      CochainComplex.HomComplex (tensorComplex S A E H) J) : Prop :=
  IsLinearHomMap S A (U ⊗ V) (tensorComplex S A E H) J p ∧
  ∀ (r s q t : ℤ) (W : Cᵒᵖ) (w : U.X r) (z : V.X s)
    (e : (E.X q).val.obj W) (h : (H.X t).val.obj W),
    (((((p.f (r + s)) (coefficientTensor A U V r s w z)).v
      (q + t) ((q + t) + (r + s)) rfl).val.app W)
        (tensorComplexSection S A E H q t (q + t) rfl W e h)) =
      (s * q).negOnePow • unsignedEvaluation S A U V E H N M J u v i
        r s q t ((q + t) + (r + s)) (by omega) W w z e h

/-- The balancing shift comparison has the specified sign in the shifted first degree.
Source: Stacks 0A8X and the two-variable sign calculation
(blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def IsBalancingShift (U : Coeff A) (E : Complex S A)
    (η : tensorComplex S A ((constantComplex S A).obj (U⟦(-1 : ℤ)⟧)) (E⟦(1 : ℤ)⟧) ≅
      tensorComplex S A ((constantComplex S A).obj U) E) : Prop :=
  ∀ (r q : ℤ) (W : Cᵒᵖ) (w : (U⟦(-1 : ℤ)⟧).X r)
    (e : ((E⟦(1 : ℤ)⟧).X q).val.obj W),
    ((η.hom.f (r + q)).val.app W)
      (tensorComplexSection S A ((constantComplex S A).obj (U⟦(-1 : ℤ)⟧))
        (E⟦(1 : ℤ)⟧) r q (r + q) rfl W
        (constantSection S A ((U⟦(-1 : ℤ)⟧).X r) W w) e) =
      r.negOnePow • tensorComplexSection S A ((constantComplex S A).obj U) E
        (r + -1) (q + 1) (r + q) (by omega) W
        (constantSection S A (U.X (r + -1)) W w) e

/-- The first-variable Hom shift is normalized by `(-1)^n` in Hom degree `n`.
Source: Stacks 0A8X and lemma-RHom-triangulated
(blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def IsHomShift (B J : Complex S A)
    (θ : CochainComplex.HomComplex (B⟦(1 : ℤ)⟧) J ≅
      (CochainComplex.HomComplex B J)⟦(-1 : ℤ)⟧) : Prop :=
  ∀ (n : ℤ) (f : CochainComplex.HomComplex.Cochain (B⟦(1 : ℤ)⟧) J n)
    (j k : ℤ) (hjk : j + (n + -1) = k),
    ((θ.hom.f n) f).v j k hjk =
      n.negOnePow • ((B.shiftFunctorObjXIso 1 (j - 1) j (by omega)).inv ≫
        f.v (j - 1) k (by omega))

/-- Precompose a global Hom cochain with a chain map, component by component.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
def precomposeCochain {B B' J : Complex S A} (f : B' ⟶ B) {n : ℤ}
    (g : CochainComplex.HomComplex.Cochain B J n) :
    CochainComplex.HomComplex.Cochain B' J n :=
  (CochainComplex.HomComplex.Cochain.ofHom f).comp g (zero_add n)

/-- The unsigned first tensor-shift comparison for module sheaves.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
abbrev tensorShift₁ (E H : Complex S A) (a : ℤ) :
    tensorComplex S A (E⟦a⟧) H ≅ (tensorComplex S A E H)⟦a⟧ :=
  CochainComplex.mapBifunctorShift₁Iso E H (curriedTensor (Modules S A)) a

/-- The second tensor-shift comparison, with sign `(-1)^(a*q)` in first degree `q`.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
abbrev tensorShift₂ (E H : Complex S A) (a : ℤ) :
    tensorComplex S A E (H⟦a⟧) ≅ (tensorComplex S A E H)⟦a⟧ :=
  CochainComplex.mapBifunctorShift₂Iso E H (curriedTensor (Modules S A)) a

/-- The unsigned first tensor-shift comparison for coefficient complexes.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
abbrev coefficientShift₁ (R : Type w) [CommRing R] (U V : Coeff R) (a : ℤ) :
    (U⟦a⟧ ⊗ V) ≅ (U ⊗ V)⟦a⟧ :=
  CochainComplex.mapBifunctorShift₁Iso U V (curriedTensor (ModuleCat.{w} R)) a

/-- The coefficient comparison with sign `(-1)^(a*r)` in first degree `r`.
Source: Stacks 0A8X (blueprint: lem-pur-external-evaluation-two-shift-squares). -/
abbrev coefficientShift₂ (R : Type w) [CommRing R] (U V : Coeff R) (a : ℤ) :
    (U ⊗ V⟦a⟧) ≅ (U ⊗ V)⟦a⟧ :=
  CochainComplex.mapBifunctorShift₂Iso U V (curriedTensor (ModuleCat.{w} R)) a

/-- Both coefficient shift squares for the signed external chain evaluation.

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, Tag 0A90 (lemma-compose),
and lemma-RHom-triangulated; agent two-variable sign calculation from steps 8 and 9
of lem-pur-external-rhom-cone-pairing
(blueprint: lem-pur-external-evaluation-two-shift-squares).

Proof: (1) Extend the displayed balanced local formula through module sheafification
and the direct-sum tensor universal property, taking products of all Hom components.
This also gives an equality test on homogeneous pure tensors (constant module functor,
sheaf tensor, sheafification, total tensor and Hom-complex dependency nodes).
(2) Expand the Hom differential of the external evaluation. The four terms have signs
sq, sq+r, sq+r+q and sq+r+q+s. Subtraction of the two source-differential terms cancels
those differentiating e and h, leaving exactly p(dw,z)+(-1)^r p(w,dz).
(3) The Hom shift sends f to (-1)^n f with its source index reduced by one; expanding
both differentials verifies the chain-map identity and the same sign gives its inverse.
(4) For the balancing comparison, the two shifted differential terms both become
(-1)^r dw tensor e minus w tensor de. The same signed reindexing is its inverse.
(5) The first tensor shift is unsigned; the second carries (-1)^(a*r). Checking the
two differential terms gives chain isomorphisms for a=1 and a=-1. Precomposition with
the inverse coefficient comparison, followed by the Hom shift, gives rho.
(6) In the E square the four signs are sq, r, 0 and r+s, summing to sq+s modulo two.
The right side has sign s(q+1), the same exponent modulo two.
(7) In the H square the signs are sq, s, q and r+s, summing to sq+q+r modulo two.
The right side has r+(s-1)q, again the same exponent. The equality test of (1) proves
both equalities of chain maps. All calculations hold in every integer degree and use
no boundedness, flatness or injectivity. -/
theorem external_evaluation_two_shift_squares
    (U V : Coeff A) (E H N M J : Complex S A)
    (u : tensorComplex S A ((constantComplex S A).obj U) E ⟶ N)
    (v : tensorComplex S A ((constantComplex S A).obj V) H ⟶ M)
    (i : tensorComplex S A N M ⟶ J) :
    ∃ θ : ∀ B : Complex S A,
        CochainComplex.HomComplex (B⟦(1 : ℤ)⟧) J ≅
          (CochainComplex.HomComplex B J)⟦(-1 : ℤ)⟧,
      (∀ B : Complex S A, IsHomShift S A B J (θ B)) ∧
      ∃ (ηU : tensorComplex S A ((constantComplex S A).obj (U⟦(-1 : ℤ)⟧))
          (E⟦(1 : ℤ)⟧) ≅ tensorComplex S A ((constantComplex S A).obj U) E)
        (ηV : tensorComplex S A ((constantComplex S A).obj (V⟦(-1 : ℤ)⟧))
          (H⟦(1 : ℤ)⟧) ≅ tensorComplex S A ((constantComplex S A).obj V) H),
        IsBalancingShift S A U E ηU ∧ IsBalancingShift S A V H ηV ∧
        ∃ (p : (underlying A).obj (U ⊗ V) ⟶
            CochainComplex.HomComplex (tensorComplex S A E H) J)
          (pE : (underlying A).obj (U⟦(-1 : ℤ)⟧ ⊗ V) ⟶
            CochainComplex.HomComplex (tensorComplex S A (E⟦(1 : ℤ)⟧) H) J)
          (pH : (underlying A).obj (U ⊗ V⟦(-1 : ℤ)⟧) ⟶
            CochainComplex.HomComplex (tensorComplex S A E (H⟦(1 : ℤ)⟧)) J)
          (ρE : CochainComplex.HomComplex (tensorComplex S A (E⟦(1 : ℤ)⟧) H) J ≅
            (CochainComplex.HomComplex (tensorComplex S A E H) J)⟦(-1 : ℤ)⟧)
          (ρH : CochainComplex.HomComplex (tensorComplex S A E (H⟦(1 : ℤ)⟧)) J ≅
            (CochainComplex.HomComplex (tensorComplex S A E H) J)⟦(-1 : ℤ)⟧),
          IsExternalPairing S A U V E H N M J u v i p ∧
          IsExternalPairing S A (U⟦(-1 : ℤ)⟧) V (E⟦(1 : ℤ)⟧) H N M J
            (ηU.hom ≫ u) v i pE ∧
          IsExternalPairing S A U (V⟦(-1 : ℤ)⟧) E (H⟦(1 : ℤ)⟧) N M J
            u (ηV.hom ≫ v) i pH ∧
          (∀ (n : ℤ)
            (f : CochainComplex.HomComplex.Cochain
              (tensorComplex S A (E⟦(1 : ℤ)⟧) H) J n),
            (ρE.hom.f n) f = ((θ (tensorComplex S A E H)).hom.f n)
              (precomposeCochain S A (tensorShift₁ S A E H 1).inv f)) ∧
          (∀ (n : ℤ)
            (f : CochainComplex.HomComplex.Cochain
              (tensorComplex S A E (H⟦(1 : ℤ)⟧)) J n),
            (ρH.hom.f n) f = ((θ (tensorComplex S A E H)).hom.f n)
              (precomposeCochain S A (tensorShift₂ S A E H 1).inv f)) ∧
          pE ≫ ρE.hom =
            (underlying A).map (coefficientShift₁ A U V (-1)).hom ≫
              (((underlying A).commShiftIso (-1)).inv.app (U ⊗ V)) ≫ p⟦(-1 : ℤ)⟧' ∧
          pH ≫ ρH.hom =
            (underlying A).map (coefficientShift₂ A U V (-1)).hom ≫
              (((underlying A).commShiftIso (-1)).inv.app (U ⊗ V)) ≫ p⟦(-1 : ℤ)⟧' ∧
          (∀ (r s q t : ℤ) (W : Cᵒᵖ) (w : (U⟦(-1 : ℤ)⟧).X r) (z : V.X s)
            (e : ((E⟦(1 : ℤ)⟧).X q).val.obj W) (h : (H.X t).val.obj W),
            ((((((pE ≫ ρE.hom).f (r + s))
              (coefficientTensor A (U⟦(-1 : ℤ)⟧) V r s w z)).v
                ((q + t) + 1) (((q + t) + 1) + ((r + s) + -1)) rfl).val.app W)
                  (tensorComplexSection S A E H (q + 1) t ((q + t) + 1)
                    (by omega) W e h)) =
              (s * q + s).negOnePow • unsignedEvaluation S A U V E H N M J u v i
                (r + -1) s (q + 1) t (((q + t) + 1) + ((r + s) + -1))
                (by omega) W w z e h) ∧
          (∀ (r s q t : ℤ) (W : Cᵒᵖ) (w : U.X r) (z : (V⟦(-1 : ℤ)⟧).X s)
            (e : (E.X q).val.obj W) (h : ((H⟦(1 : ℤ)⟧).X t).val.obj W),
            ((((((pH ≫ ρH.hom).f (r + s))
              (coefficientTensor A U (V⟦(-1 : ℤ)⟧) r s w z)).v
                ((q + t) + 1) (((q + t) + 1) + ((r + s) + -1)) rfl).val.app W)
                  (tensorComplexSection S A E H q (t + 1) ((q + t) + 1)
                    (by omega) W e h)) =
              (s * q + q + r).negOnePow • unsignedEvaluation S A U V E H N M J u v i
                r (s + -1) q (t + 1) (((q + t) + 1) + ((r + s) + -1))
                (by omega) W w z e h) := by
  sorry

end CategoryTheory.ExternalEvaluation
