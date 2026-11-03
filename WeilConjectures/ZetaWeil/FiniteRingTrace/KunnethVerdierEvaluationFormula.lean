/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CurrentTrace.CurrentSixFunctorKunnethMaps

/-! # Evaluation of the canonical Künneth–Verdier map

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/sk-def-sf-kv-maps/
def-sf-kv-maps.md (iii)--(iv),
and literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/
thm-trf-verdier-duality.proof.md Step 3
(blueprint: lem-trf-kv-evaluation-formula).

All coefficients are arbitrary finite commutative ell-primary rings. The geometric
exceptional functors are the current Brown restrictions on the full constructible finite-Tor
categories. The tensor, internal Hom and pullbacks are the ordinary native module operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.FiniteRingTrace

private lemma native_transpose_identity {C : Type*} [Category C] [MonoidalCategory C]
    [MonoidalClosed C] (U Q : C) :
    MonoidalClosed.uncurry (𝟙 ((ihom U).obj Q)) = (ihom.ev U).app Q :=
  MonoidalClosed.uncurry_id_eq_ev _ _


open CompactificationReindexing RelativeKunneth ProductComparisons KVConstructible

variable (A : Type) [CommRing A] [Finite A]

local instance baseLocallyOfFiniteType (k : Type u) [Field k] :
    LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))
local instance baseQuasiCompact (k : Type u) [Field k] :
    QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))
local instance baseIsSeparated (k : Type u) [Field k] :
    IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
variable (hell : ell ≠ D.p) (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)

/-- The discrete finite ring as a bundled commutative condensed ring, without changing data.
Source: coefficient convention (blueprint: lem-trf-kv-evaluation-formula). -/
abbrev kvRing : ScalarSixRing.{u} := CommMon.mk (coefficient A)

/-- The actual coefficient sheaf in degree zero, bundled in the existing Dctf subcategory.
Source: the input to Ra_Y^! (blueprint: lem-trf-kv-evaluation-formula). -/
def kvCoefficientUnit : Ctf A (Spec (.of D.k)) :=
  ⟨constantCoefficientObject (coefficient A) (Spec (.of D.k)),
    constantCoefficientObject_mem (coefficient A) (Spec (.of D.k))⟩

variable (X Y W : SepFinType D.k) (pX : W ⟶ X) (pY : W ⟶ Y)
variable (sq : IsPullback pX.hom.left pY.hom.left X.obj.hom Y.obj.hom)

/-- Rp_X^! on the stated constructible domain. The identity in the product-map geometry
is retained in its displayed composite; id_W followed by p_X is p_X itself.
Source: the exceptional target (blueprint: lem-trf-kv-evaluation-formula). -/
abbrev kvExceptional : Ctf A X.obj.left ⥤ Ctf A W.obj.left :=
  (exceptionalDatum A D ell hell hA ((𝟙 W) ≫ pX).hom).right

/-- The equality-induced identification of the two presentations of the structure map.
`Over.mkIdTerminal.from Y` and `Over.homMk Y.hom` are equal by terminal uniqueness.
Applying the same chosen Brown datum to this equality identifies the dualizing objects;
no isomorphism is selected from an unnormalized existence theorem.
Source: the structure-map notation (blueprint: lem-trf-kv-evaluation-formula). -/
def kvOmegaComparison :
    ((exceptionalDatum A D ell hell hA
      (ObjectProperty.homMk (Over.homMk Y.obj.hom) : Y ⟶ base D.k).hom).right.obj
        (kvCoefficientUnit A D)).obj ≅ dualizingComplex A D ell hell hA Y.obj := by
  let f : Y.obj ⟶ (base D.k).obj := Over.homMk Y.obj.hom
  have hf : f = Over.mkIdTerminal.from Y.obj := Over.mkIdTerminal.hom_ext _ _
  apply eqToIso
  change ((exceptionalDatum A D ell hell hA f).right.obj
    (kvCoefficientUnit A D)).obj = _
  rw [hf]
  rfl

/-- The arrow e: reassociation, inverse pullback--tensor comparison, then pulled-back
Verdier evaluation. The native monoidal multiplication is the inverse of the comparison
Lf^*(K tensor L) -> Lf^*K tensor Lf^*L, so its direction is the one in the node.
Source: definition of e (blueprint: lem-trf-kv-evaluation-formula). -/
def kvExternalEvaluation (M : Ctf A X.obj.left) (N : Ctf A Y.obj.left) :
    ((P (coefficient A) pX.hom.left).obj M.obj ⊗
        (P (coefficient A) pY.hom.left).obj
          ((verdierDual A D ell hell hA Y.obj).obj (op N))) ⊗
        (P (coefficient A) pY.hom.left).obj N.obj ⟶
      (P (coefficient A) pX.hom.left).obj M.obj ⊗
        (P (coefficient A) pY.hom.left).obj
          (dualizingComplex A D ell hell hA Y.obj) :=
  (α_ _ _ _).hom ≫
    (𝟙 _ ⊗ₘ (Functor.Monoidal.μIso (P (coefficient A) pY.hom.left)
      ((verdierDual A D ell hell hA Y.obj).obj (op N)) N.obj).hom) ≫
    (𝟙 _ ⊗ₘ (P (coefficient A) pY.hom.left).map (evaluation A D ell hell hA Y.obj N))

/-- Right-ordered tensor--Hom evaluation, obtained from the same adjunction as the
recorded Verdier evaluation. The braiding is the derived Koszul braiding.
Source: internal-Hom evaluation in the conclusion
(blueprint: lem-trf-kv-evaluation-formula). -/
def kvRightEvaluation (T : Scheme.{u}) (U Q : Ambient A T) : (ihom U).obj Q ⊗ U ⟶ Q :=
  letI : BraidedCategory (Ambient A T) := DerivedCategory.braidedCategory' _
  (β_ _ _).hom ≫ (ihom.ev U).app Q

/-- Evaluation of kappa and its naturality on exactly the finite-Tor constructible domains.
Source: def-sf-kv-maps (iii)--(iv), and thm-trf-verdier-duality proof Step 3
(blueprint: lem-trf-kv-evaluation-formula).

Proof plan:
1. The natural tensor--Hom adjunction, supplied by the internal currying and global-RHom
   lemmas, identifies a transpose with evaluation after tensoring by the identity. It
   commutes with postcomposition in the target.
2. Expand beta from def-sf-kv-maps (iii) at (A_X,M) and (N,omega_Y). The first evaluation
   is the unit action; remove its degree-zero factor. Reassociation followed by the inverse
   pullback--tensor comparison gives precisely kvExternalEvaluation. On K-flat flat-term
   models the comparison sends a tensor x tensor y to (a tensor x) tensor (1 tensor y).
   The signed constraints agree: the discarded unit contributes sign +1, while D(N) and N
   keep their order. Use lem-weil-pbc-ringed-topoi-derived-tensor-pullback and the signed
   closed symmetric monoidal structure lem-sf-ringed-derived-closed-symmetric-monoidal.
3. Kappa is RHom(1,alpha) after beta. Postcomposition naturality of transposition gives
   alpha after e, and the evaluation description gives the second displayed equality.
4. Tensor and pullback functoriality, naturality of the relative Ku map and of the
   exceptional counits give covariance in M, including the uncurried square below.
5. For w:N' -> N, dinaturality of Verdier evaluation gives evaluation_N' after
   (D(w) tensor 1) = evaluation_N after (1 tensor w). Pull back and tensor with M,
   then postcompose with alpha. Transposition gives the contravariant kappa square.
   None of these steps assumes that alpha or kappa is invertible, or that N is site-perfect.
-/
theorem kv_evaluation_formula (M : Ctf A X.obj.left) (N : Ctf A Y.obj.left) :
    letI : BraidedCategory (Ambient A W.obj.left) := DerivedCategory.braidedCategory' _
    let B := (P (coefficient A) pX.hom.left).obj M.obj ⊗
      (P (coefficient A) pY.hom.left).obj ((verdierDual A D ell hell hA Y.obj).obj (op N))
    let U := (P (coefficient A) pY.hom.left).obj N.obj
    let Q := ((kvExceptional A D ell hell hA X W pX).obj M).obj
    let e := kvExternalEvaluation A D ell hell hA X Y W pX pY M N
    let a := kvAlpha A D ell hell hA X Y W pX pY sq M
    let κ := kvKappa A D ell hell hA X Y W pX pY sq M N
    ((β_ B U).hom ≫ MonoidalClosed.uncurry κ = e ≫ a) ∧
    ((κ ⊗ₘ 𝟙 U) ≫ kvRightEvaluation A W.obj.left U Q = e ≫ a) ∧
    (∀ (M' : Ctf A X.obj.left) (v : M ⟶ M'),
      let b := (P (coefficient A) pX.hom.left).map v.hom ⊗ₘ 𝟙 _
      let q := ((kvExceptional A D ell hell hA X W pX).map v).hom
      (b ≫ kvKappa A D ell hell hA X Y W pX pY sq M' N = κ ≫ (ihom U).map q) ∧
      ((b ⊗ₘ 𝟙 U) ≫ kvExternalEvaluation A D ell hell hA X Y W pX pY M' N ≫
        kvAlpha A D ell hell hA X Y W pX pY sq M' = e ≫ a ≫ q)) ∧
    (∀ (N' : Ctf A Y.obj.left) (w : N' ⟶ N),
      let b := 𝟙 ((P (coefficient A) pX.hom.left).obj M.obj) ⊗ₘ
        (P (coefficient A) pY.hom.left).map
          ((verdierDual A D ell hell hA Y.obj).map w.op)
      let w' := (P (coefficient A) pY.hom.left).map w.hom
      (b ≫ kvKappa A D ell hell hA X Y W pX pY sq M N' =
        κ ≫ (MonoidalClosed.pre w').app Q) ∧
      ((b ⊗ₘ 𝟙 _) ≫ kvExternalEvaluation A D ell hell hA X Y W pX pY M N' ≫ a =
        (𝟙 B ⊗ₘ w') ≫ e ≫ a)) := by
  sorry

end WeilConjectures.FiniteRingTrace
