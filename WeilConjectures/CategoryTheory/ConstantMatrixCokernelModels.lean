/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantFiniteFreePresentationExtension
public import WeilConjectures.CategoryTheory.SiteConstantModuleHomSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIsoSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherenceSupplement
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarDualEvaluationDescent
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.CategoryTheory.ConstantScalarCokernel
import all WeilConjectures.CategoryTheory.ConstantFiniteFreePresentationExtension
import all WeilConjectures.CategoryTheory.SiteConstantModuleHomSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIsoSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import all Mathlib.Algebra.Category.ModuleCat.Products
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherenceSupplement
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarDualEvaluationDescent

/-! # Transport of normalized matrix cokernels to constant scalar models

Source: Stacks Project, Tags 03CY, 03EI and 03EK; Bhatt--Scholze,
Proposition 6.8.14(2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
universe u v
open CategoryTheory CategoryTheory.Limits SheafOfModules
namespace CategoryTheory.ConstantFiniteFreePresentationExtension

variable {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Type (max u v)) [CommRing R]
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [HasWeakSheafify J RingCat.{max u v}]
    [HasWeakSheafify J CommRingCat.{max u v}]
    (B : Sheaf J CommRingCat.{max u v})
    (σ : (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of R) ⟶ B)

local notation "Pow" =>
  (power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
local notation "Real" => (extension J R B σ)
local notation "cs" => (fun U x ↦ σ.hom.app U
  ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app U x))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] [HasWeakSheafify J RingCat.{max u v}] in
private theorem matrixMap_matrix (m n : ℕ) (D : Matrix (Fin n) (Fin m) R)
    (U : Cᵒᵖ) (x : (Pow m).val.obj U) (i : Fin n) :
    commCoordinate J B n U ((matrixMap J R B σ m n
      (ModuleCat.ofHom (Matrix.toLin' D))).val.app U x) i =
        ∑ j : Fin m, cs U (D i j) * commCoordinate J B m U x j := by
  refine (matrixMap_apply J R B σ m n
    (ModuleCat.ofHom (Matrix.toLin' D)) U x i).trans ?_
  apply Finset.sum_congr rfl
  intro j _
  simp only [ModuleCat.hom_ofHom, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  exact congrArg (· * commCoordinate J B m U x j)
    (scalarRingUnit_apply J R B σ U (D i j))

omit [HasWeakSheafify J RingCat.{max u v}] in
private theorem beta_generator (n : ℕ) (U : Cᵒᵖ) (x : Fin n → R) (i : Fin n) :
    commCoordinate J B n U ((beta J R B σ n).hom.val.app U
      (scalarConstantGenerator J R B σ (ModuleCat.of R (Fin n → R)) U 1 x)) i =
        cs U (x i) := by
  change coordinate J _ n U ((betaHom J R B σ n).val.app U
    (scalarExtensionRingIsoTmul σ _ U
      ((constantModuleHomUnit J R (ModuleCat.of R (Fin n → R))).app U x) 1)) i = _
  rw [betaHom_tmul, alpha_unit, one_mul]
  exact scalarRingUnit_apply J R B σ U (x i)

private def matrixIso (n : ℕ) (P : Matrix.GeneralLinearGroup (Fin n) R) : Pow n ≅ Pow n :=
  (beta J R B σ n).symm ≪≫
    (extensionFunctor J R B σ).mapIso
      (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv.toModuleIso ≪≫ beta J R B σ n

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] [HasWeakSheafify J RingCat.{max u v}] in
private theorem matrixIso_hom (n : ℕ) (P : Matrix.GeneralLinearGroup (Fin n) R)
    (U : Cᵒᵖ) (x : (Pow n).val.obj U) (i : Fin n) :
    commCoordinate J B n U ((matrixIso J R B σ n P).hom.val.app U x) i =
      ∑ j : Fin n, cs U ((P : Matrix (Fin n) (Fin n) R) i j) *
        commCoordinate J B n U x j := by
  exact matrixMap_matrix J R B σ n n (P : Matrix (Fin n) (Fin n) R) U x i

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] [HasWeakSheafify J RingCat.{max u v}] in
private theorem matrixIso_inv (n : ℕ) (P : Matrix.GeneralLinearGroup (Fin n) R)
    (U : Cᵒᵖ) (x : (Pow n).val.obj U) (i : Fin n) :
    commCoordinate J B n U ((matrixIso J R B σ n P).inv.val.app U x) i =
      ∑ j : Fin n, cs U ((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) R) i j) *
        commCoordinate J B n U x j := by
  exact matrixMap_matrix J R B σ n n
    ((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) U x i

-- The CommRing sheafification instance occurs in the section parameter σ;
-- `omit` rejects removing it even though the elaborated lemma needs no such instance.
set_option linter.unusedSectionVars false in
omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] [HasWeakSheafify J RingCat.{max u v}] in
private theorem matrixMap_tail (n r : ℕ) (t : Fin r → Fin n)
    (U : Cᵒᵖ) (x : (Pow n).val.obj U) (j : Fin r) :
    commCoordinate J B r U ((matrixMap J R B σ n r
      (ModuleCat.ofHom (LinearMap.funLeft R R t))).val.app U x) j =
        commCoordinate J B n U x (t j) := by
  refine (matrixMap_apply J R B σ n r
    (ModuleCat.ofHom (LinearMap.funLeft R R t)) U x j).trans ?_
  simp [Pi.single_apply]

/-- A normalized ordinary matrix cokernel and any prescribed tail quotient transport
to the constant scalar model. The quotient generators and all invertible matrix
coordinates are retained. Source: Stacks Project, Tags 03EI and 03EK;
Bhatt--Scholze, Proposition 6.8.14(2).
(blueprint: lem-per-constant-matrix-cokernel-models).

Proof: Conjugate realization of the relation matrix by the normalized finite-power
isomorphisms beta. Realization preserves its cokernel, so realization of the given
ordinary quotient and its specified cokernel isomorphism gives the sheaf quotient.
The beta tensor formula and naturality on constant generators give the quotient
formula. Realize each invertible matrix and its inverse and conjugate by beta.
For a supplied ordinary cokernel identification whose projection is a row operation
followed by coordinate extraction, functoriality carries that equation to sheaves.
The matrix coordinate formula for coordinate extraction is precisely the stated
tail equation. Every step includes empty powers and empty extracted coordinate sets. -/
theorem constantMatrixCokernelModels
    (V : ModuleCat.{max u v} R) (m n : ℕ) (D : Matrix (Fin n) (Fin m) R)
    (p : ModuleCat.of R (Fin n → R) ⟶ V)
    (a₀ : V ≅ cokernel (ModuleCat.ofHom (Matrix.toLin' D)))
    (hp : p ≫ a₀.hom = cokernel.π (ModuleCat.ofHom (Matrix.toLin' D))) :
    ∃ (dB : Pow m ⟶ Pow n) (pB : Pow n ⟶ Real V)
      (w : Real V ≅ cokernel dB),
      pB ≫ w.hom = cokernel.π dB ∧
      (∀ (U : Cᵒᵖ) (x : (Pow m).val.obj U) (i : Fin n),
        commCoordinate J B n U (dB.val.app U x) i =
          ∑ j : Fin m, cs U (D i j) * commCoordinate J B m U x j) ∧
      (∀ (U : Cᵒᵖ) (x : Fin n → R), ∃ y : (Pow n).val.obj U,
        (∀ i : Fin n, commCoordinate J B n U y i = cs U (x i)) ∧
        pB.val.app U y = scalarConstantGenerator J R B σ V U 1 (p x)) ∧
      (∀ (r : ℕ) (t : Fin r → Fin n)
        (P : Matrix.GeneralLinearGroup (Fin n) R)
        (Q : Matrix.GeneralLinearGroup (Fin m) R)
        (a : cokernel (ModuleCat.ofHom (Matrix.toLin' D)) ≅
          ModuleCat.of R (Fin r → R)),
        (∀ (x : Fin n → R) (j : Fin r),
          a.hom (cokernel.π (ModuleCat.ofHom (Matrix.toLin' D)) x) j =
            (P : Matrix (Fin n) (Fin n) R).mulVec x (t j)) →
        ∃ (p' : Pow n ≅ Pow n) (q' : Pow m ≅ Pow m)
          (b : cokernel dB ≅ Pow r),
          (∀ (U : Cᵒᵖ) (x : (Pow n).val.obj U) (i : Fin n),
            commCoordinate J B n U (p'.hom.val.app U x) i =
              ∑ j : Fin n, cs U (P i j) * commCoordinate J B n U x j) ∧
          (∀ (U : Cᵒᵖ) (x : (Pow n).val.obj U) (i : Fin n),
            commCoordinate J B n U (p'.inv.val.app U x) i =
              ∑ j : Fin n, cs U ((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) R) i j) *
                commCoordinate J B n U x j) ∧
          (∀ (U : Cᵒᵖ) (x : (Pow m).val.obj U) (i : Fin m),
            commCoordinate J B m U (q'.hom.val.app U x) i =
              ∑ j : Fin m, cs U (Q i j) * commCoordinate J B m U x j) ∧
          (∀ (U : Cᵒᵖ) (x : (Pow m).val.obj U) (i : Fin m),
            commCoordinate J B m U (q'.inv.val.app U x) i =
              ∑ j : Fin m, cs U ((Q⁻¹ : Matrix.GeneralLinearGroup (Fin m) R) i j) *
                commCoordinate J B m U x j) ∧
          (∀ (U : Cᵒᵖ) (x : (Pow n).val.obj U) (j : Fin r),
            commCoordinate J B r U (b.hom.val.app U ((cokernel.π dB).val.app U x)) j =
              commCoordinate J B n U (p'.hom.val.app U x) (t j))) := by
  let F := extensionFunctor J R B σ
  let d := ModuleCat.ofHom (Matrix.toLin' D)
  let dB := matrixMap J R B σ m n d
  obtain ⟨c₀, hc₀⟩ := constantScalarCokernel J R B σ d
  let c : F.obj (cokernel d) ≅ cokernel (F.map d) := c₀
  have hc : F.map (cokernel.π d) ≫ c.hom = cokernel.π (F.map d) := hc₀
  have hp' : p ≫ a₀.hom = cokernel.π d := hp
  let k := cokernel.mapIso (F.map d) dB (beta J R B σ m) (beta J R B σ n)
    (matrixMap_commutes J R B σ m n d)
  let w := F.mapIso a₀ ≪≫ c ≪≫ k
  let pB := (beta J R B σ n).inv ≫ F.map p
  refine ⟨dB, pB, w, ?_, matrixMap_matrix J R B σ m n D, ?_, ?_⟩
  · change (beta J R B σ n).inv ≫ F.map p ≫ F.map a₀.hom ≫ c.hom ≫ k.hom = _
    rw [← F.map_comp_assoc, hp', reassoc_of% hc]
    simp [k]
  · intro U x
    let y := (beta J R B σ n).hom.val.app U
      (scalarConstantGenerator J R B σ (ModuleCat.of R (Fin n → R)) U 1 x)
    refine ⟨y, beta_generator J R B σ n U x, ?_⟩
    have hi := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.val.app U) (beta J R B σ n).hom_inv_id)
      (scalarConstantGenerator J R B σ (ModuleCat.of R (Fin n → R)) U 1 x)
    change (F.map p).val.app U ((beta J R B σ n).inv.val.app U y) = _
    rw [show (beta J R B σ n).inv.val.app U y = _ from hi]
    exact scalarMap_generator J R B σ p U 1 x
  · intro r t P Q a ha
    let b := k.symm ≪≫ c.symm ≪≫ F.mapIso a ≪≫ beta J R B σ r
    refine ⟨matrixIso J R B σ n P, matrixIso J R B σ m Q, b,
      matrixIso_hom J R B σ n P, matrixIso_inv J R B σ n P,
      matrixIso_hom J R B σ m Q, matrixIso_inv J R B σ m Q, ?_⟩
    have he : cokernel.π d ≫ a.hom =
        ModuleCat.ofHom (Matrix.toLin' (P : Matrix (Fin n) (Fin n) R)) ≫
          ModuleCat.ofHom (LinearMap.funLeft R R t) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext j
      exact ha x j
    have hk : cokernel.π dB ≫ k.inv = (beta J R B σ n).inv ≫ cokernel.π (F.map d) := by
      simp [k]
    have hc' : cokernel.π (F.map d) ≫ c.inv = F.map (cokernel.π d) := by
      rw [← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hb : cokernel.π dB ≫ b.hom =
        (matrixIso J R B σ n P).hom ≫
          matrixMap J R B σ n r (ModuleCat.ofHom (LinearMap.funLeft R R t)) := by
      dsimp only [b, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
      rw [reassoc_of% hk, reassoc_of% hc', ← F.map_comp_assoc, he, F.map_comp]
      simp [matrixIso, matrixMap]
      rfl
    intro U x j
    have hh := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.val.app U) hb) x
    change commCoordinate J B r U
      (((cokernel.π dB ≫ b.hom).val.app U) x) j = _
    rw [hh]
    exact matrixMap_tail J R B σ n r t U
      ((matrixIso J R B σ n P).hom.val.app U x) j

end CategoryTheory.ConstantFiniteFreePresentationExtension
