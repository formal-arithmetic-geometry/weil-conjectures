/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.Paper.FiniteProjectiveTensorProducts
import Sheaf.Paper.CompletedFiniteReductionTensorComparison
import WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # A strict-perfect tensor model of finite scalar reduction

Source: blueprint order 1249, bounded finite-projective coefficient construction;
Stacks Tags 093J--093M and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

/-- Finite reduction with its completed scalar action is tensor by a bounded complex
whose terms are finite-free retracts. This comparison concerns the entire functor,
independently of any input object or quotient tower.

Source: blueprint order 1249, step 1; Stacks Tags 093J--093M and 06YY
(blueprint: lem-weil-pbc-completed-finite-reduction-tensor-model).
Proof: quotientPerfect supplies a bounded finite-projective A-complex representing
A/I^(n+1). Its bounded-above projective property lifts its derived isomorphism to a
quasi-isomorphism to the quotient in degree zero. Constant module sheafification and
extension from constant A to the completed ring give P. Apply
completed_constant_sheaf_reduction: its augmentation is a quasi-isomorphism, its terms
remain finite-free retracts, and its two bounds persist. Replace the finite coproduct
in each splitting by the canonical finite biproduct product. P is K-flat since it is
bounded and its finite-free retract terms are flat. Tensoring a K-flat input with this
augmentation identifies tensor with P with ordinary extension to the quotient followed
by restriction. These comparisons are natural in maps of K-flat inputs. The universal
left-derived scalar-extension pair and full faithfulness of precomposition with derived
localization descend them to the displayed natural isomorphism. This includes the zero
quotient and zero-fold free summands; the quotient need not itself be flat. -/
theorem completedFiniteReductionTensorModel (n : ℕ) :
    ∃ (P : CochainComplex (adicDatumModules T d) ℤ)
      (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
      (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
        ((adicLisseForget T).obj (adicDatumRing T d)) P),
      Nonempty (adicDatumReductionUnderlying T d n ≅
        finiteProjectiveTensorRight T d P hb p) := by
  classical
  have : IsNoetherianRing A := d.noetherian
  let := HasDerivedCategory.standard (ModuleCat.{t + 1} A)
  obtain ⟨F, a, b, ha, hb, hF, ⟨eF⟩⟩ :=
    d.quotientPerfect (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  have := ha
  have := hb
  have (i : ℤ) : Module.Projective A (F.X i) := (hF i).1
  have (i : ℤ) : Projective (F.X i) := inferInstance
  let Q := (CochainComplex.singleFunctor (ModuleCat.{t + 1} A) 0).obj
    (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1)))
  obtain ⟨q, hq⟩ := DerivedCategory.Q_map_surjective_of_projective F Q b eF.inv
  have : IsIso (DerivedCategory.Q.map q) := by rw [hq]; infer_instance
  have hq' : QuasiIso q :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{t + 1} A) q).mp inferInstance
  have hbound : ∀ i : ℤ, i < a ∨ b < i → IsZero (F.X i) := by
    intro i hi
    rcases hi with hi | hi
    · exact F.isZero_of_isStrictlyGE a i hi
    · exact F.isZero_of_isStrictlyLE b i hi
  obtain ⟨hred, hret, hbounded⟩ :=
    (CompletedConstantReduction.completed_constant_sheaf_reduction T d.ideal).2.2.2
      n F q a b hq' (fun i ↦ ⟨(hF i).2, (hF i).1⟩) hbound
  let P := ((completedAdicChange T
    (CompletedConstantReduction.base T d.ideal)).mapHomologicalComplex
    (.up ℤ)).obj ((CompletedConstantReduction.constantComplex T A).obj F)
  have : HasFiniteBiproducts (adicDatumModules T d) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  choose N i p hip using hret
  let e (j : ℤ) := biproductIso (fun _ : Fin (N j) ↦
    SheafOfModules.unit ((adicLisseForget T).obj (adicDatumRing T d)))
  let pkg : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P :=
    { N := N
      i := fun j ↦ i j ≫ (e j).inv
      p := fun j ↦ (e j).hom ≫ p j
      splitting := fun j ↦ by
        simp only [Category.assoc, Iso.inv_hom_id_assoc, hip]
        rfl }
  let α := CompletedConstantReduction.reductionComplex T d.ideal n
    ((CompletedConstantReduction.constantComplex T A).obj F)
    (CompletedConstantReduction.constantAugmentation T d.ideal n F q)
  exact ⟨P, ⟨a, b, hbounded⟩, pkg,
    completedFiniteReductionTensorComparison T d n P ⟨a, b, hbounded⟩ pkg α hred⟩

end AlgebraicGeometry.Scheme
