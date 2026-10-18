/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Sheaf.RingTheory.FiniteFreeModuleTowerInverseLimit
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Limits
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Compatible finite-free complex towers

Source: Stacks Project, More on Algebra, Tag 0CQF.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A compatible finite-free complex tower has a finite-free termwise limit.
Source: Stacks Project, Tag 0CQF, compatible-basis calculation in its proof
(blueprint: lem-weil-pbc-finite-free-complex-tower-inverse-limit).

Proof: Choose a finite basis in each degree at level zero. Lift it recursively through
the surjective transitions. Each lifted list is a basis: its reduction is the old basis;
lift the inverse matrix and invert both error matrices by finite geometric sums in the
nilpotent kernel. This proves the assertion also for rank zero. Form the complex of
compatible tuples with componentwise operations and differential. In these compatible
bases its term in degree i is a finite power of the compatible scalar tuples, hence a
finite power of A by the given ring-limit universal property. This gives freeness and
finiteness, and the common upper cutoff. The tuple projections have the asserted
universal property. Their adjoint scalar-extension maps send a unit tensor to the tuple
projection. They are isomorphisms in each degree, because in these bases they send each
standard basis vector to the corresponding standard basis vector. The chain equations
then assemble them into the stated complex isomorphisms. -/
theorem exists_finiteFree_complexTower_inverseLimit
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (hsurj : ∀ n, Function.Surjective (φ n))
    (hnil : ∀ n, IsNilpotent (RingHom.ker (φ n)))
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1)))
    (hlim : ∀ x : ∀ n, R n, (∀ n, φ n (x (n + 1)) = x n) →
      ∃! a : A, ∀ n, q n a = x n)
    (Pₙ : ∀ n, CochainComplex (ModuleCat.{max u v} (R n)) ℤ)
      (b : ℤ)
      (uₙ : ∀ n, Pₙ (n + 1) ⟶
        ((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj (Pₙ n))
      (θₙ : ∀ n, ((ModuleCat.extendScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj
        (Pₙ (n + 1)) ≅ Pₙ n)
    (hbound : ∀ n, (Pₙ n).IsStrictlyLE b)
    (hterms : ∀ n i, Module.Free (R n) ((Pₙ n).X i) ∧
      Module.Finite (R n) ((Pₙ n).X i))
    (hsurju : ∀ n i, Function.Surjective ((uₙ n).f i))
    (hθₙ : ∀ n i, (ModuleCat.extendRestrictScalarsAdj (φ n)).homEquiv
      ((Pₙ (n + 1)).X i) ((Pₙ n).X i) ((θₙ n).hom.f i) = (uₙ n).f i) :
    ∃ (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
      (p : ∀ n, P ⟶
        ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).obj (Pₙ n))
      (θ : ∀ n, ((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P ≅ Pₙ n),
      P.IsStrictlyLE b ∧
      (∀ i, Module.Free A (P.X i) ∧ Module.Finite A (P.X i)) ∧
      (∀ n i (y : P.X i), (uₙ n).f i ((p (n + 1)).f i y) = (p n).f i y) ∧
      (∀ i (x : ∀ n, (Pₙ n).X i), (∀ n, (uₙ n).f i (x (n + 1)) = x n) →
        ∃! y : P.X i, ∀ n, (p n).f i y = x n) ∧
      (∀ n i, (ModuleCat.extendRestrictScalarsAdj (q n)).homEquiv
        (P.X i) ((Pₙ n).X i) ((θ n).hom.f i) = (p n).f i) := by
  classical
  let s := fun n ↦
    ((ModuleCat.restrictScalars (q (n + 1))).mapHomologicalComplex (.up ℤ)).map (uₙ n) ≫
      (NatIso.mapHomologicalComplex
        (ModuleCat.restrictScalarsComp' (q (n + 1)) (φ n) (q n) (hq n))
        (.up ℤ)).inv.app (Pₙ n)
  let S := Functor.ofOpSequence
    (X := fun n ↦ ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).obj
      (Pₙ n)) s
  have hs (n : ℕ) : S.map (homOfLE (Nat.le_succ n)).op = s n := by
    dsimp [S]
    exact Functor.ofOpSequence_map_homOfLE_succ
      (X := fun n ↦ ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).obj
        (Pₙ n)) s n
  let c := HomologicalComplex.coneOfHasLimitEval S
  let P : CochainComplex (ModuleCat.{max u v} A) ℤ := c.pt
  let p := fun n ↦ c.π.app ⟨n⟩
  have hp : ∀ n i (y : P.X i), (uₙ n).f i ((p (n + 1)).f i y) = (p n).f i y := by
    intro n i y
    have hw := c.w (homOfLE (Nat.le_succ n)).op
    rw [hs] at hw
    have h := congrArg (fun f ↦ (f.f i).hom y) hw
    change (uₙ n).f i ((p (n + 1)).f i y) = (p n).f i y at h
    exact h
  have hP : ∀ i (x : ∀ n, (Pₙ n).X i),
      (∀ n, (uₙ n).f i (x (n + 1)) = x n) →
        ∃! y : P.X i, ∀ n, (p n).f i y = x n := by
    intro i x hx
    let D := S ⋙ HomologicalComplex.eval _ _ i ⋙ forget (ModuleCat A)
    let πx : (Functor.const ℕᵒᵖ).obj PUnit ⟶ D :=
      NatTrans.ofOpSequence (fun n ↦ ↾fun _ ↦ x n) (by
        intro n
        simp only [Functor.const_obj_map, D, Functor.comp_map, hs]
        ext y
        change x n = (uₙ n).f i (x (n + 1))
        exact (hx n).symm)
    have hx' : (fun n : ℕᵒᵖ ↦ x n.unop) ∈ D.sections := by
      intro j k f
      exact (ConcreteCategory.congr_hom (πx.naturality f) PUnit.unit).symm
    have hi := isLimitOfPreserves (forget (ModuleCat A))
      (isLimitOfPreserves (HomologicalComplex.eval _ _ i)
        (HomologicalComplex.isLimitConeOfHasLimitEval S))
    obtain ⟨y, hy, huniq⟩ := (Types.isLimit_iff _).1 ⟨hi⟩ _ hx'
    exact ⟨y, fun n ↦ hy ⟨n⟩, fun z hz ↦ huniq z (fun n ↦ hz n.unop)⟩
  have hdeg (i : ℤ) : (Module.Free A (P.X i) ∧ Module.Finite A (P.X i)) ∧
      ∀ n, IsIso (((ModuleCat.extendRestrictScalarsAdj (q n)).homEquiv
        (P.X i) ((Pₙ n).X i)).symm ((p n).f i)) := by
    exact ModuleCat.finiteFree_moduleTower_inverseLimit R φ hsurj hnil A q hq hlim
      (fun n ↦ (Pₙ n).X i) (fun n ↦ (uₙ n).f i)
      (fun n ↦ (HomologicalComplex.eval _ _ i).mapIso (θₙ n))
      (fun n ↦ hterms n i) (fun n ↦ hsurju n i) (fun n ↦ hθₙ n i)
      (P.X i) (fun n ↦ (p n).f i) (fun n ↦ hp n i) (hP i)
  have hb : P.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    apply ModuleCat.isZero_iff_subsingleton.mpr
    constructor
    intro y z
    have hzero (n : ℕ) : Subsingleton ((Pₙ n).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp
        ((CochainComplex.isStrictlyLE_iff (Pₙ n) b).mp (hbound n) i hi)
    obtain ⟨a, ha, huniq⟩ := hP i (fun n ↦ (p n).f i z)
      (fun n ↦ hp n i z)
    exact (huniq y (fun n ↦ (hzero n).elim _ _)).trans (huniq z (fun _ ↦ rfl)).symm
  have (n : ℕ) : (ModuleCat.extendScalars (q n)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (q n)).left_adjoint_additive
  let θmap := fun n ↦
    (((ModuleCat.extendRestrictScalarsAdj (q n)).mapHomologicalComplex (.up ℤ)).homEquiv
      P (Pₙ n)).symm (p n)
  have hθmap (n : ℕ) (i : ℤ) : (θmap n).f i =
      ((ModuleCat.extendRestrictScalarsAdj (q n)).homEquiv
        (P.X i) ((Pₙ n).X i)).symm ((p n).f i) := rfl
  have hiso (n : ℕ) : IsIso (θmap n) := by
    have (i : ℤ) : IsIso ((θmap n).f i) := by
      rw [hθmap]
      exact (hdeg i).2 n
    exact HomologicalComplex.Hom.isIso_of_components _
  refine ⟨P, p, fun n ↦ asIso (θmap n), hb, fun i ↦ (hdeg i).1, hp, hP, ?_⟩
  intro n i
  change (ModuleCat.extendRestrictScalarsAdj (q n)).homEquiv _ _ ((θmap n).f i) = _
  rw [hθmap]
  exact Equiv.apply_symm_apply _ _

end DerivedCategory
