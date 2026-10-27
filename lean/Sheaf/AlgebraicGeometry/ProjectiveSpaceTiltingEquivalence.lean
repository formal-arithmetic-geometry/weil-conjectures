/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.AlgebraicGeometry.PerfectObjectCompact
import WeilConjectures.AlgebraicGeometry.PerfectRHomTensorComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre

/-! # Projective-space tilting equivalence

Source: Stacks Project, perfect.tex, Tag 0BQU and equations 0CS8 and 0CS9;
dga.tex, Tags 09LX and 09LY (blueprint: lem-sfb-projective-space-tilting-equivalence).

## Main definitions and statement

* `tiltingBundle`: the finite direct sum of negative twists on projective space.
* `tiltingBaseScalars`, `tiltingScalarsCompatible`: the structural A-action.
* `tiltingGlobalHom`: the shared global derived Hom restricted to A.
* `tiltingEquivalenceStatement`: matrix identification and specified derived equivalence.
* `projectiveSpace_tilting_equivalence`: all clauses of Stacks 0BQU and its Hom inverse.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u wX wB wA wG

open CategoryTheory CategoryTheory.Limits Opposite

open scoped ModuleCat.Algebra

namespace AlgebraicGeometry.ProjectiveSpace

/-- Projective space over Spec A, in the model of the recorded twist dependency.
Source: Stacks, Tag 0BQU (blueprint: lem-sfb-projective-space-tilting-equivalence). -/
abbrev tiltingSpace (A : Type u) [CommRing A] (n : ℕ) : Scheme.{u} :=
  ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A))

/-- The actual finite direct sum O ⊕ O(-1) ⊕ ... ⊕ O(-n).
Source: Stacks, equation 0CS8 (blueprint: lem-sfb-projective-space-tilting-equivalence). -/
def tiltingBundle (A : Type u) [CommRing A] (n : ℕ) :
    SheafOfModules.{u} (moduleRings (tiltingSpace A n).toRingedSpace) :=
  ∐ (fun i : Fin (n + 1) ↦
    (twist (ULift.{u} (Fin (n + 1))) (Spec (.of A)) (-(i.val : ℤ)) :
      SheafOfModules.{u} (moduleRings (tiltingSpace A n).toRingedSpace)))

/-- The structural homomorphism A → Γ(Pⁿ_A, O).
Source: Stacks, Tag 0BQU (blueprint: lem-sfb-projective-space-tilting-equivalence). -/
def tiltingBaseScalars (A : Type u) [CommRing A] (n : ℕ) :
    A →+* (moduleRings (tiltingSpace A n).toRingedSpace).obj.obj (op ⊤) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫
    (tiltingSpace A n ↘ Spec (.of A)).appTop).hom

/-- Additivity of the existing balanced tensor, from its existing tensor-Hom adjunction.
Source: Stacks, Tag 09LX (blueprint: lem-sfb-projective-space-tilting-equivalence). -/
instance tiltingTensor_additive (A : Type u) [CommRing A] (n : ℕ) :
    (IsGrothendieckAbelian.tensorObj (tiltingBundle A n)).Additive :=
  (IsGrothendieckAbelian.tensorObjPreadditiveCoyonedaObjAdjunction
    (tiltingBundle A n)).left_adjoint_additive

/-- The structural A-action on sheaf morphisms, specified sectionwise rather than chosen
arbitrarily. Source: Stacks, Tag 0BQU
(blueprint: lem-sfb-projective-space-tilting-equivalence). -/
def tiltingScalarsCompatible (A : Type u) [CommRing A] (n : ℕ)
    [linearInst : Linear A
      (SheafOfModules.{u} (moduleRings (tiltingSpace A n).toRingedSpace))] : Prop :=
  ∀ (M N : SheafOfModules.{u} (moduleRings (tiltingSpace A n).toRingedSpace))
    (a : A) (f : M ⟶ N),
    a • f = f ≫ @id (N ⟶ N)
      (Scheme.Modules.smulHom (X := tiltingSpace A n) N (tiltingBaseScalars A n a))

/-- The shared global derived Hom from T, restricted from Γ(Pⁿ_A,O) to A.
Source: Stacks, Tags 0BQU and 09LY
(blueprint: lem-sfb-projective-space-tilting-equivalence). -/
def tiltingGlobalHom (A : Type u) [CommRing A] (n : ℕ)
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (tiltingSpace A n).toRingedSpace))]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wG} (ModuleCat.{u}
      ((moduleRings (tiltingSpace A n).toRingedSpace).obj.obj (op ⊤)))] :
    schemeDerivedQCohCategory (tiltingSpace A n) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (Functor.const _).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj (tiltingBundle A n))) |>.prod'
    (schemeDerivedQCohProperty (tiltingSpace A n)).ι |>.comp
    (schemeGlobalDerivedHom (tiltingSpace A n) ⋙
      (ModuleCat.restrictScalars (tiltingBaseScalars A n)).mapDerivedCategory)

/-- All clauses of the tilting assertion, with the A-linear structure supplied separately
and constrained by `tiltingScalarsCompatible`. The matrix image condition is an algebra
identification: the injective algebra map has exactly the displayed homogeneous upper
triangular matrices as its image. The left-derived universal property is imposed on the
specified ordinary tensor, and the inverse retains its right action through coyoneda.
Source: Stacks, Tag 0BQU, equation 0CS9 and Tags 09LX, 09LY
(blueprint: lem-sfb-projective-space-tilting-equivalence). -/
def tiltingEquivalenceStatement (A : Type u) [CommRing A] (n : ℕ)
    [linearInst : Linear A
      (SheafOfModules.{u} (moduleRings (tiltingSpace A n).toRingedSpace))]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (tiltingSpace A n).toRingedSpace))]
    [HasDerivedCategory.{wB} (ModuleCat.{u} (End (tiltingBundle A n))ᵐᵒᵖ)]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wG} (ModuleCat.{u}
      ((moduleRings (tiltingSpace A n).toRingedSpace).obj.obj (op ⊤)))] : Prop :=
  (∃ rho : End (tiltingBundle A n) →ₐ[A]
      Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (ULift.{u} (Fin (n + 1))) A),
    Function.Injective rho ∧ ∀ m,
      (∃ b, rho b = m) ↔ ∀ i j,
        if i ≤ j then (m i j).IsHomogeneous (j.val - i.val) else m i j = 0) ∧
  ∃ e : DerivedCategory (ModuleCat.{u} (End (tiltingBundle A n))ᵐᵒᵖ) ≌
      schemeDerivedQCohCategory (tiltingSpace A n),
    e.functor.Linear A ∧
    Nonempty (e.inverse ≅ (schemeDerivedQCohProperty (tiltingSpace A n)).ι ⋙
      (preadditiveCoyonedaObj (tiltingBundle A n)).rightDerivedFunctor) ∧
    Nonempty (e.inverse ⋙
      (ModuleCat.restrictScalars (algebraMap A (End (tiltingBundle A n))ᵐᵒᵖ)).rightDerivedFunctor ≅
        tiltingGlobalHom A n) ∧
    (∃ eps : DerivedCategory.Qh ⋙
        (e.functor ⋙ (schemeDerivedQCohProperty (tiltingSpace A n)).ι) ⟶
        (IsGrothendieckAbelian.tensorObj (tiltingBundle A n)).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh,
      (e.functor ⋙ (schemeDerivedQCohProperty (tiltingSpace A n)).ι).IsLeftDerivedFunctor
        eps (HomotopyCategory.quasiIso _ (.up ℤ))) ∧
    (∃ s : (e.functor ⋙ (schemeDerivedQCohProperty (tiltingSpace A n)).ι).CommShift ℤ,
      @Functor.IsTriangulated _ _ _ _ _ _
        (e.functor ⋙ (schemeDerivedQCohProperty (tiltingSpace A n)).ι) s _ _ _ _ _ _ _ _) ∧
    ∀ K : schemeDerivedQCohCategory (tiltingSpace A n),
      ∃ M : DerivedCategory (ModuleCat.{u} (End (tiltingBundle A n))ᵐᵒᵖ),
        Nonempty (e.functor.obj M ≅ K) ∧
        Nonempty
          (((ModuleCat.restrictScalars
              (algebraMap A (End (tiltingBundle A n))ᵐᵒᵖ)).rightDerivedFunctor).obj M ≅
            (tiltingGlobalHom A n).obj K)

/-- The projective-space tilting equivalence, its matrix algebra and global-Hom inverse.
Source: Stacks Project, perfect.tex, Tag 0BQU, equations 0CS8 and 0CS9;
dga.tex, Tags 09LX and 09LY
(blueprint: lem-sfb-projective-space-tilting-equivalence).

Proof:
1. On each standard affine, every twist is free of rank one, so T is a vector bundle
and perfect. The finite standard cover and its affine overlaps make projective space
quasi-compact and quasi-separated. By lem-pc-perfect-object-compact T is compact in
D_QCoh, and lem-sfb-projective-negative-twists-generator makes it a generator.
2. The twist pairing (lem-pc-twist-tensor) and perfect duality
(lem-pc-perfect-rhom-tensor-comparison) reduce self-Ext to the cohomology of O(j-i).
By lem-pc-projective-space-twist-cohomology it vanishes in every nonzero degree:
-n ≤ j-i ≤ n excludes the top-degree negative monomials. For n=0 use the affine
clause. Degree zero gives S_(j-i) for i≤j, zero otherwise. Composition is polynomial
matrix multiplication, with (i,j) = Hom(O(-j),O(-i)).
3. The bundle-endomorphism derived adjunction
(lem-sfb-bundle-endomorphism-derived-adjunction) constructs the unbounded left derived
functor of the ordinary balanced tensor and its right adjoint, retaining the right
B-action by precomposition. Its A-restriction is the shared global derived Hom.
Compactness and self-Ext vanishing imply full faithfulness by
lem-sfb-compact-bundle-self-ext-full-faithfulness.
4. If the right adjoint kills K, all Hom(T,K[q]) vanish. The generator lemma forces
K=0; lem-sfb-exact-adjoint-zero-kernel-equivalence then makes both unit and counit
invertible. The constructions preserve the structural A-action and triangles.
For the final clause choose M to be the inverse image of K; the counit and the
natural global-Hom comparison give the two asserted isomorphisms. -/
theorem projectiveSpace_tilting_equivalence (A : Type u) [CommRing A] (n : ℕ)
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (tiltingSpace A n).toRingedSpace))]
    [HasDerivedCategory.{wB} (ModuleCat.{u} (End (tiltingBundle A n))ᵐᵒᵖ)]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wG} (ModuleCat.{u}
      ((moduleRings (tiltingSpace A n).toRingedSpace).obj.obj (op ⊤)))] :
    ∃ linearInst : Linear A
        (SheafOfModules.{u} (moduleRings (tiltingSpace A n).toRingedSpace)),
      tiltingScalarsCompatible (linearInst := linearInst) A n ∧
      tiltingEquivalenceStatement (linearInst := linearInst) A n := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
