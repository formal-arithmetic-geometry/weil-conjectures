/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.Paper.PQFCohomology
import Sheaf.AlgebraicGeometry.AffineModuleCorrespondence
import Sheaf.AlgebraicGeometry.AffineModuleFiniteType
import Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge
import Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum
import Sheaf.AlgebraicGeometry.RelativeSpecBaseChange
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex

/-!
# Finiteness for a compatible graded cohomology action

Source: Stacks Project, Cohomology of Schemes, Lemma 0897
(blueprint: lem-weil-pbc-graded-cohomology-module-finite).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry


/-- The compatible graded cohomology direct sum has a finitely generated top submodule.

Source: Stacks Project, Cohomology of Schemes, Lemma 0897(1), relative-spectrum
proof of finiteness, with the compatible action given as an input.
(blueprint: lem-weil-pbc-graded-cohomology-module-finite-generators).

Proof:
1. Let X' = X times_(Spec A) Spec B, with projection pi to X and f' to Spec B.
Properness is preserved by base change. Since B is finite type over Noetherian A,
B is Noetherian, and the finite-type scheme X' over Spec B is Noetherian. Also X
is quasi-compact and quasi-separated, since it is proper over the affine base.
2. Form the sheaf direct sum F = directSum_m G_m. The homogeneous maps extend by
finite sums to a B-action on F; hmu_add and hmu_mul give additivity and the product
law, and hmu_scalar gives the unit and compatibility with A. On an affine open
Spec C, this is the action of C tensor_A B on directSum_m G_m(Spec C).
Quasi-coherence of each G_m and localization of direct sums show that these
modules glue to a quasi-coherent module over the algebra sheaf f^* B~.
The sections s_i in hfinite generate F over this algebra sheaf locally: their
homogeneous multiples generate each degree by the given span condition, and a
section of a sheaf direct sum is locally a finite sum of homogeneous sections.
The coefficients from O_X are absorbed into f^* B~. Thus F is of finite type.
3. Relative-spec base change identifies X' with Spec_X(f^* B~). The affine module
correspondence realizes F as pi_* F' for a quasi-coherent module F' on X'.
The affine finite-type correspondence makes F' finite type, hence coherent on
the locally Noetherian scheme X'. Proper coherent cohomology finiteness for f'
gives a finite B-module H^p(X', F').
4. The affine cohomology edge isomorphism identifies H^p(X, F) with H^p(X', F').
It intertwines B: for each b, multiplication on F' pushes forward to the
multiplication map on F, and naturality of the edge map gives the commuting
square with these endomorphisms. Since X is qcqs, the canonical direct-sum
cohomology isomorphism identifies directSum_m H^p(X, G_m) with H^p(X, F).
For homogeneous b, its square with the inclusion of G_m has other side mu m k b,
so applying cohomology shows that this isomorphism intertwines exactly the
homogeneous action stated in the hypothesis on mod. Every scalar in B and every
vector are finite sums of homogeneous terms; distributivity therefore makes
the composite isomorphism B-linear for the given mod, not an arbitrary action.
The inverse images of a finite set of B-generators of H^p(X', F') generate the
direct sum, proving Module.Finite for mod.
-/
theorem gradedCohomologyModuleFinite_generators
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (graded : ℕ → Submodule A B)
    (hgrading : DirectSum.IsInternal graded)
    (hunit : (1 : B) ∈ graded 0)
    (hmul : ∀ (k l : ℕ) {x y : B}, x ∈ graded k → y ∈ graded l → x * y ∈ graded (k + l))
    (hscalar : ∀ (a : A), algebraMap A B a ∈ graded 0)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (G : ℕ → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hG : ∀ m : ℕ, (G m).IsQuasicoherent)
    (mu : ∀ (m k : ℕ), graded k → (G m ⟶ G (m + k)))
    (hmu_add : ∀ (m k : ℕ) (b b' : graded k),
      mu m k (b + b') = mu m k b + mu m k b')
    (hmu_mul : ∀ (m k l : ℕ) (b : graded k) (b' : graded l),
      HEq (mu m l b' ≫ mu (m + l) k b)
        (mu m (k + l) ⟨b.val * b'.val, hmul k l b.property b'.property⟩))
    (hmu_scalar : ∀ (m : ℕ) (a : A) (U : X.Opens)
      (t : (G m).val.obj (op U)),
      HEq ((mu m 0 ⟨algebraMap A B a, hscalar a⟩).val.app (op U) t)
        ((X.presheaf.map (homOfLE (le_top (a := U))).op).hom
          (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a) • t))
    (hfinite : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      ∃ (r : ℕ) (d : Fin r → ℕ) (s : ∀ i : Fin r, (G (d i)).val.obj (op U)),
        ∀ (m : ℕ) (V : X.Opens) (hVU : V ≤ U) (t : (G m).val.obj (op V))
          (y : X), y ∈ V → ∃ (W : X.Opens) (hWV : W ≤ V), y ∈ W ∧
            (G m).val.map (homOfLE hWV).op t ∈
              Submodule.span ((moduleRings X.toRingedSpace).obj.obj (op W))
                {z | ∃ (i : Fin r), d i ≤ m ∧
                  ∃ b : graded (m - d i),
                    HEq z ((mu (d i) (m - d i) b).val.app (op W)
                      ((G (d i)).val.map (homOfLE (hWV.trans hVU)).op (s i)))})
    (p : ℕ)
    :
    ∀ (mod : Module B (DirectSum ℕ (fun m =>
      ((RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m) : Type u)))),
      (∀ (k m : ℕ) (b : graded k)
        (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m)),
        @SMul.smul B _ mod.toDistribMulAction.toMulAction.toSemigroupAction.toSMul b.val
          (DirectSum.of (fun n => ((RingedSpace.moduleCohomology
            X.toRingedSpace p).obj (G n) : Type u)) m x) =
        DirectSum.of (fun n =>
          ((RingedSpace.moduleCohomology X.toRingedSpace p).obj (G n) : Type u)) (m + k)
          ((RingedSpace.moduleCohomology X.toRingedSpace p).map (mu m k b) x)) →
      (⊤ : Submodule B (DirectSum ℕ (fun m =>
        ((RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m) : Type u)))).FG := by
  sorry

theorem gradedCohomologyModuleFinite
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (graded : ℕ → Submodule A B)
    (hgrading : DirectSum.IsInternal graded)
    (hunit : (1 : B) ∈ graded 0)
    (hmul : ∀ (k l : ℕ) {x y : B}, x ∈ graded k → y ∈ graded l → x * y ∈ graded (k + l))
    (hscalar : ∀ (a : A), algebraMap A B a ∈ graded 0)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (G : ℕ → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hG : ∀ m : ℕ, (G m).IsQuasicoherent)
    (mu : ∀ (m k : ℕ), graded k → (G m ⟶ G (m + k)))
    (hmu_add : ∀ (m k : ℕ) (b b' : graded k),
      mu m k (b + b') = mu m k b + mu m k b')
    (hmu_mul : ∀ (m k l : ℕ) (b : graded k) (b' : graded l),
      HEq (mu m l b' ≫ mu (m + l) k b)
        (mu m (k + l) ⟨b.val * b'.val, hmul k l b.property b'.property⟩))
    (hmu_scalar : ∀ (m : ℕ) (a : A) (U : X.Opens)
      (t : (G m).val.obj (op U)),
      HEq ((mu m 0 ⟨algebraMap A B a, hscalar a⟩).val.app (op U) t)
        ((X.presheaf.map (homOfLE (le_top (a := U))).op).hom
          (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a) • t))
    (hfinite : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      ∃ (r : ℕ) (d : Fin r → ℕ) (s : ∀ i : Fin r, (G (d i)).val.obj (op U)),
        ∀ (m : ℕ) (V : X.Opens) (hVU : V ≤ U) (t : (G m).val.obj (op V))
          (y : X), y ∈ V → ∃ (W : X.Opens) (hWV : W ≤ V), y ∈ W ∧
            (G m).val.map (homOfLE hWV).op t ∈
              Submodule.span ((moduleRings X.toRingedSpace).obj.obj (op W))
                {z | ∃ (i : Fin r), d i ≤ m ∧
                  ∃ b : graded (m - d i),
                    HEq z ((mu (d i) (m - d i) b).val.app (op W)
                      ((G (d i)).val.map (homOfLE (hWV.trans hVU)).op (s i)))})
    (p : ℕ)
    :
    ∀ (mod : Module B (DirectSum ℕ (fun m => ((RingedSpace.moduleCohomology
      X.toRingedSpace p).obj (G m) : Type u)))),
      (∀ (k m : ℕ) (b : graded k)
        (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m)),
        @SMul.smul B _ mod.toDistribMulAction.toMulAction.toSemigroupAction.toSMul b.val
          (DirectSum.of (fun n => ((RingedSpace.moduleCohomology
            X.toRingedSpace p).obj (G n) : Type u)) m x) =
        DirectSum.of (fun n => ((RingedSpace.moduleCohomology
          X.toRingedSpace p).obj (G n) : Type u)) (m + k)
          ((RingedSpace.moduleCohomology X.toRingedSpace p).map (mu m k b) x)) →
      @Module.Finite B _ _ _ mod     := by
  intro mod hcompat
  let htop : Module.Finite B (⊤ : Submodule B
      (DirectSum ℕ (fun m => ((RingedSpace.moduleCohomology X.toRingedSpace p).obj
        (G m) : Type u)))) :=
    Module.Finite.iff_fg.mpr (gradedCohomologyModuleFinite_generators
      graded hgrading hunit hmul hscalar f G hG mu hmu_add hmu_mul hmu_scalar hfinite p mod hcompat)
  have hsurj : Function.Surjective (Submodule.subtype (⊤ : Submodule B (DirectSum ℕ (fun m =>
      ((RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m) : Type u)))) ) := by
    intro x
    exact ⟨⟨x, trivial⟩, rfl⟩
  exact Module.Finite.of_surjective (Submodule.subtype (⊤ : Submodule B (DirectSum ℕ (fun m =>
      ((RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m) : Type u)))) ) hsurj
end AlgebraicGeometry
