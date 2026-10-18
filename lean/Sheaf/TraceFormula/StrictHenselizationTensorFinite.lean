/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.RingTheory.FiniteRingMapQuasiFinite
import Sheaf.TraceFormula.StrictHenselizationQuasiFiniteRing
import WeilConjectures.RingTheory.ProEtale.IntegralLocal

/-!
# Tensor compatibility of strict henselizations for a finite map

Source: Stacks Project, Algebra, Tag 0GIP,
lemma `lemma-base-change-strict-henselization-quasi-finite`,
case (1) (blueprint: lem-trf-strict-henselization-tensor-finite).
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option linter.defProp false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct

/-- The ring homomorphism induced by the canonical pointed strict-local map.
Source: Stacks Project, Algebra, Tag 04GU
(blueprint: lem-weil-pbc-strict-henselization-functoriality).
The strict-local map is transported across the affine spectrum--global-sections equivalences. -/
noncomputable def strictHenselizationRingMap
    {X S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (f : X ⟶ S) (x : Spec (.of Ω) ⟶ X) :
    strictHenselizationRing (x ≫ f) →+* strictHenselizationRing x :=
  ((ΓSpecIso (strictHenselizationRing (x ≫ f))).inv ≫
    (Scheme.Γ.map (strictHenselizationMap f x).op) ≫
    (ΓSpecIso (strictHenselizationRing x)).hom).hom

/-- Transport a canonical strict-local map across an equality of pointed maps.
Source: Stacks Project, Algebra, Tags 04GU and 08HV
(blueprint: lem-weil-pbc-strict-henselization-functoriality).
-/
noncomputable def strictHenselizationRingMapEq
    {X S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (f : X ⟶ S) (x : Spec (.of Ω) ⟶ X)
    {y : Spec (.of Ω) ⟶ S} (h : x ≫ f = y) :
    strictHenselizationRing y →+* strictHenselizationRing x :=
  (eqToHom (congrArg strictHenselizationRing h.symm) ≫
    CommRingCat.ofHom (strictHenselizationRingMap f x)).hom

/-- The ring tensor product with its algebra structures induced by two ring maps.
Source: Stacks Project, Algebra, Tags 00CV and 00CX
(blueprint: def-weil-pbc-module-tensor-product).
-/
noncomputable abbrev strictTensorRing
    {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
    (f : R →+* B) (g : R →+* C) : CommRingCat := by
  letI : Algebra R B := f.toAlgebra
  letI : Algebra R C := g.toAlgebra
  exact CommRingCat.of (B ⊗[R] C)

/-- The left tensor-factor inclusion for `strictTensorRing`.
Source: Stacks Project, Algebra, Tags 00CV and 00CX
(blueprint: def-weil-pbc-module-tensor-product).
-/
noncomputable abbrev strictTensorLeft
    {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
    (f : R →+* B) (g : R →+* C) : B →+* (strictTensorRing f g) := by
  letI : Algebra R B := f.toAlgebra
  letI : Algebra R C := g.toAlgebra
  change B →+* (B ⊗[R] C)
  exact (Algebra.TensorProduct.includeLeft (R := R) (S := R)
    (A := B) (B := C)).toRingHom

/-- The right tensor-factor inclusion for `strictTensorRing`.
Source: Stacks Project, Algebra, Tags 00CV and 00CX
(blueprint: def-weil-pbc-module-tensor-product).
-/
noncomputable abbrev strictTensorRight
    {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
    (f : R →+* B) (g : R →+* C) : C →+* (strictTensorRing f g) := by
  letI : Algebra R B := f.toAlgebra
  letI : Algebra R C := g.toAlgebra
  change C →+* (B ⊗[R] C)
  exact (Algebra.TensorProduct.includeRight (R := R) (A := B)
    (B := C)).toRingHom

/-- The pure tensor used to express compatibility with the chosen geometric point.
Source: Stacks Project, Algebra, Tags 00CV and 00CX
(blueprint: def-weil-pbc-module-tensor-product).
-/
noncomputable abbrev strictTensorTmul
    {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
    (f : R →+* B) (g : R →+* C) (b : B) (c : C) : strictTensorRing f g := by
  letI : Algebra R B := f.toAlgebra
  letI : Algebra R C := g.toAlgebra
  exact TensorProduct.tmul R b c

/-- The geometric point induced on `Spec B` by a point of `Spec (B ⊗[A] C)`.
Source: Stacks Project, Algebra, Tag 0GIP (blueprint: lem-trf-strict-henselization-tensor-finite).
-/
noncomputable def strictTensorPointB
    {A B C Ω : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of (B ⊗[A] C))) :
    Spec (.of Ω) ⟶ Spec (.of B) :=
  s ≫ Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeft (R := A) (S := A)
      (A := B) (B := C)).toRingHom)

/-- The geometric point induced on `Spec C` by a point of `Spec (B ⊗[A] C)`.
Source: Stacks Project, Algebra, Tag 0GIP (blueprint: lem-trf-strict-henselization-tensor-finite).
-/
noncomputable def strictTensorPointC
    {A B C Ω : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of (B ⊗[A] C))) :
    Spec (.of Ω) ⟶ Spec (.of C) :=
  s ≫ Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := A) (A := B)
      (B := C)).toRingHom)

/-- The geometric point induced on `Spec A` by a point of `Spec (B ⊗[A] C)`.
Source: Stacks Project, Algebra, Tag 0GIP (blueprint: lem-trf-strict-henselization-tensor-finite).
-/
noncomputable def strictTensorPointA
    {A B C Ω : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of (B ⊗[A] C))) :
    Spec (.of Ω) ⟶ Spec (.of A) :=
  strictTensorPointB s ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))

/-- The two induced maps to `Spec A` agree by the tensor-product identities.
Source: Stacks Project, Algebra, Tag 0GIP (blueprint: lem-trf-strict-henselization-tensor-finite).
-/
noncomputable def strictTensorPointCBaseEq
    {A B C Ω : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of (B ⊗[A] C))) :
    strictTensorPointC s ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) =
      strictTensorPointA s := by
  dsimp [strictTensorPointC, strictTensorPointA, strictTensorPointB]
  rw [Category.assoc, Category.assoc]
  apply congrArg (fun k => s ≫ k)
  rw [← AlgebraicGeometry.Spec.map_comp]
  rw [← AlgebraicGeometry.Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  simp

/-- Canonical strict-local maps for the four structure maps in the tensor square.
Source: Stacks Project, Algebra, Tags 04GU and 0GIP
(blueprint: lem-trf-strict-henselization-tensor-finite).
-/
noncomputable def strictTensorMapAB
    {A B C Ω : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of (B ⊗[A] C))) :
    strictHenselizationRing (strictTensorPointA s) →+*
      strictHenselizationRing (strictTensorPointB s) :=
  strictHenselizationRingMap
    (Spec.map (CommRingCat.ofHom (algebraMap A B))) (strictTensorPointB s)

noncomputable def strictTensorMapAC
    {A B C Ω : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of (B ⊗[A] C))) :
    strictHenselizationRing (strictTensorPointA s) →+*
      strictHenselizationRing (strictTensorPointC s) :=
  strictHenselizationRingMapEq
    (Spec.map (CommRingCat.ofHom (algebraMap A C))) (strictTensorPointC s)
    (y := strictTensorPointA s) (strictTensorPointCBaseEq s)

noncomputable def strictTensorMapBD
    {A B C Ω : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of (B ⊗[A] C))) :
    strictHenselizationRing (strictTensorPointB s) →+*
      strictHenselizationRing s :=
  strictHenselizationRingMap
    (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft (R := A) (S := A)
        (A := B) (B := C)).toRingHom)) s

noncomputable def strictTensorMapCD
    {A B C Ω : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of (B ⊗[A] C))) :
    strictHenselizationRing (strictTensorPointC s) →+*
      strictHenselizationRing s :=
  strictHenselizationRingMap
    (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := A) (A := B)
        (B := C)).toRingHom)) s

namespace AlgebraicGeometry.Scheme

/-- Tensor compatibility of strict henselizations for a finite ring map.
Source: Stacks Project, Algebra, Tag 0GIP,
lemma `lemma-base-change-strict-henselization-quasi-finite`,
case (1) (blueprint: lem-trf-strict-henselization-tensor-finite).

Proof (to be supplied in stage 3):
1. Apply strict-henselization functoriality to the four affine spectrum maps induced by the
   tensor inclusions and the base map; uniqueness gives the two compatible composites.
2. Finiteness of `A → B` implies finiteness and quasi-finiteness of `C → B ⊗[A] C`.
   The quasi-finite strict-henselization description identifies the two strict henselizations
   with the corresponding localizations of tensor products.
3. The localization formulas identify the source tensor product with a localization of the
   ring for `B ⊗[A] C`; the induced comparison is the canonical map characterized by its
   two tensor-factor inclusions.
4. The integral-local tensor lemma makes the source local. The kernel of evaluation at the
   chosen geometric point is maximal, so the localization is exactly the target strict
   henselization. This proves bijectivity of the canonical comparison.
5. The factor equations with the two tensor inclusions give compatibility with `Spec B` and
   `Spec C`; the evaluation equation on pure tensors gives compatibility with `Spec (B ⊗[A] C)`
   and with the chosen geometric point.
-/
theorem strictHenselization_tensor_finite
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Module.Finite A B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of (B ⊗[A] C))) :
    ∃ φ : strictTensorRing (strictTensorMapAB s) (strictTensorMapAC s) →+*
        strictHenselizationRing s,
      Function.Bijective φ ∧
      φ.comp (strictTensorLeft (strictTensorMapAB s) (strictTensorMapAC s)) =
        strictTensorMapBD s ∧
      φ.comp (strictTensorRight (strictTensorMapAB s) (strictTensorMapAC s)) =
        strictTensorMapCD s ∧
      ∀ b c,
        strictHenselizationPointEvaluation s (φ
          (strictTensorTmul (strictTensorMapAB s) (strictTensorMapAC s) b c)) =
          strictHenselizationPointEvaluation (strictTensorPointB s) b *
            strictHenselizationPointEvaluation (strictTensorPointC s) c := by
  sorry

end AlgebraicGeometry.Scheme

end
