/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.FieldTheory.FieldTower
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Generic points under finite scalar extension

Source: Stacks Project, Tags 00HS, 01I4, 01JR and 01JT; ILO X 2.3, Step 2,
printed p.150, diagram (2.b) (blueprint: lem-sfb-finite-scalar-extension-generic-points).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

/-- Scalar extension of `V/F` to `K`, using the chosen scheme fibre product.
Source: Stacks 01I4 (blueprint: lem-sfb-finite-scalar-extension-generic-points). -/
noncomputable abbrev finiteScalarExtension {F K : Type u} [Field F] [Field K]
    [Algebra F K] {V : Scheme.{u}} (f : V ⟶ Spec (.of F)) : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap F K)))

/-- The canonical projection from scalar extension to the original scheme.
Source: Stacks 01I4 (blueprint: lem-sfb-finite-scalar-extension-generic-points). -/
noncomputable abbrev scalarExtensionProjection {F K : Type u} [Field F] [Field K]
    [Algebra F K] {V : Scheme.{u}} (f : V ⟶ Spec (.of F)) :
    finiteScalarExtension (K := K) f ⟶ V :=
  pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F K)))

/-- The canonical map from the base field to a point's residue field, by global evaluation.
Source: Stacks 01JT (blueprint: lem-sfb-finite-scalar-extension-generic-points). -/
noncomputable def fieldToResidue {F : Type u} [Field F] {V : Scheme.{u}}
    (f : V ⟶ Spec (.of F)) (x : V) : F →+* V.residueField x :=
  ((ΓSpecIso (.of F)).inv ≫ f.appTop ≫ V.Γevaluation x).hom

/-- The fibre algebra `κ(x) ⊗[F] K`, with its canonical scalar structure.
Source: Stacks 01JT (blueprint: lem-sfb-finite-scalar-extension-generic-points). -/
noncomputable abbrev scalarExtensionFiberAlgebra {F K : Type u} [Field F] [Field K]
    [Algebra F K] {V : Scheme.{u}} (f : V ⟶ Spec (.of F)) (x : V) : Type u := by
  letI := (fieldToResidue f x).toAlgebra
  exact V.residueField x ⊗[F] K

/-- The pure tensor in the fibre algebra, using its specified base-field action.
Source: Stacks 01JT (blueprint: lem-sfb-finite-scalar-extension-generic-points). -/
noncomputable def scalarExtensionFiberTmul {F K : Type u} [Field F] [Field K]
    [Algebra F K] {V : Scheme.{u}} (f : V ⟶ Spec (.of F)) (x : V)
    (a : V.residueField x) (b : K) : scalarExtensionFiberAlgebra (K := K) f x := by
  letI := (fieldToResidue f x).toAlgebra
  exact a ⊗ₜ[F] b

/-- Finite scalar extension has the affine, generic-point and residue-field properties stated
in Stacks 00HS, 01I4, 01JR and 01JT and used in ILO X 2.3 Step 2, diagram (2.b).
(blueprint: lem-sfb-finite-scalar-extension-generic-points).

Proof plan:
1. Restrict the pullback to an affine open (lem-weil-pbc-open-fibre-product), then use
   lem-weil-pbc-fibre-product-affine-spectra to obtain Spec of the tensor algebra, with
   projection induced by r ↦ r ⊗ 1.
2. Choose a finite F-basis of K (def-pc-field-tower, def-weil-pbc-free-module). Tensoring
   its basis and coordinate maps gives mutually inverse R-linear maps R^n and R ⊗[F] K,
   including when R is the zero ring (def-weil-pbc-module-tensor-product).
3. Tensoring an injection with that algebra becomes the coordinatewise injection on n
   copies, proving flatness (def-weil-pbc-flat-ring-map).
4. A point in an open is a component generic point exactly when it is one in the ambient
   space: intersect closures with the open, and use density of a nonempty open in an
   irreducible closed set. On affine spectra use
   lem-weil-pbc-spec-irreducible-components-minimal-primes.
5. Apply lem-sc-flat-going-down to a minimal prime upstairs; a prime below its contraction
   lifts below it, hence equals it by minimality. Thus its contraction is minimal.
6. By lem-weil-pbc-fibre-product-points and the fibre universal property, the fibre is
   Spec(κ(x) ⊗[F] K), and the point prime is the kernel of the displayed pure-tensor map.
   The same basis calculation makes this algebra finite-dimensional. Its prime quotient
   is a finite-dimensional domain, hence a field by
   lem-weil-pbc-finite-dimensional-domain-is-field. The canonical quotient map identifies
   it with κ(y) by lem-weil-pbc-fibre-product-point-residue-field.
7. Generic points compose by step 5 and the hypothesis on v. Residue maps compose
   (def-weil-residue-field); products of finite spanning sets prove finiteness of the
   composite field extension (def-pc-field-tower). Empty schemes are included.
-/
theorem finite_scalar_extension_generic_points
    (F K : Type u) [Field F] [Field K] [Algebra F K] [Module.Finite F K]
    (V : Scheme.{u}) (f : V ⟶ Spec (.of F)) :
    (∀ (R : Type u) [CommRing R] [Algebra F R]
      (i : Spec (.of R) ⟶ V) [IsOpenImmersion i],
      i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap F R)) →
      (∃ e : pullback (scalarExtensionProjection (K := K) f) i ≅
          Spec (.of (R ⊗[F] K)),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[F] K))) =
          pullback.snd (scalarExtensionProjection (K := K) f) i) ∧
      (∃ n : ℕ, FieldExtension.degree F K = (n : WithTop ℕ) ∧
        Nonempty (Module.Basis (Fin n) R (R ⊗[F] K))) ∧
      (algebraMap R (R ⊗[F] K)).Flat) ∧
    (∀ y : finiteScalarExtension (K := K) f,
      y ∈ genericPoints (finiteScalarExtension (K := K) f) →
      scalarExtensionProjection (K := K) f y ∈ genericPoints V) ∧
    (∀ y : finiteScalarExtension (K := K) f,
      ∃ ψ : scalarExtensionFiberAlgebra (K := K) f
          (scalarExtensionProjection (K := K) f y) →+*
          (finiteScalarExtension (K := K) f).residueField y,
        (∀ (a : V.residueField (scalarExtensionProjection (K := K) f y)) (b : K),
          ψ (scalarExtensionFiberTmul f _ a b) =
            ((scalarExtensionProjection (K := K) f).residueFieldMap y).hom a *
              fieldToResidue (pullback.snd f
                (Spec.map (CommRingCat.ofHom (algebraMap F K)))) y b) ∧
        (RingHom.ker ψ).IsPrime ∧
        Module.Finite (V.residueField (scalarExtensionProjection (K := K) f y))
          (scalarExtensionFiberAlgebra (K := K) f
            (scalarExtensionProjection (K := K) f y)) ∧
        IsField (scalarExtensionFiberAlgebra (K := K) f
          (scalarExtensionProjection (K := K) f y) ⧸ RingHom.ker ψ) ∧
        (∃ e : (scalarExtensionFiberAlgebra (K := K) f
            (scalarExtensionProjection (K := K) f y) ⧸ RingHom.ker ψ) ≃+*
            (finiteScalarExtension (K := K) f).residueField y,
          e.toRingHom.comp (Ideal.Quotient.mk (RingHom.ker ψ)) = ψ) ∧
        ((scalarExtensionProjection (K := K) f).residueFieldMap y).hom.Finite) ∧
    (∀ (B : Scheme.{u}) (v : V ⟶ B),
      (∀ x : V, x ∈ genericPoints V →
        v x ∈ genericPoints B ∧ (v.residueFieldMap x).hom.Finite) →
      ∀ y : finiteScalarExtension (K := K) f,
        y ∈ genericPoints (finiteScalarExtension (K := K) f) →
        (scalarExtensionProjection (K := K) f ≫ v) y ∈ genericPoints B ∧
          ((scalarExtensionProjection (K := K) f ≫ v).residueFieldMap y).hom.Finite) := by
  sorry

end AlgebraicGeometry.Scheme
