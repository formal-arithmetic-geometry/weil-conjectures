/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import WeilConjectures.RingTheory.RingPseudoCoherent
import Sheaf.TraceFormula.AlgebraicShriekRelativePerfect
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.Algebra.Module.Projective
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.Algebra.Homology.PerfectCoinductionTorIndependentBaseChange
import Sheaf.AlgebraicGeometry.RingDerivedScalarExtension
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses

/-! # Polynomial dual detection for relatively perfect complexes

Source: Stacks Project, dualizing.tex, Tags 0A7C and 0BZW, with Noetherian
approximation from algebra.tex, Tag 02JO. The arbitrary-base detection assertion
is the agent corollary in the DAG, not the statement of Tag 0A7C.
(blueprint: lem-sfb-relative-perfect-polynomial-dual-detection).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace ModuleCat

/-- The polynomial dual detects zero relatively perfect objects and isomorphisms
between them over an arbitrary flat finitely presented base algebra.
Source: Stacks 0A7C, 0BZW and 02JO, with the agent localizing-generation argument
(blueprint: lem-sfb-relative-perfect-polynomial-dual-detection).

Proof, following the eight steps of the node:
1. Apply lem-sfb-flat-fp-presentation-noetherian-model to the specified surjection.
Obtain a compatible flat finitely presented Noetherian model R₀ → A₀ and the same
number of polynomial variables, with P = P₀ tensor_R₀ R and A = A₀ tensor_R₀ R.
2. lem-sfb-arbitrary-polynomial-dual-properties makes A₀ perfect over P₀.
lem-trf-algebraic-shriek-relative-perfect gives bounded finite cohomology for C₀
and the scalar isomorphism A₀[0] ≅ RHom_A₀(C₀,C₀), using only Noetherian rings.
3. Localizations are flat and Noetherian (lem-weil-pbc-localization-flat and
lem-weil-pbc-localization-noetherian). By lem-trf-flat-coherent-homothety-base-change,
C₀ localized at any prime is nonzero: otherwise its scalar isomorphism makes the
nonzero local ring zero. lem-sfb-noetherian-full-support-localizing-generation
therefore puts A₀[0] in Loc(C₀). For A₀ = 0 the assertion is immediate.
4. Choose a bounded finite-projective P₀-resolution F of A₀. The polynomial monomial
basis and def-weil-pbc-projective-module make its terms R₀-flat. F and A₀[0] are
K-flat over R₀ by lem-pc-module-bounded-flat-kflat. By lem-pur-derived-change-of-rings,
F tensor_R₀ R represents A[0]. The P₀-K-flat model from
lem-pc-source-kflat-module-tensor-model also computes A₀ tensor-derived_P₀ P by
that complex. Thus the polynomial square is Tor-independent, without R₀ → R flat.
5. lem-sfb-perfect-coinduction-tor-independent-base-change, applied to P₀[0] and
shifted by n, gives C₀ tensor-derived_A₀ A ≅ C in D(A), retaining its A-action.
6. The extension functor is exact (lem-pur-derived-change-of-rings) and left adjoint
to restriction (def-zl-ring-derived-scalar-extension), hence preserves coproducts.
The inverse image of Loc(C) is closed under shifts, triangles, coproducts and retracts,
and contains C₀. Step 3 then puts A[0] in Loc(C).
7. If RHom_A(C,Z) is zero, the closed adjunction
lem-sf-ringed-derived-closed-symmetric-monoidal gives Hom(C,Z[j]) = 0 for every j.
By lem-weil-pbc-hom-out-of-triangle-exact the class of V with Hom(V,Z[j]) = 0 for
all j is closed under triangles and shifts; coproducts and retracts preserve it too.
It contains Loc(C), hence A[0], and by lem-pc-derived-module-free-generation it
contains Z. Thus the identity of Z is zero. This argument works for every Z,
so in particular for the relatively perfect objects in the statement.
8. RHom_A(C,-) is exact by lem-weil-pbc-ringed-internal-hom-exact-restriction.
For a morphism whose image is invertible, lem-kun-distinguished-cone-zero makes
the image of its cone zero. Step 7 makes the cone itself zero, and the same
zero-cone criterion makes the morphism invertible. Zero rings and n = 0 are included.
-/
theorem relativePerfect_polynomialDual_detection
    {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) (hflat : RingHom.Flat φ) (hfp : RingHom.FinitePresentation φ)
    (n : ℕ) (p : MvPolynomial (Fin n) R →+* A)
    (hp : Function.Surjective p) (hcomp : p.comp MvPolynomial.C = φ) :
    (∀ Z : DerivedCategory (ModuleCat.{u} A),
      DerivedCategory.IsPseudoCoherent Z →
      (∃ a b : ℤ, a ≤ b ∧ ∀ (Q : ModuleCat.{u} R) (i : ℤ),
        i < a ∨ b < i → IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
            (((restrictScalars φ).mapDerivedCategory.obj Z) ⊗
              (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Q))) →
      IsZero ((ordinaryModuleDerivedInternalHom A).obj
        (op (((derivedCoinduction p).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) R)) 0).obj
                (of (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R))))⟦(n : ℤ)⟧),
          Z)) → IsZero Z) ∧
    (∀ (X Y : DerivedCategory (ModuleCat.{u} A)) (f : X ⟶ Y),
      DerivedCategory.IsPseudoCoherent X →
      (∃ a b : ℤ, a ≤ b ∧ ∀ (Q : ModuleCat.{u} R) (i : ℤ),
        i < a ∨ b < i → IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
            (((restrictScalars φ).mapDerivedCategory.obj X) ⊗
              (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Q))) →
      DerivedCategory.IsPseudoCoherent Y →
      (∃ a b : ℤ, a ≤ b ∧ ∀ (Q : ModuleCat.{u} R) (i : ℤ),
        i < a ∨ b < i → IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
            (((restrictScalars φ).mapDerivedCategory.obj Y) ⊗
              (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Q))) →
      IsIso (((Functor.curry.obj (ordinaryModuleDerivedInternalHom A)).obj
        (op (((derivedCoinduction p).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) R)) 0).obj
                (of (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R))))⟦(n : ℤ)⟧))).map f) →
        IsIso f) := by
  sorry

end ModuleCat
