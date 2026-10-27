/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.DerivedCoinductionUnderlyingComparison
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Bounded injective models for derived coinduction

Source: Stacks Project, dualizing.tex, Tags 08XR, 0AX0 (first proof paragraph),
and 0A70--0A71 (blueprint: lem-trf-coinduction-bounded-injective-model).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u wA wB

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- A bounded injective A-complex coinduces to a complex of injective B-modules
with the same support interval, canonically representing derived coinduction.
The complex is the existing `coinductionComplexFunctor`: its terms are Hom_A(B,Iⁿ),
its differential is postcomposition by d_I, and (c • φ)(x) = φ(xc).
The comparison `e` is fixed by the existing K-injective comparison and the supplied `s`.
The final equation uses the fixed natural isomorphism
`derivedCoinductionUnderlyingComparison` to identify restriction of this comparison
with the ordinary K-injective computation of RHom_A(B[0],L).

Source: Stacks Project, dualizing.tex, Tags 08XR, 0AX0 (first proof paragraph),
0A70 and 0A71 (blueprint: lem-trf-coinduction-bounded-injective-model).

Proof:
1. Ordinary coextension has action (cφ)(x) = φ(xc) and maps by postcomposition.
Applying it degreewise gives the stated differential and support. If Iⁿ is zero,
Hom_A(B,Iⁿ) is zero; composition with d_I is B-linear and squares to zero.
2. Evaluation at one identifies Hom_B(N,Hom_A(B,M)) with Hom_A(UN,M).
The inverse sends g to (n ↦ (x ↦ g(xn))). Restriction preserves monomorphisms,
so lem-exc-rg-right-adjoint-preserves-injectives gives injectivity of every term.
3. The support assumption makes I strictly bounded below by a. Apply
lem-weil-pbc-bounded-below-injectives-kinjective to obtain hI.
4. Use def-trf-derived-coinduction on this K-injective representative and transport
its model isomorphism along s. Equivalently, the lifts of s to any chosen replacement
are unique in the homotopy category by lem-weil-pbc-kinjective-hom-derived.
They have homotopy inverse lifts. Coextension preserves these homotopies by
postcomposition, proving independence and compatibility of the comparison.
5. Forgetting the B-action gives the ordinary Hom_A(B[0],I) complex: only its
source-degree-zero factor survives, and its differential is d_I composed with φ.
This is the one-object ringed-site computation of def-pur-derived-internal-hom.
The underlying model comparison is postcomposition with the same lifted maps.
The canonical derived-composition isomorphism and exact restriction comparison
commute with their derived units. On I, inverting these units gives the stated
model maps. Naturality and transport along s give the final equation for the fixed
`derivedCoinductionUnderlyingComparison`, without choosing an isomorphism at L.
No Noetherian, finite-map, flatness or scalar-action-isomorphism assumption is used. -/
theorem coinduction_bounded_injective_model
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} B)]
    (L : DerivedCategory (ModuleCat.{u} A)) (a b : ℤ) (_hab : a ≤ b)
    (I : CochainComplex (ModuleCat.{u} A) ℤ)
    (hIinj : ∀ q : ℤ, Injective (I.X q))
    (hIsupp : ∀ q : ℤ, q < a ∨ b < q → IsZero (I.X q))
    (s : DerivedCategory.Q.obj I ≅ L) :
    (∀ q : ℤ, Injective (((coinductionComplexFunctor f).obj I).X q)) ∧
    (∀ q : ℤ, q < a ∨ b < q →
      IsZero (((coinductionComplexFunctor f).obj I).X q)) ∧
    ∃ (hI : I.IsKInjective)
      (e : DerivedCategory.Q.obj ((coinductionComplexFunctor f).obj I) ≅
        (derivedCoinduction f).obj L),
      e = (@derivedCoinductionModel A B _ _ f _ _ I hI).symm ≪≫
        (derivedCoinduction f).mapIso s ∧
      (restrictScalars f).mapDerivedCategory.map e.hom ≫
          (derivedCoinductionUnderlyingComparison f).hom.app L =
        (restrictScalars f).mapDerivedCategoryFactors.hom.app
            ((coinductionComplexFunctor f).obj I) ≫
          (@derivedCoinductionUnderlyingModel A B _ _ f _ I hI).inv ≫
          (derivedCoinductionUnderlyingHom f).map s.hom := by
  sorry

end ModuleCat
