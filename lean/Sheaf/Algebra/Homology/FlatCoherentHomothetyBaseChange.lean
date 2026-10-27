module

public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.RingHom.Flat
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Sheaf.Algebra.Homology.PseudoCoherentRHomFlatBaseChange
import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction

/-! # Flat base change of coherent complexes and homotheties

Source: Stacks Project, more-algebra.tex, Tag 0A6A(3), Equation 0E1X and Tag 0E1W
(blueprint: lem-trf-flat-coherent-homothety-base-change).

Ordinary module derived categories use the existing K-injective internal Hom and
K-flat normalized strong monoidal scalar extension. The canonical comparison is the
existing mate of its tensorator. Scalar action is `MonoidalClosed.id`: the transpose
of the right unitor under left tensor--Hom adjunction, equivalently the transpose of
the left unitor under right tensor--Hom adjunction by symmetry.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace DerivedCategory

/-- Flat change of Noetherian rings preserves bounded finite cohomology, the derived
Hom comparison for two such objects, homothety isomorphisms, and vanishing of Hom.
The unit comparison `ε` identifies the extended ring with the new tensor unit.
Source: Stacks Project, more-algebra.tex, Tag 0A6A(3), Equation 0E1X and Tag 0E1W
(blueprint: lem-trf-flat-coherent-homothety-base-change).

Proof:
1. Flat tensor preserves the exact sequences defining cycles and boundaries, so
   H^i(K_S) is S tensor H^i(K), as in lem-trf-flat-projective-hom-models. This
   preserves the finite vanishing interval. Tensoring a finite generating family
   with 1 gives a finite S-generating family, by expanding each pure tensor.
2. Over the Noetherian ring R, the upper bound and finite cohomology make C
   pseudo-coherent by lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion.
   The lower bound on Z makes Z bounded below. Apply
   lem-trf-pseudocoherent-rhom-flat-base-change to obtain the canonical comparison
   isomorphism, with no projective or injective dimension hypothesis.
3. By lem-sfb-dc-hom-scalar-adjunction, transpose the comparison composed with
   extended scalar action across extension/restriction and tensor--Hom adjunction.
   Its transpose is the scalar-extension unit composed with the unitor, since
   homothety transposes to the unitor. The transpose of scalar action on C_S is
   the same arrow: r tensor x maps to f(r) times eta(x) = eta(rx). Injectivity
   of both adjunction bijections proves the displayed homothety equality. The
   normalized monoidal comparison is exactly this evaluation-normalized map.
4. If homothety on C is invertible, its image under scalar extension is invertible;
   compose with the comparison isomorphism and the unit identification from step 3.
   If RHom_R(C,Z) is zero, its derived scalar extension is zero (compute using the
   zero flat model), and step 2 then gives zero RHom_S(C_S,Z_S). -/
theorem flat_coherent_homothety_base_change
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (φ : R →+* S) (hφ : φ.Flat) :
    (∀ K : DerivedCategory (ModuleCat.{u} R),
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj K)) →
      (∀ i : ℤ, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj K)) →
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((homologyFunctor (ModuleCat.{u} S) i).obj
          ((ModuleCat.ordinaryDerivedExtendScalars φ).obj K))) ∧
      (∀ i : ℤ, Module.Finite S ((homologyFunctor (ModuleCat.{u} S) i).obj
        ((ModuleCat.ordinaryDerivedExtendScalars φ).obj K)))) ∧
    (∀ C Z : DerivedCategory (ModuleCat.{u} R),
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj C)) →
      (∀ i : ℤ, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C)) →
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj Z)) →
      (∀ i : ℤ, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj Z)) →
      IsIso ((Functor.LaxMonoidal.ihomComparison
        (ModuleCat.ordinaryDerivedExtendScalars φ) C).natTrans.app Z) ∧
      (Functor.LaxMonoidal.ε (ModuleCat.ordinaryDerivedExtendScalars φ) ≫
          (ModuleCat.ordinaryDerivedExtendScalars φ).map (MonoidalClosed.id C) ≫
          (Functor.LaxMonoidal.ihomComparison
            (ModuleCat.ordinaryDerivedExtendScalars φ) C).natTrans.app C =
        MonoidalClosed.id ((ModuleCat.ordinaryDerivedExtendScalars φ).obj C)) ∧
      (IsIso (MonoidalClosed.id C) →
        IsIso (MonoidalClosed.id ((ModuleCat.ordinaryDerivedExtendScalars φ).obj C))) ∧
      (IsZero ((ordinaryModuleDerivedInternalHom R).obj (op C, Z)) →
        IsZero ((ordinaryModuleDerivedInternalHom S).obj
          (op ((ModuleCat.ordinaryDerivedExtendScalars φ).obj C),
            (ModuleCat.ordinaryDerivedExtendScalars φ).obj Z)))) := by
  sorry

end DerivedCategory
