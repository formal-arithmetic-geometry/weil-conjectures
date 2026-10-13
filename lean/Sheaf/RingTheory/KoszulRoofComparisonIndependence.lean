/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.RingTheory.KoszulConormalComparison
public import Sheaf.RingTheory.KoszulRegularSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

/-! # Koszul roofs and normalized comparisons

Source: Stacks Project, Tags 0BQZ and 0BQY, local finite free Koszul computation.
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

/-- Equal roofs have the same normalized conormal value on different generators.
Source: Stacks Project, Tags 0BQY and 0BQZ, determinant classes and the map on
Ext induced by A -> A/I (blueprint: lem-sc-koszul-roof-comparison-independence).

Proof: Express each f_i as a linear combination of the g_j, producing t with
linearCombination g composed with t = linearCombination f. Its exterior powers
form a Koszul chain map K(f) -> K(g): contraction commutes with exterior powers
by the equation on the generator functionals. In degree zero it is the identity,
so the normalized augmentations commute with its integer extension. Thus pulling
z_g back along this chain map represents the same roof class as z_g. Equality of
the two displayed derived morphisms first permits cancellation of the common
single shift isomorphism on the right. Precompose with Q(epsilon_f), and use
u followed by epsilon_g = epsilon_f to cancel Q(epsilon_g) with its inverse.
This gives Q(z_f)=Q(u followed by z_g). Each natural-number Koszul term is free
by its finite exterior basis and hence projective. The integer extension is zero
above 0, so CochainComplex.isKProjective_of_projective at bound 0 applies (also
the extension instance in HomotopyCategory/KProjective.lean:126). Naturality of
quotientCompQhIso transfers the equality to Qh of the two homotopy classes.
Injectivity of CochainComplex.IsKProjective.Qh_map_bijective reflects this to
equality of homotopy classes; HomotopyCategory.homotopyOfEq extracts a homotopy.
Equivalently, shift the maps to single(A,0)[r], use Cocycle.equivHomShift and
CohomologyClass.toHom_bijective to obtain equality of their degree-r cocycle
classes. The equations mk_sub and mk_eq_zero_iff say their difference is a
coboundary. Cocycle.toSingleMk_mem_coboundaries_iff extracts its top component
as E_f.d(-r,1-r) followed by a map E_f^(1-r) to A. For r>0, transport this to
precomposition with d_(r,r-1); it is a signed dual boundary after absorbing the
unit (-1)^r. For r=0, E_f^1=0 and the difference is zero. All boundary values lie
in I because contraction with f is a sum of terms multiplied by f_i.
The normalized comparison kills it by reduction modulo I. Finally the two
normalized comparisons agree on pullback of a top functional: c_g composed with
t equals c_f, exterior powers take wedges to wedges of their images, and the
normalization equations coincide on every conormal wedge. The conormal basis
makes the determinant pairing injective, proving equality of the values.
For r=0 the chain map is the identity on A and there are no top coboundaries;
for a zero quotient both conormal determinant values vanish. -/
theorem koszul_roof_comparison_independent
    (A : Type u) [CommRing A] [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (I : Ideal A) (r : ℕ) (f g : Fin r → A)
    (hregf : RingTheory.Sequence.IsKoszulRegular f)
    (hregg : RingTheory.Sequence.IsKoszulRegular g)
    (hf : Ideal.span (Set.range f) = I) (hg : Ideal.span (Set.range g) = I)
    (φ : koszulDualComplex A r f ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
        (koszulNormalDeterminant A I r))
    (ψ : koszulDualComplex A r g ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
        (koszulNormalDeterminant A I r))
    (hφ : IsKoszulConormalComparison A I r f hf φ)
    (hψ : IsKoszulConormalComparison A I r g hg ψ)
    (εf : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)))
    (εg : (koszulComplex A r g).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)))
    [QuasiIso εf] [QuasiIso εg]
    (haugf : ∀ x : ⋀[A]^0 (Fin r →₀ A),
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of A (A ⧸ I))).hom
        (εf.f 0 (((koszulComplex A r f).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
      Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x))
    (haugg : ∀ x : ⋀[A]^0 (Fin r →₀ A),
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of A (A ⧸ I))).hom
        (εg.f 0 (((koszulComplex A r g).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
      Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x))
    (zf : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj (ModuleCat.of A A))
    (zg : (koszulComplex A r g).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj (ModuleCat.of A A))
    (heq : inv (DerivedCategory.Q.map εf) ≫ DerivedCategory.Q.map zf ≫
        ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
          (r : ℤ) (-(r : ℤ)) 0 (add_neg_cancel (r : ℤ))).inv.app (ModuleCat.of A A) =
      inv (DerivedCategory.Q.map εg) ≫ DerivedCategory.Q.map zg ≫
        ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
          (r : ℤ) (-(r : ℤ)) 0 (add_neg_cancel (r : ℤ))).inv.app (ModuleCat.of A A)) :
    koszulComparisonValue A I r f φ ((((koszulComplex A r f).extendXIso
      ComplexShape.embeddingDownNat (i := r) rfl).inv ≫ zf.f (-(r : ℤ)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
          (ModuleCat.of A A)).hom)) =
      koszulComparisonValue A I r g ψ ((((koszulComplex A r g).extendXIso
      ComplexShape.embeddingDownNat (i := r) rfl).inv ≫ zg.f (-(r : ℤ)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
          (ModuleCat.of A A)).hom)) := by
  sorry

end ExteriorAlgebra
