/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.RingTheory.KoszulDualComplex
public import Sheaf.RingTheory.KoszulRegularSequence
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

/-! # Koszul roofs and normalized comparisons

Source: Stacks Project, Tags 0BQZ and 0BQY, local finite free Koszul computation.
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

/-- Ext classes have roof representatives with their actual signed-dual cycle class.
Source: Stacks Project, Tag 0BQZ, computation of derived Hom by a finite free
resolution; Mathlib ProjectiveResolution.extEquivCohomologyClass.
(blueprint: lem-sc-koszul-ext-roof-representatives).

Proof: Construct the quotient augmentation q using I.mkQ after zeroEquiv.
Finite exterior bases and hreg make this K a projective resolution P. Its
integer extension E is zero above 0 with projective terms below 0, hence is
K-projective by CochainComplex.isKProjective_of_projective at bound 0.
For T=single(A,0), evaluate a degree-n Hom cochain at (-n,0), using extendXIso
and singleObjXSelf, to obtain e_n(c) in Hom(K_n,A). Cochain.toSingleEquiv gives
its inverse. Cochain.delta_toSingleMk (the declaration with Greek delta) makes
e_(n+1)(delta c) equal to (-1)^(n+1) times precomposition of e_n(c) with d_(n+1,n),
exactly the differential of L=koszulDualComplex A r f. Thus e_r identifies
cocycles Z with ker(L.d r (r+1)), and boundaries B with the incoming image BL.
For r=0 the degree-minus-one Hom term and incoming image are both zero.
Define F([c])=L.homologyPi((L.sc r).moduleCatCyclesIso.inv(e_r(c))). The equation
for moduleCatHomologyIso and homologyPi identifies this with the quotient map
ker(L.d)/BL. Hence B maps to zero, the map is well defined, its kernel is zero
because e_r reflects BL, and it is surjective because every kernel element
lifts along e_r. All component and quotient maps are A-linear.
Set d=F composed with P.extEquivCohomologyClass. The roof formula
extEquivCohomologyClass_symm_mk_hom and Abelian.Ext.smul_hom show that scalar
multiplication of a cocycle gives scalar multiplication of its Ext class;
Ext.homLinearEquiv is injective. Thus d is an A-linear equivalence.
Use P.extMk_surjective to represent x by a. Cocycle.toSingleMk constructs c;
Cocycle.equivHomShift.symm followed by the inverse single shift constructs z,
and y is the inverse cycles isomorphism applied to e_r(c). The formula
Cochain.toSingleMk_v gives the exact top evaluation equation. The declarations
extEquivCohomologyClass_extMk and extMk_hom give precisely the displayed roof
with the standard augmentation, including its single and shift identifications.
The definition of F gives d(x)=homologyPi(y). Any normalized augmentation equals
q: its degree-zero component is fixed by the quotient formula, and
to_single_hom_ext identifies the maps. Substitute this equality in the roof.
No normalization is inferred from Nonempty of an equivalence. For r=0 this
is Hom evaluation; for a zero quotient both Ext and dual homology vanish. -/
theorem exists_koszul_ext_roof_representatives
    (A : Type u) [CommRing A] [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I) :
    ∃ d : Abelian.Ext (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A A) r ≃ₗ[A]
        (koszulDualComplex A r f).homology r,
      ∀ (ε : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
          (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)))
        [QuasiIso ε],
        (∀ x : ⋀[A]^0 (Fin r →₀ A),
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (ModuleCat.of A (A ⧸ I))).hom
            (ε.f 0 (((koszulComplex A r f).extendXIso
              ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
          Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x)) →
        ∀ x : Abelian.Ext (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A A) r,
          ∃ (z : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
              (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj
                (ModuleCat.of A A))
            (y : (koszulDualComplex A r f).cycles r),
            x = (Abelian.Ext.homLinearEquiv (R := A)).symm
              (inv (DerivedCategory.Q.map ε) ≫ DerivedCategory.Q.map z ≫
                ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
                  (r : ℤ) (-(r : ℤ)) 0 (add_neg_cancel (r : ℤ))).inv.app
                    (ModuleCat.of A A)) ∧
            d x = (koszulDualComplex A r f).homologyπ r y ∧
            (koszulDualComplex A r f).iCycles r y = (((koszulComplex A r f).extendXIso
      ComplexShape.embeddingDownNat (i := r) rfl).inv ≫ z.f (-(r : ℤ)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
          (ModuleCat.of A A)).hom) := by
  sorry

end ExteriorAlgebra
