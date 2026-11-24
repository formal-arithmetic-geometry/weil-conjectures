/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import Mathlib.Algebra.DirectSum.Basic

import WeilConjectures.AlgebraicGeometry.DetIndHeartIISums
import WeilConjectures.AlgebraicGeometry.DetIndHeartIIVanishing

/-!
# Ext from constructible sheaves into ind-constructible sheaves

The supplied nonnegative cutoff retains its value on passing from constructible to
ind-constructible targets. In every integer degree the canonical direct-sum comparison
is bijective. Ext is written as Hom between degree-zero sheaves in the ordinary derived
category, as in `Abelian.Ext.homAddEquiv` in nonnegative degrees.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj DirectSum

namespace AlgebraicGeometry.ProEtale

/-- The uniform constructible-target Ext bound also applies to ind-constructible
sheaves, and Ext in every integer degree preserves small sums of such sheaves.
The cutoff is supplied with the property of the uniform constructible Ext bound;
its existence is not an additional conclusion. The coefficient equality
is equality of bundled monoid objects, so it includes the ring multiplication. -/
theorem indConstructible_ext_vanishing_and_sums
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [CharP k p]
    (_hp : 0 < p) (_hne : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (C : ConstantModelConstructible Λ X) (d : ℕ)
    (_hbound : ∀ N : ConstantModelConstructible Λ X, ∀ q : ℤ, (d : ℤ) < q →
      Subsingleton ((DerivedCategory.singleFunctor _ 0).obj C.obj ⟶
        (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj N.obj))) :
    (∀ B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
      ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) B →
      ∀ q : ℤ, (d : ℤ) < q →
        Subsingleton ((DerivedCategory.singleFunctor _ 0).obj C.obj ⟶
          (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj B))) ∧
    (∀ (q : ℤ) (S : Type (u + 1))
      (B : S → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      (∀ s : S, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) (B s)) →
      ∀ (c : Cofan B), IsColimit c →
        Function.Bijective
          (@DirectSum.toAddMonoid S _ _ (Classical.decEq S) _ _ (fun s : S ↦
            Preadditive.rightComp ((DerivedCategory.singleFunctor _ 0).obj C.obj)
              ((shiftFunctor _ q).map ((DerivedCategory.singleFunctor _ 0).map (c.inj s)))) :
            (⨁ s : S,
              ((DerivedCategory.singleFunctor _ 0).obj C.obj ⟶
                (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj (B s)))) →+
              ((DerivedCategory.singleFunctor _ 0).obj C.obj ⟶
                (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj c.pt)))) := by
  constructor
  · exact (det_ind_heart_ii_vanishing ℓ k p _hp _hne X Λ _hΛ C d _hbound).2
  · intro q S B hB c hc
    rcases _hΛ with ⟨⟨E, hE⟩⟩ | hE
    · cases hE
      let R := Profinite.padicSubfieldCondensedRing ℓ E
      have hR : R = Profinite.padicSubfieldCondensedRing ℓ E ∨
          R = Profinite.padicAlgClCondensedRing ℓ := Or.inl rfl
      have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
      have hs := det_ind_heart_ii_sums ℓ E X R hR
        (C := C.obj) (hC := C.property) q S B hB c hc
      simpa [R, coefficientHeartRingObj] using hs
    · cases hE
      let E : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
      let R := Profinite.padicAlgClCondensedRing ℓ
      have hR : R = Profinite.padicSubfieldCondensedRing ℓ E ∨
          R = Profinite.padicAlgClCondensedRing ℓ := Or.inr rfl
      have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
      have hs := det_ind_heart_ii_sums ℓ E X R hR
        (C := C.obj) (hC := C.property) q S B hB c hc
      simpa [R, coefficientHeartRingObj] using hs

end AlgebraicGeometry.ProEtale
