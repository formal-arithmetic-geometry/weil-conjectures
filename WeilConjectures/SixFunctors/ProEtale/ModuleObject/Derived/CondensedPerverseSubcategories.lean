/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPerverseSupport
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.AlgebraicGeometry.FiniteTypeOverFieldNoetherian

/-!
# Perverse full subcategories for ordinary condensed algebraic ell-adic coefficients

Source: latest blueprint, `sec-deligne-laumon-a1/sk-lem-wft-curve-heart/`
`def-per-perverse-subcategories.md`, order 4192
(blueprint: def-per-perverse-subcategories).

The object properties below select full subcategories of the ordinary bounded constructible
category. Its integer shift is inherited from the ambient derived category. The chosen
compactification is supplied by Nagata and passed to the recorded condensed cosupport condition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The degree-zero support class, with all morphisms inherited from `D_cons`.
Construction: use the finite-subextension condensed coefficient ring, its canonical pullback,
and the ordinary bounded constructible category; select exactly `SuppCon` from the support node.
Source: latest blueprint, order 4192, first displayed equality
(blueprint: def-per-perverse-subcategories). -/
def CondensedPerverseLEZero (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (_hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] :
    ObjectProperty
      (BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :=
  CondensedSupportCondition ℓ

/-- The degree-zero cosupport class, using the constructible exceptional dual relative to `k`.
Construction: in the same ordinary condensed category, select exactly `CosuppCon(K)`, namely
`SuppCon(RHom(K, Ra_X^! Ω_s[0]))`, with the dualizing complex of the support node.
Source: latest blueprint, order 4192, second displayed equality
(blueprint: def-per-perverse-subcategories). -/
def CondensedPerverseGEZero (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    ObjectProperty
      (BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :=
  CondensedCosupportCondition ℓ hk X

/-- The class `pD^{≤n} = pD^{≤0}[-n]`: an object belongs precisely when its shift by `n`
belongs to the degree-zero support class. The shift is the inherited ordinary derived shift.
Construction: pull the degree-zero object property back along `[n]`, which describes its
translation by `[-n]`. Finite type over a field supplies the Noetherian-space instance needed
by the existing bounded constructible shift, with no characteristic restriction.
Source: latest blueprint, order 4192, third displayed formula
(blueprint: def-per-perverse-subcategories). -/
def CondensedPerverseLE (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (n : ℤ) :
    ObjectProperty
      (BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :=
  (CondensedPerverseLEZero ℓ hk X).shift n

/-- The class `pD^{≥n} = pD^{≥0}[-n]`: an object belongs precisely when its shift by `n`
satisfies the recorded condensed cosupport condition.
Construction: pull the degree-zero cosupport property back along the inherited shift `[n]`;
this is the inverse-shift convention of the source, for every integer `n`.
Source: latest blueprint, order 4192, fourth displayed formula
(blueprint: def-per-perverse-subcategories). -/
def CondensedPerverseGE (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (n : ℤ) :
    ObjectProperty
      (BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :=
  (CondensedPerverseGEZero ℓ hk X).shift n

/-- The heart candidate is the intersection of the two degree-zero object properties.
Construction: after selecting the support and cosupport classes above, take their pointwise
conjunction. This definition asserts no t-structure or abelian-category theorem.
Source: latest blueprint, order 4192, final displayed equality
(blueprint: def-per-perverse-subcategories). -/
def CondensedPerverseHeart (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] :
    ObjectProperty
      (BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :=
  CondensedPerverseLEZero ℓ hk X ⊓ CondensedPerverseGEZero ℓ hk X

/-- The full category `pD^{≤n}`, with exactly the ambient morphisms between selected objects.
Source: latest blueprint, order 4192 (blueprint: def-per-perverse-subcategories). -/
abbrev CondensedPerverseLECategory (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (n : ℤ) : Type _ :=
  (CondensedPerverseLE ℓ hk X n).FullSubcategory

/-- The full category `pD^{≥n}`, with exactly the ambient morphisms between selected objects.
Source: latest blueprint, order 4192 (blueprint: def-per-perverse-subcategories). -/
abbrev CondensedPerverseGECategory (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (n : ℤ) : Type _ :=
  (CondensedPerverseGE ℓ hk X n).FullSubcategory

/-- The full perverse heart candidate, with all ambient morphisms between its objects.
Source: latest blueprint, order 4192 (blueprint: def-per-perverse-subcategories). -/
abbrev CondensedPerverseHeartCategory (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] : Type _ :=
  (CondensedPerverseHeart ℓ hk X).FullSubcategory

end AlgebraicGeometry.ProEtale.CondensedRing
