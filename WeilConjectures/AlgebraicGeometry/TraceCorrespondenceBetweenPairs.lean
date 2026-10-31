/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TraceFixedScheme
public import WeilConjectures.SixFunctors.Etale.Derived.Identity
import WeilConjectures.AlgebraicGeometry.TraceGraphCorrespondence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOrigin

/-!
# Finite-coefficient correspondences between pairs

Source: Weil conjectures blueprint, latest, sec-trace-formula/sk-d-corr,
def-trf-correspondence-between-pairs.md (blueprint: def-trf-correspondence-between-pairs).

The positive stage is `A_{E,n+1}`, as in the recorded endocorrespondence and admissibility
interfaces. Supports and morphisms are actual data, and intersections are chosen scheme
pullbacks with their actual projections. Opposite means reversing the two pairs, with an
independently specified coefficient map; it does not mean reversing the coefficient arrow.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)

set_option synthInstance.maxHeartbeats 80000 in
-- Derived pullback instance search on the support leg needs the dependency's larger budget.
/-- A correspondence from `(X,K)` to `(Y,L)` at the finite coefficient stage `n+1`.
Its support is separated of finite type over `k`; leg 1 is exceptional and leg 2 ordinary.
Source: latest blueprint, def-trf-correspondence-between-pairs, clause 1
(blueprint: def-trf-correspondence-between-pairs). -/
structure TrfCorrespondenceBetween (hl : l ≠ F.p)
    (X Y : Over (Spec (.of F.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (K : (trfFiniteTorFixed l E n X.left).FullSubcategory)
    (L : (trfFiniteTorFixed l E n Y.left).FullSubcategory) where
  C : Over (Spec (.of F.k))
  [separated : IsSeparated C.hom]
  [finiteType : LocallyOfFiniteType C.hom]
  [quasiCompact : QuasiCompact C.hom]
  c₁ : C ⟶ Y
  c₂ : C ⟶ X
  u : ((ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
      c₂.left).leftDerivedFunctor).obj K.obj ⟶
    (trfCorrespondenceExceptional F l E n C Y c₁).obj L.obj

attribute [instance] TrfCorrespondenceBetween.separated TrfCorrespondenceBetween.finiteType
  TrfCorrespondenceBetween.quasiCompact

namespace TrfCorrespondenceBetween

variable {F l E n} {hl : l ≠ F.p} {X Y : Over (Spec (.of F.k))}
  [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  {K : (trfFiniteTorFixed l E n X.left).FullSubcategory}
  {L : (trfFiniteTorFixed l E n Y.left).FullSubcategory}

/-- The specified map `c=(c₁,c₂)` to `Z=Y ×_s X`.
Source: latest blueprint, clause 1 (blueprint: def-trf-correspondence-between-pairs). -/
def toProduct (c : TrfCorrespondenceBetween F l E n hl X Y K L) :
    c.C.left ⟶ pullback Y.hom X.hom :=
  pullback.lift c.c₁.left c.c₂.left (c.c₁.w.trans c.c₂.w.symm)

/-- Exceptional admissibility of leg 1 and its Cartesian base changes in the stated
separated finite-type setting, using the dependency's fixed-stage admissibility predicate.
Source: latest blueprint, clause 1 (blueprint: def-trf-correspondence-between-pairs). -/
def IsAdmissible (c : TrfCorrespondenceBetween F l E n hl X Y K L) : Prop :=
  trfCorrespondenceLegAdmissible F l E n hl c.C Y c.c₁ ∧
    ∀ (C' Y' : Over (Spec (.of F.k)))
      [IsSeparated C'.hom] [LocallyOfFiniteType C'.hom] [QuasiCompact C'.hom]
      [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
      (g' : C' ⟶ c.C) (f' : C' ⟶ Y') (g : Y' ⟶ Y),
      IsPullback g'.left f'.left c.c₁.left g.left →
        trfCorrespondenceLegAdmissible F l E n hl C' Y' f'

/-- An opposite correspondence has its own support and coefficient map, with the pairs
reversed. Source: latest blueprint, clause 2
(blueprint: def-trf-correspondence-between-pairs). -/
abbrev Opposite (_c : TrfCorrespondenceBetween F l E n hl X Y K L) :=
  TrfCorrespondenceBetween F l E n hl Y X L K

/-- The factor exchange `τ : X ×_s Y ≅ Y ×_s X` is the standard pullback symmetry.
Source: latest blueprint, clause 3 (blueprint: def-trf-correspondence-between-pairs). -/
def factorExchange : pullback X.hom Y.hom ≅ pullback Y.hom X.hom :=
  pullbackSymmetry X.hom Y.hom

/-- The opposite support map `bar d = τ d`, retaining the actual support `D`.
Source: latest blueprint, clause 3 (blueprint: def-trf-correspondence-between-pairs). -/
def oppositeToProduct (d : TrfCorrespondenceBetween F l E n hl Y X L K) :
    d.C.left ⟶ pullback Y.hom X.hom :=
  d.toProduct ≫ (factorExchange (X := X) (Y := Y)).hom

/-- The intersection scheme `E(C,D)=C ×_Z D`, with no quotient by isomorphism.
Source: latest blueprint, clause 3 (blueprint: def-trf-correspondence-between-pairs). -/
def intersection (c : TrfCorrespondenceBetween F l E n hl X Y K L) (d : c.Opposite) :
    Scheme.{u} :=
  pullback c.toProduct d.oppositeToProduct

/-- The specified projection `E(C,D) → C`.
Source: latest blueprint, specified-data paragraph
(blueprint: def-trf-correspondence-between-pairs). -/
def intersectionFst (c : TrfCorrespondenceBetween F l E n hl X Y K L) (d : c.Opposite) :
    c.intersection d ⟶ c.C.left :=
  pullback.fst c.toProduct d.oppositeToProduct

/-- The specified projection `E(C,D) → D`.
Source: latest blueprint, specified-data paragraph
(blueprint: def-trf-correspondence-between-pairs). -/
def intersectionSnd (c : TrfCorrespondenceBetween F l E n hl X Y K L) (d : c.Opposite) :
    c.intersection d ⟶ d.C.left :=
  pullback.snd c.toProduct d.oppositeToProduct

/-- The projection formulas identify the ordered legs and the swapped opposite legs.
Source: latest blueprint, clause 3 (blueprint: def-trf-correspondence-between-pairs).

Proof: apply `pullback.lift_fst` and `pullback.lift_snd` to the support map; for the
opposite support also use the two projection formulas for `pullbackSymmetry`. -/
theorem toProduct_projections (c : TrfCorrespondenceBetween F l E n hl X Y K L)
    (d : c.Opposite) :
    c.toProduct ≫ pullback.fst Y.hom X.hom = c.c₁.left ∧
      c.toProduct ≫ pullback.snd Y.hom X.hom = c.c₂.left ∧
      d.oppositeToProduct ≫ pullback.fst Y.hom X.hom = d.c₂.left ∧
      d.oppositeToProduct ≫ pullback.snd Y.hom X.hom = d.c₁.left := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [toProduct, pullback.lift_fst]
  · simp only [toProduct, pullback.lift_snd]
  · simp only [oppositeToProduct, factorExchange, Category.assoc,
      pullbackSymmetry_hom_comp_fst, toProduct, pullback.lift_snd]
  · simp only [oppositeToProduct, factorExchange, Category.assoc,
      pullbackSymmetry_hom_comp_snd, toProduct, pullback.lift_fst]

/-- Endocorrespondences are exactly the dependency's cohomological correspondences,
retaining the support, both legs and the coefficient arrow in both directions.
Source: latest blueprint, clause 1 (blueprint: def-trf-correspondence-between-pairs). -/
def endoEquiv : TrfCorrespondenceBetween F l E n hl X X K K ≃
    TrfCohomologicalCorrespondence F l E n hl X K where
  toFun c := ⟨c.C, c.c₁, c.c₂, c.u⟩
  invFun c := ⟨c.C, c.c₁, c.c₂, c.u⟩

end TrfCorrespondenceBetween

variable (X : Over (Spec (.of F.k)))
  [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  (K : (trfFiniteTorFixed l E n X.left).FullSubcategory)

/-- The canonical comparison from the specified exceptional inverse image along `id` to
`K`: the etale identity adjoint comparison, followed by the pro-etale comparison counit.
Source: latest blueprint, final paragraph, `R(id)^! K=K`
(blueprint: def-trf-correspondence-between-pairs). -/
def trfPairExceptionalIdentityComparison :
    (trfCorrespondenceExceptional F l E n X X (𝟙 X)).obj K.obj ⟶ K.obj := by
  letI := trfCorrespondenceCompactifiable F X X (𝟙 X)
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))
  let G := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (HasCompactification.compactification (𝟙 X.left))
  letI : G.IsLeftAdjoint := Etale.isLeftAdjoint_rightDerivedLowerShriek A (𝟙 X.left)
  let e := (Adjunction.ofIsLeftAdjoint G).rightAdjointUniq
    (Adjunction.id.ofNatIsoLeft (Etale.rightDerivedLowerShriekIdIso
      (ModuleCat.{u + 1} A) X.left).symm)
  exact (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X.left).mapDerivedCategory.map
      (e.hom.app ((ProEtale.comparisonLowerStar
        (ModuleCat.{u + 1} A) X.left).rightDerivedFunctor.obj K.obj)) ≫
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X.left).counit.app K.obj

/-- The identity exceptional comparison is invertible on the finite-Tor constructible
category. No assertion is made on arbitrary pro-etale complexes.
Source: latest blueprint, final paragraph (blueprint: def-trf-correspondence-between-pairs).

Proof: the etale identity right-adjoint comparison is an isomorphism by uniqueness of
right adjoints. A bounded finite constructible complex is of etale origin; on this full
subcategory the comparison counit is an isomorphism. Their composite is the displayed map. -/
theorem trfPairExceptionalIdentityComparison_isIso :
    IsIso (trfPairExceptionalIdentityComparison F l E n X K) := by
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))
  have hK := trfGraphOrigin l E n X.left K
  have hCounit :
      IsIso ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X.left).counit.app
        K.obj) :=
    ((ProEtale.DerivedCategory.plusEtaleOrigin_iff K.obj).mp hK).2
  let _ := hCounit
  unfold trfPairExceptionalIdentityComparison
  infer_instance

namespace TrfCorrespondenceBetween

/-- The identity correspondence has both legs `id`; its coefficient arrow is `1_K`
under the canonical ordinary and exceptional identity comparisons.
Source: latest blueprint, final paragraph (blueprint: def-trf-correspondence-between-pairs). -/
def identity (hl : l ≠ F.p) : TrfCorrespondenceBetween F l E n hl X X K K := by
  letI := trfPairExceptionalIdentityComparison_isIso F l E n X K
  exact
    { C := X
      c₁ := 𝟙 X
      c₂ := 𝟙 X
      u := (ProEtale.leftDerivedUpperStarId
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
        X.left).hom.app K.obj ≫ inv (trfPairExceptionalIdentityComparison F l E n X K) }

variable {F l E n X K} {hl : l ≠ F.p}

/-- The opposite support of the identity is exactly the diagonal, and intersection with
it is the recorded fixed scheme, with the same two projections.
Source: latest blueprint, final paragraph (blueprint: def-trf-correspondence-between-pairs).

Proof: the two identity legs are identities. Pullback uniqueness shows their support
and its factor swap both equal the diagonal. Substituting this equality into the
intersection pullback gives exactly the definition of `fixedScheme`; its projections
are the very same pullback projections. -/
theorem intersection_identity (c : TrfCorrespondenceBetween F l E n hl X X K K) :
    (identity F l E n X K hl).oppositeToProduct = pullback.diagonal X.hom ∧
      c.intersection (identity F l E n X K hl) = (endoEquiv c).fixedScheme := by
  have hdiag : (identity F l E n X K hl).oppositeToProduct =
      pullback.diagonal X.hom := by
    apply pullback.hom_ext
    · simp [identity, oppositeToProduct, factorExchange, toProduct, Category.assoc]
    · simp [identity, oppositeToProduct, factorExchange, toProduct, Category.assoc]
  refine ⟨hdiag, ?_⟩
  change pullback c.toProduct (identity F l E n X K hl).oppositeToProduct = _
  rw [hdiag]
  rfl

end TrfCorrespondenceBetween
end WeilConjectures
