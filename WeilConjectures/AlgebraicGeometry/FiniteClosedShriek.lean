/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.CompactSupportRestrictionOfScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
import all WeilConjectures.AlgebraicGeometry.FiniteCoefficientDirectImage
import WeilConjectures.AlgebraicGeometry.EtaleProEtaleScalarMateData
import all WeilConjectures.AlgebraicGeometry.FiniteClosedRealizationDomain
import all WeilConjectures.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import WeilConjectures.AlgebraicGeometry.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor
import WeilConjectures.AlgebraicGeometry.FiniteClosedShriekMapPart
import all WeilConjectures.AlgebraicGeometry.FiniteClosedShriekDomainPart

/-! # Finite coefficient change for closed exceptional inverse image

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general, order 2139,
lemma finite coefficient change for closed support (blueprint: lem-coef-finite-closed-shriek).

The maps use the specified pro-etale exceptional functor and ordinary derived scalar
extension. The closed map is uniquely normalized by the exceptional counit. Total
extensions by zero below are used only outside the domains asserted by the theorems.
The closed-composition map is likewise uniquely normalized by the pasted counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

-- Cache these repeated derived-category prerequisites inside this proof module.
private theorem finiteClosedProEtGroth (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  inferInstance

private theorem finiteClosedEtGroth (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  inferInstance

private theorem finiteClosedEtSheafify (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) : HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  inferInstance

private theorem finiteClosedProEtInjectives (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  inferInstance

attribute [local instance] finiteClosedProEtGroth finiteClosedEtGroth
  finiteClosedEtSheafify finiteClosedProEtInjectives

namespace WeilConjectures

/-- The fixed-scalar presentation of the actual small pro-etale derived category.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev finiteClosedDerived (T : Scheme.{u}) (A : Type u) [CommRing A] :=
  DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))

/-- The positive coefficient stage with exponent n+1; this covers every level at least one.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev finiteClosedCoefficient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :=
  Padic.coefficientExtensionRing l E (n + 1)

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- The recorded ordinary uncompleted derived change of constant coefficients.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev finiteClosedScalar (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    (T : Scheme.{u}) : finiteClosedDerived T A ⥤ finiteClosedDerived T B :=
  @ProEtale.pbcFixedScalarExtension.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T) _ _ _ _ φ

/-- Ordinary derived direct image in these coefficient coordinates.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev finiteClosedPush (A : Type u) [CommRing A] {Z X : Scheme.{u}} (i : Z ⟶ X) :
    finiteClosedDerived Z A ⥤ finiteClosedDerived X A :=
  (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).rightDerivedFunctor

/-- Exact derived inverse image, written with its published left-derived functor.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev finiteClosedPull (A : Type u) [CommRing A] {Z X : Scheme.{u}} (i : Z ⟶ X) :
    finiteClosedDerived X A ⥤ finiteClosedDerived Z A :=
  (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).leftDerivedFunctor

/-- The recorded constructible exceptional functor at the identity-open compactification.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev finiteClosedExceptional (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  ProEtale.sfFiniteExceptionalFixed A (Compactification.ofIsProper i)

/-- The exceptional counit, using the relative constructible adjunction on bounded inputs.
The zero value elsewhere only makes the formula total.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
def finiteClosedCounit (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : finiteClosedDerived X A) :
    (finiteClosedPush A i).obj ((finiteClosedExceptional A i).obj M) ⟶ M := by
  letI := (Compactification.ofIsProper i).hasCompactification
  exact
    open Classical in
    if hX : CompactSpace X then
      letI := hX
      if hM : DerivedCategory.TStructure.t.plus M then
        (ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).inv.app _ ≫
          ProEtale.rightDerivedUpperShriekCounit i M hM
      else 0
    else 0

/-- Inverse of the specified ordinary coefficient comparison on its isomorphism domain.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
def finiteClosedDirectInverse
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {Z X : Scheme.{u}} (i : Z ⟶ X) (N : finiteClosedDerived Z A) :
    (finiteClosedPush B i).obj ((finiteClosedScalar φ Z).obj N) ⟶
      (finiteClosedScalar φ X).obj ((finiteClosedPush A i).obj N) :=
  open Classical in
  if h : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ i N) then
    @inv _ _ _ _ (ProEtale.finiteCoefficientChangeDirectImageMap φ i N) h
  else 0

/-- The defining exceptional-counit equation, in the B-linear derived category.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
def IsFiniteClosedShriekMap [Finite A] [Finite B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : finiteClosedDerived X A)
    (b : (finiteClosedScalar φ Z).obj ((finiteClosedExceptional A i).obj M) ⟶
      (finiteClosedExceptional B i).obj ((finiteClosedScalar φ X).obj M)) : Prop :=
  (finiteClosedPush B i).map b ≫
      finiteClosedCounit B i ((finiteClosedScalar φ X).obj M) =
    finiteClosedDirectInverse φ i ((finiteClosedExceptional A i).obj M) ≫
      (finiteClosedScalar φ X).map (finiteClosedCounit A i M)

/-- The canonical adjoint-defined comparison. Its normalization uniquely specifies
the arrow on the stated finite-Tor domain; elsewhere the definition is extended by zero.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
def finiteClosedShriekMap [Finite A] [Finite B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : finiteClosedDerived X A) :
    (finiteClosedScalar φ Z).obj ((finiteClosedExceptional A i).obj M) ⟶
      (finiteClosedExceptional B i).obj ((finiteClosedScalar φ X).obj M) :=
  open Classical in
  if h : ∃! b, IsFiniteClosedShriekMap φ i M b then h.exists.choose else 0

/-- The canonical exceptional composition map, normalized by the pasted closed counits.
Its normalization is the chained relative adjunction, not a chosen arbitrary isomorphism.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
def IsFiniteClosedComposition (A : Type u) [CommRing A] [Finite A]
    {W Z X : Scheme.{u}} (k : W ⟶ Z) (i : Z ⟶ X)
    [IsClosedImmersion k] [IsClosedImmersion i] (M : finiteClosedDerived X A)
    (d : (finiteClosedExceptional A k).obj ((finiteClosedExceptional A i).obj M) ⟶
      (finiteClosedExceptional A (k ≫ i)).obj M) : Prop :=
  (finiteClosedPush A (k ≫ i)).map d ≫ finiteClosedCounit A (k ≫ i) M =
    (ProEtale.finiteDirectImageComposition (ULift.{u + 1, u} A) k i).hom.app
        ((finiteClosedExceptional A k).obj ((finiteClosedExceptional A i).obj M)) ≫
      (finiteClosedPush A i).map
        (finiteClosedCounit A k ((finiteClosedExceptional A i).obj M)) ≫
      finiteClosedCounit A i M

/-- The unique pasted-counit composition comparison, extended by zero off its domain.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
def finiteClosedComposition (A : Type u) [CommRing A] [Finite A]
    {W Z X : Scheme.{u}} (k : W ⟶ Z) (i : Z ⟶ X)
    [IsClosedImmersion k] [IsClosedImmersion i] (M : finiteClosedDerived X A) :
    (finiteClosedExceptional A k).obj ((finiteClosedExceptional A i).obj M) ⟶
      (finiteClosedExceptional A (k ≫ i)).obj M :=
  open Classical in
  if h : ∃! d, IsFiniteClosedComposition A k i M d then h.exists.choose else 0

/-- Canonical scalar extension versus inverse image, conjugate to the actual
restriction/direct-image comparison. Its inverse gives the open-restriction coefficient map.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
def finiteClosedScalarPullIso [Finite A] [Finite B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {V X : Scheme.{u}} (j : V ⟶ X) :
    finiteClosedScalar φ X ⋙ finiteClosedPull B j ≅
      finiteClosedPull A j ⋙ finiteClosedScalar φ V := by
    letI : EssentiallySmall.{u + 1} X.ProEt :=
      essentiallySmallSelf.{0, u, u + 1} _
    letI : EssentiallySmall.{u + 1} V.ProEt :=
      essentiallySmallSelf.{0, u, u + 1} _
    exact
      (conjugateIsoEquiv
        ((ProEtale.derivedUpperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).comp
          (Adjunction.ofIsRightAdjoint
            (@Sheaf.derivedRestrictScalars.{u} V.ProEt inferInstance
              (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology V) _ _ _ _ φ)))
        ((Adjunction.ofIsRightAdjoint
            (@Sheaf.derivedRestrictScalars.{u} X.ProEt inferInstance
              (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology X) _ _ _ _ φ)).comp
          (ProEtale.derivedUpperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j))).symm
        (ProEtale.fixedScalarRestrictionDirectImage φ j)

/-- Open extension by zero, the exact left adjoint of open restriction.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev finiteClosedOpenPush (A : Type u) [CommRing A]
    {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] :=
  (ProEtale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory

/-- The canonical coefficient isomorphism for extension by zero, obtained from
the open/scalar adjunctions and the recorded restriction/pullback comparison.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
def finiteClosedOpenScalarIso [Finite A] [Finite B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] :
    finiteClosedOpenPush A j ⋙ finiteClosedScalar φ X ≅
    finiteClosedScalar φ V ⋙ finiteClosedOpenPush B j := by
    letI : EssentiallySmall.{u + 1} X.ProEt :=
      essentiallySmallSelf.{0, u, u + 1} _
    letI : EssentiallySmall.{u + 1} V.ProEt :=
      essentiallySmallSelf.{0, u, u + 1} _
    exact
      ((conjugateIsoEquiv
        ((ProEtale.fixedScalarOpenAdjunction (ULift.{u + 1, u} A) j).comp
          (Adjunction.ofIsRightAdjoint
            (@Sheaf.derivedRestrictScalars.{u} X.ProEt inferInstance
              (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology X) _ _ _ _ φ)))
        ((Adjunction.ofIsRightAdjoint
            (@Sheaf.derivedRestrictScalars.{u} V.ProEt inferInstance
              (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology V) _ _ _ _ φ)).comp
          (ProEtale.fixedScalarOpenAdjunction (ULift.{u + 1, u} B) j))).symm
        (ProEtale.fixedScalarRestrictionPullback φ j)).symm

/-- The locally closed exceptional functor for the specified closed/open factorization.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev finiteLocallyClosedExceptional (A : Type u) [CommRing A] [Finite A]
    {W V X : Scheme.{u}} (k : W ⟶ V) (j : V ⟶ X)
    [IsClosedImmersion k] [IsOpenImmersion j] :=
  finiteClosedPull A j ⋙ finiteClosedExceptional A k

/-- The corresponding compact-support direct image j_! k_*.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
abbrev finiteLocallyClosedPush (A : Type u) [CommRing A]
    {W V X : Scheme.{u}} (k : W ⟶ V) (j : V ⟶ X) [IsOpenImmersion j] :=
  finiteClosedPush A k ⋙ finiteClosedOpenPush A j

/-- The locally closed comparison: closed comparison on j^*M followed by
exceptional image of the canonical open-restriction coefficient isomorphism.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
def finiteLocallyClosedShriekMap [Finite A] [Finite B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {W V X : Scheme.{u}} (k : W ⟶ V) (j : V ⟶ X)
    [IsClosedImmersion k] [IsOpenImmersion j] (M : finiteClosedDerived X A) :
    (finiteClosedScalar φ W).obj ((finiteLocallyClosedExceptional A k j).obj M) ⟶
      (finiteLocallyClosedExceptional B k j).obj ((finiteClosedScalar φ X).obj M) :=
  finiteClosedShriekMap φ k ((finiteClosedPull A j).obj M) ≫
    (finiteClosedExceptional B k).map ((finiteClosedScalarPullIso φ j).inv.app M)

/-- The pasted locally closed exceptional counit ε_j followed after j_!ε_k.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
def finiteLocallyClosedCounit (A : Type u) [CommRing A] [Finite A]
    {W V X : Scheme.{u}} (k : W ⟶ V) (j : V ⟶ X)
    [IsClosedImmersion k] [IsOpenImmersion j] (M : finiteClosedDerived X A) :
    (finiteLocallyClosedPush A k j).obj
      ((finiteLocallyClosedExceptional A k j).obj M) ⟶ M :=
  (finiteClosedOpenPush A j).map (finiteClosedCounit A k ((finiteClosedPull A j).obj M)) ≫
    (ProEtale.fixedScalarOpenAdjunction (ULift.{u + 1, u} A) j).counit.app M

/-- The locally closed compact-support coefficient map, the open coefficient
isomorphism followed by j_! of the closed direct-image coefficient comparison.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
def finiteLocallyClosedCoefficientMap [Finite A] [Finite B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {W V X : Scheme.{u}} (k : W ⟶ V) (j : V ⟶ X)
    [IsClosedImmersion k] [IsOpenImmersion j] (N : finiteClosedDerived W A) :
    (finiteClosedScalar φ X).obj ((finiteLocallyClosedPush A k j).obj N) ⟶
      (finiteLocallyClosedPush B k j).obj ((finiteClosedScalar φ W).obj N) :=
  (finiteClosedOpenScalarIso φ j).hom.app ((finiteClosedPush A k).obj N) ≫
    (finiteClosedOpenPush B j).map (by
      simpa only [Functor.comp_obj] using
        (ProEtale.finiteCoefficientChangeDirectImageMap φ k N))

/-- Inverse of the normalized locally closed compact-support coefficient map
on its isomorphism domain, extended by zero elsewhere.
Source: blueprint finite coefficient change for closed support
(blueprint: lem-coef-finite-closed-shriek). -/
def finiteLocallyClosedCoefficientInverse [Finite A] [Finite B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {W V X : Scheme.{u}} (k : W ⟶ V) (j : V ⟶ X)
    [IsClosedImmersion k] [IsOpenImmersion j] (N : finiteClosedDerived W A) :
    (finiteLocallyClosedPush B k j).obj ((finiteClosedScalar φ W).obj N) ⟶
      (finiteClosedScalar φ X).obj ((finiteLocallyClosedPush A k j).obj N) :=
  open Classical in
  if h : IsIso (finiteLocallyClosedCoefficientMap φ k j N) then
    @inv _ _ _ _ (finiteLocallyClosedCoefficientMap φ k j N) h
  else 0

private theorem finiteClosedCounit_naturality (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [CompactSpace X]
    {M N : finiteClosedDerived X A}
    (hM : DerivedCategory.TStructure.t.plus M) (hN : DerivedCategory.TStructure.t.plus N)
    (f : M ⟶ N) :
    (finiteClosedPush A i).map ((finiteClosedExceptional A i).map f) ≫
        finiteClosedCounit A i N = finiteClosedCounit A i M ≫ f := by
  let := (Compactification.ofIsProper i).hasCompactification
  simp only [finiteClosedCounit, dif_pos (inferInstance : CompactSpace X), dif_pos hM,
    dif_pos hN]
  let e := ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i
  erw [← Category.assoc, e.inv.naturality]
  erw [Category.assoc, ProEtale.rightDerivedUpperShriekCounit_naturality i hM hN f]
  simp only [Category.assoc]
  rfl

private theorem finiteClosedCounit_injective (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [CompactSpace X]
    {K : finiteClosedDerived Z A} {M : finiteClosedDerived X A}
    (hK : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z K)
    (hM : DerivedCategory.TStructure.t.plus M)
    {b b' : K ⟶ (finiteClosedExceptional A i).obj M}
    (h : (finiteClosedPush A i).map b ≫ finiteClosedCounit A i M =
      (finiteClosedPush A i).map b' ≫ finiteClosedCounit A i M) : b = b' := by
  let := (Compactification.ofIsProper i).hasCompactification
  let e := ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i
  have eqn (b : K ⟶ (finiteClosedExceptional A i).obj M) :
      (finiteClosedPush A i).map b ≫ finiteClosedCounit A i M =
        e.inv.app K ≫ (ProEtale.rightDerivedUpperShriekHomEquiv i hK hM).symm b := by
    simp only [finiteClosedCounit, dif_pos (inferInstance : CompactSpace X), dif_pos hM]
    erw [← Category.assoc, e.inv.naturality]
    simp only [ProEtale.rightDerivedUpperShriekHomEquiv_symm_apply, Category.assoc]
  rw [eqn, eqn] at h
  exact (ProEtale.rightDerivedUpperShriekHomEquiv i hK hM).symm.injective
    ((cancel_epi (e.inv.app K)).1 h)

private theorem finiteClosedDirectInverse_naturality
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {Z X : Scheme.{u}} (i : Z ⟶ X) {K N : finiteClosedDerived Z A}
    (hK : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ i K))
    (hN : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ i N)) (f : K ⟶ N) :
    (finiteClosedPush B i).map ((finiteClosedScalar φ Z).map f) ≫
        finiteClosedDirectInverse φ i N =
      finiteClosedDirectInverse φ i K ≫ (finiteClosedScalar φ X).map
        ((finiteClosedPush A i).map f) := by
  have := hK
  have := hN
  simp only [finiteClosedDirectInverse, dif_pos hK, dif_pos hN]
  apply (cancel_epi (ProEtale.finiteCoefficientChangeDirectImageMap φ i K)).1
  rw [IsIso.hom_inv_id_assoc]
  rw [← Category.assoc,
    ← ProEtale.finiteCoefficientDirectImageMap_naturality φ i f, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- The specified closed comparison is an isomorphism, both vertices are finite-Tor
constructible over B, and its adjoint and exceptional-counit normalizations hold.
Source: blueprint sec-six-functors/sk-prop-sf-biduality-general, order 2139,
finite coefficient change for closed support (blueprint: lem-coef-finite-closed-shriek).

Proof: 1. Descend to bounded constructible etale-origin flat models by
lem-sf-proetale-constructible-origin, lem-sf-comparison-tor-amplitude and
lem-sf-etale-flat-constructible. Scalar extension preserves their Tor interval.
2. Apply thm-sf-preservation-class separately over E and L to check both exceptional
domains. 3. Tensor the localization triangle using prop-sf-localization-all-stages.
The first and third ordinary comparisons are lem-coef-finite-direct-image. The open
unit square follows by transposing the extended ordinary counit. 4. TR3 and
lem-sf-triangle-morphism-iso give an invertible first arrow. The full faithfulness
of the closed image, prop-sf-closed-unit-all-stages, identifies it with the unique
exceptional transpose. Thus precisely finiteClosedShriekMap is invertible.
5. Injectivity of the relative Hom bijection proves its displayed normalization.
No flatness or finite projective dimension of B over A is assumed. -/
theorem finiteCoefficientClosedShriek
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (m n : ℕ)
    (φ : ULift.{u + 1, u} (finiteClosedCoefficient l E m) →+* ULift.{u + 1, u}
      (finiteClosedCoefficient l L n))
    (X Z : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (M : finiteClosedDerived X.left (finiteClosedCoefficient l E m))
    (_hM : finiteTorConstructibleProEtaleModule l E (m + 1)
      (Nat.succ_pos m) X.left M) :
    (∃! b, IsFiniteClosedShriekMap φ i.left M b) ∧
    IsFiniteClosedShriekMap φ i.left M (finiteClosedShriekMap φ i.left M) ∧
    IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ i.left
      ((finiteClosedExceptional (finiteClosedCoefficient l E m) i.left).obj M)) ∧
    IsIso (finiteClosedShriekMap φ i.left M) ∧
    finiteTorConstructibleProEtaleModule l L (n + 1) (Nat.succ_pos n) X.left
      ((finiteClosedScalar φ X.left).obj M) ∧
    finiteTorConstructibleProEtaleModule l L (n + 1) (Nat.succ_pos n) Z.left
      ((finiteClosedScalar φ Z.left).obj ((finiteClosedExceptional (finiteClosedCoefficient l E m)
        i.left).obj M)) ∧
    finiteTorConstructibleProEtaleModule l L (n + 1) (Nat.succ_pos n) Z.left
      ((finiteClosedExceptional (finiteClosedCoefficient l L n) i.left).obj ((finiteClosedScalar φ
        X.left).obj M)) := by
  have hm := finiteClosedShriek_mapPart D l _hl E L m n φ X Z i M _hM
  have hd := finiteClosedShriek_domainPart D l _hl E L m n φ X Z i M _hM
  refine ⟨?_, ?_, hm.2.2.1, hm.2.2.2, hd.1, hd.2.1, hd.2.2⟩
  · exact hm.1
  · exact hm.2.1

-- Keep the total comparison maps folded while manipulating their counit equations.
attribute [local irreducible] finiteClosedCounit finiteClosedShriekMap finiteClosedComposition
  finiteClosedDirectInverse

/-- Naturality in every morphism between finite-Tor constructible inputs.
Source: blueprint sec-six-functors/sk-prop-sf-biduality-general, order 2139,
finite coefficient change for closed support (blueprint: lem-coef-finite-closed-shriek).

Proof: Transpose both paths through the B exceptional adjunction. Naturality of the
ordinary coefficient comparison and of the A exceptional counit gives equal
transposes. Injectivity of the Hom bijection gives equality. -/
theorem finiteCoefficientClosedShriek_naturality
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (m n : ℕ)
    (φ : ULift.{u + 1, u} (finiteClosedCoefficient l E m) →+* ULift.{u + 1, u}
      (finiteClosedCoefficient l L n))
    (X Z : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (M N : finiteClosedDerived X.left (finiteClosedCoefficient l E m))
    (_hM : finiteTorConstructibleProEtaleModule l E (m + 1)
      (Nat.succ_pos m) X.left M)
    (_hN : finiteTorConstructibleProEtaleModule l E (m + 1)
      (Nat.succ_pos m) X.left N) (f : M ⟶ N) :
    (finiteClosedScalar φ Z.left).map ((finiteClosedExceptional (finiteClosedCoefficient l E m)
      i.left).map f) ≫
        finiteClosedShriekMap φ i.left N =
      finiteClosedShriekMap φ i.left M ≫
        (finiteClosedExceptional (finiteClosedCoefficient l L n) i.left).map ((finiteClosedScalar
          φ X.left).map f) := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have hM := finiteCoefficientClosedShriek D l _hl E L m n φ X Z i M _hM
  have hN := finiteCoefficientClosedShriek D l _hl E L m n φ X Z i N _hN
  have hK := (finiteClosed_intrinsic_bc_realization_iff l L (n + 1) (Nat.succ_pos n) Z.left _).1
    hM.2.2.2.2.2.1.1
  have hMB := (finiteClosed_intrinsic_bc_realization_iff l L (n + 1) (Nat.succ_pos n) X.left _).1
    hM.2.2.2.2.1.1
  have hNB := (finiteClosed_intrinsic_bc_realization_iff l L (n + 1) (Nat.succ_pos n) X.left _).1
    hN.2.2.2.2.1.1
  have hMA := (finiteClosed_intrinsic_bc_realization_iff l E (m + 1)
    (Nat.succ_pos m) X.left _).1 _hM.1
  have hNA := (finiteClosed_intrinsic_bc_realization_iff l E (m + 1)
    (Nat.succ_pos m) X.left _).1 _hN.1
  apply finiteClosedCounit_injective (finiteClosedCoefficient l L n) i.left
    hK.plusEtaleOrigin hNB.bounded.1
  rw [Functor.map_comp, Functor.map_comp, Category.assoc]
  rw [show (finiteClosedPush (finiteClosedCoefficient l L n) i.left).map
      (finiteClosedShriekMap φ i.left N) ≫
        finiteClosedCounit (finiteClosedCoefficient l L n) i.left
          ((finiteClosedScalar φ X.left).obj N) = _ from hN.2.1]
  rw [Category.assoc, finiteClosedCounit_naturality _ i.left
    hMB.bounded.1 hNB.bounded.1 ((finiteClosedScalar φ X.left).map f)]
  rw [reassoc_of% hM.2.1]
  rw [← Category.assoc, finiteClosedDirectInverse_naturality φ i.left hM.2.2.1 hN.2.2.1,
    Category.assoc, ← Functor.map_comp, finiteClosedCounit_naturality _ i.left
      hMA.bounded.1 hNA.bounded.1 f, Functor.map_comp]

private def closedHom (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [CompactSpace X]
    {K : finiteClosedDerived Z A} {M : finiteClosedDerived X A}
    (hK : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z K)
    (hM : DerivedCategory.TStructure.t.plus M) :
    ((finiteClosedPush A i).obj K ⟶ M) ≃ (K ⟶ (finiteClosedExceptional A i).obj M) := by
  let := (Compactification.ofIsProper i).hasCompactification
  exact (ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).symm.app K |>.homFromEquiv |>.trans
      (ProEtale.rightDerivedUpperShriekHomEquiv i hK hM)

private theorem closedHom_symm (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [CompactSpace X]
    {K : finiteClosedDerived Z A} {M : finiteClosedDerived X A}
    (hK : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z K)
    (hM : DerivedCategory.TStructure.t.plus M)
    (f : K ⟶ (finiteClosedExceptional A i).obj M) :
    (closedHom A i hK hM).symm f =
      (finiteClosedPush A i).map f ≫ finiteClosedCounit A i M := by
  let := (Compactification.ofIsProper i).hasCompactification
  let e := ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i
  simp only [closedHom, Equiv.symm_trans_apply,
    Iso.homFromEquiv_symm_apply, Iso.app_hom, Iso.symm_hom,
    finiteClosedCounit, dif_pos (inferInstance : CompactSpace X), dif_pos hM]
  erw [ProEtale.rightDerivedUpperShriekHomEquiv_symm_apply]
  symm
  erw [← Category.assoc, e.inv.naturality]
  simp only [Category.assoc]
  rfl

private theorem closedPush_origin (A : Type u) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {K : finiteClosedDerived Z A}
    (hK : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z K) :
    ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X ((finiteClosedPush A i).obj K) := by
  let := (Compactification.ofIsProper i).hasCompactification
  exact (ProEtale.DerivedCategory.plusEtaleOrigin _ X).prop_of_iso
    ((ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).app K)
    (hK.rightDerivedLowerShriek_obj i)

private theorem closedRight_origin (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [CompactSpace X]
    {M : finiteClosedDerived X A} (hM : DerivedCategory.TStructure.t.plus M) :
    ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z
      ((finiteClosedExceptional A i).obj M) := by
  let := (Compactification.ofIsProper i).hasCompactification
  exact ProEtale.plusEtaleOrigin_rightDerivedUpperShriek_obj i hM

private theorem closedComposition_part (A : Type u) [CommRing A] [Finite A]
    {W Z X : Scheme.{u}} (k : W ⟶ Z) (i : Z ⟶ X)
    [IsClosedImmersion k] [IsClosedImmersion i] [CompactSpace X] [CompactSpace Z]
    (M : finiteClosedDerived X A) (hM : DerivedCategory.TStructure.t.plus M) :
    (∃! d, IsFiniteClosedComposition A k i M d) ∧
    IsFiniteClosedComposition A k i M (finiteClosedComposition A k i M) ∧
    IsIso (finiteClosedComposition A k i M) := by
  let J := (finiteClosedExceptional A k).obj ((finiteClosedExceptional A i).obj M)
  have hi := closedRight_origin A i hM
  have hJ := closedRight_origin A k hi.plus
  let p := (ProEtale.finiteDirectImageComposition (ULift.{u + 1, u} A) k i).hom.app J ≫
    (finiteClosedPush A i).map (finiteClosedCounit A k
      ((finiteClosedExceptional A i).obj M)) ≫ finiteClosedCounit A i M
  let e := closedHom A (k ≫ i) hJ hM
  have hd : IsFiniteClosedComposition A k i M (e p) := by
    change (finiteClosedPush A (k ≫ i)).map (e p) ≫ finiteClosedCounit A (k ≫ i) M = p
    rw [← closedHom_symm A (k ≫ i) hJ hM, Equiv.symm_apply_apply]
  have hu : ∃! d, IsFiniteClosedComposition A k i M d := by
    refine ⟨e p, hd, ?_⟩
    intro d hd'
    exact e.symm.injective (by rw [closedHom_symm, closedHom_symm]; exact hd'.trans hd.symm)
  have hchosen : finiteClosedComposition A k i M = e p := by
    simp only [finiteClosedComposition, dif_pos hu]
    exact hu.unique hu.exists.choose_spec hd
  refine ⟨hu, hchosen ▸ hd, ?_⟩
  rw [hchosen]
  have key {K : finiteClosedDerived W A}
      (hK : ProEtale.DerivedCategory.plusEtaleOrigin
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) W K) :
      Function.Bijective (fun g : K ⟶ J ↦ g ≫ e p) := by
    let c := (closedHom A k hK hi.plus).symm.trans
      ((closedHom A i (closedPush_origin A k hK) hM).symm.trans
        ((ProEtale.finiteDirectImageComposition (ULift.{u + 1, u} A) k i).symm.app K).homFromEquiv)
    have heq : (fun g : K ⟶ J ↦ g ≫ e p) =
        (closedHom A (k ≫ i) hK hM) ∘ c := by
      funext g
      apply (closedHom A (k ≫ i) hK hM).symm.injective
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
      simp only [closedHom_symm, Functor.map_comp, Category.assoc]
      rw [show (finiteClosedPush A (k ≫ i)).map (e p) ≫
        finiteClosedCounit A (k ≫ i) M = p from hd]
      dsimp only [c, Equiv.trans_apply, Iso.homFromEquiv_apply]
      rw [closedHom_symm, closedHom_symm]
      simp only [Functor.map_comp, Category.assoc]
      dsimp only [p]
      rw [← Category.assoc,
        (ProEtale.finiteDirectImageComposition (ULift.{u + 1, u} A) k i).hom.naturality]
      simp only [Functor.comp_map, Category.assoc]
      rfl
    rw [heq]
    exact (closedHom A (k ≫ i) hK hM).bijective.comp c.bijective
  obtain ⟨r, hr⟩ := (key (closedRight_origin A (k ≫ i) hM)).2 (𝟙 _)
  refine ⟨r, (key hJ).1 ?_, hr⟩
  simp only [Category.assoc, hr, Category.comp_id, Category.id_comp]

private theorem closedComposition_naturality (A : Type u) [CommRing A] [Finite A]
    {W Z X : Scheme.{u}} (k : W ⟶ Z) (i : Z ⟶ X)
    [IsClosedImmersion k] [IsClosedImmersion i] [CompactSpace X] [CompactSpace Z]
    {M N : finiteClosedDerived X A}
    (hM : DerivedCategory.TStructure.t.plus M) (hN : DerivedCategory.TStructure.t.plus N)
    (f : M ⟶ N) :
    (finiteClosedExceptional A k).map ((finiteClosedExceptional A i).map f) ≫
        finiteClosedComposition A k i N =
      finiteClosedComposition A k i M ≫ (finiteClosedExceptional A (k ≫ i)).map f := by
  have hJM := closedRight_origin A i hM
  have hJN := closedRight_origin A i hN
  have hm := (closedComposition_part A k i M hM).2.1
  have hn := (closedComposition_part A k i N hN).2.1
  apply finiteClosedCounit_injective A (k ≫ i) (closedRight_origin A k hJM.plus) hN
  simp only [Functor.map_comp, Category.assoc]
  rw [finiteClosedCounit_naturality A (k ≫ i) hM hN f]
  rw [show (finiteClosedPush A (k ≫ i)).map (finiteClosedComposition A k i N) ≫
      finiteClosedCounit A (k ≫ i) N = _ from hn]
  rw [reassoc_of% hm]
  rw [← Category.assoc,
    (ProEtale.finiteDirectImageComposition (ULift.{u + 1, u} A) k i).hom.naturality]
  simp only [Functor.comp_map, Category.assoc]
  slice_lhs 2 3 =>
    rw [← Functor.map_comp, finiteClosedCounit_naturality A k hJM.plus hJN.plus,
      Functor.map_comp]
  simp only [Category.assoc]
  rw [finiteClosedCounit_naturality A i hM hN f]

/-- Compatibility with closed composition under the uniquely counit-normalized
composition identifications, including their invertibility on the required objects.
Source: blueprint sec-six-functors/sk-prop-sf-biduality-general, order 2139,
finite coefficient change for closed support (blueprint: lem-coef-finite-closed-shriek).

Proof: Transpose under the chained closed Hom bijections. Substitute the two defining
exceptional-counit equations, use lem-coef-finite-direct-image for composition
and lem-weil-derived-direct-image-composition for the direct-image compositor.
Both transposes are scalar extension of the pasted A counit. Its uniqueness also
identifies the composition comparisons and proves their invertibility. -/
theorem finiteCoefficientClosedShriek_comp
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (m n : ℕ)
    (φ : ULift.{u + 1, u} (finiteClosedCoefficient l E m) →+* ULift.{u + 1, u}
      (finiteClosedCoefficient l L n))
    (X Z : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (W : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated W.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (k : W ⟶ Z) [IsClosedImmersion k.left]
    (M : finiteClosedDerived X.left (finiteClosedCoefficient l E m))
    (_hM : finiteTorConstructibleProEtaleModule l E (m + 1)
      (Nat.succ_pos m) X.left M) :
    (∃! d, IsFiniteClosedComposition (finiteClosedCoefficient l E m) k.left i.left M d) ∧
    IsFiniteClosedComposition (finiteClosedCoefficient l E m) k.left i.left M
      (finiteClosedComposition (finiteClosedCoefficient l E m) k.left i.left M) ∧
    IsIso (finiteClosedComposition (finiteClosedCoefficient l E m) k.left i.left M) ∧
    (∃! d, IsFiniteClosedComposition (finiteClosedCoefficient l L n) k.left i.left
      ((finiteClosedScalar φ X.left).obj M) d) ∧
    IsFiniteClosedComposition (finiteClosedCoefficient l L n) k.left i.left ((finiteClosedScalar φ
      X.left).obj M)
      (finiteClosedComposition (finiteClosedCoefficient l L n) k.left i.left ((finiteClosedScalar
        φ X.left).obj M)) ∧
    IsIso (finiteClosedComposition (finiteClosedCoefficient l L n) k.left i.left
      ((finiteClosedScalar φ X.left).obj M)) ∧
    (finiteClosedScalar φ W.left).map (finiteClosedComposition (finiteClosedCoefficient l E m)
      k.left i.left M) ≫
        finiteClosedShriekMap φ (k.left ≫ i.left) M =
      finiteClosedShriekMap φ k.left ((finiteClosedExceptional (finiteClosedCoefficient l E m)
        i.left).obj M) ≫
        (finiteClosedExceptional (finiteClosedCoefficient l L n) k.left).map
          (finiteClosedShriekMap φ i.left M) ≫
        finiteClosedComposition (finiteClosedCoefficient l L n) k.left i.left ((finiteClosedScalar
          φ X.left).obj M) := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  let A := finiteClosedCoefficient l E m
  let B := finiteClosedCoefficient l L n
  let NA := (finiteClosedExceptional A i.left).obj M
  let JA := (finiteClosedExceptional A k.left).obj NA
  let MB := (finiteClosedScalar φ X.left).obj M
  let NB := (finiteClosedExceptional B i.left).obj MB
  have hMA := (finiteClosed_intrinsic_bc_realization_iff l E (m + 1)
    (Nat.succ_pos m) X.left M).1 _hM.1
  have hNA := splitExceptionalDomain_preserves D l _hl E m X Z i M _hM
  have hi := finiteCoefficientClosedShriek D l _hl E L m n φ X Z i M _hM
  have hk := finiteCoefficientClosedShriek D l _hl E L m n φ Z W k NA hNA
  have : IsClosedImmersion (k ≫ i).left := by
    change IsClosedImmersion (k.left ≫ i.left)
    infer_instance
  have hc := finiteCoefficientClosedShriek D l _hl E L m n φ X W (k ≫ i) M _hM
  have hMB := (finiteClosed_intrinsic_bc_realization_iff l L (n + 1)
    (Nat.succ_pos n) X.left MB).1 hi.2.2.2.2.1.1
  have hSJA := (finiteClosed_intrinsic_bc_realization_iff l L (n + 1)
    (Nat.succ_pos n) W.left _).1 hk.2.2.2.2.2.1.1
  have hSNA := (finiteClosed_intrinsic_bc_realization_iff l L (n + 1)
    (Nat.succ_pos n) Z.left _).1 hi.2.2.2.2.2.1.1
  have hNB := (finiteClosed_intrinsic_bc_realization_iff l L (n + 1)
    (Nat.succ_pos n) Z.left NB).1 hi.2.2.2.2.2.2.1
  have hcompA := closedComposition_part A k.left i.left M hMA.bounded.1
  have hcompB := closedComposition_part B k.left i.left MB hMB.bounded.1
  refine ⟨hcompA.1, hcompA.2.1, hcompA.2.2,
    hcompB.1, hcompB.2.1, hcompB.2.2, ?_⟩
  have normalized {R S : Type u} [CommRing R] [CommRing S] [Finite R] [Finite S]
      (φ : ULift.{u + 1, u} R →+* ULift.{u + 1, u} S)
      {V T : Scheme.{u}} (j : V ⟶ T) [IsClosedImmersion j]
      (N : finiteClosedDerived T R)
      (h : IsFiniteClosedShriekMap φ j N (finiteClosedShriekMap φ j N))
      (hc : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ j
        ((finiteClosedExceptional R j).obj N))) :
      ProEtale.finiteCoefficientChangeDirectImageMap φ j
          ((finiteClosedExceptional R j).obj N) ≫
        (finiteClosedPush S j).map (finiteClosedShriekMap φ j N) ≫
        finiteClosedCounit S j ((finiteClosedScalar φ T).obj N) =
      (finiteClosedScalar φ T).map (finiteClosedCounit R j N) := by
    change _ ≫ ((finiteClosedPush S j).map _ ≫ _) = _
    rw [show (finiteClosedPush S j).map (finiteClosedShriekMap φ j N) ≫
      finiteClosedCounit S j ((finiteClosedScalar φ T).obj N) = _ from h]
    simp only [finiteClosedDirectInverse, dif_pos hc, IsIso.hom_inv_id_assoc]
  have hni := normalized φ i.left M hi.2.1 hi.2.2.1
  have hnk := normalized φ k.left NA hk.2.1 hk.2.2.1
  have hnc := normalized φ (k.left ≫ i.left) M hc.2.1 hc.2.2.1
  have ciso : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ
      (k.left ≫ i.left) JA) := by
    have hn := ProEtale.finiteCoefficientDirectImageMap_naturality φ
      (k.left ≫ i.left) (finiteClosedComposition A k.left i.left M)
    have hδ : IsIso (finiteClosedComposition A k.left i.left M) := hcompA.2.2
    have hciso := hc.2.2.1
    have hboth : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ
        (k.left ≫ i.left) JA ≫ (finiteClosedPush B (k.left ≫ i.left)).map
          ((finiteClosedScalar φ W.left).map (finiteClosedComposition A k.left i.left M))) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((finiteClosedPush B (k.left ≫ i.left)).map
        ((finiteClosedScalar φ W.left).map (finiteClosedComposition A k.left i.left M)))
  apply finiteClosedCounit_injective B (k.left ≫ i.left)
    hSJA.plusEtaleOrigin hMB.bounded.1
  apply (cancel_epi (ProEtale.finiteCoefficientChangeDirectImageMap φ
    (k.left ≫ i.left) JA)).1
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (ProEtale.finiteCoefficientDirectImageMap_naturality φ
    (k.left ≫ i.left) (finiteClosedComposition A k.left i.left M)), hnc]
  rw [← Functor.map_comp, show (finiteClosedPush A (k.left ≫ i.left)).map
      (finiteClosedComposition A k.left i.left M) ≫
      finiteClosedCounit A (k.left ≫ i.left) M = _ from hcompA.2.1]
  rw [show (finiteClosedPush B (k.left ≫ i.left)).map
      (finiteClosedComposition B k.left i.left MB) ≫
      finiteClosedCounit B (k.left ≫ i.left) MB = _ from hcompB.2.1]
  slice_rhs 2 4 =>
    rw [← Functor.map_comp_assoc,
      (ProEtale.finiteDirectImageComposition (ULift.{u + 1, u} B)
        k.left i.left).hom.naturality]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [ProEtale.finiteCoefficientDirectImageMap_comp]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  slice_rhs 5 6 =>
    rw [← Functor.map_comp, finiteClosedCounit_naturality B k.left
      hSNA.bounded.1 hNB.bounded.1, Functor.map_comp]
  simp only [Category.assoc]
  slice_rhs 3 5 => rw [← Functor.map_comp, ← Functor.map_comp, hnk]
  simp only [Category.assoc]
  rw [← reassoc_of% (ProEtale.finiteCoefficientDirectImageMap_naturality φ i.left
    (finiteClosedCounit A k.left NA))]
  rw [hni]

private abbrev finiteClosedScalarComp
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    (ψ : ULift.{u + 1, u} B →+* ULift.{u + 1, u} C) (T : Scheme.{u}) :
    finiteClosedScalar φ T ⋙ finiteClosedScalar ψ T ≅
      finiteClosedScalar (ψ.comp φ) T :=
  @ProEtale.pbcFixedScalarExtensionComp.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
    _ _ _ _ _ _ φ ψ (ψ.comp φ) rfl

private theorem finiteClosedDirectInverse_chain
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    (ψ : ULift.{u + 1, u} B →+* ULift.{u + 1, u} C)
    {Z X : Scheme.{u}} (i : Z ⟶ X) (K : finiteClosedDerived Z A)
    (hφ : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ i K))
    (hψ : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap ψ i
      ((finiteClosedScalar φ Z).obj K)))
    (hχ : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap (ψ.comp φ) i K)) :
    (finiteClosedPush C i).map ((finiteClosedScalarComp φ ψ Z).hom.app K) ≫
        finiteClosedDirectInverse (ψ.comp φ) i K =
      finiteClosedDirectInverse ψ i ((finiteClosedScalar φ Z).obj K) ≫
        (finiteClosedScalar ψ X).map (finiteClosedDirectInverse φ i K) ≫
        (finiteClosedScalarComp φ ψ X).hom.app ((finiteClosedPush A i).obj K) := by
  let e := (finiteClosedScalarComp φ ψ X).symm.app ((finiteClosedPush A i).obj K) ≪≫
    (finiteClosedScalar ψ X).mapIso
      (asIso (ProEtale.finiteCoefficientChangeDirectImageMap φ i K)) ≪≫
    asIso (ProEtale.finiteCoefficientChangeDirectImageMap ψ i
      ((finiteClosedScalar φ Z).obj K)) ≪≫
    (finiteClosedPush C i).mapIso ((finiteClosedScalarComp φ ψ Z).app K)
  have he : asIso (ProEtale.finiteCoefficientChangeDirectImageMap (ψ.comp φ) i K) = e := by
    apply Iso.ext
    exact ProEtale.finiteCoefficientDirectImageMap_coefficientChain φ ψ i K
  have hi := congrArg Iso.inv he
  simp only [e, Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Functor.mapIso_inv,
    Category.assoc, asIso_inv] at hi
  simp only [finiteClosedDirectInverse, dif_pos hφ, dif_pos hψ, dif_pos hχ]
  rw [hi, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- Successive arbitrary finite coefficient homomorphisms, with canonical derived
scalar reassociation; identity maps and nonflat maps are included.
Source: blueprint sec-six-functors/sk-prop-sf-biduality-general, order 2139,
finite coefficient change for closed support (blueprint: lem-coef-finite-closed-shriek).

Proof: Compute iterated scalar extension on flat K-flat models by
lem-pur-kflat-change-of-rings and lem-pur-derived-change-of-rings. The compositor
is ordinary balancing (p tensor b) tensor c to p tensor bc. Ordinary coefficient
comparisons satisfy the same reassociation by their counit transpose. Transpose
both exceptional paths, substitute their defining counit equations and cancel
using the C exceptional adjunction. This also includes identity coefficient maps. -/
theorem finiteCoefficientClosedShriek_coefficientChain
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (m n : ℕ)
    (φ : ULift.{u + 1, u} (finiteClosedCoefficient l E m) →+* ULift.{u + 1, u}
      (finiteClosedCoefficient l L n))
    (X Z : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (r : ℕ) (ψ : ULift.{u + 1, u} (finiteClosedCoefficient l L n) →+*
      ULift.{u + 1, u} (finiteClosedCoefficient l F r))
    (M : finiteClosedDerived X.left (finiteClosedCoefficient l E m))
    (_hM : finiteTorConstructibleProEtaleModule l E (m + 1)
      (Nat.succ_pos m) X.left M) :
    (finiteClosedScalar ψ Z.left).map (finiteClosedShriekMap φ i.left M) ≫
        finiteClosedShriekMap ψ i.left ((finiteClosedScalar φ X.left).obj M) ≫
        (finiteClosedExceptional (finiteClosedCoefficient l F r) i.left).map
          (by
            simpa only [Functor.comp_obj] using
              (@ProEtale.pbcFixedScalarExtensionComp.{u} X.left.ProEt inferInstance
                (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology X.left)
                _ _ _ _ _ _ φ ψ (ψ.comp φ) rfl).hom.app M) =
      (by
        simpa only [Functor.comp_obj] using
          (@ProEtale.pbcFixedScalarExtensionComp.{u} Z.left.ProEt inferInstance
            (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology Z.left)
            _ _ _ _ _ _ φ ψ (ψ.comp φ) rfl).hom.app
            ((finiteClosedExceptional (finiteClosedCoefficient l E m) i.left).obj M)) ≫
        finiteClosedShriekMap (ψ.comp φ) i.left M := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let KA := (finiteClosedExceptional (finiteClosedCoefficient l E m) i.left).obj M
  let MB := (finiteClosedScalar φ X.left).obj M
  let KB := (finiteClosedExceptional (finiteClosedCoefficient l L n) i.left).obj MB
  have hφ := finiteCoefficientClosedShriek D l _hl E L m n φ X Z i M _hM
  have hψ := finiteCoefficientClosedShriek D l _hl L F n r ψ X Z i MB
    hφ.2.2.2.2.1
  have hχ := finiteCoefficientClosedShriek D l _hl E F m r (ψ.comp φ) X Z i M _hM
  have hφiso : IsIso (finiteClosedShriekMap φ i.left M) := hφ.2.2.2.1
  have hψdirect := hψ.2.2.1
  have hψsource : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap ψ i.left
      ((finiteClosedScalar φ Z.left).obj KA)) := by
    have hn := ProEtale.finiteCoefficientDirectImageMap_naturality ψ i.left
      (finiteClosedShriekMap φ i.left M)
    have hc : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap ψ i.left
        ((finiteClosedScalar φ Z.left).obj KA) ≫
        (finiteClosedPush (finiteClosedCoefficient l F r) i.left).map
          ((finiteClosedScalar ψ Z.left).map
            (finiteClosedShriekMap φ i.left M))) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((finiteClosedPush (finiteClosedCoefficient l F r) i.left).map
        ((finiteClosedScalar ψ Z.left).map (finiteClosedShriekMap φ i.left M)))
  have hsource := (finiteClosed_intrinsic_bc_realization_iff l F (r + 1) (Nat.succ_pos r)
    Z.left _).1 hψ.2.2.2.2.2.1.1
  have hsource' := (ProEtale.DerivedCategory.boundedConstructible
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (finiteClosedCoefficient l F r))) Z.left).prop_of_iso
      ((finiteClosedScalar ψ Z.left).mapIso (asIso (finiteClosedShriekMap φ i.left M))).symm
      hsource
  have htarget := (finiteClosed_intrinsic_bc_realization_iff l F (r + 1) (Nat.succ_pos r)
    X.left _).1 hχ.2.2.2.2.1.1
  have hmiddle := (finiteClosed_intrinsic_bc_realization_iff l F (r + 1) (Nat.succ_pos r)
    X.left _).1 hψ.2.2.2.2.1.1
  apply finiteClosedCounit_injective (finiteClosedCoefficient l F r) i.left
    hsource'.plusEtaleOrigin htarget.bounded.1
  change (finiteClosedPush (finiteClosedCoefficient l F r) i.left).map
      ((finiteClosedScalar ψ Z.left).map (finiteClosedShriekMap φ i.left M) ≫
        finiteClosedShriekMap ψ i.left MB ≫
        (finiteClosedExceptional (finiteClosedCoefficient l F r) i.left).map
          ((finiteClosedScalarComp φ ψ X.left).hom.app M)) ≫ _ =
    (finiteClosedPush (finiteClosedCoefficient l F r) i.left).map
      ((finiteClosedScalarComp φ ψ Z.left).hom.app KA ≫
        finiteClosedShriekMap (ψ.comp φ) i.left M) ≫ _
  simp only [Functor.map_comp, Category.assoc]
  rw [finiteClosedCounit_naturality _ i.left hmiddle.bounded.1 htarget.bounded.1,
    reassoc_of% hψ.2.1, hχ.2.1]
  rw [← Category.assoc, finiteClosedDirectInverse_naturality ψ i.left hψsource
    hψdirect (finiteClosedShriekMap φ i.left M)]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← Functor.map_comp, hφ.2.1, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (finiteClosedDirectInverse_chain φ ψ i.left KA
    hφ.2.2.1 hψsource hχ.2.2.1)]
  have hn := (finiteClosedScalarComp φ ψ X.left).hom.naturality
    (finiteClosedCounit (finiteClosedCoefficient l E m) i.left M)
  simp only [Functor.comp_map] at hn
  rw [hn]

private theorem finiteClosedPullInverseMate
    {CA DA CB DB : Type*} [Category CA] [Category DA] [Category CB] [Category DB]
    {PA : CA ⥤ DA} {IA : DA ⥤ CA} {PB : CB ⥤ DB} {IB : DB ⥤ CB}
    {SX : CA ⥤ CB} {RX : CB ⥤ CA} {SV : DA ⥤ DB} {RV : DB ⥤ DA}
    (a : PA ⊣ IA) (b : PB ⊣ IB) (x : SX ⊣ RX) (v : SV ⊣ RV)
    (q : RX ⋙ PA ≅ PB ⋙ RV)
    [IsIso (mateEquiv b a (TwoSquare.mk _ _ _ _ q.hom)).natTrans] :
    ((conjugateIsoEquiv (a.comp v) (x.comp b)).symm
      (asIso (mateEquiv b a (TwoSquare.mk _ _ _ _ q.hom)).natTrans).symm).inv =
      ((mateEquiv x v).symm (TwoSquare.mk _ _ _ _ q.hom)).natTrans := by
  apply (conjugateEquiv (x.comp b) (a.comp v)).injective
  change (conjugateEquiv (x.comp b) (a.comp v))
      ((conjugateEquiv (x.comp b) (a.comp v)).symm _) = _
  rw [Equiv.apply_symm_apply]
  have h := iterated_mateEquiv_conjugateEquiv x v a b
    ((mateEquiv x v).symm (TwoSquare.mk _ _ _ _ q.hom))
  rw [Equiv.apply_symm_apply] at h
  exact h

private theorem finiteClosedPullInverse {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {V X : Scheme.{u}} (j : V ⟶ X) :
    (finiteClosedScalarPullIso φ j).inv = ProEtale.scalarPullbackReverseProEtale φ j := by
  let a := ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j
  let b := ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j
  let x := Adjunction.ofIsRightAdjoint
    (@Sheaf.derivedRestrictScalars.{u} X.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology X) _ _ _ _ φ)
  let v := Adjunction.ofIsRightAdjoint
    (@Sheaf.derivedRestrictScalars.{u} V.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology V) _ _ _ _ φ)
  have hi := ProEtale.fixedScalarRestrictionDirectImageMap_isIso φ j
  change IsIso (mateEquiv b a
    (TwoSquare.mk _ _ _ _ (ProEtale.fixedScalarRestrictionPullback φ j).hom)).natTrans at hi
  dsimp only [finiteClosedScalarPullIso, ProEtale.scalarPullbackReverseProEtale,
    ProEtale.fixedScalarRestrictionDirectImage]
  exact finiteClosedPullInverseMate a b x v (ProEtale.fixedScalarRestrictionPullback φ j)

private theorem finiteClosedOpenCounitMate
    {CA DA CB DB : Type*} [Category CA] [Category DA] [Category CB] [Category DB]
    {JA : DA ⥤ CA} {PA : CA ⥤ DA} {JB : DB ⥤ CB} {PB : CB ⥤ DB}
    {SX : CA ⥤ CB} {RX : CB ⥤ CA} {SV : DA ⥤ DB} {RV : DB ⥤ DA}
    (a : JA ⊣ PA) (b : JB ⊣ PB) (x : SX ⊣ RX) (v : SV ⊣ RV)
    (q : RX ⋙ PA ≅ PB ⋙ RV) (M : CA) :
    (((conjugateIsoEquiv (a.comp x) (v.comp b)).symm q).symm).hom.app (PA.obj M) ≫
        JB.map (((mateEquiv x v).symm (TwoSquare.mk _ _ _ _ q.hom)).natTrans.app M) ≫
        b.counit.app (SX.obj M) = SX.map (a.counit.app M) := by
  let α := ((mateEquiv x v).symm (TwoSquare.mk _ _ _ _ q.hom))
  let e := ((conjugateIsoEquiv (a.comp x) (v.comp b)).symm q).symm
  have he : ((mateEquiv a b).symm α).natTrans = e.inv := by
    exact congrArg TwoSquare.natTrans
      (iterated_mateEquiv_conjugateEquiv_symm a b v x
        (TwoSquare.mk _ _ _ _ q.hom))
  have h := mateEquiv_counit_symm a b α M
  change JB.map (α.natTrans.app M) ≫ b.counit.app (SX.obj M) =
    ((mateEquiv a b).symm α).natTrans.app (PA.obj M) ≫ SX.map (a.counit.app M) at h
  rw [he] at h
  change e.hom.app _ ≫ _ = _
  rw [h, Iso.hom_inv_id_app_assoc]

private theorem finiteClosedOpenCounit {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    (M : finiteClosedDerived X A) :
    (finiteClosedOpenScalarIso φ j).hom.app ((finiteClosedPull A j).obj M) ≫
        (finiteClosedOpenPush B j).map ((finiteClosedScalarPullIso φ j).inv.app M) ≫
        (ProEtale.fixedScalarOpenAdjunction (ULift.{u + 1, u} B) j).counit.app
          ((finiteClosedScalar φ X).obj M) =
      (finiteClosedScalar φ X).map
        ((ProEtale.fixedScalarOpenAdjunction (ULift.{u + 1, u} A) j).counit.app M) := by
  rw [finiteClosedPullInverse]
  exact finiteClosedOpenCounitMate
    (ProEtale.fixedScalarOpenAdjunction (ULift.{u + 1, u} A) j)
    (ProEtale.fixedScalarOpenAdjunction (ULift.{u + 1, u} B) j)
    (Adjunction.ofIsRightAdjoint
      (@Sheaf.derivedRestrictScalars.{u} X.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology X) _ _ _ _ φ))
    (Adjunction.ofIsRightAdjoint
      (@Sheaf.derivedRestrictScalars.{u} V.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology V) _ _ _ _ φ))
    (ProEtale.fixedScalarRestrictionPullback φ j) M

attribute [local irreducible] finiteClosedScalarPullIso finiteClosedOpenScalarIso

private theorem finiteClosedPull_finiteTor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (m : ℕ)
    {V X : Scheme.{u}} (j : V ⟶ X)
    (M : finiteClosedDerived X (finiteClosedCoefficient l E m))
    (hM : finiteTorConstructibleProEtaleModule l E (m + 1) (Nat.succ_pos m) X M) :
    finiteTorConstructibleProEtaleModule l E (m + 1) (Nat.succ_pos m) V
      ((finiteClosedPull (finiteClosedCoefficient l E m) j).obj M) := by
  obtain ⟨hbc, a, b, ht⟩ := hM
  have hbc' := (finiteClosed_intrinsic_bc_realization_iff l E (m + 1) (Nat.succ_pos m) X M).1 hbc
  have ht' := (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    (finiteClosedCoefficient l E m) X a b ht.1 M).1 ht
  have h := ProEtale.boundedConstructible_and_torAmplitudeIn_leftDerivedFunctor_upperStar_obj
    j hbc' ht'
  exact ⟨(finiteClosed_intrinsic_bc_realization_iff l E (m + 1) (Nat.succ_pos m) V _).2 h.1,
    a, b, (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
      (finiteClosedCoefficient l E m) V a b ht.1 _).2 h.2⟩

private theorem finiteClosed_finiteTor_of_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (m : ℕ)
    (X : Scheme.{u}) {K L : finiteClosedDerived X (finiteClosedCoefficient l E m)}
    (e : K ≅ L)
    (hK : finiteTorConstructibleProEtaleModule l E (m + 1) (Nat.succ_pos m) X K) :
    finiteTorConstructibleProEtaleModule l E (m + 1) (Nat.succ_pos m) X L := by
  obtain ⟨hbc, a, b, ht⟩ := hK
  have hbc' := (finiteClosed_intrinsic_bc_realization_iff l E (m + 1) (Nat.succ_pos m) X K).1 hbc
  have ht' := (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    (finiteClosedCoefficient l E m) X a b ht.1 K).1 ht
  exact ⟨(finiteClosed_intrinsic_bc_realization_iff l E (m + 1) (Nat.succ_pos m) X L).2
      ((ProEtale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (finiteClosedCoefficient l E m))) X).prop_of_iso
        e hbc'),
    a, b, (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
      (finiteClosedCoefficient l E m) X a b ht.1 L).2
      ((DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e ht')⟩

/-- The chosen locally closed comparison has finite-Tor constructible vertices,
is invertible, and obeys the compact-support exceptional-counit equation.
Source: blueprint sec-six-functors/sk-prop-sf-biduality-general, order 2139,
finite coefficient change for closed support (blueprint: lem-coef-finite-closed-shriek).

Proof: Use lem-sf-pullback-tor-amplitude for j^*M. The closed theorem applied to k
and j^*M followed by the open scalar/pullback comparison gives the stated map.
The open extension-zero scalar comparison is the adjunction conjugate, so its
counit normalization and the closed counit equation give the pasted equation.
The compact-support coefficient comparison is invertible by its two factors,
using lem-cbc-extension-zero-projection-formula and lem-coef-finite-direct-image.
The factorized exceptional functor is Rk^!j^* by thm-sf-comp-composition
and prop-exc-open-adjoint. -/
theorem finiteCoefficientLocallyClosedShriek
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (m n : ℕ)
    (φ : ULift.{u + 1, u} (finiteClosedCoefficient l E m) →+* ULift.{u + 1, u}
      (finiteClosedCoefficient l L n))
    (X Z : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (j : Z ⟶ X) [IsOpenImmersion j.left]
    (W : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated W.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (k : W ⟶ Z) [IsClosedImmersion k.left]
    (M : finiteClosedDerived X.left (finiteClosedCoefficient l E m))
    (_hM : finiteTorConstructibleProEtaleModule l E (m + 1)
      (Nat.succ_pos m) X.left M) :
    IsIso (finiteLocallyClosedShriekMap φ k.left j.left M) ∧
    finiteTorConstructibleProEtaleModule l L (n + 1) (Nat.succ_pos n) W.left
      ((finiteClosedScalar φ W.left).obj
        ((finiteLocallyClosedExceptional (finiteClosedCoefficient l E m) k.left j.left).obj M)) ∧
    finiteTorConstructibleProEtaleModule l L (n + 1) (Nat.succ_pos n) W.left
      ((finiteLocallyClosedExceptional (finiteClosedCoefficient l L n) k.left j.left).obj
        ((finiteClosedScalar φ X.left).obj M)) ∧
    IsIso (finiteLocallyClosedCoefficientMap φ k.left j.left
      ((finiteLocallyClosedExceptional (finiteClosedCoefficient l E m) k.left j.left).obj M)) ∧
    (finiteLocallyClosedPush (finiteClosedCoefficient l L n) k.left j.left).map
        (finiteLocallyClosedShriekMap φ k.left j.left M) ≫
      finiteLocallyClosedCounit (finiteClosedCoefficient l L n) k.left j.left ((finiteClosedScalar
        φ X.left).obj M) =
    finiteLocallyClosedCoefficientInverse φ k.left j.left
        ((finiteLocallyClosedExceptional (finiteClosedCoefficient l E m) k.left j.left).obj M) ≫
      (finiteClosedScalar φ X.left).map (finiteLocallyClosedCounit (finiteClosedCoefficient l E m)
        k.left j.left M) := by
  have hJM := finiteClosedPull_finiteTor l E m j.left M _hM
  have hc := finiteCoefficientClosedShriek D l _hl E L m n φ Z W k
    ((finiteClosedPull (finiteClosedCoefficient l E m) j.left).obj M) hJM
  have hiso : IsIso (finiteClosedShriekMap φ k.left
      ((finiteClosedPull (finiteClosedCoefficient l E m) j.left).obj M)) := hc.2.2.2.1
  have hd : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ k.left
      ((finiteLocallyClosedExceptional (finiteClosedCoefficient l E m) k.left j.left).obj M)) :=
    hc.2.2.1
  have hci : IsIso (finiteLocallyClosedCoefficientMap φ k.left j.left
      ((finiteLocallyClosedExceptional (finiteClosedCoefficient l E m) k.left j.left).obj M)) := by
    dsimp only [finiteLocallyClosedCoefficientMap]
    have : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ k.left
        ((finiteLocallyClosedExceptional (finiteClosedCoefficient l E m)
          k.left j.left).obj M)) := hd
    infer_instance
  refine ⟨?_, hc.2.2.2.2.2.1, ?_, hci, ?_⟩
  · dsimp only [finiteLocallyClosedShriekMap]
    infer_instance
  · exact finiteClosed_finiteTor_of_iso l L n W.left
      ((finiteClosedExceptional (finiteClosedCoefficient l L n) k.left).mapIso
        ((finiteClosedScalarPullIso φ j.left).symm.app M)) hc.2.2.2.2.2.2
  · have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
    have hbc := (finiteClosed_intrinsic_bc_realization_iff l L (n + 1) (Nat.succ_pos n) Z.left _).1
      hc.2.2.2.2.1.1
    have hMb := finiteClosed_finiteTor_of_iso l L n Z.left
      ((finiteClosedScalarPullIso φ j.left).symm.app M) hc.2.2.2.2.1
    have hbcTarget := (finiteClosed_intrinsic_bc_realization_iff l L (n + 1)
      (Nat.succ_pos n) Z.left _).1 hMb.1
    have hclosed := hc.2.1
    change (finiteClosedPush (finiteClosedCoefficient l L n) k.left).map
        (finiteClosedShriekMap φ k.left
          ((finiteClosedPull (finiteClosedCoefficient l E m) j.left).obj M)) ≫
        finiteClosedCounit (finiteClosedCoefficient l L n) k.left
          ((finiteClosedScalar φ Z.left).obj
            ((finiteClosedPull (finiteClosedCoefficient l E m) j.left).obj M)) = _ at hclosed
    have hclosed' := congrArg
      (fun f ↦ ProEtale.finiteCoefficientChangeDirectImageMap φ k.left
        ((finiteLocallyClosedExceptional (finiteClosedCoefficient l E m)
          k.left j.left).obj M) ≫ f) hclosed
    dsimp only [finiteLocallyClosedExceptional, Functor.comp_obj] at hd hclosed'
    simp only [finiteClosedDirectInverse, dif_pos hd, ← Category.assoc,
      IsIso.hom_inv_id, Category.id_comp] at hclosed'
    simp only [Category.assoc] at hclosed'
    have hnClosed := finiteClosedCounit_naturality _ k.left
      hbc.bounded.1 hbcTarget.bounded.1 ((finiteClosedScalarPullIso φ j.left).inv.app M)
    simp only [Functor.comp_obj] at hnClosed
    simp only [finiteLocallyClosedCoefficientInverse, dif_pos hci]
    apply (cancel_epi (finiteLocallyClosedCoefficientMap φ k.left j.left
      ((finiteLocallyClosedExceptional (finiteClosedCoefficient l E m) k.left j.left).obj M))).1
    rw [IsIso.hom_inv_id_assoc]
    dsimp only [finiteLocallyClosedCoefficientMap, finiteLocallyClosedPush,
      finiteLocallyClosedShriekMap, finiteLocallyClosedCounit, Functor.comp_map]
    simp only [Functor.map_comp, Category.assoc]
    slice_lhs 4 5 =>
      rw [← Functor.map_comp, hnClosed, Functor.map_comp]
    slice_lhs 2 4 =>
      rw [← Functor.map_comp, ← Functor.map_comp]
      erw [hclosed']
    have hn := (finiteClosedOpenScalarIso φ j.left).hom.naturality
      (finiteClosedCounit (finiteClosedCoefficient l E m) k.left
        ((finiteClosedPull (finiteClosedCoefficient l E m) j.left).obj M))
    simp only [Functor.comp_map] at hn
    simp only [Category.assoc]
    erw [← reassoc_of% hn]
    rw [finiteClosedOpenCounit]

/-- Naturality of the specified locally closed comparison in every input morphism.
Source: blueprint sec-six-functors/sk-prop-sf-biduality-general, order 2139,
finite coefficient change for closed support (blueprint: lem-coef-finite-closed-shriek).

Proof: Apply closed naturality on j^* of the input morphism, then naturality of
the open scalar/pullback isomorphism. Compose the resulting two squares. -/
theorem finiteCoefficientLocallyClosedShriek_naturality
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (m n : ℕ)
    (φ : ULift.{u + 1, u} (finiteClosedCoefficient l E m) →+* ULift.{u + 1, u}
      (finiteClosedCoefficient l L n))
    (X Z : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (j : Z ⟶ X) [IsOpenImmersion j.left]
    (W : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated W.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (k : W ⟶ Z) [IsClosedImmersion k.left]
    (M N : finiteClosedDerived X.left (finiteClosedCoefficient l E m))
    (_hM : finiteTorConstructibleProEtaleModule l E (m + 1)
      (Nat.succ_pos m) X.left M)
    (_hN : finiteTorConstructibleProEtaleModule l E (m + 1)
      (Nat.succ_pos m) X.left N) (f : M ⟶ N) :
    (finiteClosedScalar φ W.left).map
        ((finiteLocallyClosedExceptional (finiteClosedCoefficient l E m) k.left j.left).map f) ≫
        finiteLocallyClosedShriekMap φ k.left j.left N =
      finiteLocallyClosedShriekMap φ k.left j.left M ≫
        (finiteLocallyClosedExceptional (finiteClosedCoefficient l L n) k.left j.left).map
          ((finiteClosedScalar φ X.left).map f) := by
  have hM := finiteClosedPull_finiteTor l E m j.left M _hM
  have hN := finiteClosedPull_finiteTor l E m j.left N _hN
  have hc := finiteCoefficientClosedShriek_naturality D l _hl E L m n φ Z W k
    ((finiteClosedPull (finiteClosedCoefficient l E m) j.left).obj M)
    ((finiteClosedPull (finiteClosedCoefficient l E m) j.left).obj N)
    hM hN ((finiteClosedPull (finiteClosedCoefficient l E m) j.left).map f)
  dsimp only [finiteLocallyClosedExceptional, Functor.comp_map] at hc ⊢
  dsimp only [finiteLocallyClosedShriekMap]
  rw [← Category.assoc, hc, Category.assoc, ← Functor.map_comp]
  have ho := (finiteClosedScalarPullIso φ j.left).inv.naturality f
  simp only [Functor.comp_map] at ho
  rw [ho]
  simp only [Functor.map_comp, Category.assoc]

private theorem finiteClosedPull_chain {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    (ψ : ULift.{u + 1, u} B →+* ULift.{u + 1, u} C)
    {V X : Scheme.{u}} (j : V ⟶ X) (M : finiteClosedDerived X A) :
    (finiteClosedScalar ψ V).map ((finiteClosedScalarPullIso φ j).inv.app M) ≫
        (finiteClosedScalarPullIso ψ j).inv.app ((finiteClosedScalar φ X).obj M) ≫
        (finiteClosedPull C j).map
          ((@ProEtale.pbcFixedScalarExtensionComp.{u} X.ProEt inferInstance
            (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology X)
            _ _ _ _ _ _ φ ψ (ψ.comp φ) rfl).hom.app M) =
      (@ProEtale.pbcFixedScalarExtensionComp.{u} V.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology V)
          _ _ _ _ _ _ φ ψ (ψ.comp φ) rfl).hom.app ((finiteClosedPull A j).obj M) ≫
        (finiteClosedScalarPullIso (ψ.comp φ) j).inv.app M := by
  have eqIso {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
      (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B) :
      finiteClosedScalarPullIso φ j = ProEtale.scalarPullbackProEtaleIso φ j := by
    have h : (finiteClosedScalarPullIso φ j).symm =
        (ProEtale.scalarPullbackProEtaleIso φ j).symm := by
      apply Iso.ext
      exact finiteClosedPullInverse φ j
    exact congrArg Iso.symm h
  rw [eqIso φ, eqIso ψ, eqIso (ψ.comp φ)]
  let cx := @ProEtale.pbcFixedScalarExtensionComp.{u} X.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology X)
    _ _ _ _ _ _ φ ψ (ψ.comp φ) rfl
  let cv := @ProEtale.pbcFixedScalarExtensionComp.{u} V.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology V)
    _ _ _ _ _ _ φ ψ (ψ.comp φ) rfl
  let e := (finiteClosedPull C j).mapIso (cx.symm.app M) ≪≫
    (ProEtale.scalarPullbackProEtaleIso ψ j).app ((finiteClosedScalar φ X).obj M) ≪≫
    (finiteClosedScalar ψ V).mapIso ((ProEtale.scalarPullbackProEtaleIso φ j).app M) ≪≫
    cv.app ((finiteClosedPull A j).obj M)
  have he : (ProEtale.scalarPullbackProEtaleIso (ψ.comp φ) j).app M = e := by
    apply Iso.ext
    exact ProEtale.scalarPullback_chain φ ψ j M
  have hi := congrArg Iso.inv he
  simp only [e, Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Functor.mapIso_inv,
    Category.assoc] at hi
  rw [hi, Iso.hom_inv_id_app_assoc]

/-- Successive finite coefficient maps for the chosen locally closed factorization.
Source: blueprint sec-six-functors/sk-prop-sf-biduality-general, order 2139,
finite coefficient change for closed support (blueprint: lem-coef-finite-closed-shriek).

Proof: Expand the locally closed map. Closed naturality moves the open comparison
through the next closed comparison. Apply closed coefficient coherence and
associativity of the open scalar/pullback conjugate; both sides reduce to the
one-step closed map followed by the one-step open comparison. -/
theorem finiteCoefficientLocallyClosedShriek_coefficientChain
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (m n : ℕ)
    (φ : ULift.{u + 1, u} (finiteClosedCoefficient l E m) →+* ULift.{u + 1, u}
      (finiteClosedCoefficient l L n))
    (X Z : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (j : Z ⟶ X) [IsOpenImmersion j.left]
    (W : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated W.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (k : W ⟶ Z) [IsClosedImmersion k.left]
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (r : ℕ) (ψ : ULift.{u + 1, u} (finiteClosedCoefficient l L n) →+*
      ULift.{u + 1, u} (finiteClosedCoefficient l F r))
    (M : finiteClosedDerived X.left (finiteClosedCoefficient l E m))
    (_hM : finiteTorConstructibleProEtaleModule l E (m + 1)
      (Nat.succ_pos m) X.left M) :
    (finiteClosedScalar ψ W.left).map (finiteLocallyClosedShriekMap φ k.left j.left M) ≫
        finiteLocallyClosedShriekMap ψ k.left j.left ((finiteClosedScalar φ X.left).obj M) ≫
        (finiteLocallyClosedExceptional (finiteClosedCoefficient l F r) k.left j.left).map
          (by
            simpa only [Functor.comp_obj] using
              (@ProEtale.pbcFixedScalarExtensionComp.{u} X.left.ProEt inferInstance
                (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology X.left)
                _ _ _ _ _ _ φ ψ (ψ.comp φ) rfl).hom.app M) =
      (by
        simpa only [Functor.comp_obj] using
          (@ProEtale.pbcFixedScalarExtensionComp.{u} W.left.ProEt inferInstance
            (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology W.left)
            _ _ _ _ _ _ φ ψ (ψ.comp φ) rfl).hom.app
            ((finiteLocallyClosedExceptional
              (finiteClosedCoefficient l E m) k.left j.left).obj M)) ≫
        finiteLocallyClosedShriekMap (ψ.comp φ) k.left j.left M := by
  have hJM := finiteClosedPull_finiteTor l E m j.left M _hM
  have hc := finiteCoefficientClosedShriek D l _hl E L m n φ Z W k
    ((finiteClosedPull (finiteClosedCoefficient l E m) j.left).obj M) hJM
  have hJMB := finiteClosed_finiteTor_of_iso l L n Z.left
    ((finiteClosedScalarPullIso φ j.left).symm.app M) hc.2.2.2.2.1
  have hn := finiteCoefficientClosedShriek_naturality D l _hl L F n r ψ Z W k
    ((finiteClosedScalar φ Z.left).obj
      ((finiteClosedPull (finiteClosedCoefficient l E m) j.left).obj M))
    ((finiteClosedPull (finiteClosedCoefficient l L n) j.left).obj
      ((finiteClosedScalar φ X.left).obj M))
    hc.2.2.2.2.1 hJMB ((finiteClosedScalarPullIso φ j.left).inv.app M)
  have hh := finiteCoefficientClosedShriek_coefficientChain D l _hl E L m n φ Z W k
    F r ψ ((finiteClosedPull (finiteClosedCoefficient l E m) j.left).obj M) hJM
  dsimp only [finiteLocallyClosedShriekMap, finiteLocallyClosedExceptional,
    Functor.comp_obj, Functor.comp_map]
  simp only [Functor.map_comp, Category.assoc]
  slice_lhs 2 3 => rw [hn]
  simp only [Category.assoc]
  slice_lhs 3 5 =>
    rw [← Functor.map_comp, ← Functor.map_comp, finiteClosedPull_chain, Functor.map_comp]
  rw [reassoc_of% hh]
  rfl

/-- Closed composition inside the specified open, with the same counit-normalized
composition identification evaluated at j^*M.
Source: blueprint sec-six-functors/sk-prop-sf-biduality-general, order 2139,
finite coefficient change for closed support (blueprint: lem-coef-finite-closed-shriek).

Proof: Expand the locally closed comparison, apply the closed-composition equation
at j^*M and use naturality of the counit-normalized closed compositor. The
open-restriction factor then gives the displayed equation; the pasted counit
is epsilon_j after j_!epsilon_k after j_!k_*epsilon_t. -/
theorem finiteCoefficientLocallyClosedShriek_comp
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (m n : ℕ)
    (φ : ULift.{u + 1, u} (finiteClosedCoefficient l E m) →+* ULift.{u + 1, u}
      (finiteClosedCoefficient l L n))
    (X Z : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (j : Z ⟶ X) [IsOpenImmersion j.left]
    (W : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated W.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (k : W ⟶ Z) [IsClosedImmersion k.left]
    (T : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated T.hom] [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    (t : T ⟶ W) [IsClosedImmersion t.left]
    (M : finiteClosedDerived X.left (finiteClosedCoefficient l E m))
    (_hM : finiteTorConstructibleProEtaleModule l E (m + 1)
      (Nat.succ_pos m) X.left M) :
    (finiteClosedScalar φ T.left).map
        (finiteClosedComposition (finiteClosedCoefficient l E m) t.left k.left ((finiteClosedPull
          (finiteClosedCoefficient l E m) j.left).obj M)) ≫
        finiteLocallyClosedShriekMap φ (t.left ≫ k.left) j.left M =
      finiteClosedShriekMap φ t.left
        ((finiteLocallyClosedExceptional (finiteClosedCoefficient l E m) k.left j.left).obj M) ≫
        (finiteClosedExceptional (finiteClosedCoefficient l L n) t.left).map
          (finiteLocallyClosedShriekMap φ k.left j.left M) ≫
        finiteClosedComposition (finiteClosedCoefficient l L n) t.left k.left
          ((finiteClosedPull (finiteClosedCoefficient l L n) j.left).obj ((finiteClosedScalar φ
            X.left).obj M)) := by
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : CompactSpace W.left := QuasiCompact.compactSpace_of_compactSpace W.hom
  have hJM := finiteClosedPull_finiteTor l E m j.left M _hM
  have hc := finiteCoefficientClosedShriek_comp D l _hl E L m n φ Z W k T t
    ((finiteClosedPull (finiteClosedCoefficient l E m) j.left).obj M) hJM
  have hd := finiteCoefficientClosedShriek D l _hl E L m n φ Z W k
    ((finiteClosedPull (finiteClosedCoefficient l E m) j.left).obj M) hJM
  have hJMB := finiteClosed_finiteTor_of_iso l L n Z.left
    ((finiteClosedScalarPullIso φ j.left).symm.app M) hd.2.2.2.2.1
  have hsource := (finiteClosed_intrinsic_bc_realization_iff l L (n + 1)
    (Nat.succ_pos n) Z.left _).1 hd.2.2.2.2.1.1
  have htarget := (finiteClosed_intrinsic_bc_realization_iff l L (n + 1)
    (Nat.succ_pos n) Z.left _).1 hJMB.1
  have hn := closedComposition_naturality (finiteClosedCoefficient l L n) t.left k.left
    hsource.bounded.1 htarget.bounded.1 ((finiteClosedScalarPullIso φ j.left).inv.app M)
  dsimp only [finiteLocallyClosedShriekMap, finiteLocallyClosedExceptional,
    Functor.comp_obj, Functor.comp_map]
  simp only [Functor.map_comp, Category.assoc]
  simp only [Functor.comp_obj] at hn
  rw [reassoc_of% hc.2.2.2.2.2.2, ← hn]

end WeilConjectures
