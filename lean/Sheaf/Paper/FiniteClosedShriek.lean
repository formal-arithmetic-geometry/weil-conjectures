/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.Paper.FiniteCoefficientDirectImage
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
import all Sheaf.Paper.FiniteCompactSupportConstructibility
import Sheaf.AlgebraicGeometry.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor
import Sheaf.Paper.FiniteClosedShriekMapPart
import Sheaf.Paper.FiniteClosedShriekDomainPart

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
  · simpa only [splitIsMap, IsFiniteClosedShriekMap, splitPush, splitCounit,
      splitDirectInverse, splitExceptional, finiteClosedExceptional,
      splitScalar, finiteClosedScalar, splitMap, finiteClosedShriekMap,
      splitCoefficient, finiteClosedCoefficient, finiteClosedDerived,
      finiteClosedExceptional, finiteClosedScalar, finiteClosedPush,
      finiteClosedCounit, finiteClosedDirectInverse] using hm.1
  · simpa only [splitIsMap, IsFiniteClosedShriekMap, splitPush, splitCounit,
      splitDirectInverse, splitExceptional, finiteClosedExceptional,
      splitScalar, finiteClosedScalar, splitMap, finiteClosedShriekMap,
      splitCoefficient, finiteClosedCoefficient, finiteClosedDerived,
      finiteClosedExceptional, finiteClosedScalar, finiteClosedPush,
      finiteClosedCounit, finiteClosedDirectInverse] using hm.2.1

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
  have hK := (intrinsic_bc_realization_iff l L (n + 1) (Nat.succ_pos n) Z.left _).1
    hM.2.2.2.2.2.1.1
  have hMB := (intrinsic_bc_realization_iff l L (n + 1) (Nat.succ_pos n) X.left _).1
    hM.2.2.2.2.1.1
  have hNB := (intrinsic_bc_realization_iff l L (n + 1) (Nat.succ_pos n) X.left _).1
    hN.2.2.2.2.1.1
  have hMA := (intrinsic_bc_realization_iff l E (m + 1) (Nat.succ_pos m) X.left _).1 _hM.1
  have hNA := (intrinsic_bc_realization_iff l E (m + 1) (Nat.succ_pos m) X.left _).1 _hN.1
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
  sorry

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
  sorry

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
  sorry

private theorem finiteClosedPull_finiteTor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (m : ℕ)
    {V X : Scheme.{u}} (j : V ⟶ X)
    (M : finiteClosedDerived X (finiteClosedCoefficient l E m))
    (hM : finiteTorConstructibleProEtaleModule l E (m + 1) (Nat.succ_pos m) X M) :
    finiteTorConstructibleProEtaleModule l E (m + 1) (Nat.succ_pos m) V
      ((finiteClosedPull (finiteClosedCoefficient l E m) j).obj M) := by
  obtain ⟨hbc, a, b, ht⟩ := hM
  have hbc' := (intrinsic_bc_realization_iff l E (m + 1) (Nat.succ_pos m) X M).1 hbc
  have ht' := (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    (finiteClosedCoefficient l E m) X a b ht.1 M).1 ht
  have h := ProEtale.boundedConstructible_and_torAmplitudeIn_leftDerivedFunctor_upperStar_obj
    j hbc' ht'
  exact ⟨(intrinsic_bc_realization_iff l E (m + 1) (Nat.succ_pos m) V _).2 h.1,
    a, b, (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
      (finiteClosedCoefficient l E m) V a b ht.1 _).2 h.2⟩

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
  sorry

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
  sorry

end WeilConjectures
