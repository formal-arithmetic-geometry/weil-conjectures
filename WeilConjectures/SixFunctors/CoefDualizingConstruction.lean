/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficientComparison
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficientComparison
public import WeilConjectures.SixFunctors.CompactCoefficientComposition
public import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Yoneda
import all WeilConjectures.AlgebraicGeometry.WeilVerdierPreservationStrata

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportComparisons
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportCoefficientChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedScalarTensor
import all WeilConjectures.AlgebraicGeometry.EtaleCompactSupportCoefficientChange

/-! # Ordinary etale dualizing objects and their coefficient counit mates

Source: main-20261015, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.proof.md, paragraphs 1--2
(blueprint: lem-coef-dualizing-construction).

The statements use the existing unbounded ordinary etale adjunctions and the
proper/open coefficient mate. The normalization on D+ tests only bounded-below
objects. No coefficient compatibility of an exceptional adjoint is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
attribute [local instance 2000] CommRing.toRing
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale


private theorem regular_unit_ctf
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X (𝟙_ _) :=
  ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (DerivedCategory.boundedConstructible_singleFunctor_obj _ 0), 0, 0,
    (DerivedCategory.torAmplitudeIn _ X 0 0).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        (ObjectProperty.flat_of_isDualizable isDualizable_unit))⟩

private theorem representing_counit_unique
    {C T : Type*} [Category C] [Category T] (F : C ⥤ T) (N : T)
    (Q Q' : C) (e : yoneda.obj Q ≅ F.op ⋙ yoneda.obj N)
    (e' : yoneda.obj Q' ≅ F.op ⋙ yoneda.obj N) :
    IsIso (Yoneda.fullyFaithful.preimage (e.hom ≫ e'.inv)) ∧
    ∀ t : Q ⟶ Q',
      (F.map t ≫ e'.hom.app (op Q') (𝟙 Q') = e.hom.app (op Q) (𝟙 Q)) ↔
      t = Yoneda.fullyFaithful.preimage (e.hom ≫ e'.inv) := by
  let θ := Yoneda.fullyFaithful.preimage (e.hom ≫ e'.inv)
  have hi : IsIso θ := (Yoneda.fullyFaithful.preimageIso (e ≪≫ e'.symm)).isIso_hom
  refine ⟨hi, fun t ↦ ?_⟩
  have hn := e'.hom.naturality_apply t.op (𝟙 Q')
  change e'.hom.app (op Q) (t ≫ 𝟙 Q') =
    F.map t ≫ e'.hom.app (op Q') (𝟙 Q') at hn
  rw [Category.comp_id] at hn
  have hθ : e'.hom.app (op Q) θ = e.hom.app (op Q) (𝟙 Q) := by
    change e'.hom.app (op Q)
      (e'.inv.app (op Q) (e.hom.app (op Q) (𝟙 Q))) = _
    exact congrFun (congrArg (fun α ↦ α.app (op Q)) e'.inv_hom_id) _
  rw [← hn, ← hθ]
  constructor
  · intro h
    apply (e'.app (op Q)).toEquiv.injective
    exact h
  · rintro rfl
    rfl


/-- At every positive finite coefficient level the ordinary dualizing object is bounded
constructible and has finite Tor amplitude; the compact-support functor has its ordinary
unbounded right adjoint, and the scheme is Noetherian.
Source: lem-coef-finite-dualizing.proof.md paragraph 1
(blueprint: lem-coef-dualizing-construction).
Proof: step 1 uses the extended nonarchimedean absolute value, the DVR integer ring and
finite residue quotients to prove finiteness of the coefficients. Finite type over the
Noetherian field spectrum makes Y Noetherian, and Nagata supplies a compactification.
Step 2 uses the unbounded compact-support comparisons and exceptional-adjoint theorem.
Step 3 observes that the regular sheaf in degree zero is constructible, bounded, and
K-flat, with Tor amplitude [0,0]. Step 4 applies verdier-preservation-strata to this
regular object; evaluation at 1 identifies its derived Hom into omega with omega.
The same argument applies to every positive level, including every further quotient. -/
theorem coefDualizingConstruction
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (n : ℕ+) :
    IsNoetherian Y ∧
    (rightDerivedLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))
      (Y ↘ Spec (.of D.k))).IsLeftAdjoint ∧
    DerivedCategory.isBoundedConstructible
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) Y
      (dualizingComplex
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))
        (Y ↘ Spec (.of D.k))) ∧
    ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) Y a b
      (dualizingComplex
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))
        (Y ↘ Spec (.of D.k))) := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E n)
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of D.k))
  let : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  let : IsNoetherian Y := ⟨⟩
  refine ⟨inferInstance, inferInstance, ?_⟩
  obtain ⟨hu, a, b, ht⟩ := regular_unit_ctf A Y
  have hc := (WeilConjectures.boundedConstructible_iff A Y _).2 hu
  have htor := DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 ht
  obtain ⟨hd, c, d, hdtor⟩ :=
    WeilConjectures.verdier_preserves_boundedConstructible_finiteTor D l _hl E n n.property
      Y (𝟙_ _) hc ⟨a, b, htor⟩
  let e : ((derivedHom (ModuleCat.{u + 1} A) Y).obj (op (𝟙_ _))) ≅ 𝟭 _ :=
    (derivedTensorHomAdjunction _ (𝟙_ _)).rightAdjointUniq
      (Adjunction.id.ofNatIsoLeft (derivedTensorLeftUnitorNatIso _ Y).symm)
  let ω := dualizingComplex A (Y ↘ Spec (.of D.k))
  change DerivedCategory.isBoundedConstructible A Y
    (((derivedHom (ModuleCat.{u + 1} A) Y).obj (op (𝟙_ _))).obj ω) at hd
  change DerivedCategory.hasTorAmplitudeIn A Y c d
    (((derivedHom (ModuleCat.{u + 1} A) Y).obj (op (𝟙_ _))).obj ω) at hdtor
  have hd' := (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y).prop_of_iso
    (e.app ω) ((WeilConjectures.boundedConstructible_iff A Y _).1 hd)
  have ht' := (DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) Y c d).prop_of_iso
    (e.app ω) (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hdtor)
  exact ⟨(WeilConjectures.boundedConstructible_iff A Y ω).2 hd',
    min c d, d, min_le_right _ _,
    DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
      (ht'.mono (min_le_left _ _) le_rfl)⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The existing coefficient mate is the unique map with the displayed counit equation.
Source: lem-coef-finite-dualizing.proof.md paragraph 1
(blueprint: lem-coef-dualizing-construction).
Proof: step 5 applies compact-support coefficient change to the bounded constructible
finite-Tor dualizing object, so its canonical comparison is invertible. Multiplication
identifies the scalar extension of the regular unit with the regular unit. Transpose
its inverse followed by scalar extension of epsilon and this unit identification under
F_B adjoint G_B. The Hom bijection gives the counit equation and uniqueness. This is
exactly the existing dualizingScalarMap, constructed from the same normalized mate.
No flatness of the quotient and no invertibility of the exceptional mate is assumed. -/
theorem coefDualizingConstruction_mate
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (n m : ℕ+) (hmn : m ≤ n)
    (_hc : DerivedCategory.isBoundedConstructible (ULift.{u + 1} (Padic.coefficientExtensionRing l
        E n)) Y
      (dualizingComplex
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))
        (Y ↘ Spec (.of D.k))))
    (_ht : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) Y a b
      (dualizingComplex
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))
        (Y ↘ Spec (.of D.k)))) :
    IsIso (ExceptionalCoefficients.compactSupportMap (ProEtale.finiteCompositionReduction l E n m
        hmn)
      (HasCompactification.compactification (Y ↘ Spec (.of D.k)))
      (dualizingComplex
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))
        (Y ↘ Spec (.of D.k)))) ∧
    ∀ v : (scalarExtension (ProEtale.finiteCompositionReduction l E n m hmn) Y).obj
        (dualizingComplex
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))
        (Y ↘ Spec (.of D.k))) ⟶
      (dualizingComplex
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E m))
        (Y ↘ Spec (.of D.k))),
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing
        l E m)))
        (Y ↘ Spec (.of D.k))).map v ≫
        ((rightDerivedUpperShriekAdjunction
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)) (Y ↘ Spec (.of
        D.k))).counit.app
          (𝟙_ (DerivedCategoryModule (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)) (Spec
        (.of D.k))))) =
      ExceptionalCoefficients.comparisonInverse (ProEtale.finiteCompositionReduction l E n m hmn)
        (HasCompactification.compactification (Y ↘ Spec (.of D.k)))
        (dualizingComplex
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))
        (Y ↘ Spec (.of D.k))) ≫
      (scalarExtension (ProEtale.finiteCompositionReduction l E n m hmn) (Spec (.of D.k))).map
        ((rightDerivedUpperShriekAdjunction
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) (Y ↘ Spec (.of
        D.k))).counit.app
          (𝟙_ (DerivedCategoryModule (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) (Spec
        (.of D.k))))) ≫
      (ExceptionalCoefficients.unitIso (ProEtale.finiteCompositionReduction l E n m hmn) (Spec
        (.of D.k))).hom) ↔
      v = ExceptionalCoefficients.dualizingScalarMap (ProEtale.finiteCompositionReduction l E n m
        hmn) (Y ↘ Spec (.of D.k)) := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E n)
  let B := ULift.{u + 1} (Padic.coefficientExtensionRing l E m)
  let φ := ProEtale.finiteCompositionReduction l E n m hmn
  let f := Y ↘ Spec (.of D.k)
  let a := rightDerivedUpperShriekAdjunction A f
  let b := rightDerivedUpperShriekAdjunction B f
  have hi := ExceptionalCoefficients.compactSupport_isIso φ
    (HasCompactification.compactification f) (dualizingComplex A f)
  refine ⟨hi, fun v ↦ ?_⟩
  have hv : (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).map
        (ExceptionalCoefficients.dualizingScalarMap φ f) ≫ b.counit.app (𝟙_ _) =
      ExceptionalCoefficients.comparisonInverse φ (HasCompactification.compactification f)
        (dualizingComplex A f) ≫
      (scalarExtension φ (Spec (.of D.k))).map (a.counit.app (𝟙_ _)) ≫
      (ExceptionalCoefficients.unitIso φ (Spec (.of D.k))).hom := by
    rw [ExceptionalCoefficients.dualizingScalarMap_eq, Functor.map_comp, Category.assoc]
    have hn := b.counit.naturality (ExceptionalCoefficients.unitIso φ (Spec (.of D.k))).hom
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [hn, ← Category.assoc]
    have hm := (b.homEquiv _ _).symm_apply_apply
      (ExceptionalCoefficients.comparisonInverse φ (HasCompactification.compactification f)
        (dualizingComplex A f) ≫
      (scalarExtension φ (Spec (.of D.k))).map (a.counit.app (𝟙_ _)))
    change (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).map
      (ExceptionalCoefficients.mateMap φ f (𝟙_ _)) ≫ b.counit.app _ = _ at hm
    rw [hm, Category.assoc]
  constructor
  · intro h
    apply (b.homEquiv _ _).symm.injective
    simpa only [Adjunction.homEquiv_counit] using h.trans hv.symm
  · rintro rfl
    exact hv


/-- On D+, the comparison induced by representing Hom bijections is the unique
counit-compatible isomorphism. The functor is the actual compact support of pi.
Source: lem-coef-finite-dualizing.proof.md paragraph 2; Stacks Tag 001P
(blueprint: lem-coef-dualizing-construction).
Proof: step 6 takes beta=(phi') inverse phi on represented presheaves. Yoneda gives
its unique map theta=beta_Q(identity). The inverse presheaf isomorphism gives theta'
and faithfulness shows that both composites are identities. Naturality gives the
counit equation. Conversely a counit-compatible map has the same image under the
injective Hom bijection, hence equals theta. Q and Q' lie in D+, so both are valid
test objects; no preservation of D+ by an arbitrary unbounded adjoint is asserted. -/
theorem coefDualizingConstruction_representing
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (P : Scheme.{u}) [P.Over (Spec (.of D.k))]
    [IsSeparated (P ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (P ↘ Spec (.of D.k))]
    [QuasiCompact (P ↘ Spec (.of D.k))]
    (i : Y ⟶ P) [i.IsOver (Spec (.of D.k))]
    [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    (n : ℕ+)
    (N : _root_.DerivedCategory.Plus
      (Sheaf (Spec (.of D.k)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E n)))))
    (Q Q' : _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u +
        1} (Padic.coefficientExtensionRing l E n)))))
    (e : yoneda.obj Q ≅
      (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E n)))
        (i ≫ (P ↘ Spec (.of D.k)))).op ⋙ yoneda.obj N)
    (e' : yoneda.obj Q' ≅
      (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E n)))
        (i ≫ (P ↘ Spec (.of D.k)))).op ⋙ yoneda.obj N) :
    IsIso (Yoneda.fullyFaithful.preimage (e.hom ≫ e'.inv)) ∧
    ∀ t : Q ⟶ Q',
      ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E n)))
        (i ≫ (P ↘ Spec (.of D.k)))).map t ≫
        e'.hom.app (op Q') (𝟙 Q') = e.hom.app (op Q) (𝟙 Q)) ↔
      t = Yoneda.fullyFaithful.preimage (e.hom ≫ e'.inv) := by
  exact representing_counit_unique _ N Q Q' e e'

/-- The factorization normalization: the composed counit, and the canonical
coefficient-comparison composition equation, with compact-support identifications.
Source: lem-coef-finite-dualizing.proof.md paragraph 2; Stacks Tags 0DV0 and 0F7J
(blueprint: lem-coef-dualizing-construction).
Proof: step 7 composes the adjunction Hom bijections using
 def-weil-pbc-composite-adjunction. Its inverse is F_p of epsilon_i followed by
epsilon_p. Transport the left adjoint through the canonical compact-support
composition isomorphism; this inserts its inverse before the two counits. The
preceding representing-object uniqueness identifies every D+ representative with
this normalization. Step 8 applies lem-sf-compact-coefficient-composition to i,p
and the quotient n to m. These are separated finite-type morphisms between
separated finite-type k-schemes. The unbounded comparisons restrict to the
bounded-below comparisons by lem-amb-unbounded-compact-support-comparisons.
Thus the normalized coefficient square is precisely the displayed equation. -/
theorem coefDualizingConstruction_factorization
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (P : Scheme.{u}) [P.Over (Spec (.of D.k))]
    [IsSeparated (P ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (P ↘ Spec (.of D.k))]
    [QuasiCompact (P ↘ Spec (.of D.k))]
    (i : Y ⟶ P) [i.IsOver (Spec (.of D.k))]
    [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    (n m : ℕ+) (hmn : m ≤ n)
    (N : _root_.DerivedCategory.Plus
      (Sheaf (Spec (.of D.k)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E n)))))
    (K : _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E n)))))
    (_hc : DerivedCategory.isBoundedConstructible (ULift.{u + 1} (Padic.coefficientExtensionRing l
        E n)) Y K.obj)
    (_ht : ∃ a b : ℤ, a ≤ b ∧
      DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) Y a
        b K.obj) :
    (((@rightDerivedUpperShriekAdjunction (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E n)) _ _ _ _ i
        (ProEtale.finiteCompositionCompactification D.k i).hasCompactification).comp
      (rightDerivedUpperShriekAdjunction
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) (P ↘ Spec (.of
        D.k)))).ofNatIsoLeft
        (@unboundedEtaleLowerShriekCompIso (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))
        _ _ _ _ _ i (P ↘ Spec (.of D.k))
        (ProEtale.finiteCompositionCompactification D.k i).hasCompactification _ _ _ _)).counit.app
        N.obj =
      (@unboundedEtaleLowerShriekCompIso (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) _
        _ _ _ _ i (P ↘ Spec (.of D.k))
        (ProEtale.finiteCompositionCompactification D.k i).hasCompactification _ _ _ _).inv.app
        ((@rightDerivedUpperShriek (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E n)) _ _ _ _ i
        (ProEtale.finiteCompositionCompactification D.k i).hasCompactification).obj
          ((rightDerivedUpperShriek (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E n)) (P ↘ Spec (.of D.k))).obj N.obj)) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l
        E n))) (P ↘ Spec (.of D.k))).map
        ((@rightDerivedUpperShriekAdjunction (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E n)) _ _ _ _ i
        (ProEtale.finiteCompositionCompactification D.k i).hasCompactification).counit.app
          ((rightDerivedUpperShriek (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E n)) (P ↘ Spec (.of D.k))).obj N.obj)) ≫
      (rightDerivedUpperShriekAdjunction
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) (P ↘ Spec (.of
        D.k))).counit.app N.obj ∧
    (scalarExtension (ProEtale.finiteCompositionReduction l E n m hmn) (Spec (.of D.k))).map
        ((@unboundedEtaleLowerShriekCompIso (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))
        _ _ _ _ _ i (P ↘ Spec (.of D.k))
        (ProEtale.finiteCompositionCompactification D.k i).hasCompactification _ _ _ _).hom.app
        K.obj) ≫
      ExceptionalCoefficients.compactSupportMap (ProEtale.finiteCompositionReduction l E n m hmn)
        (HasCompactification.compactification (i ≫ (P ↘ Spec (.of D.k)))) K.obj =
      ExceptionalCoefficients.compactSupportMap (ProEtale.finiteCompositionReduction l E n m hmn)
        (HasCompactification.compactification (P ↘ Spec (.of D.k)))
        ((@rightDerivedLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E n))) _ _ _ _ _ i
        (ProEtale.finiteCompositionCompactification D.k i).hasCompactification).obj K.obj) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l
        E m))) (P ↘ Spec (.of D.k))).map
        (ExceptionalCoefficients.compactSupportMap
          (ProEtale.finiteCompositionReduction l E n m hmn)
          (@HasCompactification.compactification _ _ i
            (ProEtale.finiteCompositionCompactification D.k i).hasCompactification) K.obj) ≫
      (@unboundedEtaleLowerShriekCompIso (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)) _
        _ _ _ _ i (P ↘ Spec (.of D.k))
        (ProEtale.finiteCompositionCompactification D.k i).hasCompactification _ _ _ _).hom.app
        ((scalarExtension (ProEtale.finiteCompositionReduction l E n m hmn) Y).obj K.obj) := by
  constructor
  · simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Adjunction.comp_counit_app, Functor.comp_obj]
  · let := (ProEtale.finiteCompositionCompactification D.k i).hasCompactification
    let : IsLocallyNoetherian Y :=
      LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of D.k))
    let : CompactSpace Y :=
      QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
    let : IsNoetherian Y := ⟨⟩
    let : IsLocallyNoetherian P :=
      LocallyOfFiniteType.isLocallyNoetherian (P ↘ Spec (.of D.k))
    let : CompactSpace P :=
      QuasiCompact.compactSpace_of_compactSpace (P ↘ Spec (.of D.k))
    let : IsNoetherian P := ⟨⟩
    obtain ⟨a, b, _, ht⟩ := _ht
    have hplus := scalarExtension_plus_of_finiteTor
      (ProEtale.finiteCompositionReduction l E n m hmn) Y K.obj a b ht
    exact etaleCompactScalarComposition
      (ProEtale.finiteCompositionReduction l E n m hmn) i (P ↘ Spec (.of D.k)) K
      ⟨⟨_, hplus⟩, rfl⟩

end AlgebraicGeometry.Etale
