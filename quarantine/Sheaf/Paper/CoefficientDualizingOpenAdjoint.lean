/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
public import Sheaf.Paper.EtaleCompactSupportCoefficientChange
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Sheaf.Paper.CoefficientDualizingOpenCompositorPlus

/-! # Open restriction of the ordinary etale structural adjunction

Source: main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-dualizing.proof.md, paragraph 2, first sentence;
Stacks Project, Tags 07A4 and 0G7E
(blueprint: lem-coef-dualizing-open-adjoint).

The comparison functors are the ordinary small-etale functors. The left comparison
uses the open compactification (j, identity) and the published unbounded compositor.
The right comparison is the counit-normalized uniqueness isomorphism for the composite
adjunction. Scalar pullback uses the existing K-flat-normalized, B-linear isomorphism.
The final statement includes both coefficient levels, the geometric assertions and
the agreement with the bounded-below compositor and evaluation adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The canonical right-adjoint identification, built from the evaluation adjunction,
its composite with the structural adjunction, and right-adjoint uniqueness.
At R_s this is j^* omega_Y to omega_U.
Source: lem-coef-finite-dualizing, paragraph 2, open locality
(blueprint: lem-coef-dualizing-open-adjoint). -/
def coefDualizingOpenRightIso
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U Y S : Scheme.{u}} (j : U ⟶ Y) (f : Y ⟶ S) [IsOpenImmersion j]
    [QuasiCompact j] [QuasiCompact (j ≫ f)]
    [HasCompactification j] [HasCompactification f] [HasCompactification (j ≫ f)]
    (G : DerivedCategoryModule R S ⥤ DerivedCategoryModule R Y)
    (H : DerivedCategoryModule R S ⥤ DerivedCategoryModule R U)
    (adjY : rightDerivedLowerShriek (ModuleCat.{u + 1} R) f ⊣ G)
    (adjU : rightDerivedLowerShriek (ModuleCat.{u + 1} R) (j ≫ f) ⊣ H) :
    G ⋙ (upperStar (ModuleCat.{u + 1} R) j).mapDerivedCategory ≅ H :=
  (((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).comp
    adjY).ofNatIsoLeft (coefDualizingOpenLeftIso R j f)).rightAdjointUniq adjU

/-- The composite counit equation, with the actual degreewise evaluation counit e.
No adjunction or comparison in this assertion is an arbitrary map.
Source: lem-coef-finite-dualizing, paragraph 2, open composite counit
(blueprint: lem-coef-dualizing-open-adjoint). -/
def CoefDualizingOpenCounitStatement
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U Y S : Scheme.{u}} (j : U ⟶ Y) (f : Y ⟶ S) [IsOpenImmersion j]
    [QuasiCompact j] [QuasiCompact (j ≫ f)]
    [HasCompactification j] [HasCompactification f] [HasCompactification (j ≫ f)] : Prop :=
  ∀ (G : DerivedCategoryModule R S ⥤ DerivedCategoryModule R Y)
    (H : DerivedCategoryModule R S ⥤ DerivedCategoryModule R U)
    (adjY : rightDerivedLowerShriek (ModuleCat.{u + 1} R) f ⊣ G)
    (adjU : rightDerivedLowerShriek (ModuleCat.{u + 1} R) (j ≫ f) ⊣ H),
    (rightDerivedLowerShriek (ModuleCat.{u + 1} R) (j ≫ f)).map
        ((coefDualizingOpenRightIso R j f G H adjY adjU).hom.app (constantComplex R S)) ≫
      adjU.counit.app (constantComplex R S) =
    (coefDualizingOpenLeftIso R j f).inv.app
        ((upperStar (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj
          (G.obj (constantComplex R S))) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} R) f).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} R) j).counit.app (G.obj (constantComplex R S))) ≫
      adjY.counit.app (constantComplex R S)

/-- The canonical coefficient-tensor/open-restriction identification, in B-modules.
Transport the existing K-flat-normalized scalar-pullback isomorphism through the
identification of left derived inverse image with exact termwise inverse image.
Source: Stacks 07A4 and 0G7E; lem-coef-finite-dualizing, paragraph 2
(blueprint: lem-coef-dualizing-open-adjoint). -/
def coefDualizingOpenTensorIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] :
    scalarExtension φ Y ⋙ (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙ scalarExtension φ U :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).symm ≪≫
    scalarPullbackIso φ j ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j) _

/-- The actual finite coefficient reduction A to B, including the identity-level case.
Source: lem-coef-finite-dualizing, finite coefficient convention
(blueprint: lem-coef-dualizing-open-adjoint). -/
def coefDualizingOpenReduction
    (P : WeilConjectures.PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) :
    P.Coefficient →+* ({ P with level := m, level_pos := hm }).Coefficient :=
  RingHom.ulift (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level)
    (T := Padic.coefficientExtensionIdeal P.coefficients.l P.extension m)
    (Ideal.pow_le_pow_right hmn))

/-- The complete two-level assertion. The local instances in this definition are
existing Mathlib consequences of finite type over a field and of the open immersion;
they impose no extra Noetherianity, compactifiability or flatness hypothesis.
The tensor identification is the named `coefDualizingOpenTensorIso` applied to
`coefDualizingOpenReduction P m hm hmn`, and is constructed above, without a theorem hole.
Source: lem-coef-finite-dualizing, paragraph 2, first sentence
(blueprint: lem-coef-dualizing-open-adjoint). -/
def CoefDualizingOpenAdjointStatement
    (P : WeilConjectures.PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (Y U : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k)) (j : U ⟶ Y)
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsOpenImmersion j] [IsAffine U] : Prop :=
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  letI : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  letI : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  letI : Finite (Padic.coefficientExtensionRing P.coefficients.l P.extension m) :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension m hm
  letI : Finite ({ P with level := m, level_pos := hm }).Coefficient :=
    inferInstanceAs (Finite
      (ULift.{u + 1} (Padic.coefficientExtensionRing P.coefficients.l P.extension m)))
  QuasiCompact j ∧ IsSeparated j ∧ Etale j ∧ LocallyOfFiniteType j ∧
    CoefDualizingOpenCounitStatement P.Coefficient j aY ∧
    CoefDualizingOpenCounitStatement ({ P with level := m, level_pos := hm }).Coefficient j aY ∧
    CoefDualizingOpenPlusStatement P.Coefficient j aY ∧
    CoefDualizingOpenPlusStatement ({ P with level := m, level_pos := hm }).Coefficient j aY

set_option Elab.async false
attribute [local irreducible] upperStar lowerStar Functor.mapDerivedCategory
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorPlus
  coefDualizingOpenLeftIso coefDualizingOpenNormalization openImmersionLowerShriek
  unboundedEtaleLowerShriekCompIso rightDerivedLowerShriekPlusCompIso

private theorem open_counit
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U Y S : Scheme.{u}} (j : U ⟶ Y) (f : Y ⟶ S) [IsOpenImmersion j]
    [QuasiCompact j] [QuasiCompact (j ≫ f)]
    [HasCompactification j] [HasCompactification f] [HasCompactification (j ≫ f)] :
    CoefDualizingOpenCounitStatement R j f := by
  intro G H adjY adjU
  simpa only [coefDualizingOpenRightIso, Adjunction.ofNatIsoLeft_counit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Adjunction.comp_counit_app,
    Functor.comp_obj, Category.assoc] using
    (((derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} R) j).comp adjY).ofNatIsoLeft
      (coefDualizingOpenLeftIso R j f)).rightAdjointUniq_hom_app_counit
        adjU (constantComplex R S)


/-- Open structural adjunction with its specified composite evaluation counit, at both
finite coefficient levels. The canonical tensor identification is constructed by
`coefDualizingOpenTensorIso (coefDualizingOpenReduction P m hm hmn) j`.

Source: main-20261015, lem-coef-finite-dualizing.proof.md, paragraph 2, first sentence
(blueprint: lem-coef-dualizing-open-adjoint).

Proof plan (the six steps of the DAG node):
1. A finite-type scheme over Spec k is locally Noetherian and quasi-compact. The affine
   open U is Noetherian. Its inclusion is etale and separated; intersections of affine
   opens in a quasi-separated scheme are quasi-compact, so j is quasi-compact and of
   finite type. Nagata supplies the structural compactifications; (j, identity) is
   the open compactification (pqf-lem-locnoeth-lft, pqf-lem-affine-open-locnoeth,
   lem-weil-pbc-open-immersion-etale, lem-weil-pbc-locally-noetherian-quasi-separated,
   lem-weil-pbc-qc-open-immersion-finite-type, def-asd-compactifiable).
2. The exact sum-extension adjunction of lem-amb-etale-adjoint-locality, for an open
   immersion, is the extension-by-zero adjunction. On an etale test factoring through
   U its counit is evaluation, and elsewhere zero; descend that very map degreewise
   (def-weil-pbc-extension-by-zero, lem-weil-pbc-extension-by-zero-adjunction).
3. Normalize Rj_! by (j, identity), then apply the canonical unbounded compositor
   (lem-asd-etale-compact-support-normalization,
   lem-amb-unbounded-compact-support-comparisons). This is coefDualizingOpenLeftIso.
4. Compose the open evaluation and structural adjunctions using
   def-weil-pbc-composite-adjunction. Transport along the left comparison, then use
   det-sp-unique-right-adjoint. Its counit equation, evaluated at R_s, is precisely
   the displayed identity. This constructs coefDualizingOpenRightIso, hence the
   dualizing-object identification, without changing the evaluation map.
5. Compare the actual coefDualizingOpenLeftIso on bounded-below inputs with
   coefDualizingOpenLeftPlusIso: compare the chosen compactification of j to
   (j, identity) by rightDerivedLowerShriekOfCompactificationPlusIso, remove the
   identity image, invert, and follow by rightDerivedLowerShriekPlusCompIso.
   The bounded-below compatibilities for open extension and structural compact
   support identify their sources and targets. The restriction clause of
   lem-amb-unbounded-compact-support-comparisons and the normalization laws of
   lem-amb-etale-compact-comparisons prove this equality. Right-adjoint uniqueness
   then identifies the counit-preserving right comparison with the ordinary one;
   the evaluation counit remains the specified degreewise open counit.
6. For tensor comparison choose a flat-term K-flat resolution P to K. Restriction
   preserves K-flatness, flat terms, quasi-isomorphisms, tensor and direct sums
   (lem-weil-pbc-ringed-topoi-derived-tensor-pullback). The termwise comparison
   j^*(P tensor_A B) = j^*P tensor_A B respects the B-action on the second factor.
   Descend this B-linear comparison; it is the existing uniquely normalized
   scalarPullbackIso used above. No flatness of A to B or boundedness of K is used.
-/
theorem coefDualizingOpenAdjoint
    (P : WeilConjectures.PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (_hmn : m ≤ P.level)
    (Y U : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k)) (j : U ⟶ Y)
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsOpenImmersion j] [IsAffine U] :
    CoefDualizingOpenAdjointStatement P m hm Y U aY j := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  let : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  let : IsNoetherian Y := ⟨⟩
  let : IsNoetherian U := ⟨⟩
  let : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  let : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  let : Finite (Padic.coefficientExtensionRing P.coefficients.l P.extension m) :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension m hm
  let : Finite ({ P with level := m, level_pos := hm }).Coefficient :=
    inferInstanceAs (Finite
      (ULift.{u + 1} (Padic.coefficientExtensionRing P.coefficients.l P.extension m)))
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    open_counit P.Coefficient j aY, open_counit _ j aY,
    ?_, ?_⟩
  · exact coefDualizingOpenCompositorPlus P.Coefficient j aY
  · exact coefDualizingOpenCompositorPlus _ j aY

end AlgebraicGeometry.Etale
