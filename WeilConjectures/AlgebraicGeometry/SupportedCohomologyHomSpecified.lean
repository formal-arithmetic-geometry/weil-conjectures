/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportedCohomologyHom
public import WeilConjectures.AlgebraicGeometry.SupportLongExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor

/-! # The specified supported-Hom identification

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an,
lem-pur-supported-hom.md and its proof; used in sk-lem-sp-reduction,
lem-pur-gysin-structure.proof.md, step 4
(blueprint: lem-pur-supported-hom).

The older existence theorem forgets which natural isomorphism is meant. Here the
cocycle formula determines a unique natural isomorphism. Choosing that uniquely
specified isomorphism postpones only its existence proof, not its mathematical data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.ProEtale

/-- The canonical comparison of the recorded coefficient unit with the constant
module on the small pro-etale site. Source: purity conventions, comparison pullback
of constants (blueprint: lem-pur-supported-hom). -/
def supportedHomConstantIso (P : WeilConjectures.PurityFiniteSetting.{u}) (Z : Scheme.{u}) :
    P.constant Z ≅ (constantSheaf (Scheme.ProEt.topology Z)
      (ModuleCat.{u + 1} P.Coefficient)).obj (ModuleCat.of P.Coefficient P.Coefficient) :=
  ((Functor.isoWhiskerLeft
      (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
      (Functor.sheafPullbackConstruction.sheafPullbackIso (Scheme.toProEt Z)
        (ModuleCat.{u + 1} P.Coefficient) Z.smallEtaleTopology
        (Scheme.ProEt.topology Z)).symm ≪≫
    (Scheme.toProEt Z).constantSheafsheafPullbackIso (ModuleCat.{u + 1} P.Coefficient)
      Z.smallEtaleTopology (Scheme.ProEt.topology Z)
      (terminalIsTerminal : IsTerminal (⊤_ Z.Etale))
      (terminalIsTerminal.isTerminalObj (Scheme.toProEt Z))).app
        (ModuleCat.of P.Coefficient P.Coefficient))

/-- The supported coefficient object is the underived direct image in degree zero.
Source: lem-pur-supported-hom (blueprint: lem-pur-supported-hom). -/
abbrev supportedHomSource (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)

/-- The two additive-group-valued functors in the supported-Hom statement.
Source: lem-pur-supported-hom, displayed identification
(blueprint: lem-pur-supported-hom). -/
abbrev SupportedHomIdentification (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (a : ℤ) :=
  (derivedSupportSections i P.Coefficient ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) a ⋙
    forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}) ≅
  (DerivedCategory.Plus.ι ⋙
    shiftFunctor (ModuleDerivedCategory X P.Coefficient) a ⋙
    preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
        (supportedHomSource P i))))

/-- Evaluation on the quotient of the coefficient unit specifies the cocycle map.
A supported cycle is sent to the chain map from i_*A_Z in degree zero, shifted
with the cochain convention, then localized. Source: lem-pur-supported-hom,
proof steps 4--6 (blueprint: lem-pur-supported-hom). -/
def SupportedHomCocycleNormalization (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (a : ℤ)
    (χ : SupportedHomIdentification P i a) : Prop :=
  ∀ (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (_hi : ∀ r : ℤ, Injective (I.obj.X r))
    (f : supportedHomSource P i ⟶ I.obj.X a)
    (hf : f ≫ I.obj.d a (a + 1) = 0)
    (s : (((supportSections i P.Coefficient).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I.obj).cycles a),
    kernel.ι ((I.obj.X a).obj.map (supportRestrictionArrow i).op)
        ((((supportSections i P.Coefficient).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I.obj).iCycles a s) =
      f.hom.app (op (Scheme.ProEt.mk (𝟙 X)))
        ((Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} P.Coefficient)
            (ModuleCat.of P.Coefficient P.Coefficient) ≫
          (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).map
            (supportedHomConstantIso P Z).inv).hom.app
              (op (Scheme.ProEt.mk (𝟙 X)))
                ((toSheafify (Scheme.ProEt.topology X)
                  ((Functor.const X.ProEtᵒᵖ).obj
                    (ModuleCat.of P.Coefficient P.Coefficient))).app
                      (op (Scheme.ProEt.mk (𝟙 X))) (1 : P.Coefficient))) →
    χ.hom.app (DerivedCategory.Plus.Q.obj I)
        ((Sheaf.supportSequenceModelIso (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} P.Coefficient) (supportSections i P.Coefficient)
          I (DerivedCategory.Plus.Q.obj I) (Iso.refl _) a).hom
            ((((supportSections i P.Coefficient).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I.obj).homologyπ a s)) =
      (DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app (supportedHomSource P i) ≫
        ShiftedHom.map (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q ≫
        ((DerivedCategory.quotientCompQhIso _).inv.app I.obj)⟦a⟧'

/-- Existence of a supported-Hom comparison satisfying the cocycle formula.
Source: lem-pur-supported-hom and its proof (latest blueprint, sk-prop-an),
used in lem-pur-gysin-structure.proof.md, step 4
(blueprint: lem-pur-supported-hom-specified-existence).

Proof: identify constant-coefficient sections with locally constant functions.
The restriction A_X to i_*A_Z is epic and its kernel is extension by zero of
A_U. Hence Hom(i_*A_Z,M) is the support kernel, with the identification fixed
by evaluation on the image of 1 (lem-pur-supported-sections-hom). Exact scalar
forgetting commutes with bounded-below right derived functors, so this additive
identification derives on bounded-below injective complexes
(lem-weil-pbc-right-derived-plus-injective). The derived-Hom roof formula
(lem-sc-p1-rhom-hom-derived-roof) sends each cycle to exactly the displayed
localized chain map, which gives a natural isomorphism satisfying the formula.
No constructibility, Tor bound, or locally Noetherian assumption is used. -/
theorem exists_supportedCohomologyHom (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (a : ℤ) :
    ∃ χ : SupportedHomIdentification P i a, SupportedHomCocycleNormalization P i a χ := by
  sorry

/-- Uniqueness of a supported-Hom comparison satisfying the cocycle formula.
Source: lem-pur-supported-hom and its proof (latest blueprint, sk-prop-an)
(blueprint: lem-pur-supported-hom-specified-uniqueness).

Proof: by naturality it suffices to compare the components of χ₁ and χ₂ at
Q(I) for I a bounded-below complex of injectives, since every bounded-below
object is isomorphic to such a Q(I) (K-injective resolutions exist). Every
class in H^a_Z(X,I) is the image of a cycle s of Γ_Z(X,I). By the underived
identification Hom(i_*A_Z,I^a) ≅ Γ_Z(X,I^a), natural in I^a, there is a map
f : i_*A_Z → I^a whose value on the image of 1 is s, and f ≫ d = 0 because s is
a cycle. The normalizations h₁ and h₂ then give χ₁ and χ₂ the same value on the
class of s, so the components agree and χ₁ = χ₂. -/
theorem unique_supportedCohomologyHom (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (a : ℤ)
    (χ₁ χ₂ : SupportedHomIdentification P i a)
    (h₁ : SupportedHomCocycleNormalization P i a χ₁)
    (h₂ : SupportedHomCocycleNormalization P i a χ₂) : χ₁ = χ₂ := by
  sorry

/-- The supported-Hom isomorphism is uniquely determined by the cocycle formula.
Source: lem-pur-supported-hom and its proof, used in the latest
lem-pur-gysin-structure.proof.md, step 4 (blueprint: lem-pur-supported-hom).

Proof: existence is `exists_supportedCohomologyHom`; any second normalized
comparison equals it by `unique_supportedCohomologyHom`. -/
theorem existsUnique_supportedCohomologyHom (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (a : ℤ) :
    ∃! χ : SupportedHomIdentification P i a, SupportedHomCocycleNormalization P i a χ := by
  obtain ⟨χ, hχ⟩ := exists_supportedCohomologyHom P i a
  refine ⟨χ, hχ, ?_⟩
  intro χ' hχ'
  exact unique_supportedCohomologyHom P i a χ' χ hχ' hχ

/-- The specified natural supported-Hom isomorphism. Its data are determined uniquely
by evaluation on injective cycles, not by a bare Nonempty choice.
Source: lem-pur-supported-hom (blueprint: lem-pur-supported-hom). -/
def supportedCohomologyHom (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (a : ℤ) :
    SupportedHomIdentification P i a :=
  (existsUnique_supportedCohomologyHom P i a).exists.choose

end AlgebraicGeometry.ProEtale
