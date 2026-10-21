/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.SupportQuotientFlat
public import Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.OpenClosed.Conservative
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-!
# Normalized multiplication of support quotients

Source: blueprint main-20261015, `lem-pur-kunneth-supported`, support-quotient
refinement (blueprint: lem-pur-support-quotient-product).

The coefficient ring and the base field are independent. The generator equations
specify multiplication, including zero coefficients. The derived map is the actual
localization comparison followed by the degree-zero multiplication. Naturality is
expressed by its quotient-generator test: every pullback square preserving the
constant generators commutes. In particular this applies to the maps induced by
morphisms of pairs and their product.
-/

/-- Reuse the tensor dictionaries recorded in the localization map's type.
Reconstructing these arguments during specialization unfolds the derived tensor objects.
The generated term is an application of the proved generic lemma and is kernel checked. -/
private meta def apply_localization_dictionary (helper cacheEq laxEq : Lean.Name) :
    Lean.Elab.Tactic.TacticM Unit := do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let t ← goal.getType
  let ca := t.getAppArgs.back!.getAppArgs
  unless ca.size == 7 do
    throwError "expected the composite defining the supported localization map"
  let ma := ca[5]!.getAppArgs
  unless ma.size == 10 do
    throwError "expected the localization tensorator"
  let mc := ma[2]!
  let md := ma[5]!
  let cm := mc.getAppArgs
  let dm := md.getAppArgs
  unless cm.size == 8 && dm.size == 10 do
    throwError "unexpected cached tensor dictionaries"
  let lax := ma[7]!
  let f ← Lean.Meta.mkConstWithFreshMVarLevels helper
  let mut ty ← Lean.Meta.inferType f
  for a in #[cm[0]!, cm[1]!, cm[2]!, dm[3]!, cm[3]!,
      cm[4]!, cm[5]!, cm[7]!, cm[6]!] do
    unless ← Lean.Meta.isDefEq ty.bindingDomain! (← Lean.Meta.inferType a) do
      throwError "localization dictionary prefix mismatch"
    ty := ty.bindingBody!.instantiate1 a
  let flat ← Lean.Meta.synthInstance ty.bindingDomain!
  let mut flatHypothesis : Option Lean.Expr := none
  for d in ← Lean.getLCtx do
    if d.userName.eraseMacroScopes == `hF then flatHypothesis := some d.toExpr
  let some hf := flatHypothesis | throwError "missing flatness hypothesis"
  let e := ca[6]!.getAppArgs.back!.getAppArgs.back!
  let et ← Lean.Meta.inferType e
  let hmc ← Lean.Meta.mkAppOptM cacheEq
    ((#[cm[0]!, cm[1]!, cm[2]!, cm[3]!, cm[4]!, cm[5]!, cm[6]!, cm[7]!]).map some)
  let la := lax.getAppArgs
  let hlax ← Lean.Meta.mkAppOptM laxEq
    ((#[la[0]!, la[1]!, la[2]!, la[3]!, la[4]!, la[5]!, la[6]!,
      la[8]!, la[9]!, la[7]!]).map some)
  let term := Lean.mkAppN f #[cm[0]!, cm[1]!, cm[2]!, dm[3]!, cm[3]!,
    cm[4]!, cm[5]!, cm[7]!, cm[6]!, flat, dm[4]!,
    mc, hmc, md, ← Lean.Meta.mkEqRefl md,
    lax, hlax,
    ma[8]!.getAppArgs.back!, ma[9]!.getAppArgs.back!, hf, et.getAppArgs[2]!, e]
  goal.assign term
  Lean.Elab.Tactic.replaceMainGoal []

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

attribute [local instance 20000] AlgebraicGeometry.Etale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory AlgebraicGeometry.Etale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
  instMonoidalCategoryHomologicalComplexIntUp_weilConjectures
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  AlgebraicGeometry.Etale.upperStar AlgebraicGeometry.ProEtale.upperStar

namespace AlgebraicGeometry.Scheme

attribute [local implicit_reducible] etaleSupportQuotient etaleSupportQuotientMap
  proEtaleSupportQuotient proEtaleSupportQuotientMap

/-- Pull back the recorded cokernel, without choosing a new support object.
Source: blueprint support-quotient refinement
(blueprint: lem-pur-support-quotient-product). -/
def etaleSupportQuotientPullback (A : Type u) [CommRing A] [Finite A]
    {C T V : Scheme.{u}} (a : C ⟶ T) [IsClosedImmersion a] (h : V ⟶ T) :=
  (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).obj (etaleSupportQuotient A a)

/-- The tensor of the two quotient generators, with constant one sent to one tensor one.
Source: blueprint support-quotient refinement
(blueprint: lem-pur-support-quotient-product). -/
def etaleSupportQuotientProductGenerator (A : Type u) [CommRing A] [Finite A]
    {B X Y Z W : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] :
    (constantSheaf (pullback f g).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶
      etaleSupportQuotientPullback A i (pullback.fst f g) ⊗
        etaleSupportQuotientPullback A j (pullback.snd f g) :=
  (constantSheaf (pullback f g).smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).map
      (λ_ (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))).inv ≫
    Etale.constantExteriorTensor (ULift.{u + 1, u} A) f g
      (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
      (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ≫
    ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.fst f g)).map (etaleSupportQuotientMap A i) ⊗ₘ
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.snd f g)).map (etaleSupportQuotientMap A j))

/-- The canonical derived-to-ordinary tensor comparison for the two degree-zero
factors. Composing with the canonical single-complex collapse and the ordinary
multiplication gives the derived multiplication. Both latter arrows are isomorphisms,
so invertibility of this arrow is exactly invertibility of that multiplication.
Source: blueprint support-quotient refinement
(blueprint: lem-pur-support-quotient-product). -/
def etaleSupportQuotientDerivedComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u})
    (F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  Etale.supportedDerivedTensorLocalizationGeneric
    (ModuleCat.{u + 1} A) T
    ((HomologicalComplex.single _ (.up ℤ) 0).obj F)
    ((HomologicalComplex.single _ (.up ℤ) 0).obj G)

/-- Naturality tested on the quotient generators. Here `s` is the induced map on the
pulled-back tensor and `c` the induced map on the product support quotient. Requiring
commutation with the generators describes those maps without choosing replacements.
The quantification also includes identity and composite maps of pairs.
Source: blueprint support-quotient refinement
(blueprint: lem-pur-support-quotient-product). -/
def etaleSupportQuotientProductNatural (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u})
    {F H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))}
    (m : (constantSheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶ F)
    (r : (constantSheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶ H)
    (e : F ⟶ H) : Prop :=
  ∀ (T' : Scheme.{u}) (h : T' ⟶ T)
    (F' H' : Sheaf T'.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (m' : (constantSheaf T'.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶ F')
    (r' : (constantSheaf T'.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶ H')
    (e' : F' ⟶ H')
    (s : (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).obj F ⟶ F')
    (c : (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).obj H ⟶ H'),
    m' ≫ e' = r' →
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).map m ≫ s =
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).hom.app
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ≫ m' →
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).map r ≫ c =
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).hom.app
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ≫ r' →
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).map e ≫ c = s ≫ e'

/-- Pull back the recorded cokernel, without choosing a new support object.
Source: blueprint support-quotient refinement
(blueprint: lem-pur-support-quotient-product). -/
def proEtaleSupportQuotientPullback (A : Type u) [CommRing A] [Finite A]
    {C T V : Scheme.{u}} (a : C ⟶ T) [IsClosedImmersion a] (h : V ⟶ T) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).obj (proEtaleSupportQuotient A a)

/-- The tensor of the two quotient generators, with constant one sent to one tensor one.
Source: blueprint support-quotient refinement
(blueprint: lem-pur-support-quotient-product). -/
def proEtaleSupportQuotientProductGenerator (A : Type u) [CommRing A] [Finite A]
    {B X Y Z W : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] :
    (constantSheaf (ProEt.topology (pullback f g))
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶
      proEtaleSupportQuotientPullback A i (pullback.fst f g) ⊗
        proEtaleSupportQuotientPullback A j (pullback.snd f g) :=
  (constantSheaf (ProEt.topology (pullback f g))
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).map
      (λ_ (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))).inv ≫
    ProEtale.constantExteriorTensor (ULift.{u + 1, u} A) f g
      (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
      (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ≫
    ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.fst f g)).map (proEtaleSupportQuotientMap A i) ⊗ₘ
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.snd f g)).map (proEtaleSupportQuotientMap A j))

/-- The canonical derived-to-ordinary tensor comparison for the two degree-zero
factors. Composing with the canonical single-complex collapse and the ordinary
multiplication gives the derived multiplication. Both latter arrows are isomorphisms,
so invertibility of this arrow is exactly invertibility of that multiplication.
Source: blueprint support-quotient refinement
(blueprint: lem-pur-support-quotient-product). -/
def proEtaleSupportQuotientDerivedComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u})
    (F G : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) :=
  ProEtale.supportedDerivedTensorLocalizationGeneric
    (ModuleCat.{u + 1} A) T
    ((HomologicalComplex.single _ (.up ℤ) 0).obj F)
    ((HomologicalComplex.single _ (.up ℤ) 0).obj G)

/-- Naturality tested on the quotient generators. Here `s` is the induced map on the
pulled-back tensor and `c` the induced map on the product support quotient. Requiring
commutation with the generators describes those maps without choosing replacements.
The quantification also includes identity and composite maps of pairs.
Source: blueprint support-quotient refinement
(blueprint: lem-pur-support-quotient-product). -/
def proEtaleSupportQuotientProductNatural (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u})
    {F H : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))}
    (m : (constantSheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶ F)
    (r : (constantSheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶ H)
    (e : F ⟶ H) : Prop :=
  ∀ (T' : Scheme.{u}) (h : T' ⟶ T)
    (F' H' : Sheaf (ProEt.topology T')
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (m' : (constantSheaf (ProEt.topology T')
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶ F')
    (r' : (constantSheaf (ProEt.topology T')
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⟶ H')
    (e' : F' ⟶ H')
    (s : (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).obj F ⟶ F')
    (c : (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).obj H ⟶ H'),
    m' ≫ e' = r' →
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).map m ≫ s =
      (ProEtale.constantSheafCompUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).hom.app
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ≫ m' →
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).map r ≫ c =
      (ProEtale.constantSheafCompUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).hom.app
        (𝟙_ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ≫ r' →
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).map e ≫ c = s ≫ e'

attribute [local irreducible] constantSheaf

-- Generic coefficient APIs inherit their coefficient braiding from symmetry.
attribute [local instance 2000] SymmetricCategory.toBraidedCategory

attribute [local irreducible] etaleSupportQuotientDerivedComparison
  proEtaleSupportQuotientDerivedComparison etaleSupportQuotientProductNatural
  proEtaleSupportQuotientProductNatural

attribute [local implicit_reducible] etaleSupportQuotientPullback
  proEtaleSupportQuotientPullback

-- Use the recorded adjunction directly instead of searching through site constructions.
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private instance (priority := 20000) etale_pullback_preservesEpi
    (A : Type (u + 1)) [CommRing A] {V T : Scheme.{u}} (h : V ⟶ T) :
    (Etale.upperStar (ModuleCat.{u + 1} A) h).PreservesEpimorphisms :=
  Functor.preservesEpimorphisms_of_adjunction
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h)

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private instance (priority := 20000) etale_pullback_preservesColimits
    (A : Type (u + 1)) [CommRing A] {V T : Scheme.{u}} (h : V ⟶ T) :
    PreservesColimitsOfSize.{0, 0} (Etale.upperStar (ModuleCat.{u + 1} A) h) :=
  (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).leftAdjoint_preservesColimits

-- Use the recorded adjunction directly instead of searching through site constructions.
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private instance (priority := 20000) proetale_pullback_preservesEpi
    (A : Type (u + 1)) [CommRing A] {V T : Scheme.{u}} (h : V ⟶ T) :
    (ProEtale.upperStar (ModuleCat.{u + 1} A) h).PreservesEpimorphisms :=
  Functor.preservesEpimorphisms_of_adjunction
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h)

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private instance (priority := 20000) proetale_pullback_preservesColimits
    (A : Type (u + 1)) [CommRing A] {V T : Scheme.{u}} (h : V ⟶ T) :
    PreservesColimitsOfSize.{0, 0} (ProEtale.upperStar (ModuleCat.{u + 1} A) h) :=
  (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).leftAdjoint_preservesColimits

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem cached_complex_eq
    (C : Type*) [Category.{u + 1} C] [Abelian C] [HasColimitsOfSize.{0, 0} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C] :
    instMonoidalCategoryHomologicalComplexIntUp_weilConjectures C =
      HomologicalComplex.monoidalCategory C (.up ℤ) := by rfl

attribute [local instance 20000] Etale.sheafMonoidalCategory
  Etale.sheafBraidedCategory Etale.sheafMonoidalClosed in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem etale_lax_eq
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (T : Scheme.{u}) :
    HEq (Etale.laxMonoidal_Q C T)
      (DerivedCategory.laxMonoidalQ (Sheaf T.smallEtaleTopology C)) := by rfl

attribute [local instance 20000] ProEtale.sheafMonoidalCategory
  ProEtale.sheafBraidedCategory ProEtale.sheafMonoidalClosed in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem proetale_lax_eq
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (T : Scheme.{u}) :
    HEq (ProEtale.laxMonoidal_Q C T)
      (DerivedCategory.laxMonoidalQ (Sheaf (ProEt.topology T) C)) := by rfl

-- Keep the source dictionaries as arguments, so specialization does not unfold tensorators.
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem localization_single_tensor_isIso
    {C : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [HasColimitsOfSize.{0, 0} C]
    [mon : MonoidalCategory C] [MonoidalPreadditive C] [braid : BraidedCategory C]
    [cl : MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory.{u + 1} C]
    (MC : MonoidalCategory (CochainComplex C ℤ))
    (hMC : MC = HomologicalComplex.monoidalCategory C (.up ℤ))
    (MD : MonoidalCategory (DerivedCategory C))
    (hMD : MD = DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory C)
    (lax : @Functor.LaxMonoidal (CochainComplex C ℤ) _ MC
      (DerivedCategory C) _ MD DerivedCategory.Q)
    (hlax : HEq lax (DerivedCategory.laxMonoidalQ C))
    (F G : C) (hF : ObjectProperty.flat F) (H : CochainComplex C ℤ)
    (e : ((@curriedTensor (CochainComplex C ℤ) _ MC).obj
      ((HomologicalComplex.single C (.up ℤ) 0).obj F)).obj
      ((HomologicalComplex.single C (.up ℤ) 0).obj G) = H) :
    IsIso (C := DerivedCategory C) (@Functor.LaxMonoidal.μ (CochainComplex C ℤ) _ MC
      (DerivedCategory C) _ MD DerivedCategory.Q lax
      ((HomologicalComplex.single C (.up ℤ) 0).obj F)
      ((HomologicalComplex.single C (.up ℤ) 0).obj G) ≫
      DerivedCategory.Q.map (eqToHom e)) := by
  subst MC
  subst MD
  cases hlax
  have hk := (HomotopyCategory.kFlat_quotient_obj_iff _).2
    ((CochainComplex.kFlat_single_obj_iff_flat F 0).2 hF)
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj F))
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj G))) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_left DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ)) _ _ hk
  have : IsIso (C := DerivedCategory C) (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((HomologicalComplex.single C (.up ℤ) 0).obj F)
      ((HomologicalComplex.single C (.up ℤ) 0).obj G)) := by
    change IsIso ((_ ⊗ₘ _) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
    infer_instance
  exact IsIso.comp_isIso' this
    (Functor.map_isIso (DerivedCategory.Q (C := C)) (eqToHom e))



attribute [local instance 20000] Etale.sheafMonoidalCategory
  Etale.sheafBraidedCategory Etale.sheafMonoidalClosed in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem etale_generic_comparison_isIso
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (T : Scheme.{u}) (F G : Sheaf T.smallEtaleTopology C) (hF : ObjectProperty.flat F) :
    IsIso (C := DerivedCategory (Sheaf T.smallEtaleTopology C))
      (Etale.supportedDerivedTensorLocalizationGeneric C T
        ((HomologicalComplex.single _ (.up ℤ) 0).obj F)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj G)) := by
  unfold Etale.supportedDerivedTensorLocalizationGeneric
  run_tac (apply_localization_dictionary ``localization_single_tensor_isIso
    ``cached_complex_eq ``etale_lax_eq)

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem etale_derivedComparison_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hF : ObjectProperty.flat F) :
    IsIso (C := DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (etaleSupportQuotientDerivedComparison A T F G) := by
  unfold etaleSupportQuotientDerivedComparison
  exact etale_generic_comparison_isIso (ModuleCat.{u + 1} A) T F G hF

attribute [local instance 20000] ProEtale.sheafMonoidalCategory
  ProEtale.sheafBraidedCategory ProEtale.sheafMonoidalClosed in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem proEtale_generic_comparison_isIso
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (T : Scheme.{u}) (F G : Sheaf (ProEt.topology T) C) (hF : ObjectProperty.flat F) :
    IsIso (C := DerivedCategory (Sheaf (ProEt.topology T) C))
      (ProEtale.supportedDerivedTensorLocalizationGeneric C T
        ((HomologicalComplex.single _ (.up ℤ) 0).obj F)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj G)) := by
  unfold ProEtale.supportedDerivedTensorLocalizationGeneric
  run_tac (apply_localization_dictionary ``localization_single_tensor_isIso
    ``cached_complex_eq ``proetale_lax_eq)

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem proEtale_derivedComparison_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (F G : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A))
    (hF : ObjectProperty.flat F) :
    IsIso (C := DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)))
      (proEtaleSupportQuotientDerivedComparison A T F G) := by
  unfold proEtaleSupportQuotientDerivedComparison
  exact proEtale_generic_comparison_isIso (ModuleCat.{u + 1} A) T F G hF

attribute [local irreducible] DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  DerivedCategory.laxMonoidalQ DerivedCategory.laxMonoidalQh

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem etale_quotient_flat
    (A : Type u) [CommRing A] [Finite A] {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] [QuasiCompact i.openComplement.ι] :
    ObjectProperty.flat (etaleSupportQuotient A i) := by
  apply (Etale.flat_iff_forall_flat_sheafFiber_obj _).mpr
  intro Ω _ _ t
  let e := ((pointSmallEtale t).uliftSheafFiberIso.{u + 1}
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).app (etaleSupportQuotient A i)
  have hs := (supportQuotient_flat_kflat_stalk_comparison A i).2.2.2.2.1 Ω t
  by_cases ht : t (IsLocalRing.closedPoint Ω) ∈ Set.range i
  · obtain ⟨q, -⟩ := hs.1 ht
    exact ObjectProperty.prop_of_iso ObjectProperty.flat (e ≪≫ q).symm
      (ObjectProperty.prop_unit ObjectProperty.flat)
  · exact ObjectProperty.flat_of_isZero ((hs.2 ht).of_iso e)

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem proEtale_quotient_flat
    (A : Type u) [CommRing A] [Finite A] {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] [QuasiCompact i.openComplement.ι] :
    ObjectProperty.flat (proEtaleSupportQuotient A i) := by
  obtain ⟨e, -, -⟩ := (supportQuotient_flat_kflat_stalk_comparison A i).2.2.2.2.2
  exact ObjectProperty.prop_of_iso ObjectProperty.flat e
    (ProEtale.flat_comparisonUpperStar_obj (etale_quotient_flat A i))

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem etale_coefficientQuotient_natural
    (A : Type (u + 1)) [CommRing A] {Z T : Scheme.{u}} (i : Z ⟶ T)
    {M N : ModuleCat.{u + 1} A} (a : M ⟶ N) :
    (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).map a ≫
        Etale.supportedCoefficientQuotient A i N =
      Etale.supportedCoefficientQuotient A i M ≫ (Etale.supportedCoefficients A i).map a := by
  let q : constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      Etale.supportedCoefficients A i :=
    Functor.whiskerLeft
      (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit ≫
      Functor.whiskerRight
        (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).hom
        (Etale.lowerStar (ModuleCat.{u + 1} A) i)
  exact q.naturality a

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem proEtale_coefficientQuotient_natural
    (A : Type (u + 1)) [CommRing A] [Finite A] {Z T : Scheme.{u}} (i : Z ⟶ T)
    {M N : ModuleCat.{u + 1} A} (a : M ⟶ N) :
    (constantSheaf (ProEt.topology T) (ModuleCat.{u + 1} A)).map a ≫
        ProEtale.supportedCoefficientQuotient A i N =
      ProEtale.supportedCoefficientQuotient A i M ≫
        (ProEtale.supportedCoefficients A i).map a := by
  let q : constantSheaf (ProEt.topology T) (ModuleCat.{u + 1} A) ⟶
      ProEtale.supportedCoefficients A i :=
    Functor.whiskerLeft
      (constantSheaf (ProEt.topology T) (ModuleCat.{u + 1} A))
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit ≫
      Functor.whiskerRight
        (ProEtale.constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) i).hom
        (ProEtale.lowerStar (ModuleCat.{u + 1} A) i)
  exact q.naturality a

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem etale_quotient_closed
    (A : Type u) [CommRing A] [Finite A] {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] :
    ∃ e : etaleSupportQuotient A i ≅
        (Etale.supportedCoefficients (ULift.{u + 1, u} A) i).obj (𝟙_ _),
      etaleSupportQuotientMap A i ≫ e.hom =
        Etale.supportedCoefficientQuotient (ULift.{u + 1, u} A) i (𝟙_ _) ∧
      IsIso ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).map
        (etaleSupportQuotientMap A i)) ∧
      IsZero ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        i.openComplement.ι).obj (etaleSupportQuotient A i)) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let F := (constantSheaf T.smallEtaleTopology B).obj (𝟙_ B)
  let S := Etale.upperStar B i
  let R := Etale.upperStar B i.openComplement.ι
  let q := Etale.supportedCoefficientQuotient (ULift.{u + 1, u} A) i (𝟙_ B)
  have hd := disjoint_range_of_range_eq_compl _ _
    i.range_eq_compl_range_openComplement_ι
  have hz := Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range
    B i.openComplement.ι i hd
    ((Etale.openImmersionRestriction B i.openComplement.ι).obj F)
  have hzero : etaleSupportQuotientArrow A i ≫ q = 0 := by
    apply ((Etale.upperStarLowerStarAdjunction B i).homEquiv _ _).symm.injective
    exact hz.eq_of_src _ _
  let b := cokernel.desc (etaleSupportQuotientArrow A i) q hzero
  have hb : etaleSupportQuotientMap A i ≫ b = q := cokernel.π_desc _ _ _
  have hSπ : IsIso (S.map (etaleSupportQuotientMap A i)) :=
    CokernelCofork.IsColimit.isIso_π _
      (isColimitOfHasCokernelOfPreservesColimit S _) (hz.eq_of_src _ _)
  have hSunit := Etale.isIso_upperStar_map_upperStarLowerStarAdjunction_unit B i F
  have hSq : IsIso (S.map q) := by
    dsimp only [q, Etale.supportedCoefficientQuotient]
    rw [Adjunction.homEquiv_apply]
    erw [Functor.map_comp]
    change IsIso (S.map ((Etale.upperStarLowerStarAdjunction B i).unit.app F) ≫
      S.map ((Etale.lowerStar B i).map
        ((Scheme.upperStarConstantSheafIso B i).hom.app (𝟙_ B))))
    infer_instance
  have hSb : IsIso (S.map b) := by
    have : IsIso (S.map (etaleSupportQuotientMap A i) ≫ S.map b) := by
      rw [← Functor.map_comp, hb]
      exact hSq
    exact IsIso.of_isIso_comp_left (S.map (etaleSupportQuotientMap A i)) (S.map b)
  have hRf : IsIso (R.map (etaleSupportQuotientArrow A i)) := by
    apply (NatIso.isIso_map_iff
      (Etale.upperStarIsoOpenImmersionRestriction B i.openComplement.ι) _).mpr
    unfold etaleSupportQuotientArrow
    infer_instance
  have hzRsrc : IsZero (R.obj (etaleSupportQuotient A i)) :=
    (isZero_cokernel_of_epi (R.map (etaleSupportQuotientArrow A i))).of_iso
      (PreservesCokernel.iso R _)
  have hzRtgt := Etale.isZero_upperStar_lowerStar_of_disjoint_range B
    i.openComplement.ι i hd ((constantSheaf Z.smallEtaleTopology B).obj (𝟙_ B))
  have hRb : IsIso (R.map b) := ⟨0, hzRsrc.eq_of_src _ _, hzRtgt.eq_of_src _ _⟩
  have : IsIso b := Etale.isIso_of_isIso_upperStar_map B i.openComplement.ι i
    i.range_eq_compl_range_openComplement_ι b hRb hSb
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency false in
    exact ⟨asIso b, hb, hSπ, hzRsrc⟩

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem proEtale_quotient_closed
    (A : Type u) [CommRing A] [Finite A] {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] [QuasiCompact i.openComplement.ι] :
    ∃ e : proEtaleSupportQuotient A i ≅
        (ProEtale.supportedCoefficients (ULift.{u + 1, u} A) i).obj (𝟙_ _),
      proEtaleSupportQuotientMap A i ≫ e.hom =
        ProEtale.supportedCoefficientQuotient (ULift.{u + 1, u} A) i (𝟙_ _) ∧
      IsIso ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).map
        (proEtaleSupportQuotientMap A i)) ∧
      IsZero ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        i.openComplement.ι).obj (proEtaleSupportQuotient A i)) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let F := (constantSheaf (ProEt.topology T) B).obj (𝟙_ B)
  let S := ProEtale.upperStar B i
  let R := ProEtale.upperStar B i.openComplement.ι
  let q := ProEtale.supportedCoefficientQuotient (ULift.{u + 1, u} A) i (𝟙_ B)
  have hd := disjoint_range_of_range_eq_compl _ _
    i.range_eq_compl_range_openComplement_ι
  have hz : IsZero (S.obj ((ProEtale.openImmersionLowerShriek B
      i.openComplement.ι).obj
        ((ProEtale.openImmersionRestriction B i.openComplement.ι).obj F))) := by
    refine IsInitial.isZero (IsInitial.ofUnique (h := fun H ↦ ?_))
    have hz' := ProEtale.isZero_upperStar_lowerStar_of_disjoint
      B i i.openComplement.ι hd.symm H
    have : Unique (((ProEtale.openImmersionRestriction B i.openComplement.ι).obj F) ⟶
        (ProEtale.upperStar B i.openComplement.ι).obj ((ProEtale.lowerStar B i).obj H)) :=
      ⟨⟨hz'.isTerminal.from _⟩, fun _ ↦ hz'.isTerminal.hom_ext _ _⟩
    exact Equiv.unique
      (((ProEtale.upperStarLowerStarAdjunction B i).homEquiv _ H).trans
        ((ProEtale.openImmersionLowerShriekUpperStarAdjunction B
          i.openComplement.ι).homEquiv _ _))
  have hzero : proEtaleSupportQuotientArrow A i ≫ q = 0 := by
    apply ((ProEtale.upperStarLowerStarAdjunction B i).homEquiv _ _).symm.injective
    exact hz.eq_of_src _ _
  let b := cokernel.desc (proEtaleSupportQuotientArrow A i) q hzero
  have hb : proEtaleSupportQuotientMap A i ≫ b = q := cokernel.π_desc _ _ _
  have hSπ : IsIso (S.map (proEtaleSupportQuotientMap A i)) :=
    CokernelCofork.IsColimit.isIso_π _
      (isColimitOfHasCokernelOfPreservesColimit S _) (hz.eq_of_src _ _)
  have hSunit : IsIso (S.map ((ProEtale.upperStarLowerStarAdjunction B i).unit.app F)) := by
    have h := (ProEtale.upperStarLowerStarAdjunction B i).left_triangle_components F
    have : IsIso (S.map ((ProEtale.upperStarLowerStarAdjunction B i).unit.app F) ≫
        (ProEtale.upperStarLowerStarAdjunction B i).counit.app (S.obj F)) := by
      rw [h]
      exact ⟨𝟙 _, by simp [S], by simp [S]⟩
    exact IsIso.of_isIso_comp_right
      (S.map ((ProEtale.upperStarLowerStarAdjunction B i).unit.app F))
      ((ProEtale.upperStarLowerStarAdjunction B i).counit.app (S.obj F))
  have hSq : IsIso (S.map q) := by
    dsimp only [q, ProEtale.supportedCoefficientQuotient]
    rw [Adjunction.homEquiv_apply]
    erw [Functor.map_comp]
    change IsIso (S.map ((ProEtale.upperStarLowerStarAdjunction B i).unit.app F) ≫
      S.map ((ProEtale.lowerStar B i).map
        ((ProEtale.constantSheafCompUpperStarIso B i).hom.app (𝟙_ B))))
    infer_instance
  have hSb : IsIso (S.map b) := by
    have : IsIso (S.map (proEtaleSupportQuotientMap A i) ≫ S.map b) := by
      rw [← Functor.map_comp, hb]
      exact hSq
    exact IsIso.of_isIso_comp_left (S.map (proEtaleSupportQuotientMap A i)) (S.map b)
  have hRf : IsIso (R.map (proEtaleSupportQuotientArrow A i)) := by
    apply (NatIso.isIso_map_iff
      (ProEtale.upperStarIsoOpenImmersionRestriction B i.openComplement.ι) _).mpr
    unfold proEtaleSupportQuotientArrow
    infer_instance
  have hzRsrc : IsZero (R.obj (proEtaleSupportQuotient A i)) :=
    (isZero_cokernel_of_epi (R.map (proEtaleSupportQuotientArrow A i))).of_iso
      (PreservesCokernel.iso R _)
  have hzRtgt := ProEtale.isZero_upperStar_lowerStar_of_disjoint
    B i i.openComplement.ι hd.symm
    ((constantSheaf (ProEt.topology Z) B).obj (𝟙_ B))
  have hRb : IsIso (R.map b) := ⟨0, hzRsrc.eq_of_src _ _, hzRtgt.eq_of_src _ _⟩
  have : IsIso b := ProEtale.isIso_of_isIso_upperStar_of_isCompl
    (R := ULift.{u + 1, u} A) i i.openComplement.ι
    (by rw [i.range_eq_compl_range_openComplement_ι]; exact isCompl_compl.symm) b
  set_option backward.isDefEq.respectTransparency false in
    exact ⟨asIso b, hb, hSπ, hzRsrc⟩

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem etale_pullback_factor_isIso
    (A : Type (u + 1)) [CommRing A] {V T Z X : Scheme.{u}}
    (a : V ⟶ T) (b : T ⟶ X) (c : V ⟶ Z) (d : Z ⟶ X) (w : a ≫ b = c ≫ d)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)} (α : F ⟶ G)
    [IsIso ((Etale.upperStar (ModuleCat.{u + 1} A) d).map α)] :
    IsIso ((Etale.upperStar (ModuleCat.{u + 1} A) a).map
      ((Etale.upperStar (ModuleCat.{u + 1} A) b).map α)) := by
  let B := ModuleCat.{u + 1} A
  let e := (Etale.upperStarComp B a b).symm ≪≫
    eqToIso (congrArg (Etale.upperStar B) w) ≪≫ Etale.upperStarComp B c d
  apply (NatIso.isIso_map_iff e α).mpr
  change IsIso ((Etale.upperStar B c).map ((Etale.upperStar B d).map α))
  infer_instance

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem proEtale_pullback_factor_isIso
    (A : Type (u + 1)) [CommRing A] {V T Z X : Scheme.{u}}
    (a : V ⟶ T) (b : T ⟶ X) (c : V ⟶ Z) (d : Z ⟶ X) (w : a ≫ b = c ≫ d)
    {F G : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)} (α : F ⟶ G)
    [IsIso ((ProEtale.upperStar (ModuleCat.{u + 1} A) d).map α)] :
    IsIso ((ProEtale.upperStar (ModuleCat.{u + 1} A) a).map
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) b).map α)) := by
  let B := ModuleCat.{u + 1} A
  let e := (ProEtale.upperStarComp B a b).symm ≪≫
    eqToIso (congrArg (ProEtale.upperStar B) w) ≪≫ ProEtale.upperStarComp B c d
  apply (NatIso.isIso_map_iff e α).mpr
  change IsIso ((ProEtale.upperStar B c).map ((ProEtale.upperStar B d).map α))
  infer_instance

attribute [local semireducible] constantSheaf in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem etale_constantExteriorTensor_isIso
    (A : Type (u + 1)) [CommRing A] {B X Y : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (M N : ModuleCat.{u + 1} A) :
    IsIso (Etale.constantExteriorTensor A f g M N) := by
  have : IsIso (Etale.constantPresheafTensor A (pullback f g) M N) := by
    have : ∀ U, IsIso ((Etale.constantPresheafTensor A (pullback f g) M N).app U) := by
      intro U
      change IsIso (𝟙 _)
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  unfold Etale.constantExteriorTensor Etale.supportedConstantTensor
    Etale.supportedSheafTensorMapGeneric Etale.supportedSheafTensorGeneric
  dsimp only [curriedTensor]
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.isDefEq.respectTransparency false in
    infer_instance

attribute [local semireducible] constantSheaf in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem proEtale_constantExteriorTensor_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (M N : ModuleCat.{u + 1} A) :
    IsIso (ProEtale.constantExteriorTensor A f g M N) := by
  have : IsIso (ProEtale.constantPresheafTensor A (pullback f g) M N) := by
    have : ∀ U, IsIso ((ProEtale.constantPresheafTensor A (pullback f g) M N).app U) := by
      intro U
      change IsIso (𝟙 _)
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  unfold ProEtale.constantExteriorTensor ProEtale.supportedConstantTensor
    ProEtale.supportedSheafTensorMapGeneric ProEtale.supportedSheafTensorGeneric
  dsimp only [curriedTensor]
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.isDefEq.respectTransparency false in
    infer_instance

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem tensorHom_epi
    {C : Type*} [Category C] [Abelian C] [MonoidalCategory C]
    [MonoidalClosed C] [BraidedCategory C] {F F' G G' : C}
    (a : F ⟶ F') (b : G ⟶ G') [Epi a] [Epi b] : Epi (a ⊗ₘ b) := by
  rw [MonoidalCategory.tensorHom_def]
  change Epi ((tensorRight G).map a ≫ (tensorLeft F').map b)
  infer_instance

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem etale_productGenerator_epi
    (A : Type u) [CommRing A] [Finite A]
    {B X Y Z W : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] :
    Epi (etaleSupportQuotientProductGenerator A f g i j) := by
  have := etale_constantExteriorTensor_isIso (ULift.{u + 1, u} A) f g
    (𝟙_ _) (𝟙_ _)
  have : Epi (etaleSupportQuotientMap A i) := by
    unfold etaleSupportQuotientMap
    infer_instance
  have : Epi (etaleSupportQuotientMap A j) := by
    unfold etaleSupportQuotientMap
    infer_instance
  have : Epi ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.fst f g)).map (etaleSupportQuotientMap A i)) :=
    (etale_pullback_preservesEpi (ULift.{u + 1, u} A) _).preserves _
  have : Epi ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.snd f g)).map (etaleSupportQuotientMap A j)) :=
    (etale_pullback_preservesEpi (ULift.{u + 1, u} A) _).preserves _
  have hTensor := tensorHom_epi
    ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.fst f g)).map (etaleSupportQuotientMap A i))
    ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.snd f g)).map (etaleSupportQuotientMap A j))
  unfold etaleSupportQuotientProductGenerator
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.isDefEq.respectTransparency false in
    exact epi_comp' (IsIso.epi_of_iso _) (epi_comp' (IsIso.epi_of_iso _) hTensor)

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem proEtale_productGenerator_epi
    (A : Type u) [CommRing A] [Finite A]
    {B X Y Z W : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] :
    Epi (proEtaleSupportQuotientProductGenerator A f g i j) := by
  have := proEtale_constantExteriorTensor_isIso (ULift.{u + 1, u} A) f g
    (𝟙_ _) (𝟙_ _)
  have : Epi (proEtaleSupportQuotientMap A i) := by
    unfold proEtaleSupportQuotientMap
    infer_instance
  have : Epi (proEtaleSupportQuotientMap A j) := by
    unfold proEtaleSupportQuotientMap
    infer_instance
  have : Epi ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.fst f g)).map (proEtaleSupportQuotientMap A i)) :=
    (proetale_pullback_preservesEpi (ULift.{u + 1, u} A) _).preserves _
  have : Epi ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.snd f g)).map (proEtaleSupportQuotientMap A j)) :=
    (proetale_pullback_preservesEpi (ULift.{u + 1, u} A) _).preserves _
  have hTensor := tensorHom_epi
    ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.fst f g)).map (proEtaleSupportQuotientMap A i))
    ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.snd f g)).map (proEtaleSupportQuotientMap A j))
  unfold proEtaleSupportQuotientProductGenerator
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.isDefEq.respectTransparency false in
    exact epi_comp' (IsIso.epi_of_iso _) (epi_comp' (IsIso.epi_of_iso _) hTensor)

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem etale_generator_natural
    (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u})
    {F H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))}
    (m : (constantSheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj (𝟙_ _) ⟶ F)
    (r : (constantSheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj (𝟙_ _) ⟶ H)
    (e : F ⟶ H) [Epi m] (he : m ≫ e = r) :
    etaleSupportQuotientProductNatural A T m r e := by
  unfold etaleSupportQuotientProductNatural
  intro T' h F' H' m' r' e' s c he' hm hr
  have : Epi ((Etale.upperStar _ h).map m) :=
    (etale_pullback_preservesEpi (ULift.{u + 1, u} A) h).preserves m
  apply (cancel_epi ((Etale.upperStar _ h).map m)).mp
  simp only [← Category.assoc, ← Functor.map_comp, he]
  rw [hr, hm, Category.assoc, he']

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem proEtale_generator_natural
    (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u})
    {F H : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))}
    (m : (constantSheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj (𝟙_ _) ⟶ F)
    (r : (constantSheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj (𝟙_ _) ⟶ H)
    (e : F ⟶ H) [Epi m] (he : m ≫ e = r) :
    proEtaleSupportQuotientProductNatural A T m r e := by
  unfold proEtaleSupportQuotientProductNatural
  intro T' h F' H' m' r' e' s c he' hm hr
  have : Epi ((ProEtale.upperStar _ h).map m) :=
    (proetale_pullback_preservesEpi (ULift.{u + 1, u} A) h).preserves m
  apply (cancel_epi ((ProEtale.upperStar _ h).map m)).mp
  simp only [← Category.assoc, ← Functor.map_comp, he]
  rw [hr, hm, Category.assoc, he']

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem etale_product_factor
    (A : Type u) [CommRing A] [Finite A]
    {B X Y Z W : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] :
    ∃ b : etaleSupportQuotient A (Etale.supportedProductImmersion f g i j) ⟶
        etaleSupportQuotientPullback A i (pullback.fst f g) ⊗
          etaleSupportQuotientPullback A j (pullback.snd f g),
      etaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j) ≫ b =
        etaleSupportQuotientProductGenerator A f g i j := by
  let R := ULift.{u + 1, u} A
  let M := 𝟙_ (ModuleCat.{u + 1} R)
  let a := Etale.supportedProductImmersion f g i j
  let L := Etale.upperStar (ModuleCat.{u + 1} R) (pullback.fst f g)
  let K := Etale.upperStar (ModuleCat.{u + 1} R) (pullback.snd f g)
  obtain ⟨ei, hi, -, -⟩ := etale_quotient_closed A i
  obtain ⟨ej, hj, -, -⟩ := etale_quotient_closed A j
  obtain ⟨ea, ha, -, -⟩ := etale_quotient_closed A a
  obtain ⟨t, ht, -⟩ := Etale.exists_unique_supportedCoefficientTensor R f g i j M M
  let b := ea.hom ≫ (Etale.supportedCoefficients R a).map (λ_ M).inv ≫
    t ≫ (L.map ei.inv ⊗ₘ K.map ej.inv)
  refine ⟨b, ?_⟩
  dsimp only [b]
  simp only [← Category.assoc]
  erw [ha]
  rw [← etale_coefficientQuotient_natural R a (λ_ M).inv]
  rw [Category.assoc _ _ t, ht]
  simp only [Category.assoc]
  change (constantSheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} R)).map
      (λ_ M).inv ≫ Etale.constantExteriorTensor R f g M M ≫
      (L.map (Etale.supportedCoefficientQuotient R i M) ⊗ₘ
        K.map (Etale.supportedCoefficientQuotient R j M)) ≫
      (L.map ei.inv ⊗ₘ K.map ej.inv) = _
  rw [tensorHom_comp_tensorHom, ← L.map_comp, ← K.map_comp]
  have hi' : Etale.supportedCoefficientQuotient R i M ≫ ei.inv =
      etaleSupportQuotientMap A i := by
    rw [← hi, Category.assoc, ei.hom_inv_id]
    exact Category.comp_id _
  have hj' : Etale.supportedCoefficientQuotient R j M ≫ ej.inv =
      etaleSupportQuotientMap A j := by
    rw [← hj, Category.assoc, ej.hom_inv_id]
    exact Category.comp_id _
  rw [hi', hj']
  rfl

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem proEtale_product_factor
    (A : Type u) [CommRing A] [Finite A]
    {B X Y Z W : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian (pullback f g)] :
    ∃ b : proEtaleSupportQuotient A (Etale.supportedProductImmersion f g i j) ⟶
        proEtaleSupportQuotientPullback A i (pullback.fst f g) ⊗
          proEtaleSupportQuotientPullback A j (pullback.snd f g),
      proEtaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j) ≫ b =
        proEtaleSupportQuotientProductGenerator A f g i j := by
  let R := ULift.{u + 1, u} A
  let M := 𝟙_ (ModuleCat.{u + 1} R)
  let a := Etale.supportedProductImmersion f g i j
  let L := ProEtale.upperStar (ModuleCat.{u + 1} R) (pullback.fst f g)
  let K := ProEtale.upperStar (ModuleCat.{u + 1} R) (pullback.snd f g)
  obtain ⟨ei, hi, -, -⟩ := proEtale_quotient_closed A i
  obtain ⟨ej, hj, -, -⟩ := proEtale_quotient_closed A j
  obtain ⟨ea, ha, -, -⟩ := proEtale_quotient_closed A a
  obtain ⟨t, ht, -⟩ := ProEtale.exists_unique_supportedCoefficientTensor R f g i j M M
  let b := ea.hom ≫ (ProEtale.supportedCoefficients R a).map (λ_ M).inv ≫
    t ≫ (L.map ei.inv ⊗ₘ K.map ej.inv)
  refine ⟨b, ?_⟩
  dsimp only [b]
  simp only [← Category.assoc]
  erw [ha]
  rw [← proEtale_coefficientQuotient_natural R a (λ_ M).inv]
  rw [Category.assoc _ _ t, ht]
  simp only [Category.assoc]
  change (constantSheaf (ProEt.topology (pullback f g)) (ModuleCat.{u + 1} R)).map
      (λ_ M).inv ≫ ProEtale.constantExteriorTensor R f g M M ≫
      (L.map (ProEtale.supportedCoefficientQuotient R i M) ⊗ₘ
        K.map (ProEtale.supportedCoefficientQuotient R j M)) ≫
      (L.map ei.inv ⊗ₘ K.map ej.inv) = _
  rw [tensorHom_comp_tensorHom, ← L.map_comp, ← K.map_comp]
  have hi' : ProEtale.supportedCoefficientQuotient R i M ≫ ei.inv =
      proEtaleSupportQuotientMap A i := by
    rw [← hi, Category.assoc, ei.hom_inv_id]
    exact Category.comp_id _
  have hj' : ProEtale.supportedCoefficientQuotient R j M ≫ ej.inv =
      proEtaleSupportQuotientMap A j := by
    rw [← hj, Category.assoc, ej.hom_inv_id]
    exact Category.comp_id _
  rw [hi', hj']
  rfl

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem etale_product_iso
    (A : Type u) [CommRing A] [Finite A]
    {B X Y Z W : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] :
    ∃ e : etaleSupportQuotientPullback A i (pullback.fst f g) ⊗
        etaleSupportQuotientPullback A j (pullback.snd f g) ≅
        etaleSupportQuotient A (Etale.supportedProductImmersion f g i j),
      etaleSupportQuotientProductGenerator A f g i j ≫ e.hom =
        etaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j) := by
  let D := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let a := Etale.supportedProductImmersion f g i j
  let S := Etale.upperStar D a
  let R := Etale.upperStar D a.openComplement.ι
  let m := etaleSupportQuotientProductGenerator A f g i j
  let r := etaleSupportQuotientMap A a
  obtain ⟨b, hb⟩ := etale_product_factor A f g i j
  have hm : Epi m := etale_productGenerator_epi A f g i j
  have hbepi : Epi b := by
    have : Epi (r ≫ b) := hb ▸ hm
    exact epi_of_epi r b
  obtain ⟨_, _, hi, _⟩ := etale_quotient_closed A i
  obtain ⟨_, _, hj, _⟩ := etale_quotient_closed A j
  obtain ⟨_, _, ha, hz⟩ := etale_quotient_closed A a
  have hpi := etale_pullback_factor_isIso (ULift.{u + 1, u} A) a
    (pullback.fst f g) (pullback.fst (i ≫ f) (j ≫ g)) i
    (by simp only [a, Etale.supportedProductImmersion, pullback.map, pullback.lift_fst])
    (etaleSupportQuotientMap A i)
  have hpj := etale_pullback_factor_isIso (ULift.{u + 1, u} A) a
    (pullback.snd f g) (pullback.snd (i ≫ f) (j ≫ g)) j
    (by simp only [a, Etale.supportedProductImmersion, pullback.map, pullback.lift_snd])
    (etaleSupportQuotientMap A j)
  have hmS : IsIso (S.map m) := by
    have := etale_constantExteriorTensor_isIso (ULift.{u + 1, u} A) f g (𝟙_ D) (𝟙_ D)
    dsimp only [m, etaleSupportQuotientProductGenerator]
    rw [Functor.map_comp, Functor.map_comp, Functor.Monoidal.map_tensor]
    infer_instance
  have hbS : IsIso (S.map b) := by
    have : IsIso (S.map r ≫ S.map b) := by rw [← S.map_comp, hb]; exact hmS
    exact IsIso.of_isIso_comp_left (S.map r) (S.map b)
  have hz' := IsZero.of_epi (R.map b) hz
  have hbR : IsIso (R.map b) := ⟨0, hz.eq_of_src _ _, hz'.eq_of_src _ _⟩
  have : IsIso b := Etale.isIso_of_isIso_upperStar_map D a.openComplement.ι a
    a.range_eq_compl_range_openComplement_ι b hbR hbS
  refine ⟨(asIso b).symm, ?_⟩
  change m ≫ inv b = r
  change r ≫ b = m at hb
  rw [← hb, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem proEtale_product_iso
    (A : Type u) [CommRing A] [Finite A]
    {B X Y Z W : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian (pullback f g)] :
    ∃ e : proEtaleSupportQuotientPullback A i (pullback.fst f g) ⊗
        proEtaleSupportQuotientPullback A j (pullback.snd f g) ≅
        proEtaleSupportQuotient A (Etale.supportedProductImmersion f g i j),
      proEtaleSupportQuotientProductGenerator A f g i j ≫ e.hom =
        proEtaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j) := by
  let D := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let a := Etale.supportedProductImmersion f g i j
  let S := ProEtale.upperStar D a
  let R := ProEtale.upperStar D a.openComplement.ι
  let m := proEtaleSupportQuotientProductGenerator A f g i j
  let r := proEtaleSupportQuotientMap A a
  obtain ⟨b, hb⟩ := proEtale_product_factor A f g i j
  have hm : Epi m := proEtale_productGenerator_epi A f g i j
  have hbepi : Epi b := by
    have : Epi (r ≫ b) := hb ▸ hm
    exact epi_of_epi r b
  obtain ⟨_, _, hi, _⟩ := proEtale_quotient_closed A i
  obtain ⟨_, _, hj, _⟩ := proEtale_quotient_closed A j
  obtain ⟨_, _, ha, hz⟩ := proEtale_quotient_closed A a
  have hpi := proEtale_pullback_factor_isIso (ULift.{u + 1, u} A) a
    (pullback.fst f g) (pullback.fst (i ≫ f) (j ≫ g)) i
    (by simp only [a, Etale.supportedProductImmersion, pullback.map, pullback.lift_fst])
    (proEtaleSupportQuotientMap A i)
  have hpj := proEtale_pullback_factor_isIso (ULift.{u + 1, u} A) a
    (pullback.snd f g) (pullback.snd (i ≫ f) (j ≫ g)) j
    (by simp only [a, Etale.supportedProductImmersion, pullback.map, pullback.lift_snd])
    (proEtaleSupportQuotientMap A j)
  have hmS : IsIso (S.map m) := by
    have := proEtale_constantExteriorTensor_isIso (ULift.{u + 1, u} A) f g (𝟙_ D) (𝟙_ D)
    dsimp only [m, proEtaleSupportQuotientProductGenerator]
    rw [Functor.map_comp, Functor.map_comp, Functor.Monoidal.map_tensor]
    infer_instance
  have hbS : IsIso (S.map b) := by
    have : IsIso (S.map r ≫ S.map b) := by rw [← S.map_comp, hb]; exact hmS
    exact IsIso.of_isIso_comp_left (S.map r) (S.map b)
  have hz' := IsZero.of_epi (R.map b) hz
  have hbR : IsIso (R.map b) := ⟨0, hz.eq_of_src _ _, hz'.eq_of_src _ _⟩
  have : IsIso b := ProEtale.isIso_of_isIso_upperStar_of_isCompl
    (R := ULift.{u + 1, u} A) a a.openComplement.ι
    (by rw [a.range_eq_compl_range_openComplement_ι]; exact isCompl_compl.symm) b
  refine ⟨(asIso b).symm, ?_⟩
  change m ≫ inv b = r
  change r ≫ b = m at hb
  rw [← hb, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

-- The proof, stated with the coefficient braiding of the generic localization APIs.
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem supportQuotient_product_aux
    (A : Type u) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y Z W : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] :
    (∃! e :
      etaleSupportQuotientPullback A i (pullback.fst f g) ⊗
        etaleSupportQuotientPullback A j (pullback.snd f g) ≅
          etaleSupportQuotient A (Etale.supportedProductImmersion f g i j),
      etaleSupportQuotientProductGenerator A f g i j ≫ e.hom =
        etaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j) ∧
      IsIso (C := DerivedCategory (Sheaf (pullback f g).smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
        (etaleSupportQuotientDerivedComparison (ULift.{u + 1, u} A) (pullback f g)
        (etaleSupportQuotientPullback A i (pullback.fst f g))
        (etaleSupportQuotientPullback A j (pullback.snd f g))) ∧
      etaleSupportQuotientProductNatural A (pullback f g)
        (etaleSupportQuotientProductGenerator A f g i j)
        (etaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j)) e.hom) ∧
    (∃! e :
      proEtaleSupportQuotientPullback A i (pullback.fst f g) ⊗
        proEtaleSupportQuotientPullback A j (pullback.snd f g) ≅
          proEtaleSupportQuotient A (Etale.supportedProductImmersion f g i j),
      proEtaleSupportQuotientProductGenerator A f g i j ≫ e.hom =
        proEtaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j) ∧
      IsIso (C := DerivedCategory (Sheaf (ProEt.topology (pullback f g))
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
        (proEtaleSupportQuotientDerivedComparison (ULift.{u + 1, u} A) (pullback f g)
        (proEtaleSupportQuotientPullback A i (pullback.fst f g))
        (proEtaleSupportQuotientPullback A j (pullback.snd f g))) ∧
      proEtaleSupportQuotientProductNatural A (pullback f g)
        (proEtaleSupportQuotientProductGenerator A f g i j)
        (proEtaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j)) e.hom) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsLocallyNoetherian (pullback f g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g ≫ f)
  constructor
  · obtain ⟨e, he⟩ := etale_product_iso A f g i j
    have hm := etale_productGenerator_epi A f g i j
    have hflat : ObjectProperty.flat
        (etaleSupportQuotientPullback A i (pullback.fst f g)) :=
      Functor.PreservesFlat.flat_obj (F := Etale.upperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst f g))
        (etale_quotient_flat A i)
    refine ⟨e, ⟨he, etale_derivedComparison_isIso _ _ _ _ hflat,
      etale_generator_natural A _ _ _ _ he⟩, ?_⟩
    intro e' he'
    apply Iso.ext
    apply (cancel_epi (etaleSupportQuotientProductGenerator A f g i j)).mp
    exact he'.1.trans he.symm
  · obtain ⟨e, he⟩ := proEtale_product_iso A f g i j
    have hm := proEtale_productGenerator_epi A f g i j
    have hflat : ObjectProperty.flat
        (proEtaleSupportQuotientPullback A i (pullback.fst f g)) :=
      Functor.PreservesFlat.flat_obj (F := ProEtale.upperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst f g))
        (proEtale_quotient_flat A i)
    refine ⟨e, ⟨he, proEtale_derivedComparison_isIso _ _ _ _ hflat,
      proEtale_generator_natural A _ _ _ _ he⟩, ?_⟩
    intro e' he'
    apply Iso.ext
    apply (cancel_epi (proEtaleSupportQuotientProductGenerator A f g i j)).mp
    exact he'.1.trans he.symm

end AlgebraicGeometry.Scheme

-- The local coefficient-braiding instance above ends with the namespace: the statement
-- below elaborates exactly as published.
namespace AlgebraicGeometry.Scheme

/-- The normalized product multiplication in both topologies, also for derived tensor.
Source: blueprint main-20261015, support-quotient refinement of
`lem-pur-kunneth-supported` (blueprint: lem-pur-support-quotient-product).

Proof:
1. Finite type over the field makes X, Y and their product Noetherian. Thus the open
complements are quasi-compact and the quotient-flat lemma applies. Geometric stalks
of each pulled-back quotient are A on its support and zero elsewhere.
2. Write the two quotient kernels as I and J. Multiplication A tensor A to A descends
through (A/I) tensor (A/J) to A/(I+J): both kernels vanish in the product-support
quotient. On each geometric stalk this sends a tensor b to ab, and is an isomorphism.
The generator map is epic, proving uniqueness and all generator-preserving naturality
squares, including those induced by morphisms of the pairs and their products.
3. Both quotient complexes are K-flat in degree zero. The lax-monoidal localization
comparison is therefore invertible. Collapse the tensor of the two single complexes;
the resulting map is exactly the degree-zero ordinary multiplication specified here.
4. Exact etale-to-pro-etale comparison preserves the quotient generators, projection
pullbacks and tensor. It transports the normalized multiplication and its derived
map, giving the same assertions and naturality on the pro-etale site. -/
theorem supportQuotient_product
    (A : Type u) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y Z W : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] :
    (∃! e :
      etaleSupportQuotientPullback A i (pullback.fst f g) ⊗
        etaleSupportQuotientPullback A j (pullback.snd f g) ≅
          etaleSupportQuotient A (Etale.supportedProductImmersion f g i j),
      etaleSupportQuotientProductGenerator A f g i j ≫ e.hom =
        etaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j) ∧
      IsIso (etaleSupportQuotientDerivedComparison (ULift.{u + 1, u} A) (pullback f g)
        (etaleSupportQuotientPullback A i (pullback.fst f g))
        (etaleSupportQuotientPullback A j (pullback.snd f g))) ∧
      etaleSupportQuotientProductNatural A (pullback f g)
        (etaleSupportQuotientProductGenerator A f g i j)
        (etaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j)) e.hom) ∧
    (∃! e :
      proEtaleSupportQuotientPullback A i (pullback.fst f g) ⊗
        proEtaleSupportQuotientPullback A j (pullback.snd f g) ≅
          proEtaleSupportQuotient A (Etale.supportedProductImmersion f g i j),
      proEtaleSupportQuotientProductGenerator A f g i j ≫ e.hom =
        proEtaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j) ∧
      IsIso (proEtaleSupportQuotientDerivedComparison (ULift.{u + 1, u} A) (pullback f g)
        (proEtaleSupportQuotientPullback A i (pullback.fst f g))
        (proEtaleSupportQuotientPullback A j (pullback.snd f g))) ∧
      proEtaleSupportQuotientProductNatural A (pullback f g)
        (proEtaleSupportQuotientProductGenerator A f g i j)
        (proEtaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j)) e.hom) :=
  supportQuotient_product_aux A k f g i j

end AlgebraicGeometry.Scheme
