/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q92
-/
module

public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import Sheaf.Paper.ExchangeProjectionSuppliedDomains

/-!
# Coefficient factorization of the composite integration counit

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
lem-pur-projection-purity-agreement.proof.md, expanded affine-tower counit calculation;
Stacks Project, Tag 0DV0 (blueprint: lem-pur-composite-integration-counit).

`false` selects the ordinary etale site and `true` the small pro-etale site.
The fixed-scalar sheaf coordinates are the recorded canonical realization of finite
constant-ring modules. All operations and comparisons below select existing constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w a
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityIntegration

/-- Finiteness of the prescribed positive-level quotient, in its standard size lift.
Source: finite coefficient conventions (blueprint: lem-pur-composite-integration-counit). -/
instance coefficientFinite (P : PurityFiniteSetting.{u}) : Finite P.Coefficient := by
  let : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  exact inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

section Categorical

variable {C E T : Type w} [Category.{v} C] [Category.{v} E] [Category.{v} T]
  [MonoidalCategory C] [MonoidalCategory E] [MonoidalCategory T]

/-- The specified operations of one morphism, without changing any of their maps.
Source: the actual projection and pullback comparisons
(blueprint: lem-pur-composite-integration-counit). -/
structure IntegrationOperations (C E : Type w) [Category.{v} C] [Category.{v} E]
    [MonoidalCategory C] [MonoidalCategory E] where
  F : C ⥤ E
  P : E ⥤ C
  pf : ∀ M N, F.obj M ⊗ N ⟶ F.obj (M ⊗ P.obj N)
  pullTensor : ∀ K L, P.obj (K ⊗ L) ≅ P.obj K ⊗ P.obj L
  pullUnit : P.obj (𝟙_ E) ≅ 𝟙_ C

/-- The two morphisms and their actual composition comparisons.
Source: the displayed projection/compositor equation
(blueprint: lem-pur-composite-integration-counit). -/
structure CompositeOperations (C E T : Type w)
    [Category.{v} C] [Category.{v} E] [Category.{v} T]
    [MonoidalCategory C] [MonoidalCategory E] [MonoidalCategory T] where
  f : IntegrationOperations C E
  g : IntegrationOperations E T
  fg : IntegrationOperations C T
  origin : ObjectProperty C
  ctfX : ObjectProperty C
  ctfY : ObjectProperty E
  alpha : ∀ (M : C) (_hM : origin M), g.F.obj (f.F.obj M) ≅ fg.F.obj M
  pullComp : g.P ⋙ f.P ≅ fg.P

/-- Restriction of an actual operation to the supplied full subcategories.
Source: the closed-domain convention (blueprint: lem-pur-composite-integration-counit). -/
def restrict (H : C ⥤ E) (s : ObjectProperty C) (t : ObjectProperty E)
    (h : ∀ M, s M → t (H.obj M)) : s.FullSubcategory ⥤ t.FullSubcategory :=
  ObjectProperty.lift t (s.ι ⋙ H) (fun M ↦ h M.obj M.property)

/-- The supplied twisted-pullback adjunction on the stated domains.
Source: the adjunction hypotheses (blueprint: lem-pur-composite-integration-counit). -/
structure IntegrationAdjunction (o : IntegrationOperations C E)
    (s : ObjectProperty C) (t : ObjectProperty E) (L : C) where
  push_closed : ∀ M, s M → t (o.F.obj M)
  twist_closed : ∀ K, t K → s (o.P.obj K ⊗ L)
  adjunction : restrict o.F s t push_closed ⊣
    restrict (o.P ⋙ tensorRight L) t s twist_closed

/-- The actual supplied counit, read in the ambient category.
Source: supplied counits (blueprint: lem-pur-composite-integration-counit). -/
def epsilon {o : IntegrationOperations C E} {s : ObjectProperty C} {t : ObjectProperty E}
    {L : C} (adj : IntegrationAdjunction o s t L) (K : E) (hK : t K) :
    o.F.obj (o.P.obj K ⊗ L) ⟶ K := (adj.adjunction.counit.app ⟨K, hK⟩).hom

/-- The canonical unit identification in the twisted inverse image.
Source: unit constraints (blueprint: lem-pur-composite-integration-counit). -/
def twistUnit (o : IntegrationOperations C E) (L : C) : o.P.obj (𝟙_ E) ⊗ L ≅ L :=
  (o.pullUnit ⊗ᵢ Iso.refl L) ≪≫ λ_ L

/-- The supplied counit at the unit, with its canonical source identification.
Source: t_u = epsilon_{u,A} (blueprint: lem-pur-composite-integration-counit). -/
def trace {o : IntegrationOperations C E} {s : ObjectProperty C} {t : ObjectProperty E}
    {L : C} (adj : IntegrationAdjunction o s t L) (hunit : t (𝟙_ E)) :
    o.F.obj L ⟶ 𝟙_ E := o.F.map (twistUnit o L).inv ≫ epsilon adj _ hunit

/-- The inverse of the specified projection component.
Source: inverse projection convention (blueprint: lem-pur-composite-integration-counit). -/
def q (o : IntegrationOperations C E) (M : C) (N : E) (h : IsIso (o.pf M N)) :
    o.F.obj (M ⊗ o.P.obj N) ⟶ o.F.obj M ⊗ N := @inv _ _ _ _ (o.pf M N) h

variable [BraidedCategory C] [BraidedCategory E] [BraidedCategory T]

/-- The inverse projection with the specified tensor symmetries, followed by 1 tensor t.
Source: the coefficient counit formula (blueprint: lem-pur-composite-integration-counit). -/
def coefficientCounit (o : IntegrationOperations C E) (L : C)
    (t : o.F.obj L ⟶ 𝟙_ E) (K : E) (h : IsIso (o.pf L K)) :
    o.F.obj (o.P.obj K ⊗ L) ⟶ K :=
  o.F.map (β_ (o.P.obj K) L).hom ≫ q o L K h ≫
    (β_ (o.F.obj L) K).hom ≫ (K ◁ t) ≫ (ρ_ K).hom

/-- The tensor-action identity exactly on the supplied domain.
Source: the projection action hypothesis (blueprint: lem-pur-composite-integration-counit). -/
def TensorAction (o : IntegrationOperations C E) (s : ObjectProperty C)
    (t : ObjectProperty E) : Prop :=
  ∀ (M : C) (N₁ N₂ : E),
    s M → t N₁ → t N₂ → t (N₁ ⊗ N₂) → s (M ⊗ o.P.obj N₁) →
    (o.pf M N₁ ▷ N₂) ≫ o.pf (M ⊗ o.P.obj N₁) N₂ ≫
        o.F.map (α_ M (o.P.obj N₁) (o.P.obj N₂)).hom ≫
        o.F.map (M ◁ (o.pullTensor N₁ N₂).inv) =
      (α_ (o.F.obj M) N₁ N₂).hom ≫ o.pf M (N₁ ⊗ N₂)

/-- The composite twist, literally Lf tensor Pf Lg.
Source: the definition of L_gf (blueprint: lem-pur-composite-integration-counit). -/
def compositeTwist (o : CompositeOperations C E T) (Lf : C) (Lg : E) : C :=
  Lf ⊗ o.f.P.obj Lg

/-- The prescribed identification of the composite right adjoint, with Koszul symmetry.
Source: canonical reassociations (blueprint: lem-pur-composite-integration-counit). -/
def compositeTwistIso (o : CompositeOperations C E T) (Lf : C) (Lg : E) (K : T) :
    o.f.P.obj (o.g.P.obj K ⊗ Lg) ⊗ Lf ≅ o.fg.P.obj K ⊗ compositeTwist o Lf Lg :=
  (o.f.pullTensor (o.g.P.obj K) Lg ⊗ᵢ Iso.refl Lf) ≪≫
    (((o.pullComp.app K) ⊗ᵢ Iso.refl (o.f.P.obj Lg)) ⊗ᵢ Iso.refl Lf) ≪≫
    α_ (o.fg.P.obj K) (o.f.P.obj Lg) Lf ≪≫
    (Iso.refl (o.fg.P.obj K) ⊗ᵢ β_ (o.f.P.obj Lg) Lf)

/-- Exactly the supplied domains, twists, adjunctions and projection identities.
Source: all hypotheses of the node (blueprint: lem-pur-composite-integration-counit). -/
structure CompositeIntegrationData (o : CompositeOperations C E T) where
  domainX : ObjectProperty C
  domainY : ObjectProperty E
  domainZ : ObjectProperty T
  origin : ∀ M, domainX M → o.origin M
  Lf : C
  Lg : E
  ctf_f : o.ctfX Lf
  ctf_g : o.ctfY Lg
  mem_f : domainX Lf
  mem_g : domainY Lg
  mem_fg : domainX (compositeTwist o Lf Lg)
  unitY : domainY (𝟙_ E)
  unitZ : domainZ (𝟙_ T)
  af : IntegrationAdjunction o.f domainX domainY Lf
  ag : IntegrationAdjunction o.g domainY domainZ Lg
  pull_g : ∀ K, domainZ K → domainY (o.g.P.obj K)
  tensor_f : ∀ M N, domainX M → domainY N → domainX (M ⊗ o.f.P.obj N)
  tensor_g : ∀ M N, domainY M → domainZ N → domainY (M ⊗ o.g.P.obj N)
  tensor_fg : ∀ M N, domainX M → domainZ N → domainX (M ⊗ o.fg.P.obj N)
  pf_f : ∀ M N, domainX M → domainY N → IsIso (o.f.pf M N)
  pf_g : ∀ M N, domainY M → domainZ N → IsIso (o.g.pf M N)
  pf_fg : ∀ M N, domainX M → domainZ N → IsIso (o.fg.pf M N)
  action_f : TensorAction o.f domainX domainY
  action_g : TensorAction o.g domainY domainZ
  action_fg : TensorAction o.fg domainX domainZ
  projection_comp : ∀ (M : C) (K : T) (hM : domainX M) (hK : domainZ K),
    (o.alpha M (origin M hM)).hom ▷ K ≫ o.fg.pf M K =
      o.g.pf (o.f.F.obj M) K ≫ o.g.F.map (o.f.pf M (o.g.P.obj K)) ≫
        (o.alpha (M ⊗ o.f.P.obj (o.g.P.obj K))
          (origin _ (tensor_f M _ hM (pull_g K hK)))).hom ≫
        o.fg.F.map (M ◁ o.pullComp.hom.app K)
  counit_f : ∀ (K : E) (hK : domainY K),
    epsilon af K hK = coefficientCounit o.f Lf (trace af unitY) K (pf_f Lf K mem_f hK)
  counit_g : ∀ (K : T) (hK : domainZ K),
    epsilon ag K hK = coefficientCounit o.g Lg (trace ag unitZ) K (pf_g Lg K mem_g hK)

namespace CompositeIntegrationData

variable {o : CompositeOperations C E T} (d : CompositeIntegrationData o)

/-- The four-arrow composite trace, with the target unitor made explicit.
Source: displayed t_gf (blueprint: lem-pur-composite-integration-counit). -/
def compositeTrace : o.fg.F.obj (compositeTwist o d.Lf d.Lg) ⟶ 𝟙_ T :=
  (o.alpha _ (d.origin _ d.mem_fg)).inv ≫
    o.g.F.map (q o.f d.Lf d.Lg (d.pf_f _ _ d.mem_f d.mem_g)) ≫
    o.g.F.map (trace d.af d.unitY ▷ d.Lg) ≫
    o.g.F.map (λ_ d.Lg).hom ≫ trace d.ag d.unitZ

/-- The actual composite-adjunction counit, transported by the canonical comparisons.
Source: Stacks 0DV0 and the source identifications
(blueprint: lem-pur-composite-integration-counit). -/
def compositeCounit (K : T) (hK : d.domainZ K) :
    o.fg.F.obj (o.fg.P.obj K ⊗ compositeTwist o d.Lf d.Lg) ⟶ K :=
  o.fg.F.map (compositeTwistIso o d.Lf d.Lg K).inv ≫
    (o.alpha _ (d.origin _ (d.af.twist_closed _ (d.ag.twist_closed K hK)))).inv ≫
    ((d.af.adjunction.comp d.ag.adjunction).counit.app ⟨K, hK⟩).hom

/-- The three conclusions: coefficient factorization, unit value, and full naturality.
Source: the three concluding clauses (blueprint: lem-pur-composite-integration-counit). -/
def CounitFormula : Prop :=
  (∀ (K : T) (hK : d.domainZ K),
    d.compositeCounit K hK =
      coefficientCounit o.fg (compositeTwist o d.Lf d.Lg)
        d.compositeTrace K (d.pf_fg _ K d.mem_fg hK)) ∧
  (o.fg.F.map (twistUnit o.fg (compositeTwist o d.Lf d.Lg)).inv ≫
      d.compositeCounit (𝟙_ T) d.unitZ = d.compositeTrace) ∧
  (∀ (K K' : T) (hK : d.domainZ K) (hK' : d.domainZ K') (h : K ⟶ K'),
    o.fg.F.map (o.fg.P.map h ⊗ₘ 𝟙 (compositeTwist o d.Lf d.Lg)) ≫
      d.compositeCounit K' hK' = d.compositeCounit K hK ≫ h)

end CompositeIntegrationData
end Categorical

section NativeSites

variable (A : Type a) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

variable {FC : A → A → Type (u + 1)} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The canonical typed presentation is uniquely fixed by equality to every published
operation and comparison, including the actual projection map.
Source: the finite-level operations and canonical comparisons in the node statement
(blueprint: lem-pur-composite-integration-counit).

Proof: take the published compact-support and derived inverse-image functors, the
published projection transformation's components, and the published pullback tensor and
unit comparisons. Unfold the bifunctor wrappers to check their types. Every required
heterogeneous equality is reflexivity. For uniqueness, the first two equalities identify
the functor fields, after which function extensionality and the component equalities
identify all remaining fields. Thus no unspecified operation or map is chosen. -/
theorem etaleMorphOperations_existsUnique [Etale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    ∃! o : IntegrationOperations (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
        (_root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)),
      o.F = Etale.rightDerivedLowerShriek A f ∧
      o.P = (Etale.upperStar A f).leftDerivedFunctor ∧
      (∀ M N, HEq (o.pf M N) (((Etale.projectionMap A f).app M).app N)) ∧
      (∀ K L, HEq (o.pullTensor K L) (Etale.leftDerivedUpperStarTensorIso A f K L)) ∧
      HEq o.pullUnit (Etale.leftDerivedUpperStarUnitIso A f) := by
  sorry

/-- The unique presentation whose every field equals the corresponding published map.
The equality specification, rather than mere existence, determines all data.
Source: actual Etale operations (blueprint: lem-pur-composite-integration-counit). -/
def etaleMorphOperations [Etale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    IntegrationOperations (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
      (_root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :=
  Classical.choose (etaleMorphOperations_existsUnique A f)

/-- The canonical typed presentation is uniquely fixed by equality to every published
operation and comparison, including the actual projection map.
Source: the finite-level operations and canonical comparisons in the node statement
(blueprint: lem-pur-composite-integration-counit).

Proof: take the published compact-support and derived inverse-image functors, the
published projection transformation's components, and the published pullback tensor and
unit comparisons. Unfold the bifunctor wrappers to check their types. Every required
heterogeneous equality is reflexivity. For uniqueness, the first two equalities identify
the functor fields, after which function extensionality and the component equalities
identify all remaining fields. Thus no unspecified operation or map is chosen. -/
theorem proEtaleMorphOperations_existsUnique [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    ∃! o : IntegrationOperations (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
        (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)),
      o.F = ProEtale.rightDerivedLowerShriek A f ∧
      o.P = (ProEtale.upperStar A f).leftDerivedFunctor ∧
      (∀ M N, HEq (o.pf M N) (((ProEtale.projectionMap A f).app M).app N)) ∧
      (∀ K L, HEq (o.pullTensor K L) (ProEtale.leftDerivedUpperStarTensorIso A f K L)) ∧
      HEq o.pullUnit (ProEtale.leftDerivedUpperStarUnitIso A f) := by
  sorry

/-- The unique presentation whose every field equals the corresponding published map.
The equality specification, rather than mere existence, determines all data.
Source: actual ProEtale operations (blueprint: lem-pur-composite-integration-counit). -/
def proEtaleMorphOperations [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    IntegrationOperations (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :=
  Classical.choose (proEtaleMorphOperations_existsUnique A f)

/-- The presentation of the canonical composition comparisons with the specified native
operations. Every field is fixed by equality to existing data.
Source: actual site comparisons (blueprint: lem-pur-composite-integration-counit).

Proof: take the three uniquely normalized morphism operations. Their functor equalities
identify the types of the supplied compositor and the published pullback composition.
Transport those maps along these equalities and use the actual origin and constructible
properties. All specified heterogeneous equalities are then reflexivity after equality
elimination. Uniqueness follows by structure extensionality, followed by heterogeneous
equality elimination on the last two fields; proof irrelevance removes origin witnesses. -/
theorem etaleCompositeOperations_existsUnique [Etale.UpperStarPreservesFlat A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (alpha : (Etale.rightDerivedLowerShriek A f ⋙ Etale.rightDerivedLowerShriek A g) ≅
      (Etale.rightDerivedLowerShriek A (f ≫ g))) :
    ∃! o : CompositeOperations (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
        (_root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
        (_root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)),
      o.f = etaleMorphOperations A f ∧
      o.g = etaleMorphOperations A g ∧
      o.fg = etaleMorphOperations A (f ≫ g) ∧
      o.origin = (fun _ ↦ True) ∧
      o.ctfX = Etale.DerivedCategory.constructibleFiniteTor A X ∧
      o.ctfY = Etale.DerivedCategory.constructibleFiniteTor A Y ∧
      (∀ M hM, HEq (o.alpha M hM) (alpha.app M)) ∧
      HEq o.pullComp (Etale.leftDerivedUpperStarComp A f g).symm := by
  sorry

/-- The uniquely specified presentation; every component is an equality-determined map.
Source: canonical site comparisons (blueprint: lem-pur-composite-integration-counit). -/
def etaleCompositeOperations [Etale.UpperStarPreservesFlat A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (alpha : (Etale.rightDerivedLowerShriek A f ⋙ Etale.rightDerivedLowerShriek A g) ≅
      (Etale.rightDerivedLowerShriek A (f ≫ g))) :
    CompositeOperations (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
      (_root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
      (_root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :=
  Classical.choose (etaleCompositeOperations_existsUnique A f g alpha)

/-- The presentation of the canonical composition comparisons with the specified native
operations. Every field is fixed by equality to existing data.
Source: actual site comparisons (blueprint: lem-pur-composite-integration-counit).

Proof: take the three uniquely normalized morphism operations. Their functor equalities
identify the types of the supplied compositor and the published pullback composition.
Transport those maps along these equalities and use the actual origin and constructible
properties. All specified heterogeneous equalities are then reflexivity after equality
elimination. Uniqueness follows by structure extensionality, followed by heterogeneous
equality elimination on the last two fields; proof irrelevance removes origin witnesses. -/
theorem proEtaleCompositeOperations_existsUnique [ProEtale.UpperStarPreservesFlat A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (alpha : ((ProEtale.DerivedCategory.plusEtaleOrigin A X).ι ⋙
      ProEtale.rightDerivedLowerShriek A f ⋙ ProEtale.rightDerivedLowerShriek A g) ≅
      ((ProEtale.DerivedCategory.plusEtaleOrigin A X).ι ⋙
        ProEtale.rightDerivedLowerShriek A (f ≫ g))) :
    ∃! o : CompositeOperations (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
        (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
        (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)),
      o.f = proEtaleMorphOperations A f ∧
      o.g = proEtaleMorphOperations A g ∧
      o.fg = proEtaleMorphOperations A (f ≫ g) ∧
      o.origin = (ProEtale.DerivedCategory.plusEtaleOrigin A X) ∧
      o.ctfX = ProEtale.DerivedCategory.constructibleFiniteTor A X ∧
      o.ctfY = ProEtale.DerivedCategory.constructibleFiniteTor A Y ∧
      (∀ M hM (hM' : ProEtale.DerivedCategory.plusEtaleOrigin A X M),
        HEq (o.alpha M hM) (alpha.app ⟨M, hM'⟩)) ∧
      HEq o.pullComp (ProEtale.leftDerivedUpperStarComp A f g).symm := by
  sorry

/-- The uniquely specified presentation; every component is an equality-determined map.
Source: canonical site comparisons (blueprint: lem-pur-composite-integration-counit). -/
def proEtaleCompositeOperations [ProEtale.UpperStarPreservesFlat A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (alpha : ((ProEtale.DerivedCategory.plusEtaleOrigin A X).ι ⋙
      ProEtale.rightDerivedLowerShriek A f ⋙ ProEtale.rightDerivedLowerShriek A g) ≅
      ((ProEtale.DerivedCategory.plusEtaleOrigin A X).ι ⋙
        ProEtale.rightDerivedLowerShriek A (f ≫ g))) :
    CompositeOperations (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) :=
  Classical.choose (proEtaleCompositeOperations_existsUnique A f g alpha)

end NativeSites

/-- The uniquely specified native Koszul braiding, in the native derived tensor instance.
Source: canonical tensor symmetry in the node
(blueprint: lem-pur-composite-integration-counit).

Proof: the published localization braiding gives the witness. Its heterogeneous equality
is reflexivity after unfolding the monoidal shortcut instance. Any other witness is equal
by heterogeneous equality elimination. This postpones only that definitional normalization,
not the choice of a braiding. -/
theorem nativeBraiding_existsUnique (C : Type w) [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] [HasDerivedCategory.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] :
    ∃! B : BraidedCategory (_root_.DerivedCategory C),
      HEq B (DerivedMonoidal.braidedCategory' (_root_.DerivedCategory.Qh (C := C))
        (HomotopyCategory.quasiIso C (.up ℤ))) := by
  sorry

set_option warn.classDefReducibility false in
/-- The equality-determined canonical braiding of the existing derived tensor.
Source: canonical Koszul symmetries (blueprint: lem-pur-composite-integration-counit). -/
def nativeBraiding (C : Type w) [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] [HasDerivedCategory.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] : BraidedCategory (_root_.DerivedCategory C) :=
  Classical.choose (nativeBraiding_existsUnique C)

section Assembly

variable (R : Type (u + 1)) [CommRing R] [Finite R] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
  [QuasiCompact f] [QuasiCompact g]

/-- Actual Etale operations with the published normalized compact-support compositor.
Source: ordinary-site clause (blueprint: lem-pur-composite-integration-counit). -/
def etaleOperations :=
  etaleCompositeOperations (ModuleCat.{u + 1} R) f g
    (Etale.unboundedEtaleLowerShriekCompIso R f g)

/-- Actual ProEtale operations with the published origin compact-support compositor.
Source: pro-etale clause (blueprint: lem-pur-composite-integration-counit). -/
def proEtaleOperations :=
  proEtaleCompositeOperations (ModuleCat.{u + 1} R) f g
    (ProEtale.originCompositionAmbient R f g)

end Assembly

/-- Read the three conclusions with the specified canonical braidings.
Source: canonical tensor symmetries (blueprint: lem-pur-composite-integration-counit). -/
def formulaFor {C E T : Type w} [Category.{v} C] [Category.{v} E] [Category.{v} T]
    [MonoidalCategory C] [MonoidalCategory E] [MonoidalCategory T]
    (o : CompositeOperations C E T)
    (bC : BraidedCategory C) (bE : BraidedCategory E) (bT : BraidedCategory T) : Prop :=
  letI := bC
  letI := bE
  letI := bT
  ∀ d : CompositeIntegrationData o, d.CounitFormula

/-- The full assertion at the selected site, using that site's actual operations.
Source: the two concluding site clauses (blueprint: lem-pur-composite-integration-counit). -/
def integrationCounitAssertion (b : Bool) (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] : Prop :=
  match b with
  | false => formulaFor (etaleOperations R f g)
      (nativeBraiding (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
      (nativeBraiding (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)))
      (nativeBraiding (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R)))
  | true => formulaFor (proEtaleOperations R f g)
      (nativeBraiding (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)))
      (nativeBraiding (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R)))
      (nativeBraiding (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R)))

/-- Coefficient factorization of the actual composite twisted-pullback counit, at both
sites, including its tensor-unit value and naturality on the supplied domain.
Source: blueprint main-20261015, lem-pur-projection-purity-agreement.proof.md, expanded
Step 6, final canonical-reassociation paragraph; Stacks Project, Tag 0DV0
(blueprint: lem-pur-composite-integration-counit).

Proof, following all seven steps of the node:
1. Expand `Adjunction.comp`: its counit is F_g(epsilon_f) followed by epsilon_g. Use the
canonical symmetry to put both twists first, and use the pullback/tensor comparison and
associator to identify the inner source with L_gf tensor P_f P_g K.
2. Invert the supplied action identity for f at (L_f,L_g,P_g K). Put
`a = q_f(L_f,L_g) ≫ (t_f ▷ L_g) ≫ lambda`. Substitution of the given f-counit formula
then gives `epsilon_f = q_f(L_gf,P_g K) ≫ (a ▷ P_g K)`, with the source constraints.
3. Substitute this and the given g-counit formula into the actual composite counit.
Functoriality of F_g produces the three factors q_f, F_g(a tensor 1), and q_g.
4. Naturality of the inverse projection in its first variable moves F_g(a) through q_g.
Bifunctoriality combines the remaining trace factors into t_g composed with F_g(a).
5. Invert the assumed projection/compositor identity and cancel its invertible factors.
It replaces q_g composed with F_g(q_f) and alpha inverse by q_gf followed by
alpha inverse tensor identity. The remaining trace is precisely `compositeTrace`.
Insert the two canonical symmetries to recover the requested order `(1_K tensor t) Pi`.
6. At the tensor unit the action identity says q=q squared after the canonical unit
constraints. Since q is invertible it is the identity. The formula is consequently
the stated equality of the unit counit and the four-arrow composite trace.
7. Naturality of the actual counits and compositor, inverse-projection naturality,
and tensor functoriality give the displayed square for every domain morphism.
The calculation uses only the supplied identities. `b=false` repeats it on the ordinary
etale site's actual maps; `b=true` uses the canonical pro-etale origin compositor.
-/
theorem compositeIntegrationCounit
    (b : Bool) (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z) [f.IsOver (Spec (.of P.field.k))]
    [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [IsSeparated g] [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    : integrationCounitAssertion b P.Coefficient f g := by
  sorry

end WeilConjectures.PurityIntegration
