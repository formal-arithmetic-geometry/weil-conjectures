/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Compactification.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicOpenUnit
import Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing

/-! # Compactified graph maps for semilinear systems

Source: Stacks Project, Tag 0F4L, lemma-shriek-into-star-separated-etale;
blueprint det-sp-tower-gluing, Local pairs and Levels
(blueprint: lem-sp-semilinear-compactified-graph-evaluation).

The ordinary data retain their original names, constructions and helper statements
(blueprint: def-sp-semilinear-compactified-graph-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.SemilinearGraph

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- Composition into the pro-etale site, retaining the system index.
Source: Stacks 0F4L and weakly-etale localization
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
abbrev inclusion {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :=
  (𝟭 ℕ).prod (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
    (inferInstance : WeaklyEtale e))

/-- Composition preserves the vertical covering topology.
Source: Stacks 00XZ, 094T; blueprint Local pairs
(blueprint: lem-sp-semilinear-compactified-graph-evaluation).
Proof: at each index use continuity of composition of weakly etale objects;
vertical coverings are precisely coverings at that fixed index. -/
theorem inclusion_continuous {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    (inclusion e).IsContinuous (coefficientSequenceTopology (ProEt.topology U))
      (coefficientSequenceTopology (ProEt.topology T)) := by
  sorry

attribute [instance] inclusion_continuous

/-- The inverse of the constant-coefficient restriction is uniquely specified by
its action on the constant sections. This supplies actual ring transport, with
all horizontal transitions retained.
Source: Stacks 00XZ, 0F4L; blueprint Local pairs
(blueprint: lem-sp-semilinear-compactified-graph-evaluation).
Proof: apply constant-sheaf localization at every index. Its isomorphism is the
identity on constants, and naturality in C_n makes the horizontal squares commute.
Sheafification gives uniqueness on every level, hence on the sequence site. -/
theorem restrictionRing_existsUnique {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    ∃! a : SemilinearProperOpen.ringSystem C τ U ⟶
      ((inclusion e).sheafPushforwardContinuous CommRingCat.{u + 1}
        (coefficientSequenceTopology (ProEt.topology U))
        (coefficientSequenceTopology (ProEt.topology T))).obj
          (SemilinearProperOpen.ringSystem C τ T),
      IsIso a ∧ ∀ (n : ℕ) (V : U.ProEt) (x : C n),
        a.hom.app (op (n, V))
          (((toSheafify (ProEt.topology U)
            ((Functor.const U.ProEtᵒᵖ).obj (C n))).app (op V)) x) =
        ((toSheafify (ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (C n))).app
            (op ((MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
              (inferInstance : WeaklyEtale e)).obj V))) x := by
  sorry

/-- The uniquely constant-section-normalized ring identification.
Source: Stacks 00XZ, 0F4L
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def restrictionRing {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :=
  (restrictionRing_existsUnique C τ e).choose

/-- Restriction keeps all section groups, with their canonical constant-ring action.
Source: Stacks 0F4L and weakly-etale localization
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def restriction {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    SemilinearProperOpen.Modules C τ T ⥤ SemilinearProperOpen.Modules C τ U :=
  letI := inclusion_continuous e
  SheafOfModules.pushforward (F := inclusion e)
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (restrictionRing C τ e))

/-- The actual sheafified direct-sum extension exists as the left adjoint of
restriction along composition. The generic presheaf pullback is left Kan extension;
its comma category decomposes by the lifts V -> U, giving the direct-sum formula.
Source: Stacks 03DI, 0F4L
(blueprint: lem-sp-semilinear-compactified-graph-evaluation).
Proof: identify U_proet with T_proet/U by weakly-etale localization, including
constant rings. Transfer localizedSystemAdjunction to every level and assemble
its transitions. The left adjoint is extensionByZeroPresheaf followed by
PresheafOfModules.sheafification; no coefficient extension or flatness is used. -/
theorem restriction_isRightAdjoint {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    (restriction C τ e).IsRightAdjoint := by
  sorry

attribute [instance] restriction_isRightAdjoint

/-- The sheafified sum extension, specified by its localization adjunction.
Source: Stacks 03DI, 0F4L
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
abbrev sumExtension {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :=
  (restriction C τ e).leftAdjoint

/-- The sum-extension adjunction retains its generator insertion unit.
Source: Stacks 03DI, 0F4L
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def sumAdjunction {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    sumExtension C τ e ⊣ restriction C τ e := Adjunction.ofIsRightAdjoint _

/-- The sheafified sum extension is exact on all strict semilinear systems.
Source: Stacks 03DI, 03DJ, 0F4L; blueprint Local pairs
(blueprint: lem-sp-semilinear-compactified-graph-evaluation).
Proof: the slice equivalence identifies each level with localizedSystemExtension.
That functor is additive and exact. Exactness of strict systems is componentwise
by lem-coef-semilinear-derived-sections. Ring transitions need not be flat. -/
theorem sumExtension_exact {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    (sumExtension C τ e).Additive ∧ PreservesFiniteLimits (sumExtension C τ e) ∧
      PreservesFiniteColimits (sumExtension C τ e) := by
  sorry

/-- Additivity of the actual sum extension. Source: Stacks 03DI
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
instance sumExtensionAdditive {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    (sumExtension C τ e).Additive := (sumExtension_exact C τ e).1

/-- Left exactness of the actual sum extension. Source: Stacks 03DJ
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
instance sumExtensionLimits {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    PreservesFiniteLimits (sumExtension C τ e) := (sumExtension_exact C τ e).2.1

/-- Right exactness of the actual sum extension. Source: Stacks 03DI
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
instance sumExtensionColimits {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    PreservesFiniteColimits (sumExtension C τ e) := (sumExtension_exact C τ e).2.2

/-- The projection from a pulled-back test scheme, regarded over the original base.
Source: Stacks 00XZ; blueprint Local pairs
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def testProjection {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] (b : T.ProEt) :
    ((inclusion e).obj (0, (proEtaleBaseChange e).obj b)).2 ⟶ b :=
  MorphismProperty.Over.homMk (pullback.fst b.hom e) (pullback.condition (f := b.hom) (g := e))

/-- The ordinary inverse image along an open is canonically restriction. Its
normalization uses the ordinary inverse-image unit and restriction along the
actual pullback projection, not equality of unrelated chosen section carriers.
Source: Stacks 00XZ, 09AE; blueprint Local pairs
(blueprint: lem-sp-semilinear-compactified-graph-evaluation).
Proof: the site map/pullback adjunction gives restriction left adjoint to push.
Its unit is restriction along the displayed projection. The unit-preserving
unique comparison of left adjoints supplies d. -/
theorem openRestriction_existsUnique {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] :
    ∃! d : SemilinearProperOpen.pull C τ j ≅ restriction C τ j,
      ∀ (M : SemilinearProperOpen.Modules C τ Z) (n : ℕ) (b : Z.ProEt)
        (m : M.val.obj (op (n, b))),
        (((SemilinearProperOpen.ordinaryAdj C τ j).unit.app M ≫
          (SemilinearProperOpen.push C τ j).map (d.hom.app M)).val.app (op (n, b))) m =
        M.val.map (Prod.mkHom (𝟙 n) (testProjection j b)).op m := by
  sorry

/-- The open-extension unit in the literal restriction model.
Source: Stacks 09AE, 0F4L
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def openUnit {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (M : SemilinearProperOpen.Modules C τ U) :
    M ⟶ (restriction C τ j).obj ((SemilinearProperOpen.extension C τ j).obj M) :=
  (SemilinearProperOpen.ordinaryOpenAdj C τ j).unit.app M ≫
    (openRestriction_existsUnique C τ j).choose.hom.app _

/-- A section has the prescribed graph value and is zero on the complementary open.
Every complementary open presentation is allowed, so no choice of complement enters.
Source: Stacks 0F4L; blueprint Local pairs
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def GraphValue {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] (c : Compactification e)
    (n : ℕ) (b : U.ProEt)
    (γ : ((inclusion c.i).obj (n, b)).2 ⟶
      ((SemilinearProperOpen.siteMap c.g).obj ((inclusion e).obj (n, b))).2)
    (M : SemilinearProperOpen.Modules C τ U) (m : M.val.obj (op (n, b)))
    (s : ((SemilinearProperOpen.extension C τ c.i).obj M).val.obj
      (op ((SemilinearProperOpen.siteMap c.g).obj ((inclusion e).obj (n, b))))) : Prop :=
  ((SemilinearProperOpen.extension C τ c.i).obj M).val.map
      (Prod.mkHom (𝟙 n) γ).op s = (openUnit C τ c.i M).val.app (op (n, b)) m ∧
  ∀ (D : c.Z.ProEt)
    (k : D ⟶ ((SemilinearProperOpen.siteMap c.g).obj ((inclusion e).obj (n, b))).2),
    IsOpenImmersion k.left → Set.range k.left = (Set.range γ.left)ᶜ →
    ((SemilinearProperOpen.extension C τ c.i).obj M).val.map
      (Prod.mkHom (𝟙 n) k).op s = 0

/-- Graph normalization includes existence and uniqueness of the zero extension,
and identifies the map on each direct-sum generator (the sum-adjunction unit).
Source: Stacks 0F4L; blueprint Local pairs
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def IsGraphMap {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] (c : Compactification e)
    (G : sumExtension C τ e ⟶
      SemilinearProperOpen.extension C τ c.i ⋙ SemilinearProperOpen.push C τ c.g) : Prop :=
  ∀ (n : ℕ) (b : U.ProEt),
    ∃ γ : ((inclusion c.i).obj (n, b)).2 ⟶
        ((SemilinearProperOpen.siteMap c.g).obj ((inclusion e).obj (n, b))).2,
      γ.left ≫ pullback.fst (b.hom ≫ e) c.g = 𝟙 b.left ∧
      γ.left ≫ pullback.snd (b.hom ≫ e) c.g = b.hom ≫ c.i ∧
      IsOpenImmersion γ.left ∧ IsClosedImmersion γ.left ∧
      ∀ (M : SemilinearProperOpen.Modules C τ U) (m : M.val.obj (op (n, b))),
        (∃! s, GraphValue C τ e c n b γ M m s) ∧
        GraphValue C τ e c n b γ M m
          ((G.app M).val.app (op ((inclusion e).obj (n, b)))
            (((sumAdjunction C τ e).unit.app M).val.app (op (n, b)) m))

/-- Ordinary localization inclusion, used for the fixed-coefficient construction.
Source: Stacks 0F4L (blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
abbrev levelInclusion {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :=
  MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ (inferInstance : WeaklyEtale e)

/-- Constant rings commute with localization, with the sheafification-unit normalization.
Source: Stacks 00XZ, 0F4L
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def levelRestrictionRing (A : CommRingCat.{u + 1})
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :=
  ((levelInclusion e).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{u + 1} (ProEt.topology U) (ProEt.topology T)).hom.app
      ((Functor.const T.ProEtᵒᵖ).obj A)

/-- Fixed-coefficient restriction along composition.
Source: Stacks 0F4L (blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def levelRestriction (A : CommRingCat.{u + 1})
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    StrictTower.Modules A T ⥤ StrictTower.Modules A U :=
  SheafOfModules.pushforward (F := levelInclusion e)
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (levelRestrictionRing A e))

/-- The single-coefficient sum extension exists and is exact.
Source: Stacks 03DI, 03DJ, 0F4L
(blueprint: lem-sp-semilinear-compactified-graph-evaluation).
Proof: weakly-etale localization identifies restriction with overFunctor and
its left adjoint with localizedSystemExtension, the sheafified direct sum. -/
theorem levelRestriction_isRightAdjoint (A : CommRingCat.{u + 1})
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    (levelRestriction A e).IsRightAdjoint := by
  sorry

attribute [instance] levelRestriction_isRightAdjoint

/-- Single-coefficient sheafified direct sum, with its actual adjunction unit.
Source: Stacks 03DI, 0F4L
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
abbrev levelSum (A : CommRingCat.{u + 1}) {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :=
  (levelRestriction A e).leftAdjoint

/-- The single-coefficient sum adjunction, whose unit inserts a lift summand.
Source: Stacks 03DI, 0F4L
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def levelSumAdjunction (A : CommRingCat.{u + 1})
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    levelSum A e ⊣ levelRestriction A e := Adjunction.ofIsRightAdjoint _

/-- Exactness of the fixed-coefficient sum extension.
Source: Stacks 03DI, 03DJ
(blueprint: lem-sp-semilinear-compactified-graph-evaluation).
Proof: transfer localizedSystemExact through the constant-ring slice equivalence. -/
theorem levelSum_exact (A : CommRingCat.{u + 1})
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    (levelSum A e).Additive ∧ PreservesFiniteLimits (levelSum A e) ∧
      PreservesFiniteColimits (levelSum A e) := by
  sorry

/-- Additivity at one coefficient level. Source: Stacks 03DI
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
instance levelSumAdditive (A : CommRingCat.{u + 1})
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    (levelSum A e).Additive := (levelSum_exact A e).1

/-- Left exactness at one coefficient level. Source: Stacks 03DJ
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
instance levelSumLimits (A : CommRingCat.{u + 1})
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    PreservesFiniteLimits (levelSum A e) := (levelSum_exact A e).2.1

/-- Right exactness at one coefficient level. Source: Stacks 03DI
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
instance levelSumColimits (A : CommRingCat.{u + 1})
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    PreservesFiniteColimits (levelSum A e) := (levelSum_exact A e).2.2

/-- Ordinary evaluation on the recorded coefficient categories.
Source: Zheng 4.1 (blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
abbrev ev (X : Scheme.{u}) (n : ℕ) :=
  WeilConjectures.SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology X)
    (SemilinearProperOpen.coefficients C X) (SemilinearProperOpen.transition C τ X) n

/-- Additivity of exact termwise evaluation. Source: Zheng 4.1
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
instance evAdditive (X : Scheme.{u}) (n : ℕ) : (ev C τ X n).Additive :=
  evaluationAdditive.{u + 1, u, u + 1} (ProEt.topology X)
    (SemilinearProperOpen.coefficients C X) (SemilinearProperOpen.transition C τ X) n

/-- Left exactness of evaluation. Source: Zheng 4.1
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
instance evLimits (X : Scheme.{u}) (n : ℕ) : PreservesFiniteLimits (ev C τ X n) :=
  evaluationLimits.{u + 1, u, u + 1} (ProEt.topology X)
    (SemilinearProperOpen.coefficients C X) (SemilinearProperOpen.transition C τ X) n

/-- Right exactness of evaluation. Source: Zheng 4.1
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
instance evColimits (X : Scheme.{u}) (n : ℕ) : PreservesFiniteColimits (ev C τ X n) :=
  evaluationColimits.{u + 1, u, u + 1} (ProEt.topology X)
    (SemilinearProperOpen.coefficients C X) (SemilinearProperOpen.transition C τ X) n

/-- Sum extension commutes with evaluation, normalized on every lift generator.
Source: Stacks 03DI, 0F4L; Zheng 4.10
(blueprint: lem-sp-semilinear-compactified-graph-evaluation).
Proof: both sides are the same sheafified direct sum. Their units insert a section
in the same lift summand. These sections generate after sheafification, proving
existence and uniqueness of the identity comparison. -/
theorem sumEvaluation_existsUnique {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] (n : ℕ) :
    ∃! d : sumExtension C τ e ⋙ ev C τ T n ≅ ev C τ U n ⋙ levelSum (C n) e,
      ∀ (M : SemilinearProperOpen.Modules C τ U) (b : U.ProEt)
        (m : M.val.obj (op (n, b))),
        (d.hom.app M).val.app (op ((levelInclusion e).obj b))
          (((sumAdjunction C τ e).unit.app M).val.app (op (n, b)) m) =
        ((levelSumAdjunction (C n) e).unit.app ((ev C τ U n).obj M)).val.app (op b) m := by
  sorry

/-- The normalized sum-extension evaluation isomorphism.
Source: Stacks 0F4L; Zheng 4.10
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def sumEvaluation {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] (n : ℕ) :=
  (sumEvaluation_existsUnique C τ e n).choose

/-- Open restriction in the literal section model, normalized by its actual
inverse-image unit and pullback projection.
Source: Stacks 00XZ, 09AE
(blueprint: lem-sp-semilinear-compactified-graph-evaluation).
Proof: the map/pullback adjunction gives restriction left adjoint to direct image;
compare this adjunction with the recorded module inverse-image adjunction. -/
theorem levelOpenRestriction_existsUnique (A : CommRingCat.{u + 1})
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :
    ∃! d : StrictTower.modulePullback A j ≅ levelRestriction A j,
      ∀ (M : StrictTower.Modules A Z) (b : Z.ProEt) (m : M.val.obj (op b)),
        (((proEtaleRingModuleAdjunction j (StrictTower.coefficients A Z)
          (StrictTower.coefficients A U) (StrictTower.constantRingIso A j)).unit.app M ≫
          (StrictTower.moduleDirectImage A j).map (d.hom.app M)).val.app (op b)) m =
        M.val.map (testProjection j b).op m := by
  sorry

/-- The open unit at one coefficient level in the literal restriction model.
Source: Stacks 09AE, 0F4L
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def levelOpenUnit (A : CommRingCat.{u + 1})
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] (M : StrictTower.Modules A U) :
    M ⟶ (levelRestriction A j).obj ((StrictTower.moduleJ A j).obj M) :=
  (StrictTower.moduleJAdj A j).unit.app M ≫
    (levelOpenRestriction_existsUnique A j).choose.hom.app _

/-- Open extension commutes with evaluation, with its original units.
Source: Stacks 09AE; Zheng 4.10
(blueprint: lem-sp-semilinear-compactified-graph-evaluation).
Proof: both units insert the same section on the open, and extension is zero off
that open. The sheafified presheaf generators uniquely determine the comparison. -/
theorem openEvaluation_existsUnique {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) :
    ∃! d : SemilinearProperOpen.extension C τ j ⋙ ev C τ Z n ≅
        ev C τ U n ⋙ StrictTower.moduleJ (C n) j,
      ∀ (M : SemilinearProperOpen.Modules C τ U) (b : U.ProEt)
        (m : M.val.obj (op (n, b))),
        (d.hom.app M).val.app (op ((levelInclusion j).obj b))
          ((openUnit C τ j M).val.app (op (n, b)) m) =
        (levelOpenUnit (C n) j ((ev C τ U n).obj M)).val.app (op b) m := by
  sorry

/-- Open-extension evaluation with its unit normalization.
Source: Stacks 09AE; Zheng 4.10
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def openEvaluation {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] (n : ℕ) :=
  (openEvaluation_existsUnique C τ j n).choose

/-- Direct image evaluates by the identity on every section.
Source: Zheng 4.10; Stacks 03D7
(blueprint: lem-sp-semilinear-compactified-graph-evaluation).
Proof: both sides have sections M_n(V times_T Z), with the same constant-ring
action and restriction maps. Identity on these sections gives the unique map. -/
theorem pushEvaluation_existsUnique {Z T : Scheme.{u}} (p : Z ⟶ T) (n : ℕ) :
    ∃! d : SemilinearProperOpen.push C τ p ⋙ ev C τ T n ≅
        ev C τ Z n ⋙ StrictTower.moduleDirectImage (C n) p,
      ∀ (M : SemilinearProperOpen.Modules C τ Z) (b : T.ProEt),
        HEq (fun x ↦ (d.hom.app M).val.app (op b) x)
          (fun x : M.val.obj (op (n, (proEtaleBaseChange p).obj b)) ↦ x) := by
  sorry

/-- Section-normalized ordinary direct-image evaluation.
Source: Zheng 4.10 (blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def pushEvaluation {Z T : Scheme.{u}} (p : Z ⟶ T) (n : ℕ) :=
  (pushEvaluation_existsUnique C τ p n).choose

/-- The ordinary push/evaluation comparison applied termwise, with nested
complex functors retaining their own zero-morphism instances.
Source: Zheng 4.10 (blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def pushEvaluationComplex {Z T : Scheme.{u}} (p : Z ⟶ T) (n : ℕ)
    (K : CochainComplex (SemilinearProperOpen.Modules C τ Z) ℤ) :
    ((ev C τ T n).mapHomologicalComplex (.up ℤ)).obj
        (((SemilinearProperOpen.push C τ p).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      ((StrictTower.moduleDirectImage (C n) p).mapHomologicalComplex (.up ℤ)).obj
        (((ev C τ Z n).mapHomologicalComplex (.up ℤ)).obj K) where
  f i := (pushEvaluation C τ p n).hom.app (K.X i)
  comm' i j _ := ((pushEvaluation C τ p n).hom.naturality (K.d i j)).symm

/-- The single-coefficient value on the graph and its complementary open.
Source: Stacks 0F4L (blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def LevelGraphValue (A : CommRingCat.{u + 1})
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] (c : Compactification e) (b : U.ProEt)
    (γ : (levelInclusion c.i).obj b ⟶
      (proEtaleBaseChange c.g).obj ((levelInclusion e).obj b))
    (M : StrictTower.Modules A U) (m : M.val.obj (op b))
    (s : ((StrictTower.moduleJ A c.i).obj M).val.obj
      (op ((proEtaleBaseChange c.g).obj ((levelInclusion e).obj b)))) : Prop :=
  ((StrictTower.moduleJ A c.i).obj M).val.map γ.op s =
      (levelOpenUnit A c.i M).val.app (op b) m ∧
  ∀ (D : c.Z.ProEt)
    (k : D ⟶ (proEtaleBaseChange c.g).obj ((levelInclusion e).obj b)),
    IsOpenImmersion k.left → Set.range k.left = (Set.range γ.left)ᶜ →
    ((StrictTower.moduleJ A c.i).obj M).val.map k.op s = 0

/-- The single-coefficient graph specification, including unique extension by zero.
Source: Stacks 0F4L, graph sections
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def IsLevelGraphMap (A : CommRingCat.{u + 1})
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] (c : Compactification e)
    (G : levelSum A e ⟶ StrictTower.moduleJ A c.i ⋙ StrictTower.moduleDirectImage A c.g) :
    Prop :=
  ∀ b : U.ProEt,
    ∃ γ : (levelInclusion c.i).obj b ⟶
        (proEtaleBaseChange c.g).obj ((levelInclusion e).obj b),
      γ.left ≫ pullback.fst (b.hom ≫ e) c.g = 𝟙 b.left ∧
      γ.left ≫ pullback.snd (b.hom ≫ e) c.g = b.hom ≫ c.i ∧
      IsOpenImmersion γ.left ∧ IsClosedImmersion γ.left ∧
      ∀ (M : StrictTower.Modules A U) (m : M.val.obj (op b)),
        (∃! s, LevelGraphValue A e c b γ M m s) ∧
        LevelGraphValue A e c b γ M m
          ((G.app M).val.app (op ((levelInclusion e).obj b))
            (((levelSumAdjunction A e).unit.app M).val.app (op b) m))

end AlgebraicGeometry.ProEtale.SemilinearGraph

