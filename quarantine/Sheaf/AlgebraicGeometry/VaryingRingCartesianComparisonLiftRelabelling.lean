/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheafAdjoint

/-! # Lift labels for cartesian open comparison on varying coefficients

Source: Stacks Project, Tag 03DI; Tag 0F7B, cartesian open case
(blueprint: lem-sp-varying-ring-cartesian-comparison-lift-relabelling).

The direct sums below are the existing extension-by-zero presheaf, transported
along the actual equivalence of the localized and small pro-etale sites.
Inverse-image generators always retain their source-site representative.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

/-- Forget the coefficient action after ordinary evaluation.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-cartesian-comparison-lift-relabelling). -/
abbrev levelAb (X : Scheme.{u}) (n : ℕ) :
    Modules R φ X ⥤ Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  eval R φ X n ⋙ SheafOfModules.toSheaf _

/-- The actual horizontal restriction, forgetting its semilinear scalar action.
Source: Zheng 4.1 (blueprint: lem-sp-varying-ring-cartesian-comparison-lift-relabelling). -/
def sectionTransition {X : Scheme.{u}} (M : Modules R φ X) (n : ℕ) (U : X.ProEt) :
    ((levelAb R φ X (n + 1)).obj M).obj.obj (op U) →+
      ((levelAb R φ X n).obj M).obj.obj (op U) :=
  (M.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U)).op).hom.toAddMonoidHom

/-- Direct-sum extension on the actual slice, followed by abelian sheafification.
The equality `siteExtensionByZeroPresheaf_modules` identifies this with the
underlying presheaf of the recorded module construction.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-cartesian-comparison-lift-relabelling). -/
def openSum {S T : Scheme.{u}} (i : S ⟶ T) [IsOpenImmersion i] :
    Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  sheafToPresheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
      (Scheme.ProEt.sliceTo T (Scheme.ProEt.mk i)).op ⋙
    siteExtensionByZeroPresheaf (Scheme.ProEt.mk i) ⋙
    presheafToSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}

/-- The image of the summand labelled by a lift through an open immersion.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-cartesian-comparison-lift-relabelling). -/
def openSumGenerator {S T : Scheme.{u}} (i : S ⟶ T) [IsOpenImmersion i]
    (F : Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
    (H : T.ProEt) (a : H ⟶ Scheme.ProEt.mk i)
    (x : F.obj.obj (op ((Scheme.ProEt.sliceTo T (Scheme.ProEt.mk i)).obj (Over.mk a)))) :
    ((openSum i).obj F).obj.obj (op H) := by
  classical
  exact (toSheafify (Scheme.ProEt.topology T)
      ((siteExtensionByZeroPresheaf (Scheme.ProEt.mk i)).obj
        ((Scheme.ProEt.sliceTo T (Scheme.ProEt.mk i)).op ⋙ F.obj))).app (op H)
      (DirectSum.of (fun c : H ⟶ Scheme.ProEt.mk i =>
        F.obj.obj (op ((Scheme.ProEt.sliceTo T (Scheme.ProEt.mk i)).obj (Over.mk c)))) a x)

/-- A local inverse-image representative is the adjunction unit followed by restriction.
Source: Stacks 00YV (blueprint: lem-sp-varying-ring-cartesian-comparison-lift-relabelling). -/
def abelianPullRepresentative {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
    (U : Y.ProEt) (H : X.ProEt) (d : H ⟶ (Scheme.proEtaleBaseChange f).obj U)
    (x : F.obj.obj (op U)) :
    ((Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj F).obj.obj (op H) :=
  ((Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj F).obj.map d.op
    (((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app F).hom.app (op U) x)

/-- The type of underlying-abelian inverse-image comparisons, for all ordinary systems.
Source: Stacks 00YV (blueprint: lem-sp-varying-ring-cartesian-comparison-lift-relabelling). -/
abbrev PullAbPresentation := ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ),
  pull R φ f ⋙ levelAb R φ X n ≅
    levelAb R φ Y n ⋙ Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}

/-- The type of underlying-abelian direct-sum-sheafification comparisons.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-cartesian-comparison-lift-relabelling). -/
abbrev OpenAbPresentation := ∀ {S T : Scheme.{u}} (i : S ⟶ T) [IsOpenImmersion i] (n : ℕ),
  extension R φ i ⋙ levelAb R φ T n ≅ levelAb R φ S n ⋙ openSum i

/-- Interpret the actual direct-sum injection in an ordinary system extension.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-cartesian-comparison-lift-relabelling). -/
def openSystemGenerator (ε : OpenAbPresentation R φ)
    {S T : Scheme.{u}} (i : S ⟶ T) [IsOpenImmersion i]
    (M : Modules R φ S) (n : ℕ) (H : T.ProEt) (a : H ⟶ Scheme.ProEt.mk i)
    (x : ((levelAb R φ S n).obj M).obj.obj
      (op ((Scheme.ProEt.sliceTo T (Scheme.ProEt.mk i)).obj (Over.mk a)))) :
    ((levelAb R φ T n).obj ((extension R φ i).obj M)).obj.obj (op H) :=
  ((ε i n).inv.app M).hom.app (op H)
    (openSumGenerator i ((levelAb R φ S n).obj M) H a x)

/-- Interpret a source-site inverse-image representative in the ordinary module pullback.
Source: Stacks 00YV (blueprint: lem-sp-varying-ring-cartesian-comparison-lift-relabelling). -/
def pullSystemGenerator (α : PullAbPresentation R φ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules R φ Y) (n : ℕ)
    (U : Y.ProEt) (H : X.ProEt) (d : H ⟶ (Scheme.proEtaleBaseChange f).obj U)
    (x : ((levelAb R φ Y n).obj M).obj.obj (op U)) :
    ((levelAb R φ X n).obj ((pull R φ f).obj M)).obj.obj (op H) :=
  ((α f n).inv.app M).hom.app (op H)
    (abelianPullRepresentative f ((levelAb R φ Y n).obj M) U H d x)

/-- Compose a pro-etale object with an open immersion, using the existing site functor.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-cartesian-comparison-lift-relabelling). -/
abbrev openSiteImage {S T : Scheme.{u}} (i : S ⟶ T) [IsOpenImmersion i] (U : S.ProEt) :
    T.ProEt :=
  (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale i)).obj U

/-- The canonical label of an object already over the open.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-cartesian-comparison-lift-relabelling). -/
def openSiteLift {S T : Scheme.{u}} (i : S ⟶ T) [IsOpenImmersion i] (U : S.ProEt) :
    openSiteImage i U ⟶ Scheme.ProEt.mk i :=
  MorphismProperty.Over.homMk U.hom rfl

/-- The source generator: extend a source-site section and then pull it back.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-cartesian-comparison-lift-relabelling). -/
def cartesianSourceGenerator (α : PullAbPresentation R φ) (ε : OpenAbPresentation R φ)
    {W S T : Scheme.{u}} (i : S ⟶ T) (p : W ⟶ T) [IsOpenImmersion i]
    (N : Modules R φ S) (n : ℕ) (U : S.ProEt) (H : W.ProEt)
    (d : H ⟶ (Scheme.proEtaleBaseChange p).obj (openSiteImage i U))
    (x : ((levelAb R φ S n).obj N).obj.obj (op U)) :
    ((levelAb R φ W n).obj ((pull R φ p).obj ((extension R φ i).obj N))).obj.obj (op H) :=
  pullSystemGenerator R φ α p ((extension R φ i).obj N) n (openSiteImage i U) H d
    (openSystemGenerator R φ ε i N n (openSiteImage i U) (openSiteLift i U) x)

/-- The relabelled generator: pull back the same section and then extend it at its lift.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-cartesian-comparison-lift-relabelling). -/
def cartesianTargetGenerator (α : PullAbPresentation R φ) (ε : OpenAbPresentation R φ)
    {V W S : Scheme.{u}} (q : V ⟶ S) (b : V ⟶ W) [IsOpenImmersion b]
    (N : Modules R φ S) (n : ℕ) (U : S.ProEt) (H : W.ProEt)
    (a : H ⟶ Scheme.ProEt.mk b)
    (v : (Scheme.ProEt.sliceTo W (Scheme.ProEt.mk b)).obj (Over.mk a) ⟶
      (Scheme.proEtaleBaseChange q).obj U)
    (x : ((levelAb R φ S n).obj N).obj.obj (op U)) :
    ((levelAb R φ W n).obj ((extension R φ b).obj ((pull R φ q).obj N))).obj.obj (op H) :=
  openSystemGenerator R φ ε b ((pull R φ q).obj N) n H a
    (pullSystemGenerator R φ α q N n U
      ((Scheme.ProEt.sliceTo W (Scheme.ProEt.mk b)).obj (Over.mk a)) v x)

/-- The two generators describe the same inverse-image representative: their maps to the
source object agree. The map to the base is already fixed by the site morphisms.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-cartesian-comparison-lift-relabelling). -/
def SameOpenRepresentative {V W S T : Scheme.{u}}
    (q : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion b]
    (U : S.ProEt) (H : W.ProEt) (a : H ⟶ Scheme.ProEt.mk b)
    (v : (Scheme.ProEt.sliceTo W (Scheme.ProEt.mk b)).obj (Over.mk a) ⟶
      (Scheme.proEtaleBaseChange q).obj U)
    (d : H ⟶ (Scheme.proEtaleBaseChange p).obj (openSiteImage i U)) : Prop :=
  d.left ≫ pullback.fst (openSiteImage i U).hom p = v.left ≫ pullback.fst U.hom q

/-- Underlying abelian operation presentations, normalized by the actual units, together
with their transition and cartesian generator formulas. All rings remain arbitrary.
The slice-based generators are the existing module direct sums after forgetting scalars.
Source: Stacks 03DI, 00YV and 0F7B
(blueprint: lem-sp-varying-ring-cartesian-comparison-lift-relabelling). -/
structure CartesianComparisonLiftRelabellingData where
  /-- Inverse image at every level, for every system, after forgetting coefficients. -/
  pullAb : PullAbPresentation R φ
  /-- Extension at every level is the sheafification of the recorded direct sum. -/
  openAb : OpenAbPresentation R φ
  /-- The inverse-image identification carries the module unit to the abelian unit. -/
  pull_unit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) (M : Modules R φ Y)
    (U : Y.ProEt) (x : ((levelAb R φ Y n).obj M).obj.obj (op U)),
    ((pullAb f n).hom.app M).hom.app (op ((Scheme.proEtaleBaseChange f).obj U))
      (((moduleAdj R φ f).unit.app M).val.app (op (n, U)) x) =
    (((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
      ((levelAb R φ Y n).obj M)).hom.app (op U)) x
  /-- The open unit inserts a section into the identity lift summand. -/
  open_unit : ∀ {S T : Scheme.{u}} (i : S ⟶ T) [IsOpenImmersion i]
    (n : ℕ) (M : Modules R φ S) (U : S.ProEt)
    (x : ((levelAb R φ S n).obj M).obj.obj (op U)),
    ((openAb i n).hom.app M).hom.app (op (openSiteImage i U))
      (((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} i inferInstance).hom.app
        ((levelAb R φ T n).obj ((extension R φ i).obj M))).hom.app (op U)
        (((pullAb i n).hom.app ((extension R φ i).obj M)).hom.app (op U)
          (((moduleJAdj R φ i).unit.app M).val.app (op (n, U)) x))) =
    openSumGenerator i ((levelAb R φ S n).obj M) (openSiteImage i U) (openSiteLift i U) x
  /-- Pullback applies the original semilinear transition to the section coordinate. -/
  pull_transition : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules R φ Y) (n : ℕ)
    (U : Y.ProEt) (H : X.ProEt) (d : H ⟶ (Scheme.proEtaleBaseChange f).obj U)
    (x : ((levelAb R φ Y (n + 1)).obj M).obj.obj (op U)),
    sectionTransition R φ ((pull R φ f).obj M) n H
      (pullSystemGenerator R φ pullAb f M (n + 1) U H d x) =
    pullSystemGenerator R φ pullAb f M n U H d (sectionTransition R φ M n U x)
  /-- Extension applies the transition in the summand, preserving its lift label. -/
  open_transition : ∀ {S T : Scheme.{u}} (i : S ⟶ T) [IsOpenImmersion i]
    (M : Modules R φ S) (n : ℕ) (H : T.ProEt) (a : H ⟶ Scheme.ProEt.mk i)
    (x : ((levelAb R φ S (n + 1)).obj M).obj.obj
      (op ((Scheme.ProEt.sliceTo T (Scheme.ProEt.mk i)).obj (Over.mk a)))),
    sectionTransition R φ ((extension R φ i).obj M) n H
      (openSystemGenerator R φ openAb i M (n + 1) H a x) =
    openSystemGenerator R φ openAb i M n H a
      (sectionTransition R φ M n
        ((Scheme.ProEt.sliceTo T (Scheme.ProEt.mk i)).obj (Over.mk a)) x)
  /-- The specified beta sends the source lift c to its fibre-product lift (h,c). -/
  beta_generator : ∀ {V W S T : Scheme.{u}}
    (q : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion b] [QuasiCompact i]
    (h : q ≫ i = b ≫ p) (hsq : IsPullback q b i p)
    (N : Modules R φ S) (n : ℕ) (U : S.ProEt) (H : W.ProEt)
    (a : H ⟶ Scheme.ProEt.mk b)
    (v : (Scheme.ProEt.sliceTo W (Scheme.ProEt.mk b)).obj (Over.mk a) ⟶
      (Scheme.proEtaleBaseChange q).obj U)
    (d : H ⟶ (Scheme.proEtaleBaseChange p).obj (openSiteImage i U)),
    SameOpenRepresentative q b i p U H a v d →
    ∀ x : ((levelAb R φ S n).obj N).obj.obj (op U),
      ((levelAb R φ W n).map ((moduleBeta R φ q b i p h hsq).hom.app N)).hom.app (op H)
        (cartesianSourceGenerator R φ pullAb openAb i p N n U H d x) =
      cartesianTargetGenerator R φ pullAb openAb q b N n U H a v x
  /-- Its inverse sends a lift a to q composed with a. -/
  beta_inverse_generator : ∀ {V W S T : Scheme.{u}}
    (q : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion b] [QuasiCompact i]
    (h : q ≫ i = b ≫ p) (hsq : IsPullback q b i p)
    (N : Modules R φ S) (n : ℕ) (U : S.ProEt) (H : W.ProEt)
    (a : H ⟶ Scheme.ProEt.mk b)
    (v : (Scheme.ProEt.sliceTo W (Scheme.ProEt.mk b)).obj (Over.mk a) ⟶
      (Scheme.proEtaleBaseChange q).obj U)
    (d : H ⟶ (Scheme.proEtaleBaseChange p).obj (openSiteImage i U)),
    SameOpenRepresentative q b i p U H a v d →
    ∀ x : ((levelAb R φ S n).obj N).obj.obj (op U),
      ((levelAb R φ W n).map ((moduleBeta R φ q b i p h hsq).inv.app N)).hom.app (op H)
        (cartesianTargetGenerator R φ pullAb openAb q b N n U H a v x) =
      cartesianSourceGenerator R φ pullAb openAb i p N n U H d x
  /-- The isomorphism is an actual ordinary-system map, including its transitions. -/
  beta_transition : ∀ {V W S T : Scheme.{u}}
    (q : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion b] [QuasiCompact i]
    (h : q ≫ i = b ≫ p) (hsq : IsPullback q b i p)
    (N : Modules R φ S) (n : ℕ) (H : W.ProEt)
    (x : ((levelAb R φ W (n + 1)).obj
      ((pull R φ p).obj ((extension R φ i).obj N))).obj.obj (op H)),
    sectionTransition R φ ((extension R φ b).obj ((pull R φ q).obj N)) n H
      (((levelAb R φ W (n + 1)).map
        ((moduleBeta R φ q b i p h hsq).hom.app N)).hom.app (op H) x) =
    ((levelAb R φ W n).map ((moduleBeta R φ q b i p h hsq).hom.app N)).hom.app (op H)
      (sectionTransition R φ ((pull R φ p).obj ((extension R φ i).obj N)) n H x)

/-- The cartesian open comparison on varying-ring systems relabels lifts.
Source: Stacks Project, Tag 03DI, explicit direct-sum adjunction; Tag 00YV,
fixed-ring inverse image; Tag 0F7B, cartesian open context
(blueprint: lem-sp-varying-ring-cartesian-comparison-lift-relabelling).

Proof (the seven DAG steps):
1. Apply lem-pe-constant-left-module-inverse-image at each arbitrary R_n.
   Its underlying abelian comparison and unit identify ordinary system pullback,
   using lem-coef-semilinear-derived-sections and the defining left adjunction.
2. Use lem-pur-site-restriction-module-adjunction-exact and the recorded
   def-weil-extension-by-zero-presheaf. Its underlying abelian presheaf is exactly
   siteExtensionByZeroPresheaf_modules. Sheafify by
   def-weil-presheaf-modules-sheafification. The explicit adjunction in
   lem-weil-pbc-site-extension-by-zero-presheaf-adjoint gives x mapped to [id,x].
3. Apply the semilinear transition on each summand: [c,x] goes to [c,t_n(x)].
   Inverse image applies to that same map; no source section over H is presumed.
4. The fibre-product universal property gives c mapped to (h,c), inverse a mapped
   to q composed with a, compatibly with restriction and with unchanged sections.
5. Expand the actual moduleBetaInv from def-sp-varying-ring-proper-open-arrows.
   Its transpose is the open unit followed by the normalized pullback compositor.
   Step 2 evaluates its generator as [a,x] mapped to [qa,x].
6. Invert that specified isomorphism to obtain the forward formula. Additivity,
   restriction compatibility and the sheafification universal property extend
   the equations from representatives to sections and prove naturality in N.
7. Both orders with a transition send [a,x] to [qa,t_n(x)]; sheafification extends
   their equality, and inversion gives beta's transition equation. No coefficient
   flatness, finiteness or noetherian condition occurs in these calculations.
-/
theorem cartesianComparison_liftRelabelling :
    Nonempty (CartesianComparisonLiftRelabellingData R φ) := by
  sorry

end AlgebraicGeometry.ProEtale.VaryingRing
