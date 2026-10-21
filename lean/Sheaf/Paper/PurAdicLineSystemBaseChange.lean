/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.CategoryTheory.LocalizationInverseImageCoherence
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Sheaf.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.Paper.PurInverseImageCompatibleFreeTower
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Base change of adic line systems

Source: main-20261015 blueprint, sec-smooth-purity/sk-prop-an,
`sk-prop-sfb-cartesian-coefficients-twists.proof.md`, Integral twist and Rational and
algebraic closure; Stacks Project, Sites, Tag 03CF
(blueprint: lem-pur-adic-line-system-base-change).

The structures below package the diagrams and the universal properties of their chosen
limits, localizations and filtered colimits. They do not assume any base-change comparison.
Index `n : ℕ` denotes the positive level `n + 1`. Site object, morphism and sheaf universes
are independent. Algebraic inverse-image lifts use the existing graph-normalized interface;
their underlying ring isomorphisms are the given coefficient comparisons.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe w uC vC uD vD uI vI

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The positive cofinal subsequence `n + 1 ↦ e * (n + 1)`.
Source: Integral twist paragraph
(blueprint: lem-pur-adic-line-system-base-change). -/
def purAdicStride (e : ℕ) : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (OrderHom.toFunctor
    (⟨fun n : ℕ ↦ e * (n + 1) - 1,
      fun _ _ h ↦ Nat.sub_le_sub_right (Nat.mul_le_mul_left e (Nat.add_le_add_right h 1)) 1⟩ :
      ℕ →o ℕ)).op

/-- A diagram of the stated ring/module pairs, using Mathlib's module sheaves and
abelian-sheaf morphisms. The isomorphisms merely identify their two presentations.
Source: Integral twist and Rational and algebraic closure paragraphs
(blueprint: lem-pur-adic-line-system-base-change). -/
structure PurAdicPairDiagram {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) (I : Type uI) [Category.{vI} I] where
  R : I ⥤ Sheaf J CommRingCat.{w}
  P : I ⥤ Sheaf J AddCommGrpCat.{w}
  M : ∀ i : I, ringedSiteModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj (R.obj i))
  identify : ∀ i : I, (SheafOfModules.toSheaf _).obj (M i) ≅ P.obj i
  semilinear : ∀ {i j : I} (f : i ⟶ j) (V : Cᵒᵖ)
    (r : (R.obj i).obj.obj V) (x : (M i).val.obj V),
    (P.map f).hom.app V ((identify i).hom.hom.app V (r • x)) =
      (identify j).hom.hom.app V
        ((R.map f).hom.app V r •
          @id ((M j).val.obj V)
            ((identify j).inv.hom.app V ((P.map f).hom.app V ((identify i).hom.hom.app V x))))

namespace PurAdicPairDiagram

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
variable {I : Type uI} [Category.{vI} I] (A : PurAdicPairDiagram.{w} J I)

/-- The existing underlying set diagram of the rings.
Source: Sites, Tag 00YV (blueprint: lem-pur-adic-line-system-base-change). -/
abbrev rings := A.R ⋙ sheafCompose J (forget CommRingCat.{w})

/-- The existing underlying set diagram of the modules.
Source: Sites, Tag 00YV (blueprint: lem-pur-adic-line-system-base-change). -/
abbrev modules := A.P ⋙ sheafCompose J (forget AddCommGrpCat.{w})

/-- The actual action, expressed in the abelian diagram's presentation.
Source: the common-upper-bound scalar formula
(blueprint: lem-pur-adic-line-system-base-change). -/
def act (i : I) (V : Cᵒᵖ) (r : (A.R.obj i).obj.obj V)
    (x : (A.P.obj i).obj.obj V) : (A.P.obj i).obj.obj V :=
  (A.identify i).hom.hom.app V
    (r • @id ((A.M i).val.obj V) ((A.identify i).inv.hom.app V x))

end PurAdicPairDiagram

/-- The underlying module isomorphism of a semilinear inverse-image comparison.
All algebraic operations are fixed by `AlgebraicInverseImage`, rather than by an
unconstrained isomorphism of underlying sheaves.
Source: Sites, Tag 00YV, and Modules on Sites, Tag 03D2
(blueprint: lem-pur-adic-line-system-base-change). -/
def purAdicModuleIso
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {I : Type uI} [Category.{vI} I]
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (A : PurAdicPairDiagram.{w} J I) (B : PurAdicPairDiagram.{w} K I) (i : I)
    (a : SheafOfModules.AlgebraicInverseImage L (A.R.obj i) (B.R.obj i))
    (c : a.modules.obj (A.M i) ≅ B.M i) :
    L.obj (A.modules.obj i) ≅ B.modules.obj i :=
  L.mapIso ((sheafCompose J (forget AddCommGrpCat.{w})).mapIso (A.identify i).symm) ≪≫
    (a.moduleUnderlying.app (A.M i)).symm ≪≫
    (sheafCompose K (forget AddCommGrpCat.{w})).mapIso
      ((SheafOfModules.toSheaf _).mapIso c ≪≫ B.identify i)

/-- The given ring and semilinear module isomorphisms, with their specified diagram squares.
Source: Integral twist paragraph
(blueprint: lem-pur-adic-line-system-base-change). -/
structure PurAdicPairComparison
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {I : Type uI} [Category.{vI} I]
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (A : PurAdicPairDiagram.{w} J I) (B : PurAdicPairDiagram.{w} K I) where
  a : ∀ i : I, SheafOfModules.AlgebraicInverseImage L (A.R.obj i) (B.R.obj i)
  c : ∀ i : I, (a i).modules.obj (A.M i) ≅ B.M i
  ring_natural : ∀ {i j : I} (f : i ⟶ j),
    L.map (A.rings.map f) ≫ (a j).ringUnderlying.hom =
      (a i).ringUnderlying.hom ≫ B.rings.map f
  module_natural : ∀ {i j : I} (f : i ⟶ j),
    L.map (A.modules.map f) ≫ (purAdicModuleIso L A B j (a j) (c j)).hom =
      (purAdicModuleIso L A B i (a i) (c i)).hom ≫ B.modules.map f

/-- The chosen full and subsequence limits and their scalar projections. All cone
conditions and all directed-diagram squares are retained, including varying strides.
Source: Integral twist paragraph; Sites, Tag 00W2
(blueprint: lem-pur-adic-line-system-base-change). -/
structure PurAdicLineLimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] (J : GrothendieckTopology C)
    (I : Type w) [PartialOrder I] (e : I → ℕ) where
  full : I → ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}
  levels : PurAdicPairDiagram.{w} J (I × ℕᵒᵖ)
  subsequence : ∀ i : I,
    Prod.sectR i ℕᵒᵖ ⋙ levels.R ≅ purAdicStride (e i) ⋙ full i
  integral : PurAdicPairDiagram.{w} J I
  rπ : ∀ i : I, (Functor.const ℕᵒᵖ).obj (integral.R.obj i) ⟶ full i
  rlimit : ∀ i : I, IsLimit (Cone.mk (integral.R.obj i) (rπ i))
  pπ : ∀ i : I,
    (Functor.const ℕᵒᵖ).obj (integral.P.obj i) ⟶ Prod.sectR i ℕᵒᵖ ⋙ levels.P
  plimit : ∀ i : I, IsLimit (Cone.mk (integral.P.obj i) (pπ i))
  projection_smul : ∀ (i : I) (n : ℕ) (V : Cᵒᵖ)
    (r : (integral.R.obj i).obj.obj V) (x : (integral.P.obj i).obj.obj V),
    ((pπ i).app (op n)).hom.app V (integral.act i V r x) =
      levels.act (i, op n) V
        (((subsequence i).inv.app (op n)).hom.app V
          (((rπ i).app (op (e i * (n + 1) - 1))).hom.app V r))
        (((pπ i).app (op n)).hom.app V x)
  rπ_natural : ∀ {i j : I} (h : i ≤ j) (n : ℕ),
    integral.R.map (homOfLE h) ≫ (rπ j).app (op (e j * (n + 1) - 1)) ≫
        (subsequence j).inv.app (op n) =
      (rπ i).app (op (e i * (n + 1) - 1)) ≫
        (subsequence i).inv.app (op n) ≫ levels.R.map (Prod.mkHom (homOfLE h) (𝟙 (op n)))
  pπ_natural : ∀ {i j : I} (h : i ≤ j) (n : ℕ),
    integral.P.map (homOfLE h) ≫ (pπ j).app (op n) =
      (pπ i).app (op n) ≫ levels.P.map (Prod.mkHom (homOfLE h) (𝟙 (op n)))

/-- A common covering and compatible rank-one linear bases, on the actual slice sites.
There is one covering for each coefficient index, not a separate covering at each level.
Source: Integral twist paragraph and Sites, Tag 03CF
(blueprint: lem-pur-adic-line-system-base-change). -/
def PurAdicLineLocallyBased
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] [HasFiniteLimits C]
    (J₀ : Precoverage C) {I : Type w} [PartialOrder I] {e : I → ℕ}
    (A : PurAdicLineLimits.{w} J₀.toGrothendieck I e) : Prop :=
  ∀ i : I, ∃ (Q : Type w) (V : Q → C) (v : ∀ j : Q, V j ⟶ ⊤_ C),
    Presieve.ofArrows V v ∈ J₀ (⊤_ C) ∧
    ∃ b : ∀ (j : Q) (n : ℕ),
      (SheafOfModules.unit
        ((sheafCompose J₀.toGrothendieck (forget₂ CommRingCat.{w} RingCat.{w})).obj
          (A.levels.R.obj (i, op n)))).over (V j) ≅
        (A.levels.M (i, op n)).over (V j),
      ∀ (j : Q) (n : ℕ) (W : Over (V j))
        (r : (A.levels.R.obj (i, op (n + 1))).obj.obj (op W.left)),
        (A.levels.P.map (𝟙 i, (homOfLE (Nat.le_succ n)).op)).hom.app (op W.left)
            ((A.levels.identify (i, op (n + 1))).hom.hom.app (op W.left)
              ((b j (n + 1)).hom.val.app (op W) r)) =
          (A.levels.identify (i, op n)).hom.hom.app (op W.left)
            ((b j n).hom.val.app (op W)
              ((A.levels.R.map (𝟙 i, (homOfLE (Nat.le_succ n)).op)).hom.app
                (op W.left) r))

/-- An underlying module isomorphism in arbitrary abelian-sheaf presentations.
Source: Sites, Tag 00YV, and Modules on Sites, Tag 03D2
(blueprint: lem-pur-adic-line-system-base-change). -/
def purAdicPresentedModuleIso
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
    {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
    {P : Sheaf J AddCommGrpCat.{w}} {Q : Sheaf K AddCommGrpCat.{w}}
    (M : ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (N : ringedSiteModules.{w} ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (p : (SheafOfModules.toSheaf _).obj M ≅ P)
    (q : (SheafOfModules.toSheaf _).obj N ≅ Q)
    (a : SheafOfModules.AlgebraicInverseImage L R S) (c : a.modules.obj M ≅ N) :
    L.obj ((sheafCompose J (forget AddCommGrpCat.{w})).obj P) ≅
      (sheafCompose K (forget AddCommGrpCat.{w})).obj Q :=
  L.mapIso ((sheafCompose J (forget AddCommGrpCat.{w})).mapIso p.symm) ≪≫
    (a.moduleUnderlying.app M).symm ≪≫
    (sheafCompose K (forget AddCommGrpCat.{w})).mapIso
      ((SheafOfModules.toSheaf _).mapIso c ≪≫ q)

/-- Chosen localizations of a diagram of ring/module pairs. The rings are the actual
sheafified fraction rings, and restriction of the module action gives the existing
sheaf tensor localization. The units determine all directed transition maps.
This is a presentation of the localizations, not an extra base-change assumption.
Source: Rational and algebraic closure paragraph; Stacks Tags 00DK and 03CY
(blueprint: lem-pur-adic-line-system-base-change). -/
structure PurAdicLocalization
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify J CommRingCat.{w}]
    {I : Type w} [PartialOrder I] (A : PurAdicPairDiagram.{w} J I)
    (s : ∀ i : I, ((A.R.obj i).obj ⋙ forget CommRingCat.{w}).sections) where
  pairs : PurAdicPairDiagram.{w} J I
  ringIso : ∀ i : I, pairs.R.obj i ≅ ringedLocalizationRingOfUniverses.{w, uC, vC} (A.R.obj i) (s i)
  ringUnit : A.R ⟶ pairs.R
  ringUnit_eq : ∀ i : I, ringUnit.app i =
    ringedLocalizationRingUnitOfUniverses.{w, uC, vC} (A.R.obj i) (s i) ≫ (ringIso i).inv
  moduleIso : ∀ i : I,
    (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map (ringUnit.app i))).obj
        (pairs.M i) ≅ (scalarLocalization (A.R.obj i) (s i)).obj (A.M i)
  moduleUnit : A.P ⟶ pairs.P
  moduleUnit_eq : ∀ i : I,
    (A.identify i).hom ≫ moduleUnit.app i =
      (SheafOfModules.toSheaf _).map
        ((scalarLocalizationUnit (A.R.obj i) (s i)).app (A.M i) ≫ (moduleIso i).inv) ≫
          (pairs.identify i).hom

namespace PurAdicLocalization

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasSheafify J CommRingCat.{w}]
variable {I : Type w} [PartialOrder I] {A : PurAdicPairDiagram.{w} J I}
variable {s : ∀ i : I, ((A.R.obj i).obj ⋙ forget CommRingCat.{w}).sections}

/-- The localization unit on underlying ring sheaves.
Source: Stacks Tag 00CP (blueprint: lem-pur-adic-line-system-base-change). -/
abbrev ringsUnit (Q : PurAdicLocalization A s) (i : I) :=
  (sheafCompose J (forget CommRingCat.{w})).map (Q.ringUnit.app i)

/-- The localization unit on underlying module sheaves.
Source: Stacks Tag 00DK (blueprint: lem-pur-adic-line-system-base-change). -/
abbrev modulesUnit (Q : PurAdicLocalization A s) (i : I) :=
  (sheafCompose J (forget AddCommGrpCat.{w})).map (Q.moduleUnit.app i)

end PurAdicLocalization

/-- A sheafified filtered colimit of pairs, with its actual module structure. The two
colimit universal properties fix the underlying sheaves. The representative formula
fixes the module structure, including elements coming from different stages.
Source: Rational and algebraic closure paragraph; Stacks Tags 00D6, 00D7 and 03CY
(blueprint: lem-pur-adic-line-system-base-change). -/
structure PurAdicFilteredColimit
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
    {I : Type w} [PartialOrder I] (A : PurAdicPairDiagram.{w} J I) where
  R : Sheaf J CommRingCat.{w}
  P : Sheaf J AddCommGrpCat.{w}
  M : ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  identify : (SheafOfModules.toSheaf _).obj M ≅ P
  rι : A.R ⟶ (Functor.const I).obj R
  rcolimit : IsColimit (Cocone.mk R rι)
  pι : A.P ⟶ (Functor.const I).obj P
  pcolimit : IsColimit (Cocone.mk P pι)
  scalar : ∀ (i j k : I) (hi : i ≤ k) (hj : j ≤ k) (V : Cᵒᵖ)
    (r : (A.R.obj i).obj.obj V) (m : (A.P.obj j).obj.obj V),
    identify.hom.hom.app V
        (((rι.app i).hom.app V r) •
          @id (M.val.obj V) (identify.inv.hom.app V ((pι.app j).hom.app V m))) =
      (pι.app k).hom.app V
        (A.act k V ((A.R.map (homOfLE hi)).hom.app V r)
          ((A.P.map (homOfLE hj)).hom.app V m))

namespace PurAdicFilteredColimit

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
variable {I : Type w} [PartialOrder I] {A : PurAdicPairDiagram.{w} J I}

/-- Ring coprojections on underlying set sheaves.
Source: Stacks Tag 00WJ (blueprint: lem-pur-adic-line-system-base-change). -/
abbrev ringsι (F : PurAdicFilteredColimit A) (i : I) :=
  (sheafCompose J (forget CommRingCat.{w})).map (F.rι.app i)

/-- Module coprojections on underlying set sheaves.
Source: Stacks Tag 00WJ (blueprint: lem-pur-adic-line-system-base-change). -/
abbrev modulesι (F : PurAdicFilteredColimit A) (i : I) :=
  (sheafCompose J (forget AddCommGrpCat.{w})).map (F.pι.app i)

end PurAdicFilteredColimit

/-- The cofinal restriction isomorphism, including its inverse-coordinate formula.
Source: Integral twist paragraph, explicit cofinal subsequence calculation
(blueprint: lem-pur-adic-line-system-base-change). -/
def PurAdicCofinalRestriction
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {I : Type w} [PartialOrder I] {e : I → ℕ}
    (A : PurAdicLineLimits.{w} J I e) : Prop :=
  ∀ i : I, HasLimit (purAdicStride (e i) ⋙ A.full i) ∧
    ∀ T : Cone (purAdicStride (e i) ⋙ A.full i), IsLimit T →
    ∃ q : A.integral.R.obj i ≅ T.pt,
      (∀ n : ℕ, q.hom ≫ T.π.app (op n) =
        (A.rπ i).app (op (e i * (n + 1) - 1))) ∧
      (∀ (m n : ℕ) (h : m ≤ e i * (n + 1) - 1),
        q.inv ≫ (A.rπ i).app (op m) =
          T.π.app (op n) ≫ (A.full i).map (homOfLE h).op)

/-- Projection normalization for an integral semilinear comparison.
Source: Integral twist paragraph (blueprint: lem-pur-adic-line-system-base-change). -/
def PurAdicIntegralNormalized
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {I : Type w} [PartialOrder I] {e : I → ℕ}
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (A : PurAdicLineLimits.{w} J I e) (B : PurAdicLineLimits.{w} K I e)
    (c : PurAdicPairComparison L A.levels B.levels)
    (t : PurAdicPairComparison L A.integral B.integral) : Prop :=
  ∀ (i : I) (n : ℕ),
    (purAdicModuleIso L A.integral B.integral i (t.a i) (t.c i)).hom ≫
        (sheafCompose K (forget AddCommGrpCat.{w})).map ((B.pπ i).app (op n)) =
      L.map ((sheafCompose J (forget AddCommGrpCat.{w})).map ((A.pπ i).app (op n))) ≫
        (purAdicModuleIso L A.levels B.levels (i, op n) (c.a _) (c.c _)).hom

/-- Localization-unit normalization of both the coefficient and module comparisons.
Source: Rational and algebraic closure paragraph
(blueprint: lem-pur-adic-line-system-base-change). -/
def PurAdicLocalizationNormalized
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify J CommRingCat.{w}]
    [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify K CommRingCat.{w}]
    {I : Type w} [PartialOrder I]
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    {A : PurAdicPairDiagram.{w} J I} {B : PurAdicPairDiagram.{w} K I}
    {s : ∀ i : I, ((A.R.obj i).obj ⋙ forget CommRingCat.{w}).sections}
    {s' : ∀ i : I, ((B.R.obj i).obj ⋙ forget CommRingCat.{w}).sections}
    (t : PurAdicPairComparison L A B)
    (Q : PurAdicLocalization A s) (Q' : PurAdicLocalization B s')
    (d : PurAdicPairComparison L Q.pairs Q'.pairs) : Prop :=
  (∀ i : I, L.map (Q.ringsUnit i) ≫ (d.a i).ringUnderlying.hom =
    (t.a i).ringUnderlying.hom ≫ Q'.ringsUnit i) ∧
  (∀ i : I, L.map (Q.modulesUnit i) ≫
      (purAdicModuleIso L Q.pairs Q'.pairs i (d.a i) (d.c i)).hom =
    (purAdicModuleIso L A B i (t.a i) (t.c i)).hom ≫ Q'.modulesUnit i)

/-- The colimit comparison consists of a ring comparison and a linear module isomorphism.
Its two equations normalize it on every ring and module coprojection.
Source: Rational and algebraic closure paragraph
(blueprint: lem-pur-adic-line-system-base-change). -/
structure PurAdicColimitComparison
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {I : Type w} [PartialOrder I]
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    {A : PurAdicPairDiagram.{w} J I} {B : PurAdicPairDiagram.{w} K I}
    (t : PurAdicPairComparison L A B)
    (F : PurAdicFilteredColimit A) (G : PurAdicFilteredColimit B) where
  a : SheafOfModules.AlgebraicInverseImage L F.R G.R
  c : a.modules.obj F.M ≅ G.M
  ring_ι : ∀ i : I, L.map (F.ringsι i) ≫ a.ringUnderlying.hom =
    (t.a i).ringUnderlying.hom ≫ G.ringsι i
  module_ι : ∀ i : I, L.map (F.modulesι i) ≫
      (purAdicPresentedModuleIso F.M G.M F.identify G.identify a c).hom =
    (purAdicModuleIso L A B i (t.a i) (t.c i)).hom ≫ G.modulesι i

/-- Full coefficient comparisons, their projection equations, and their compatibility
with the specified subsequence comparisons. This records the input, not preservation
of an arbitrary countable limit by inverse image.
Source: Integral twist paragraph (blueprint: lem-pur-adic-line-system-base-change). -/
structure PurAdicCoefficientComparison
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {I : Type w} [PartialOrder I] {e : I → ℕ}
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (A : PurAdicLineLimits.{w} J I e) (B : PurAdicLineLimits.{w} K I e)
    (c : PurAdicPairComparison L A.levels B.levels) where
  full : ∀ (i : I) (m : ℕ),
    SheafOfModules.AlgebraicInverseImage L ((A.full i).obj (op m))
      ((B.full i).obj (op m))
  integral : ∀ i : I,
    SheafOfModules.AlgebraicInverseImage L (A.integral.R.obj i) (B.integral.R.obj i)
  full_natural : ∀ (i : I) {m n : ℕ} (h : m ≤ n),
    L.map ((sheafCompose J (forget CommRingCat.{w})).map
      ((A.full i).map (homOfLE h).op)) ≫ (full i m).ringUnderlying.hom =
        (full i n).ringUnderlying.hom ≫
          (sheafCompose K (forget CommRingCat.{w})).map ((B.full i).map (homOfLE h).op)
  projection : ∀ (i : I) (m : ℕ),
    L.map ((sheafCompose J (forget CommRingCat.{w})).map ((A.rπ i).app (op m))) ≫
        (full i m).ringUnderlying.hom =
      (integral i).ringUnderlying.hom ≫
        (sheafCompose K (forget CommRingCat.{w})).map ((B.rπ i).app (op m))
  subsequence : ∀ (i : I) (n : ℕ),
    L.map ((sheafCompose J (forget CommRingCat.{w})).map
        ((A.subsequence i).hom.app (op n))) ≫
        (full i (e i * (n + 1) - 1)).ringUnderlying.hom =
      (c.a (i, op n)).ringUnderlying.hom ≫
        (sheafCompose K (forget CommRingCat.{w})).map
          ((B.subsequence i).hom.app (op n))
  integral_natural : ∀ {i j : I} (h : i ≤ j),
    L.map (A.integral.rings.map (homOfLE h)) ≫ (integral j).ringUnderlying.hom =
      (integral i).ringUnderlying.hom ≫ B.integral.rings.map (homOfLE h)

/-- Inverse image of adic line systems, with localization and filtered coefficient change.
Source: Integral twist and Rational and algebraic closure paragraphs of
`sk-prop-sfb-cartesian-coefficients-twists.proof.md`; Stacks Sites, Tag 03CF
(blueprint: lem-pur-adic-line-system-base-change).

Proof:
1. Restriction to the positive stride is cofinal. Recover coordinate m by reducing
   any coordinate e(n+1) at least m+1; comparison at a larger coordinate proves independence.
2. The full coefficient projection equations identify the subsequence limit comparison
   with the given coefficient isomorphism, hence it is invertible.
3. Apply `lem-pur-inverse-image-compatible-free-tower` on the single common cover,
   then compose with the levelwise comparisons c. This gives the displayed projections.
4. Test scalar compatibility, uniqueness and naturality on every projection. These
   formulas mention no bases, proving independence of the cover and bases.
5. By `lem-sc-module-localization-filtered-colimit` the sheafified sequential colimit
   is the localization, with the actual fraction-ring action obtained by module sheafification.
6. `lem-weil-pbc-localization-tensor` and the module-sheafification tensor comparison
   identify it with tensor localization, preserving m/1 and m tensor 1.
7. Apply `lem-weil-pbc-localization-inverse-image-coherence`. The semilinear integral
   comparison induces a comparison of the sequential diagrams. Cocone normalization
   proves uniqueness and naturality after localization.
8. Form ring and abelian presheaf colimits and define [r_i][m_j] at a common upper bound.
   The representative criteria for filtered ring and module colimits make this independent
   of representatives and prove all ring/module laws at a common stage.
9. Sheafify. Sectionwise presheaf colimits and the sheafification adjunction give the two
   colimit universal properties. Preservation of finite products gives the displayed action.
10. Colimit preservation of inverse image gives the final comparisons. Test semilinearity
    on stage products and normalize on every coprojection to obtain uniqueness.
-/
theorem purAdicLineSystem_baseChange
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : Precoverage C) (K : Precoverage D)
    (_hJ : J.IsSiteForCoverings) (_hK : K.IsSiteForCoverings)
    (U : C ⥤ D) [PreservesFiniteLimits U]
    (_hUcover : ∀ (X : C) (S : Presieve X), S ∈ J X → S.map U ∈ K (U.obj X))
    [U.IsContinuous J.toGrothendieck K.toGrothendieck]
    (L : Sheaf J.toGrothendieck (Type w) ⥤ Sheaf K.toGrothendieck (Type w))
    (_adj : L ⊣ U.sheafPushforwardContinuous (Type w) J.toGrothendieck K.toGrothendieck)
    [PreservesFiniteLimits L]
    [HasSheafify J.toGrothendieck AddCommGrpCat.{w}]
    [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify J.toGrothendieck CommRingCat.{w}]
    [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
    [K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify K.toGrothendieck CommRingCat.{w}]
    (I : Type w) [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (e : I → ℕ) (_he : ∀ i : I, 1 ≤ e i)
    (A : PurAdicLineLimits.{w} J.toGrothendieck I e)
    (B : PurAdicLineLimits.{w} K.toGrothendieck I e)
    (c : PurAdicPairComparison L A.levels B.levels)
    (a : PurAdicCoefficientComparison L A B c)
    (_bases : PurAdicLineLocallyBased J A)
    (s : ∀ i : I, ((A.integral.R.obj i).obj ⋙ forget CommRingCat.{w}).sections)
    (s' : ∀ i : I, ((B.integral.R.obj i).obj ⋙ forget CommRingCat.{w}).sections)
    (_hs : ∀ {i j : I} (h : i ≤ j) (V : Cᵒᵖ),
      (A.integral.R.map (homOfLE h)).hom.app V ((s i).val V) = (s j).val V)
    (_hsection : ∀ i : I, IsInverseImageSection.{w, uC, vC, uD, vD} (a.integral i) (s i) (s' i)) :
    PurAdicCofinalRestriction A ∧ PurAdicCofinalRestriction B ∧
    ∃ t : PurAdicPairComparison L A.integral B.integral,
      (∀ i : I, (t.a i).ringUnderlying = (a.integral i).ringUnderlying) ∧
      PurAdicIntegralNormalized L A B c t ∧
      (∀ (i : I) (f : L.obj (A.integral.modules.obj i) ⟶ B.integral.modules.obj i),
        (∀ n : ℕ, f ≫ (sheafCompose K.toGrothendieck (forget AddCommGrpCat.{w})).map
            ((B.pπ i).app (op n)) =
          L.map ((sheafCompose J.toGrothendieck (forget AddCommGrpCat.{w})).map
              ((A.pπ i).app (op n))) ≫
            (purAdicModuleIso L A.levels B.levels (i, op n) (c.a _) (c.c _)).hom) →
        f = (purAdicModuleIso L A.integral B.integral i (t.a i) (t.c i)).hom) ∧
      ∃ (Q : PurAdicLocalization A.integral s) (Q' : PurAdicLocalization B.integral s')
        (d : PurAdicPairComparison L Q.pairs Q'.pairs),
        PurAdicLocalizationNormalized L t Q Q' d ∧
        (∀ d' : PurAdicPairComparison L Q.pairs Q'.pairs,
          PurAdicLocalizationNormalized L t Q Q' d' →
          ∀ i : I, (d'.a i).ringUnderlying = (d.a i).ringUnderlying ∧
            purAdicModuleIso L Q.pairs Q'.pairs i (d'.a i) (d'.c i) =
              purAdicModuleIso L Q.pairs Q'.pairs i (d.a i) (d.c i)) ∧
        ∃ (F : PurAdicFilteredColimit Q.pairs) (G : PurAdicFilteredColimit Q'.pairs)
          (z : PurAdicColimitComparison L d F G),
          ∀ z' : PurAdicColimitComparison L d F G,
            z'.a.ringUnderlying = z.a.ringUnderlying ∧
            purAdicPresentedModuleIso F.M G.M F.identify G.identify z'.a z'.c =
              purAdicPresentedModuleIso F.M G.M F.identify G.identify z.a z.c := by
  sorry

end CategoryTheory
