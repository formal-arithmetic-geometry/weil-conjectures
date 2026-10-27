module

public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.ProEtale.EtaleCohomologyComparison
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized

/-! # Exchange naturality of ordinary finite-twist units

Source: Stacks Project, categories.tex, Tag 0B65; blueprint sk-prop-a1-kummer,
Base change on Y and Coefficients
(blueprint: lem-pur-ordinary-unit-exchange-naturality).

The helpers expose the actual canonical maps and the equations asserted by this node.
Ordinary cohomology uses its derived-Hom presentation in every integer degree.
All coefficients are the published signed finite Tate sheaves; level changes are
maps of underlying abelian sheaves, equivalently maps over a common finite integer ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u c d e f vc vd ve vf wc wd we wf
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures

/-- The displayed unit equation and its conditional exchange invertibility, with the
specified exchange arrow retained as an argument. Source: Stacks Tag 0B65 and blueprint
Base change on Y (blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
def purityUnitExchangeEquation
    {C : Type c} {D : Type d} {E : Type e} {F : Type f}
    [Category.{vc} C] [Category.{vd} D] [Category.{ve} E] [Category.{vf} F]
    {l : C ⥤ D} {r : D ⥤ C} {l' : E ⥤ F} {r' : F ⥤ E}
    {g : C ⥤ E} {h : D ⥤ F} (adj : l ⊣ r) (adj' : l' ⊣ r')
    (θ : g ⋙ l' ≅ l ⋙ h) (β : r ⋙ g ⟶ h ⋙ r') (M : C) : Prop :=
  g.map (adj.unit.app M) ≫ β.app (l.obj M) ≫ r'.map (θ.inv.app M) =
      adj'.unit.app (g.obj M) ∧
    (IsIso (adj.unit.app M) → IsIso (adj'.unit.app (g.obj M)) →
      IsIso (β.app (l.obj M)))

section Cohomology

variable {C : Type c} {D : Type d} {E : Type e} {F : Type f}
    [Category.{vc} C] [Category.{vd} D] [Category.{ve} E] [Category.{vf} F]
  [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wd} D]
  [HasDerivedCategory.{we} E] [HasDerivedCategory.{wf} F]

/-- Ordinary integral-degree cohomology in its standard derived-Hom presentation.
For abelian sheaves the source Z is the constant sheaf of integers in degree zero.
Thus this is ordinary sheaf cohomology, including the zero negative groups.
Source: Stacks Cohomology on Sites, 01FT
(blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
abbrev purityH (Z M : C) (q : ℤ) :=
  ShiftedHom ((DerivedCategory.singleFunctor C 0).obj Z)
    ((DerivedCategory.singleFunctor C 0).obj M) q

/-- Coefficient morphisms act by postcomposition on the same ordinary groups.
Source: Stacks 01FT (blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
def purityHMap (Z : C) {M N : C} (a : M ⟶ N) (q : ℤ)
    (x : purityH Z M q) : purityH Z N q :=
  x ≫ ((DerivedCategory.singleFunctor C 0).map a)⟦q⟧'

/-- Pull an ordinary class through an exact inverse image and the specified constant
integer comparison. Every factor is the canonical termwise derived construction.
Source: Stacks 01F8, 01FB (blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
def purityHPull (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {Z : C} {Z' : D} (e : Z' ≅ G.obj Z) (M : C) (q : ℤ)
    (x : purityH Z M q) : purityH Z' (G.obj M) q :=
  (DerivedCategory.singleFunctor D 0).map e.hom ≫
    (G.mapDerivedCategorySingleFunctor 0).inv.app Z ≫
    ShiftedHom.map x G.mapDerivedCategory ≫
    ((G.mapDerivedCategorySingleFunctor 0).hom.app M)⟦q⟧'

/-- Coefficient naturality and the corresponding inverse square when the actual
pullback maps are bijective. The inverse is the inverse of that specified function.
Source: Stacks 01F8, 01FB and elementary cancellation
(blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
def purityCohomologyNaturality (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {Z : C} {Z' : D} (e : Z' ≅ G.obj Z) {M N : C} (a : M ⟶ N) : Prop :=
  ∀ q : ℤ,
    (∀ x : purityH Z M q,
      purityHPull G e N q (purityHMap Z a q x) =
        purityHMap Z' (G.map a) q (purityHPull G e M q x)) ∧
    (Function.Bijective (purityHPull G e M q) →
      Function.Bijective (purityHPull G e N q) →
      ∀ y : purityH Z' (G.obj M) q,
        Function.invFun (purityHPull G e N q) (purityHMap Z' (G.map a) q y) =
          purityHMap Z a q (Function.invFun (purityHPull G e M q) y))

/-- Pullback composition around a specified inverse-image square, and its inverse
square under precisely the invertibility of its two horizontal pullbacks.
The new horizontal pullback is expressed in the common codomain using θ.
Source: Stacks 01F8, 01FB; blueprint Base change on Y
(blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
def purityCohomologySquare
    (l : C ⥤ D) (g : C ⥤ E) (l' : E ⥤ F) (h : D ⥤ F)
    [l.Additive] [g.Additive] [l'.Additive] [h.Additive]
    [PreservesFiniteLimits l] [PreservesFiniteColimits l]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g]
    [PreservesFiniteLimits l'] [PreservesFiniteColimits l']
    [PreservesFiniteLimits h] [PreservesFiniteColimits h]
    {Z : C} {ZD : D} {ZE : E} {ZF : F}
    (el : ZD ≅ l.obj Z) (eg : ZE ≅ g.obj Z)
    (el' : ZF ≅ l'.obj ZE) (eh : ZF ≅ h.obj ZD)
    (θ : g ⋙ l' ≅ l ⋙ h) (M : C) : Prop :=
  ∀ q : ℤ,
    (∀ x : purityH Z M q,
      purityHPull h eh (l.obj M) q (purityHPull l el M q x) =
        purityHMap ZF (θ.hom.app M) q
          (purityHPull l' el' (g.obj M) q (purityHPull g eg M q x))) ∧
    (Function.Bijective (purityHPull l el M q) →
      Function.Bijective (fun x ↦ purityHMap ZF (θ.hom.app M) q
        (purityHPull l' el' (g.obj M) q x)) →
      ∀ y : purityH ZD (l.obj M) q,
        Function.invFun (fun x ↦ purityHMap ZF (θ.hom.app M) q
            (purityHPull l' el' (g.obj M) q x))
          (purityHPull h eh (l.obj M) q y) =
        purityHPull g eg M q (Function.invFun (purityHPull l el M q) y))

end Cohomology

namespace PurityFiniteSetting

/-- The signed finite etale Tate coefficient, using the canonical annihilator char A;
this includes all positive finite levels, without an e-divides-n assumption.
Source: finite purity conventions and Stacks 03PK
(blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
abbrev ordinaryEtaleTwist (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (r : ℤ) :=
  Scheme.finiteEtaleTateSheaf P.Coefficient (ringChar P.Coefficient) X
    (CharP.cast_eq_zero P.Coefficient (ringChar P.Coefficient)) r

/-- The underlying abelian sheaf, so maps between different finite coefficient
levels are allowed. Source: blueprint Coefficients paragraph
(blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
abbrev ordinaryTwistAb (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (r : ℤ) :=
  (P.forgetEtale X).obj (P.ordinaryEtaleTwist X r)

end PurityFiniteSetting

/-- The actual affine-line base-change square. Source: Mathlib AffineSpace.isPullback_map
and blueprint Base change on Y
(blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
abbrev purityAffineLineSquare {X X' : Scheme.{u}} (v : X' ⟶ X) :=
  (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) v).toCommSq

/-- The canonical constant-integer comparison for geometric pro-etale inverse image.
It is the unique comparison supplied by the constant-sheaf adjunction, normalized
on the terminal object and its base change. Source: Stacks 01F8, 01FB
(blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
def purityProEtaleIntegerPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).constantSheafsheafPullbackIso
    AddCommGrpCat.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (Scheme.ProEt.isTerminalMkId Y)
    ((Scheme.ProEt.isTerminalMkId X).ofIso
      (ProEtale.overPullbackObjMkIdIso f).symm)).symm.app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≪≫
      (Functor.sheafPullbackConstruction.sheafPullbackIso
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) AddCommGrpCat.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).app
          ((constantSheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- The affine-line projection, with the coordinate universe of def-sbc-affine-space.
Source: Stacks 01M0 (blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
abbrev purityLineProjection (X : Scheme.{u}) :=
  AffineSpace (ULift.{u} (Fin 1)) X ↘ X

/-- The actual map of affine lines induced by the base map.
Source: blueprint Base change on Y
(blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
abbrev purityLineMap {X X' : Scheme.{u}} (v : X' ⟶ X) :=
  AffineSpace.map (ULift.{u} (Fin 1)) v

/-- The chosen Cartesian identification supplied by the affine-space pullback theorem.
Source: Mathlib AffineSpace.isPullback_map; Stacks 01M0
(blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
def purityChosenLineSquare {X X' : Scheme.{u}} (v : X' ⟶ X) :
    ChosenCartesianSquare (purityLineMap v) (purityLineProjection X')
      (purityLineProjection X) v where
  toCommSq := purityAffineLineSquare v
  isoPullback := (AffineSpace.isPullback_map v).isoPullback
  hom_fst := (AffineSpace.isPullback_map v).isoPullback_hom_fst
  hom_snd := (AffineSpace.isPullback_map v).isoPullback_hom_snd

/-- The finite twist in degree zero in D+ of etale modules.
Source: finite purity conventions (blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
abbrev purityTwistPlus (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (r : ℤ) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj (P.ordinaryEtaleTwist X r)

/-- The same finite twist in the unbounded etale category.
Source: finite purity conventions (blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
abbrev purityTwistComplex (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (r : ℤ) :=
  (DerivedCategory.singleFunctor _ 0).obj (P.ordinaryEtaleTwist X r)

/-- The canonical comparison identifies the named units, with the fixed counit mate
and the specified pullback comparison, including their directions.
Source: Stacks 0B65; blueprint Base change on Y
(blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
def purityComparisonUnitEquation (A : Type (u + 1)) [CommRing A]
    {U V : Scheme.{u}} (f : U ⟶ V)
    (M : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))) : Prop :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategoryPlus.map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) f).unit.app M) ≫
    (ProEtale.fixedComparisonDirectImageMatePlus A f).app
      ((Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.obj M) ≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus.map
      ((ProEtale.fixedComparisonPullbackPlus A f).hom.app M) =
    (ProEtale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) f).unit.app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategoryPlus.obj M)

/-- The comparison conjugates the named exchanges, at the specified pulled-back
finite twist. The comparisons are the published canonical source and target maps.
Source: blueprint transport-identifies-exchange, Stacks 0B65
(blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
def purityComparisonExchangeEquation (P : PurityFiniteSetting.{u})
    {X X' : Scheme.{u}} (v : X' ⟶ X) (r : ℤ) : Prop :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map
        ((Etale.baseChange (ModuleCat.{u + 1} P.Coefficient)
          (purityAffineLineSquare v)).app
            ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (purityLineProjection
              X)).mapDerivedCategoryPlus.obj (purityTwistPlus P X r)))) ≫
    (ProEtale.baseChangeTargetComparisonIso (purityLineMap v)
      (purityLineProjection X') P.Coefficient).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (purityLineProjection
          X)).mapDerivedCategoryPlus.obj (purityTwistPlus P X r)) =
    (ProEtale.baseChangeSourceComparisonIso (purityLineProjection X) v P.Coefficient).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (purityLineProjection
          X)).mapDerivedCategoryPlus.obj (purityTwistPlus P X r)) ≫
      (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
        (purityAffineLineSquare v)).app
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
            (AffineSpace (ULift.{u} (Fin 1)) X)).mapDerivedCategory.obj
              (DerivedCategory.Plus.ι.obj
                ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (purityLineProjection
                  X)).mapDerivedCategoryPlus.obj (purityTwistPlus P X r))))

/-- The cohomology square of the canonical comparison and a geometric pullback.
Its inverse-square clause retains the same named maps.
Source: Stacks 01F8, 01FB; blueprint site comparison
(blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
def puritySiteCohomologySquare {U V : Scheme.{u}} (f : U ⟶ V)
    (M : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  purityCohomologySquare
    (Etale.upperStar AddCommGrpCat.{u + 1} f)
    (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} V)
    (ProEtale.upperStar AddCommGrpCat.{u + 1} f)
    (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} U)
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (ProEtale.constantIntIsoComparisonUpperStar V)
    (purityProEtaleIntegerPullback f)
    (ProEtale.constantIntIsoComparisonUpperStar U)
    (ProEtale.comparisonUpperStarCompUpperStarIso AddCommGrpCat.{u + 1} f) M

/-- The finite purity datum at another positive level, retaining its field and E.
Source: blueprint Coefficients paragraph
(blueprint: lem-pur-ordinary-unit-exchange-naturality). -/
abbrev PurityFiniteSetting.ordinaryAtLevel (P : PurityFiniteSetting.{u})
    (n : ℕ) (hn : 1 ≤ n) : PurityFiniteSetting.{u} :=
  { P with level := n, level_pos := hn }

/-- Ordinary finite-twist unit exchange, ordinary cohomology naturality and their
canonical site identifications. Source: Stacks 0B65, 01F8, 01FB; blueprint
sk-prop-a1-kummer, Base change on Y and Coefficients
(blueprint: lem-pur-ordinary-unit-exchange-naturality).

Proof:
1. Use the normalized signed finite-twist pullbacks. AffineSpace.isPullback_map
   supplies the Cartesian projection square; its projections are affine, hence qcqs.
   Degree-zero coefficients are bounded below. No condition on v is used.
2. Apply lem-pur-mate-unit-compatibility (Mathlib unit_mateEquiv) to the two
   derived projection adjunctions, v pullback and affine-line v pullback.
   The named exchange is exactly the right mate of the square identification.
   Compose with the direct image of the inverse square comparison and cancel.
   No invertibility is used in this equation. If both units are invertible,
   solve for the exchange as the composite of their inverses and the square iso.
3. Apply the same unit-mate identity to the canonical site-comparison square.
   The direct-image mate is fixedComparisonDirectImageMatePlus with precisely
   its counit normalization. Transport-identifies-exchange identifies the named
   exchanges; comparison-pullback coherence identifies the square comparisons
   and their inverses. Substitution identifies the complete unit equation.
4. The left-module-derived-evaluation-forget comparison identifies module
   cohomology with abelian cohomology. Site-cohomology-pullback composition
   applied to the two paths gives w pullback after p pullback equal to p'
   pullback after v pullback, with the specified square identification.
   Its coefficient naturality applies to every underlying abelian coefficient
   morphism, including level changes and quotients, without a flatness assumption.
5. The canonical global site comparison is evaluation of the comparison unit.
   Site-cohomology-pullback composition gives the four site-comparison squares;
   coefficient naturality gives their coefficient squares. The derived-Hom
   presentation retains every integer q. For negative q both sheaf cohomology
   groups vanish, as an injective resolution is concentrated in nonnegative degrees.
6. In each commuting square, when its horizontal pullbacks are invertible,
   multiply by their inverses to obtain the stated inverse square. All named
   functions and their inverses are retained. This includes identity base maps,
   zero coefficient maps, empty schemes, all signed twists and all positive levels. -/
theorem purity_ordinary_unit_exchange_naturality
    (P : PurityFiniteSetting.{u}) {X X' : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of P.field.k))]
    [X'.Over (Spec (CommRingCat.of P.field.k))]
    (v : X' ⟶ X) [v.IsOver (Spec (CommRingCat.of P.field.k))] (r : ℤ) :
    purityUnitExchangeEquation
      (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
        (purityLineProjection X))
      (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
        (purityLineProjection X'))
      (Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} P.Coefficient) (purityAffineLineSquare v))
      (Etale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient) (purityAffineLineSquare v))
      (purityTwistComplex P X r) ∧
    purityUnitExchangeEquation
      (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
        (purityLineProjection X))
      (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
        (purityLineProjection X'))
      (ProEtale.leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} P.Coefficient)
        (purityAffineLineSquare v))
      (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient) (purityAffineLineSquare v))
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
        (purityTwistComplex P X r)) ∧
    purityComparisonUnitEquation P.Coefficient (purityLineProjection X) (purityTwistPlus P X r) ∧
    purityComparisonUnitEquation P.Coefficient (purityLineProjection X')
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).mapDerivedCategoryPlus.obj
        (purityTwistPlus P X r)) ∧
    purityComparisonExchangeEquation P v r ∧
    ProEtale.ComparisonSquareComponent
      (ProEtale.comparisonSquareData (ModuleCat.{u + 1} P.Coefficient) (purityLineMap v)
        (purityLineProjection X') (purityLineProjection X) v
        (purityChosenLineSquare v)) (P.ordinaryEtaleTwist X r) ∧
    purityCohomologySquare
      (Etale.upperStar AddCommGrpCat.{u + 1} (purityLineProjection X)) (Etale.upperStar
        AddCommGrpCat.{u + 1} v)
      (Etale.upperStar AddCommGrpCat.{u + 1} (purityLineProjection X')) (Etale.upperStar
        AddCommGrpCat.{u + 1} (purityLineMap v))
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (purityLineProjection X)).symm.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} v).symm.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (purityLineProjection X')).symm.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (purityLineMap v)).symm.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      (Etale.squareUpperStarIso AddCommGrpCat.{u + 1} (purityAffineLineSquare v)) (P.ordinaryTwistAb
        X r) ∧
    purityCohomologySquare
      (ProEtale.upperStar AddCommGrpCat.{u + 1} (purityLineProjection X)) (ProEtale.upperStar
        AddCommGrpCat.{u + 1} v)
      (ProEtale.upperStar AddCommGrpCat.{u + 1} (purityLineProjection X')) (ProEtale.upperStar
        AddCommGrpCat.{u + 1} (purityLineMap v))
      (purityProEtaleIntegerPullback (purityLineProjection X))
      (purityProEtaleIntegerPullback v)
      (purityProEtaleIntegerPullback (purityLineProjection X'))
      (purityProEtaleIntegerPullback (purityLineMap v))
      (ProEtale.upperStarCompIso AddCommGrpCat.{u + 1} (purityAffineLineSquare v).w.symm)
        ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).obj (P.ordinaryTwistAb X r)) ∧
    puritySiteCohomologySquare v (P.ordinaryTwistAb X r) ∧
    puritySiteCohomologySquare (purityLineProjection X) (P.ordinaryTwistAb X r) ∧
    puritySiteCohomologySquare (purityLineProjection X') ((Etale.upperStar AddCommGrpCat.{u + 1}
      v).obj (P.ordinaryTwistAb X r)) ∧
    puritySiteCohomologySquare (purityLineMap v) ((Etale.upperStar AddCommGrpCat.{u + 1}
      (purityLineProjection X)).obj (P.ordinaryTwistAb X r)) ∧
    (∀ (n : ℕ) (hn : 1 ≤ n) (s : ℤ)
      (a : P.ordinaryTwistAb X r ⟶ (P.ordinaryAtLevel n hn).ordinaryTwistAb X s),
      purityCohomologyNaturality
        (Etale.upperStar AddCommGrpCat.{u + 1} (purityLineProjection X))
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (purityLineProjection X)).symm.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
        a ∧
      purityCohomologyNaturality
        (Etale.upperStar AddCommGrpCat.{u + 1} (purityLineProjection X'))
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (purityLineProjection X')).symm.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
        ((Etale.upperStar AddCommGrpCat.{u + 1} v).map a) ∧
      purityCohomologyNaturality
        (ProEtale.upperStar AddCommGrpCat.{u + 1} (purityLineProjection X))
        (purityProEtaleIntegerPullback (purityLineProjection X))
        ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).map a) ∧
      purityCohomologyNaturality
        (ProEtale.upperStar AddCommGrpCat.{u + 1} (purityLineProjection X'))
        (purityProEtaleIntegerPullback (purityLineProjection X'))
        ((ProEtale.upperStar AddCommGrpCat.{u + 1} v).map ((ProEtale.comparisonUpperStar
          AddCommGrpCat.{u + 1} X).map a)) ∧
      purityCohomologyNaturality
        (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X)
        (ProEtale.constantIntIsoComparisonUpperStar X)
        a ∧
      purityCohomologyNaturality
        (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1}
        (AffineSpace (ULift.{u} (Fin 1)) X))
        (ProEtale.constantIntIsoComparisonUpperStar (AffineSpace (ULift.{u} (Fin 1)) X))
        ((Etale.upperStar AddCommGrpCat.{u + 1} (purityLineProjection X)).map a) ∧
      purityCohomologyNaturality
        (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X')
        (ProEtale.constantIntIsoComparisonUpperStar X')
        ((Etale.upperStar AddCommGrpCat.{u + 1} v).map a) ∧
      purityCohomologyNaturality
        (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1}
        (AffineSpace (ULift.{u} (Fin 1)) X'))
        (ProEtale.constantIntIsoComparisonUpperStar (AffineSpace (ULift.{u} (Fin 1)) X'))
        ((Etale.upperStar AddCommGrpCat.{u + 1} (purityLineProjection X')).map ((Etale.upperStar
          AddCommGrpCat.{u + 1} v).map a))) := by
  sorry

end WeilConjectures
