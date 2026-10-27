module
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.ExchangeFunctoriality
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.Paper.MixedCompactSupportExchangeData
public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.FiniteStagePairCategory
public import Sheaf.Paper.PbcFiniteCompletedCoefficientMap
public import Sheaf.Paper.CompleteCompactSupportProetale
import Sheaf.Paper.RelativeCompactSupportPasting
public import Sheaf.Paper.FrobeniusGeometricExchange
public import Sheaf.Paper.SystemOperationExchangeRealization
public import Sheaf.Paper.SemilinearCompactSupportCoefficientTransport
public import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.FiniteCompactSupportEvaluationRefinement
import Sheaf.CategoryTheory.SemilinearScalarLocalization
import Sheaf.Paper.PbcDescentFunctors
public import Sheaf.SixFunctors.FrobeniusSquareCartesian
import Sheaf.Paper.IntegralFinitePullbackComposition
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Compactification.BaseChange
import Sheaf.Paper.FiniteExtensionCompactSupportBaseChange
import Sheaf.Paper.QbarCompactSupportBaseChange
/-! # Mixed geometric base change and semilinear exchange
Source: current blueprint prop-pur-weil-equivariance-compatibilities.proof.md,
constituent compatibility assembly; Stacks 0E47, 09AE
(blueprint: lem-pur-weil-basechange-semilinear-pasting).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures WeilConjectures.FrobeniusExchange
namespace WeilConjectures.MixedSemilinear
/-- The finite coefficient quotient in the fixed positive level is finite.
Source: purity conventions (blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
instance finiteRing (P : PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
/-- The typed mixed-pasting equation. The arguments will always be the specified
proper/open composites, and cX,cY their canonical pullback comparisons.
Source: constituent base-change equation, Stacks 0E47
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
def pathPair {CX CY CX' CY' : Type w}
    [Category.{v} CX] [Category.{v} CY] [Category.{v} CX'] [Category.{v} CY']
    (F : CX ⥤ CY) (F' : CX' ⥤ CY') (QX : CX ⥤ CX') (QY : CY ⥤ CY')
    (GX : CX ⥤ CX) (GY : CY ⥤ CY) (GX' : CX' ⥤ CX') (GY' : CY' ⥤ CY')
    (B : F ⋙ QY ⟶ QX ⋙ F') (e : F ⋙ GY ⟶ GX ⋙ F)
    (e' : F' ⋙ GY' ⟶ GX' ⋙ F')
    (cX : GX ⋙ QX ≅ QX ⋙ GX') (cY : GY ⋙ QY ≅ QY ⋙ GY')
    (M : CX) :
    (QY.obj (GY.obj (F.obj M)) ⟶ F'.obj (GX'.obj (QX.obj M))) ×
      (QY.obj (GY.obj (F.obj M)) ⟶ F'.obj (GX'.obj (QX.obj M))) :=
  (QY.map (e.app M) ≫ B.app (GX.obj M) ≫ F'.map (cX.hom.app M),
    cY.hom.app (F.obj M) ≫ GY'.map (B.app M) ≫ e'.app (QX.obj M))
/-- Select either actual composite, to state both refinement squares uniformly.
Source: the two paths in the blueprint display
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
def selectPath {C : Type w} [Category.{v} C] {A B : C}
    (paths : (A ⟶ B) × (A ⟶ B)) (b : Bool) : A ⟶ B :=
  if b then paths.1 else paths.2
/-- The retained geometric square and compatible compactifications. The middle map
is a map of k0-models. The two pullback witnesses specify that c' is a base change
of c, including its open part; they impose no linearity on geometric Frobenius.
Source: constituent base-change setup, Stacks 0E47
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
structure Square (D : FiniteFieldDatum.{u}) where
  X₀ : Over (Spec (.of D.k₀))
  Y₀ : Over (Spec (.of D.k₀))
  X₀' : Over (Spec (.of D.k₀))
  Y₀' : Over (Spec (.of D.k₀))
  [xft : LocallyOfFiniteType X₀.hom]
  [yft : LocallyOfFiniteType Y₀.hom]
  [xft' : LocallyOfFiniteType X₀'.hom]
  [yft' : LocallyOfFiniteType Y₀'.hom]
  [xqc : QuasiCompact X₀.hom]
  [yqc : QuasiCompact Y₀.hom]
  [xqc' : QuasiCompact X₀'.hom]
  [yqc' : QuasiCompact Y₀'.hom]
  [xs : IsSeparated X₀.hom]
  [ys : IsSeparated Y₀.hom]
  [xs' : IsSeparated X₀'.hom]
  [ys' : IsSeparated Y₀'.hom]
  f₀ : X₀ ⟶ Y₀
  f₀' : X₀' ⟶ Y₀'
  u₀ : X₀' ⟶ X₀
  v₀ : Y₀' ⟶ Y₀
  square : ChosenCartesianSquare u₀.left f₀'.left f₀.left v₀.left
  [fs : IsSeparated f₀.left]
  [fs' : IsSeparated f₀'.left]
  [us : IsSeparated u₀.left]
  [vs : IsSeparated v₀.left]
  [fft : LocallyOfFiniteType f₀.left]
  [fft' : LocallyOfFiniteType f₀'.left]
  [uft : LocallyOfFiniteType u₀.left]
  [vft : LocallyOfFiniteType v₀.left]
  [fqc : QuasiCompact f₀.left]
  [fqc' : QuasiCompact f₀'.left]
  [uqc : QuasiCompact u₀.left]
  [vqc : QuasiCompact v₀.left]
  c₀ : Compactification f₀.left
  c₀' : Compactification f₀'.left
  z₀ : zlCompactificationMiddle D f₀' c₀' ⟶ zlCompactificationMiddle D f₀ c₀
  properSquare : IsPullback (fiberMap D z₀)
    (geometricCompactification D f₀' c₀').g
    (geometricCompactification D f₀ c₀).g (fiberMap D v₀)
  openSquare : IsPullback (fiberMap D u₀)
    (geometricCompactification D f₀' c₀').i
    (geometricCompactification D f₀ c₀).i (fiberMap D z₀)
attribute [instance] Square.xft Square.yft Square.xft' Square.yft'
  Square.xqc Square.yqc Square.xqc' Square.yqc' Square.xs Square.ys Square.xs' Square.ys'
  Square.fs Square.fs' Square.us Square.vs Square.fft Square.fft' Square.uft Square.vft
  Square.fqc Square.fqc' Square.uqc Square.vqc
/-- Turn the actual pullback witness into the dependency's chosen square.
Source: Stacks 001U, projection-preserving identification
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
def chosen {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback a b f g) :
    ChosenCartesianSquare a b f g where
  w := s.w
  isoPullback := s.isoPullback
  hom_fst := s.isoPullback_hom_fst
  hom_snd := s.isoPullback_hom_snd
/-- Retain the open-immersion structures in the same chosen square.
Source: Stacks 03DI (blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
def chosenOpen {U' U T' T : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ T'}
    {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j g) : OpenImmersionSquare a j' j g where
  toChosenCartesianSquare := chosen s
  isOpenImmersion := inferInstance
  isOpenImmersion' := inferInstance
section Finite
open AlgebraicGeometry.ProEtale.ConstantCompactificationExchange
open AlgebraicGeometry.ProEtale.RelativeCompactSupport
variable (P : PurityFiniteSetting.{u}) (S : Square P.field)
/-- The finite mixed equation, with the existing ordinary proper/open exchange.
Source: constituent base-change equation, Stacks 0E47, 09AE
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
def finitePaths (M : DerivedCategory
    (AlgebraicGeometry.ProEtale.StrictTower.Modules P.Coefficient
      (P.field.geometricFiber S.X₀).left)) :=
  pathPair
    (ordinaryJ P.Coefficient (geometricCompactification P.field S.f₀ S.c₀).i ⋙
      ordinaryR P.Coefficient (geometricCompactification P.field S.f₀ S.c₀).g)
    (ordinaryJ P.Coefficient (geometricCompactification P.field S.f₀' S.c₀').i ⋙
      ordinaryR P.Coefficient (geometricCompactification P.field S.f₀' S.c₀').g)
    (ordinaryG P.Coefficient (fiberMap P.field S.u₀))
    (ordinaryG P.Coefficient (fiberMap P.field S.v₀))
    (ordinaryG P.Coefficient (galois P.field S.X₀))
    (ordinaryG P.Coefficient (galois P.field S.Y₀))
    (ordinaryG P.Coefficient (galois P.field S.X₀'))
    (ordinaryG P.Coefficient (galois P.field S.Y₀'))
    (MixedCompactSupportData.ordinaryExchange P.Coefficient
      (geometricCompactification P.field S.f₀ S.c₀)
      (geometricCompactification P.field S.f₀' S.c₀')
      (fiberMap P.field S.v₀) (fiberMap P.field S.u₀) (fiberMap P.field S.z₀)
      S.properSquare S.openSquare)
    (MixedCompactSupportData.ordinaryExchange P.Coefficient
      (geometricCompactification P.field S.f₀ S.c₀)
      (geometricCompactification P.field S.f₀ S.c₀)
      (galois P.field S.Y₀) (galois P.field S.X₀)
      (galois P.field (zlCompactificationMiddle P.field S.f₀ S.c₀))
      (P.field.frobenius_square_cartesian _ _
        (zlCompactificationProper P.field S.f₀ S.c₀)).2.2.2.2.2.1
      (P.field.frobenius_square_cartesian _ _
        (zlCompactificationOpen P.field S.f₀ S.c₀)).2.2.2.2.2.1)
    (MixedCompactSupportData.ordinaryExchange P.Coefficient
      (geometricCompactification P.field S.f₀' S.c₀')
      (geometricCompactification P.field S.f₀' S.c₀')
      (galois P.field S.Y₀') (galois P.field S.X₀')
      (galois P.field (zlCompactificationMiddle P.field S.f₀' S.c₀'))
      (P.field.frobenius_square_cartesian _ _
        (zlCompactificationProper P.field S.f₀' S.c₀')).2.2.2.2.2.1
      (P.field.frobenius_square_cartesian _ _
        (zlCompactificationOpen P.field S.f₀' S.c₀')).2.2.2.2.2.1)
    (sourceSquare P.Coefficient (galois P.field S.X₀') (fiberMap P.field S.u₀)
      (fiberMap P.field S.u₀) (galois P.field S.X₀)
      (P.field.frobenius_square_cartesian _ _ S.u₀).2.2.2.2.1)
    (sourceSquare P.Coefficient (galois P.field S.Y₀') (fiberMap P.field S.v₀)
      (fiberMap P.field S.v₀) (galois P.field S.Y₀)
      (P.field.frobenius_square_cartesian _ _ S.v₀).2.2.2.2.1) M
/-- The canonical ordinary refinement arrow: identity, the recorded clopen gamma,
then the direct-image compositor. No Cartesian witness is imposed on the refinement.
Source: Stacks 0F7B, 0F7F, the refinement clause
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
def finiteRefinement {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (ρ : c.Refinement d)
    (M : DerivedCategory (AlgebraicGeometry.ProEtale.StrictTower.Modules P.Coefficient X)) :=
  (AlgebraicGeometry.ProEtale.StrictTower.FiniteCompactSupport.ordinaryC
    P.Coefficient ρ).app M
end Finite
attribute [irreducible] finitePaths finiteRefinement
section Systems
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
/-- The existing quotient rings with their canonical spectral norm supplied explicitly.
The norm adds no hypothesis to the finite algebraic coefficient setting.
Source: Zheng 4.10 (blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
abbrev fixedQuotientRings :=
  letI := spectralNorm.normedField ℚ_[l] E
  letI := spectralNorm.normedAlgebra ℚ_[l] E
  CompactSupportCondensedRealization.quotientRings l E
/-- The existing adjacent quotient maps with the same canonical spectral norm.
Source: Zheng 4.10 (blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
abbrev fixedQuotientMaps :=
  letI := spectralNorm.normedField ℚ_[l] E
  letI := spectralNorm.normedAlgebra ℚ_[l] E
  CompactSupportCondensedRealization.quotientMaps l E
/-- Alias of the published whole-system P operation at the fixed quotient coefficients.
Source: Zheng 4.10 (blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
abbrev strictPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.P
    (fixedQuotientRings l E)
    (fixedQuotientMaps l E) f
/-- Alias of the published whole-system R operation at the fixed quotient coefficients.
Source: Zheng 4.10 (blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
abbrev strictPush {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.R
    (fixedQuotientRings l E)
    (fixedQuotientMaps l E) f
/-- Alias of the published whole-system J operation at the fixed quotient coefficients.
Source: Zheng 4.10 (blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
abbrev strictOpen {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.J
    (fixedQuotientRings l E)
    (fixedQuotientMaps l E) f
/-- Alias of the section-normalized whole-system pullback square.
Source: Stacks 07A7 (blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
abbrev strictSquare {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.squareP
    (fixedQuotientRings l E)
    (fixedQuotientMaps l E) k r p i h
/-- The proper mate followed by the normalized open comparison on whole strict
quotient systems. It is constructed before finite evaluation and before derived limit.
Source: Stacks 0E47; Zheng 4.10
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
def systemH {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (a : Y' ⟶ Y) (x : X' ⟶ X) (z : c'.Z ⟶ c.Z)
    (sp : IsPullback z c'.g c.g a) (sj : IsPullback x c'.i c.i z) :
    (strictOpen l E c.i ⋙ strictPush l E c.g) ⋙
        strictPull l E a ⟶
      strictPull l E x ⋙
        (strictOpen l E c'.i ⋙ strictPush l E c'.g) :=
  Functor.whiskerLeft (strictOpen l E c.i)
      (AlgebraicGeometry.ProEtale.SemilinearProperOpen.exchange
        (fixedQuotientRings l E)
        (fixedQuotientMaps l E) z c'.g c.g a sp.w) ≫
    Functor.whiskerRight
      (AlgebraicGeometry.ProEtale.SemilinearProperOpen.beta
        (fixedQuotientRings l E)
        (fixedQuotientMaps l E) x c'.i c.i z sj.w sj).hom
      (strictPush l E c'.g)
/-- The specified strict-system refinement, formed before evaluation or derived limit.
Source: Stacks 0F7B, 0F7F, proper/open refinement comparison
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
def strictRefinement {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (ρ : c.Refinement d)
    (M : coefficientSequenceDerived l E X) :=
  letI : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  let C := fixedQuotientRings l E
  let τ := fixedQuotientMaps l E
  (strictPush l E d.g).map
    ((strictOpen l E d.i).map
        ((AlgebraicGeometry.ProEtale.SemilinearProperOpen.sId C τ X).inv.app M) ≫
      (AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma C τ c.i (𝟙 X) ρ.hom d.i
        (ρ.i_hom.trans (Category.id_comp _).symm)).app M) ≫
    (AlgebraicGeometry.ProEtale.SemilinearProperOpen.sComp C τ ρ.hom d.g).hom.app
      ((strictOpen l E c.i).obj M) ≫
    (eqToIso (congrArg (strictPush l E) ρ.hom_g)).hom.app
      ((strictOpen l E c.i).obj M)
end Systems
/-- The mixed equation on actual strict quotient systems before derived limit.
Source: constituent base-change equation, Stacks 0E47, 09AE
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
def strictPaths (P : PurityFiniteSetting.{u}) (S : Square P.field)
    (M : coefficientSequenceDerived P.coefficients.l P.extension
      (P.field.geometricFiber S.X₀).left) :=
  pathPair
    (strictOpen P.coefficients.l P.extension
      (geometricCompactification P.field S.f₀ S.c₀).i ⋙
      strictPush P.coefficients.l P.extension (geometricCompactification P.field S.f₀ S.c₀).g)
    (strictOpen P.coefficients.l P.extension
      (geometricCompactification P.field S.f₀' S.c₀').i ⋙
      strictPush P.coefficients.l P.extension (geometricCompactification P.field S.f₀' S.c₀').g)
    (strictPull P.coefficients.l P.extension (fiberMap P.field S.u₀))
    (strictPull P.coefficients.l P.extension (fiberMap P.field S.v₀))
    (strictPull P.coefficients.l P.extension (galois P.field S.X₀))
    (strictPull P.coefficients.l P.extension (galois P.field S.Y₀))
    (strictPull P.coefficients.l P.extension (galois P.field S.X₀'))
    (strictPull P.coefficients.l P.extension (galois P.field S.Y₀'))
    (systemH P.coefficients.l P.extension (geometricCompactification P.field S.f₀ S.c₀)
      (geometricCompactification P.field S.f₀' S.c₀')
      (fiberMap P.field S.v₀) (fiberMap P.field S.u₀) (fiberMap P.field S.z₀)
      S.properSquare S.openSquare)
    (systemH P.coefficients.l P.extension (geometricCompactification P.field S.f₀ S.c₀)
      (geometricCompactification P.field S.f₀ S.c₀)
      (galois P.field S.Y₀) (galois P.field S.X₀)
      (galois P.field (zlCompactificationMiddle P.field S.f₀ S.c₀))
      (P.field.frobenius_square_cartesian _ _
        (zlCompactificationProper P.field S.f₀ S.c₀)).2.2.2.2.2.1
      (P.field.frobenius_square_cartesian _ _
        (zlCompactificationOpen P.field S.f₀ S.c₀)).2.2.2.2.2.1)
    (systemH P.coefficients.l P.extension (geometricCompactification P.field S.f₀' S.c₀')
      (geometricCompactification P.field S.f₀' S.c₀')
      (galois P.field S.Y₀') (galois P.field S.X₀')
      (galois P.field (zlCompactificationMiddle P.field S.f₀' S.c₀'))
      (P.field.frobenius_square_cartesian _ _
        (zlCompactificationProper P.field S.f₀' S.c₀')).2.2.2.2.2.1
      (P.field.frobenius_square_cartesian _ _
        (zlCompactificationOpen P.field S.f₀' S.c₀')).2.2.2.2.2.1)
    (strictSquare P.coefficients.l P.extension
      (galois P.field S.X₀') (fiberMap P.field S.u₀)
      (fiberMap P.field S.u₀) (galois P.field S.X₀)
      (P.field.frobenius_square_cartesian _ _ S.u₀).2.2.2.2.1)
    (strictSquare P.coefficients.l P.extension
      (galois P.field S.Y₀') (fiberMap P.field S.v₀)
      (fiberMap P.field S.v₀) (galois P.field S.Y₀)
      (P.field.frobenius_square_cartesian _ _ S.v₀).2.2.2.2.1) M
attribute [irreducible] strictPaths strictRefinement
section Completed
variable (P : PurityFiniteSetting.{u}) (S : Square P.field)
/-- The actual integral coefficient datum belonging to the fixed finite setting.
Source: purity conventions and the integral clause of exchange functoriality
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
abbrev datum := pbcIntegralDatum P.coefficients.l P.extension
/-- Canonical completed pullback square with independent corners.
Source: Stacks 099N, the unit-normalized completed pullback compositor
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
def completedSquare {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    (datum P).completedPull i ⋙ (datum P).completedPull r ≅
      (datum P).completedPull p ⋙ (datum P).completedPull k :=
  ((datum P).completedPullComp r i).symm ≪≫
    eqToIso (congrArg (fun f ↦ (datum P).completedPull f) h.symm) ≪≫
    (datum P).completedPullComp k p
/-- The specified completed compactification exchange, retaining its complete input.
Source: blueprint, definition of completed compact-support exchange, Stacks 099N
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
def completedH {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    [QuasiCompact f] (c : Compactification f) (c' : Compactification f')
    (a : Y' ⟶ Y) (x : X' ⟶ X) (z : c'.Z ⟶ c.Z)
    (sp : IsPullback z c'.g c.g a) (sj : IsPullback x c'.i c.i z)
    (r : ℕ) (q : Fin r → PbcIntegralRing P.coefficients.l P.extension)
    (hq : Ideal.span (Set.range q) = (datum P).ideal)
    (K : (cbcCompleteProperty (datum P) X r q hq).FullSubcategory) :
    ((datum P).completedPull a).obj ((cbcSupport (datum P) c).obj K.obj) ⟶
      (cbcSupport (datum P) c').obj (((datum P).completedPull x).obj K.obj) :=
  cbcExchange (datum P) c c' z (chosen sp) (chosenOpen sj) r q hq K
/-- The two actual paths have the common source QY GY F K.
Source: the source endpoint in the mixed-pasting display
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
abbrev completedSource
    (K : (datum P).derived (P.field.geometricFiber S.X₀).left) :=
  ((datum P).completedPull (fiberMap P.field S.v₀)).obj
    (((datum P).completedPull (galois P.field S.Y₀)).obj
      ((cbcSupport (datum P) (geometricCompactification P.field S.f₀ S.c₀)).obj K))
/-- The common target F' GX' QX K, with the target pullback comparison inserted.
Source: the target endpoint in the mixed-pasting display
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
abbrev completedTarget
    (K : (datum P).derived (P.field.geometricFiber S.X₀).left) :=
  (cbcSupport (datum P) (geometricCompactification P.field S.f₀' S.c₀')).obj
    (((datum P).completedPull (galois P.field S.X₀')).obj
      (((datum P).completedPull (fiberMap P.field S.u₀)).obj K))
/-- The left path QY(e) then B(GX K), followed by the canonical target comparison.
Source: mixed-pasting display of the blueprint auxiliary, Stacks 0E47
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
def completedLeft (r : ℕ) (q : Fin r → PbcIntegralRing P.coefficients.l P.extension)
    (hq : Ideal.span (Set.range q) = (datum P).ideal)
    (K : (cbcCompleteProperty (datum P)
      (P.field.geometricFiber S.X₀).left r q hq).FullSubcategory)
    (hG : cbcCompleteProperty (datum P) (P.field.geometricFiber S.X₀).left r q hq
      (((datum P).completedPull (galois P.field S.X₀)).obj K.obj)) :
    completedSource P S K.obj ⟶ completedTarget P S K.obj :=
  ((datum P).completedPull (fiberMap P.field S.v₀)).map
    (completedH P (geometricCompactification P.field S.f₀ S.c₀)
      (geometricCompactification P.field S.f₀ S.c₀)
      (galois P.field S.Y₀) (galois P.field S.X₀)
      (galois P.field (zlCompactificationMiddle P.field S.f₀ S.c₀))
      (P.field.frobenius_square_cartesian _ _
        (zlCompactificationProper P.field S.f₀ S.c₀)).2.2.2.2.2.1
      (P.field.frobenius_square_cartesian _ _
        (zlCompactificationOpen P.field S.f₀ S.c₀)).2.2.2.2.2.1 r q hq K) ≫
    completedH P (geometricCompactification P.field S.f₀ S.c₀)
      (geometricCompactification P.field S.f₀' S.c₀')
      (fiberMap P.field S.v₀) (fiberMap P.field S.u₀) (fiberMap P.field S.z₀)
      S.properSquare S.openSquare r q hq
      ⟨((datum P).completedPull (galois P.field S.X₀)).obj K.obj, hG⟩ ≫
    (cbcSupport (datum P) (geometricCompactification P.field S.f₀' S.c₀')).map
      ((completedSquare P (galois P.field S.X₀') (fiberMap P.field S.u₀)
        (fiberMap P.field S.u₀) (galois P.field S.X₀)
        (P.field.frobenius_square_cartesian _ _ S.u₀).2.2.2.2.1).hom.app K.obj)
/-- The right path, including the canonical source pullback comparison.
Source: mixed-pasting display of the blueprint auxiliary, Stacks 0E47
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
def completedRight (r : ℕ) (q : Fin r → PbcIntegralRing P.coefficients.l P.extension)
    (hq : Ideal.span (Set.range q) = (datum P).ideal)
    (K : (cbcCompleteProperty (datum P)
      (P.field.geometricFiber S.X₀).left r q hq).FullSubcategory)
    (hQ : cbcCompleteProperty (datum P) (P.field.geometricFiber S.X₀').left r q hq
      (((datum P).completedPull (fiberMap P.field S.u₀)).obj K.obj)) :
    completedSource P S K.obj ⟶ completedTarget P S K.obj :=
  (completedSquare P (galois P.field S.Y₀') (fiberMap P.field S.v₀)
      (fiberMap P.field S.v₀) (galois P.field S.Y₀)
      (P.field.frobenius_square_cartesian _ _ S.v₀).2.2.2.2.1).hom.app
      ((cbcSupport (datum P) (geometricCompactification P.field S.f₀ S.c₀)).obj K.obj) ≫
    ((datum P).completedPull (galois P.field S.Y₀')).map
      (completedH P (geometricCompactification P.field S.f₀ S.c₀)
        (geometricCompactification P.field S.f₀' S.c₀')
        (fiberMap P.field S.v₀) (fiberMap P.field S.u₀) (fiberMap P.field S.z₀)
        S.properSquare S.openSquare r q hq K) ≫
    completedH P (geometricCompactification P.field S.f₀' S.c₀')
      (geometricCompactification P.field S.f₀' S.c₀')
      (galois P.field S.Y₀') (galois P.field S.X₀')
      (galois P.field (zlCompactificationMiddle P.field S.f₀' S.c₀'))
      (P.field.frobenius_square_cartesian _ _
        (zlCompactificationProper P.field S.f₀' S.c₀')).2.2.2.2.2.1
      (P.field.frobenius_square_cartesian _ _
        (zlCompactificationOpen P.field S.f₀' S.c₀')).2.2.2.2.2.1 r q hq
      ⟨((datum P).completedPull (fiberMap P.field S.u₀)).obj K.obj, hQ⟩
/-- The target geometric scheme is Noetherian by the published finite-type theorem.
Source: finite-type geometric-fiber conventions, Stacks 01T1
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
instance target_isNoetherian : IsNoetherian (P.field.geometricFiber S.Y₀').left :=
  @isNoetherian_of_locallyOfFiniteType _ _ (P.field.geometricFiber S.Y₀').hom
    (fiber_finiteType P.field S.Y₀').1 (fiber_finiteType P.field S.Y₀').2 inferInstance

/-- Inclusion of the fixed finite field into the actual common-stage category.
The coefficient shrink is transported by its canonical algebra equivalence; the
next functor is the published finite-stage inclusion, with no new arrow choices.
Source: blueprint common-stage clause, proper-base-change scalar system
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
def commonStageInclusion
    (hdim : ∃ n : ℕ, topologicalKrullDim (P.field.geometricFiber S.Y₀').left ≤ n)
    (hl : ∀ t : (P.field.geometricFiber S.Y₀').left,
      IsUnit (P.coefficients.l : (P.field.geometricFiber S.Y₀').left.presheaf.stalk t)) :
    PbcRationalDerivedCategory P.coefficients.l P.extension
      (P.field.geometricFiber S.Y₀').left hdim hl ⥤
        PbcFiniteStagePairCategory P.coefficients.l P.coefficients.Qbar
          (P.field.geometricFiber S.Y₀').left hdim hl :=
  letI : FiniteDimensional (Padic P.coefficients.l)
      (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar
        ⟨P.extension, P.finiteExtension⟩) :=
    pbcFiniteFieldFinite P.coefficients.l P.coefficients.Qbar
      ⟨P.extension, P.finiteExtension⟩
  @pbcRationalScalarExtension P.coefficients.l _ P.extension
      (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar
        ⟨P.extension, P.finiteExtension⟩) _ _ _ _ P.finiteExtension
      (pbcFiniteFieldFinite P.coefficients.l P.coefficients.Qbar
        ⟨P.extension, P.finiteExtension⟩)
      (Shrink.algEquiv (Padic P.coefficients.l) P.extension).symm.toAlgHom
      (P.field.geometricFiber S.Y₀').left _ hdim hl ⋙
    (pbcScalarSystem P.coefficients.l P.coefficients.Qbar
      (P.field.geometricFiber S.Y₀').left hdim hl).ι ⟨P.extension, P.finiteExtension⟩
attribute [irreducible] completedLeft completedRight completedH completedSquare
  commonStageInclusion

end Completed
section Completed
variable (P : PurityFiniteSetting.{u}) (S : Square P.field)
/-- The integral mixed identity and its scalar-localized/common-stage forms.
All endpoint constructibility, complete input, and origin witnesses are retained
from the supplied domains. The two localized components are the published raw
rationalizations, and their common-stage images use commonStageInclusion.
Source: blueprint mixed-pasting auxiliary, integral and field clauses
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
def CompletedAndFieldClaim : Prop :=
  ∀ (r : ℕ) (q : Fin r → PbcIntegralRing P.coefficients.l P.extension)
    (hq : Ideal.span (Set.range q) = (datum P).ideal)
    (K : (cbcCompleteProperty (datum P)
      (P.field.geometricFiber S.X₀).left r q hq).FullSubcategory)
    (_hK : PbcIsBoundedConstructibleComplete (P.field.geometricFiber S.X₀).left
      (datum P) K.obj)
    (hG : cbcCompleteProperty (datum P) (P.field.geometricFiber S.X₀).left r q hq
      (((datum P).completedPull (galois P.field S.X₀)).obj K.obj))
    (hQ : cbcCompleteProperty (datum P) (P.field.geometricFiber S.X₀').left r q hq
      (((datum P).completedPull (fiberMap P.field S.u₀)).obj K.obj)),
    completedLeft P S r q hq K hG = completedRight P S r q hq K hQ ∧
      ∀ (hSource : PbcIsBoundedConstructibleComplete
          (P.field.geometricFiber S.Y₀').left (datum P) (completedSource P S K.obj))
        (hTarget : PbcIsBoundedConstructibleComplete
          (P.field.geometricFiber S.Y₀').left (datum P) (completedTarget P S K.obj)),
        LiftedCbc.finiteExtensionRationalArrow P.coefficients.l P.extension hSource hTarget
            (completedLeft P S r q hq K hG) =
          LiftedCbc.finiteExtensionRationalArrow P.coefficients.l P.extension hSource hTarget
            (completedRight P S r q hq K hQ) ∧
        ∀ (hdim : ∃ n : ℕ, topologicalKrullDim (P.field.geometricFiber S.Y₀').left ≤ n)
          (hl : ∀ t : (P.field.geometricFiber S.Y₀').left,
            IsUnit (P.coefficients.l :
              (P.field.geometricFiber S.Y₀').left.presheaf.stalk t)),
          (commonStageInclusion P S hdim hl).map
              (LiftedCbc.finiteExtensionRationalArrow P.coefficients.l P.extension
                hSource hTarget (completedLeft P S r q hq K hG)) =
            (commonStageInclusion P S hdim hl).map
              (LiftedCbc.finiteExtensionRationalArrow P.coefficients.l P.extension
                hSource hTarget (completedRight P S r q hq K hQ))
/-- Change compactifications without changing the original geometric square.
Source: blueprint compactification-independence clause
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
def recompactify (c : Compactification S.f₀.left) (c' : Compactification S.f₀'.left)
    (z : zlCompactificationMiddle P.field S.f₀' c' ⟶
      zlCompactificationMiddle P.field S.f₀ c)
    (sp : IsPullback (fiberMap P.field z)
      (geometricCompactification P.field S.f₀' c').g
      (geometricCompactification P.field S.f₀ c).g (fiberMap P.field S.v₀))
    (sj : IsPullback (fiberMap P.field S.u₀)
      (geometricCompactification P.field S.f₀' c').i
      (geometricCompactification P.field S.f₀ c).i (fiberMap P.field z)) :
    Square P.field := { S with
      c₀ := c
      c₀' := c'
      z₀ := z
      properSquare := sp
      openSquare := sj }

/-- Each mixed path intertwines the prescribed compactification refinements.
The comparison at the source is QY GY(C), and that at the target is C'(GX' QX K).
Source: blueprint compactification-independence clause, Stacks 0F7F
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
def RefinementClaim : Prop :=
  ∀ (c : Compactification S.f₀.left) (c' : Compactification S.f₀'.left)
    (z : zlCompactificationMiddle P.field S.f₀' c' ⟶
      zlCompactificationMiddle P.field S.f₀ c)
    (sp : IsPullback (fiberMap P.field z)
      (geometricCompactification P.field S.f₀' c').g
      (geometricCompactification P.field S.f₀ c).g (fiberMap P.field S.v₀))
    (sj : IsPullback (fiberMap P.field S.u₀)
      (geometricCompactification P.field S.f₀' c').i
      (geometricCompactification P.field S.f₀ c).i (fiberMap P.field z))
    (ρ : (geometricCompactification P.field S.f₀ S.c₀).Refinement
      (geometricCompactification P.field S.f₀ c))
    (ρ' : (geometricCompactification P.field S.f₀' S.c₀').Refinement
      (geometricCompactification P.field S.f₀' c'))
    (_hc : ρ'.hom ≫ fiberMap P.field z = fiberMap P.field S.z₀ ≫ ρ.hom)
    (_hγ : galois P.field (zlCompactificationMiddle P.field S.f₀ S.c₀) ≫ ρ.hom =
      ρ.hom ≫ galois P.field (zlCompactificationMiddle P.field S.f₀ c))
    (_hγ' : galois P.field (zlCompactificationMiddle P.field S.f₀' S.c₀') ≫ ρ'.hom =
      ρ'.hom ≫ galois P.field (zlCompactificationMiddle P.field S.f₀' c'))
    (r : ℕ) (q : Fin r → PbcIntegralRing P.coefficients.l P.extension)
    (hq : Ideal.span (Set.range q) = (datum P).ideal)
    (K : (cbcCompleteProperty (datum P)
      (P.field.geometricFiber S.X₀).left r q hq).FullSubcategory)
    (_hK : PbcIsBoundedConstructibleComplete (P.field.geometricFiber S.X₀).left
      (datum P) K.obj)
    (hG : cbcCompleteProperty (datum P) (P.field.geometricFiber S.X₀).left r q hq
      (((datum P).completedPull (galois P.field S.X₀)).obj K.obj))
    (hQ : cbcCompleteProperty (datum P) (P.field.geometricFiber S.X₀').left r q hq
      (((datum P).completedPull (fiberMap P.field S.u₀)).obj K.obj)),
    (((datum P).completedPull (galois P.field S.Y₀)) ⋙
      (datum P).completedPull (fiberMap P.field S.v₀)).map
        (cbcRefinementMap (datum P) ρ K.obj) ≫ completedLeft P S r q hq K hG =
      completedLeft P (recompactify P S c c' z sp sj) r q hq K hG ≫
        cbcRefinementMap (datum P) ρ'
          (((datum P).completedPull (galois P.field S.X₀')).obj
            (((datum P).completedPull (fiberMap P.field S.u₀)).obj K.obj)) ∧
    (((datum P).completedPull (galois P.field S.Y₀)) ⋙
      (datum P).completedPull (fiberMap P.field S.v₀)).map
        (cbcRefinementMap (datum P) ρ K.obj) ≫ completedRight P S r q hq K hQ =
      completedRight P (recompactify P S c c' z sp sj) r q hq K hQ ≫
        cbcRefinementMap (datum P) ρ'
          (((datum P).completedPull (galois P.field S.X₀')).obj
            (((datum P).completedPull (fiberMap P.field S.u₀)).obj K.obj))
/-- Both paths commute with the prescribed finite and strict-system refinements.
The first comparison is the ordinary clopen gamma; the second is the whole-system
clopen gamma, prior to evaluation or limit. Origins in the finite clause are retained.
Source: Stacks 0F7B, 0F7F, blueprint refinement-independence clause
(blueprint: lem-pur-weil-basechange-semilinear-pasting). -/
def EarlyRefinementClaim : Prop :=
  ∀ (c : Compactification S.f₀.left) (c' : Compactification S.f₀'.left)
    (z : zlCompactificationMiddle P.field S.f₀' c' ⟶
      zlCompactificationMiddle P.field S.f₀ c)
    (sp : IsPullback (fiberMap P.field z)
      (geometricCompactification P.field S.f₀' c').g
      (geometricCompactification P.field S.f₀ c).g (fiberMap P.field S.v₀))
    (sj : IsPullback (fiberMap P.field S.u₀)
      (geometricCompactification P.field S.f₀' c').i
      (geometricCompactification P.field S.f₀ c).i (fiberMap P.field z))
    (ρ : (geometricCompactification P.field S.f₀ S.c₀).Refinement
      (geometricCompactification P.field S.f₀ c))
    (ρ' : (geometricCompactification P.field S.f₀' S.c₀').Refinement
      (geometricCompactification P.field S.f₀' c'))
    (_hc : ρ'.hom ≫ fiberMap P.field z = fiberMap P.field S.z₀ ≫ ρ.hom)
    (_hγ : galois P.field (zlCompactificationMiddle P.field S.f₀ S.c₀) ≫ ρ.hom =
      ρ.hom ≫ galois P.field (zlCompactificationMiddle P.field S.f₀ c))
    (_hγ' : galois P.field (zlCompactificationMiddle P.field S.f₀' S.c₀') ≫ ρ'.hom =
      ρ'.hom ≫ galois P.field (zlCompactificationMiddle P.field S.f₀' c'))
    , (∀ (M : (finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
          (P.field.geometricFiber S.X₀).left).FullSubcategory)
        (L : DerivedCategory.Plus
          (Sheaf (P.field.geometricFiber S.X₀).left.smallEtaleTopology
            (ModuleCat.{u + 1} P.Coefficient)))
        (_α : (origin P.Ring (P.field.geometricFiber S.X₀).left).obj L.obj ≅ M.obj)
        (b : Bool),
      (AlgebraicGeometry.ProEtale.ConstantCompactificationExchange.ordinaryG P.Coefficient
          (galois P.field S.Y₀) ⋙
        AlgebraicGeometry.ProEtale.ConstantCompactificationExchange.ordinaryG P.Coefficient
          (fiberMap P.field S.v₀)).map (finiteRefinement P ρ M.obj) ≫
          selectPath (finitePaths P S M.obj) b =
        selectPath (finitePaths P (recompactify P S c c' z sp sj) M.obj) b ≫
          finiteRefinement P ρ'
            ((AlgebraicGeometry.ProEtale.ConstantCompactificationExchange.ordinaryG P.Coefficient
              (galois P.field S.X₀')).obj
              ((AlgebraicGeometry.ProEtale.ConstantCompactificationExchange.ordinaryG P.Coefficient
                (fiberMap P.field S.u₀)).obj M.obj))) ∧
      (∀ (M : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension
          (P.field.geometricFiber S.X₀).left) (b : Bool),
        (strictPull P.coefficients.l P.extension (galois P.field S.Y₀) ⋙
          strictPull P.coefficients.l P.extension (fiberMap P.field S.v₀)).map
            (strictRefinement P.coefficients.l P.extension ρ
              ((reduction P.coefficients.l P.extension
                (P.field.geometricFiber S.X₀).left).obj M.obj)) ≫
          selectPath (strictPaths P S ((reduction P.coefficients.l P.extension
            (P.field.geometricFiber S.X₀).left).obj M.obj)) b =
        selectPath (strictPaths P (recompactify P S c c' z sp sj)
          ((reduction P.coefficients.l P.extension
            (P.field.geometricFiber S.X₀).left).obj M.obj)) b ≫
          strictRefinement P.coefficients.l P.extension ρ'
            ((strictPull P.coefficients.l P.extension (galois P.field S.X₀')).obj
              ((strictPull P.coefficients.l P.extension (fiberMap P.field S.u₀)).obj
                ((reduction P.coefficients.l P.extension
                  (P.field.geometricFiber S.X₀).left).obj M.obj))))
end Completed

/-- Mixed geometric base change and semilinear geometric-Frobenius pasting.
The finite clause is restricted to D^b_ctf; the strict clause is on the actual
coherent quotient reductions of integral D^b_ctf objects, before derived limit.
The final clause is the actual completed equation and its prescribed field transports.
The quantifier over Square retains every compatible compactification and every allowed
base change. Independence uses precisely the refinement comparisons of fix-lem-exchanges.
Source: current blueprint prop-pur-weil-equivariance-compatibilities.proof.md,
constituent compatibility assembly; Stacks 0E47, 09AE
(blueprint: lem-pur-weil-basechange-semilinear-pasting).
Proof: (1) Frobenius squares commute and are Cartesian; their iterated pullbacks
are identified by their unique projection-preserving isomorphisms. Pullback
compositors give the displayed endpoint comparisons. (2) Apply relative compact
support pasting along (gY,v) and (v,gY'), both yielding the same composite square.
(3) Finite evaluation/refinement normalization identifies its proper/open factors
with the specified finite mates on the supplied etale-origin domain. Intermediate
compactification comparisons cancel and their endpoint cocycle fixes the result.
(4) Strict reduction normalization gives the same equation on simultaneous quotient
systems, including their transitions, before Rlim. Its coherent corner comparisons
and refinement equations identify the two substitutions. (5) Normalized limit
realization carries the strict equation to the actual completed equation, and
reflects equality on these complete inputs. It carries the refinement equations too.
(6) Raw scalar localization preserves both composites. At algebraically closed
coefficients, represent the object and both paths over a common finite stage;
apply the stage inclusion. The scalar-extension and refinement cocycles remove the
chosen stage and lattice. None of these steps assumes k-linearity of galois maps. -/
theorem weilBaseChangeSemilinearPasting (P : PurityFiniteSetting.{u}) (S : Square P.field) :
    (∀ M : (finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.field.geometricFiber S.X₀).left).FullSubcategory,
      ∀ (L : DerivedCategory.Plus
          (Sheaf (P.field.geometricFiber S.X₀).left.smallEtaleTopology
            (ModuleCat.{u + 1} P.Coefficient)))
        (_α : (origin P.Ring (P.field.geometricFiber S.X₀).left).obj L.obj ≅ M.obj),
        (finitePaths P S M.obj).1 = (finitePaths P S M.obj).2) ∧
    (∀ M : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension
      (P.field.geometricFiber S.X₀).left,
      (strictPaths P S ((reduction P.coefficients.l P.extension
        (P.field.geometricFiber S.X₀).left).obj M.obj)).1 =
      (strictPaths P S ((reduction P.coefficients.l P.extension
        (P.field.geometricFiber S.X₀).left).obj M.obj)).2) ∧
    CompletedAndFieldClaim P S ∧ EarlyRefinementClaim P S ∧ RefinementClaim P S := by
  sorry
end WeilConjectures.MixedSemilinear
