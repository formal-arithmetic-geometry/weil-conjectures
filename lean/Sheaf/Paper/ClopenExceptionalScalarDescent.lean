module

public import Sheaf.Paper.ClopenSystemIntegralRealization
public import Sheaf.Paper.FiniteClopenExceptionalRestriction
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.ConstantCoefficientScalarNormalization
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.ClopenCounitAdjointComparison
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.EtaleCoefficientSystemAdjoint
import Sheaf.Paper.ClopenStrictSystemSupport
import Sheaf.NumberTheory.Padics.LocalFieldCoefficientStages
import Sheaf.Paper.EtaleSystemCofinalMate
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.CategoryTheory.FiniteFreeStrictTowerTransport
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.FiniteClopenDerivedDecomposition
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.EtaleSystemCoefficientProjection
import Sheaf.CategoryTheory.SemilinearScalarLocalization

/-! # Scalar coherence and descent of the clopen exceptional comparison

Source: Zheng, Construction 5.15, Lemmas 5.16 and 5.22, pp. 35--36;
the coefficient-unit clause of the current blueprint def-pur-section-invariant
(blueprint: lem-pur-clopen-exceptional-scalar-descent).

The previously published clopen comparison records are reused, including their
strict-system, total-limit and rational pure-tensor normalizations. No exceptional
functor or coefficient category is defined a second time.

Main declarations:
* `ClopenStrictScalarSquare`: the section-normalized left square and its right mate.
* `clopenExceptionalScalarDescent_system`: the square on actual derived systems.
* `ClopenBaseScalarLaws` and `ClopenScalarLaws`: integral/rational scalar equations.
* `ClopenBaseRealizationLaws`: identification with the actual total-limit arrow.
* `clopenExceptionalScalarDescent`: scalar-compatible common-stage descent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [local irreducible] HasDerivedCategory.standard
universe u w v z
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

section Strict
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O']
  {ell : O} {mu : O'} {phi : O →+* O'} {index : ℕ →o ℕ}
  {a : StrictEtaleCoefficientChange O O' ell mu phi index}
  {X Y Xi : Scheme.{u}} {g : X ⟶ Y} {c : Compactification g}
  {j : Xi ⟶ X} [IsOpenImmersion j] [IsClosedImmersion j]
  {SA : StrictEtaleCompactSupport O ell c}
  {GA : StrictEtaleExceptionalAdjoint O ell c SA}
  {SiA : StrictEtaleCompactSupport O ell (c.precomp j)}
  {GiA : StrictEtaleExceptionalAdjoint O ell (c.precomp j) SiA}
  {SB : StrictEtaleCompactSupport O' mu c}
  {GB : StrictEtaleExceptionalAdjoint O' mu c SB}
  {SiB : StrictEtaleCompactSupport O' mu (c.precomp j)}
  {GiB : StrictEtaleExceptionalAdjoint O' mu (c.precomp j) SiB}
  (RA : StrictClopenExceptionalComparison O ell c j SA GA SiA GiA)
  (RB : StrictClopenExceptionalComparison O' mu c j SB GB SiB GiB)
  (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
  (TY : StrictEtaleCoefficientTransport a Y SA.PY SB.PY)
  (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
  (Ti : StrictEtaleCoefficientTransport a Xi SiA.PX SiB.PX)
  (TYi : StrictEtaleCoefficientTransport a Y SiA.PY SiB.PY)
  (TZi : StrictEtaleCoefficientTransport a c.Z SiA.PZ SiB.PZ)

/-- Identify the two presentations of scalar extension on the shared target.
The unit equation specifies the ordinary balancing map; the second equation
specifies its localization on complexes, rather than its finite evaluations.
Source: Zheng Construction 4.1 and the common proper part in Construction 5.15
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
structure ClopenScalarTargetIdentification where
  ordinary : TY.ordinary ≅ TYi.ordinary
  derived : TY.derived ≅ TYi.derived
  unit : ∀ n M,
    (TY.unit n).app M ≫
      (SheafOfModules.toSheaf.{u + 1} _).map
        ((SheafOfModules.coefficientEvaluation (J := Y.smallEtaleTopology)
          (O := O') (ell := mu) n).map (ordinary.hom.app M)) = (TYi.unit n).app M
  representative : ∀ K,
    derived.hom.app (DerivedCategory.Q.obj K) ≫ TYi.factors.hom.app K =
      TY.factors.hom.app K ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app K)

/-- Both sides of the scalar square, with the left side and its prescribed right
mate retained. Insertion is the mate of the section-normalized restriction square.
The target identification only reconciles the two evaluation packages on Y.
Source: Zheng Construction 5.15, Lemmas 5.16 and 5.22; Stacks 03DI, 03DJ
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
structure ClopenStrictScalarSquare
    (sg : StrictEtaleExceptionalTransport a c SA SB TX TY TZ GA GB)
    (si : StrictEtaleExceptionalTransport a (c.precomp j) SiA SiB Ti TYi TZi GiA GiB)
    (r : StrictEtaleInverseTransport Ti TX RA.restriction RB.restriction
      RA.derivedRestriction.system RB.derivedRestriction.system) where
  target : ClopenScalarTargetIdentification TY TYi
  insertion : RA.derivedRestriction.system.direct ⋙ TX.derived ≅
    Ti.derived ⋙ RB.derivedRestriction.system.direct
  insertion_mate : insertion.hom =
    (mateEquiv RA.derivedRestriction.system.adjunction
      RB.derivedRestriction.system.adjunction (.mk _ _ _ _ r.derived.hom)).natTrans
  left_square : ∀ M,
    TY.derived.map (RA.system.compactSupport.hom.app M) ≫
        target.derived.hom.app (SiA.functor.obj M) ≫ si.val.compact.projection.hom.app M =
      sg.val.compact.projection.hom.app (RA.derivedRestriction.system.direct.obj M) ≫
        SB.functor.map (insertion.hom.app M) ≫
          RB.system.compactSupport.hom.app (Ti.derived.obj M)
  right_square : ∀ L,
    Ti.derived.map (RA.system.comparison.hom.app L) ≫ si.right.hom.app L =
      r.derived.inv.app (GA.right.obj L) ≫
        RB.derivedRestriction.system.inverse.map (sg.right.hom.app L) ≫
        RB.system.comparison.hom.app (TY.derived.obj L) ≫
        GiB.right.map (target.derived.hom.app L)

/-- The actual derived-system scalar square, including cofinal coefficient changes.
The supplied data are precisely the prescribed comparisons, not an assumed square.
Source: Zheng Construction 5.15 and Lemmas 5.16, 5.22, pp. 35--36
(blueprint: lem-pur-clopen-exceptional-scalar-descent).

Proof, node steps 1--4: tensor the insertion counit, identity on this component
and zero elsewhere. The open compositor sends m tensor b to that same generator
on the component and zero off it; these formulas commute with restrictions and
quotient transitions. Transpose the two compact-support scalar composites under
coefficient extension/restriction. Their proper parts coincide because c and
c.precomp j share the same proper map; their open parts are the sectionwise
identity just checked. Injectivity of transposition gives left_square on strict
systems and then on complexes. The counit-normalized rho is the right mate of
inverse b, and sg and si are the prescribed mates of inverse projection. Mate
pasting gives right_square, including the insertion adjunction and its counit.
The tensor unit proves the identity case; multiplication of tensor factors proves
successive extension coherence. The same equations commute with restriction to
e(n+1)-1, so they include the cofinal ramified ideal identification. No faithfulness
of evaluations of arbitrary derived-system morphisms is used. -/
theorem clopenExceptionalScalarDescent_system
    (_NA : StrictClopenCompactSupportNormalization O ell c j SA GA SiA GiA RA)
    (_NB : StrictClopenCompactSupportNormalization O' mu c j SB GB SiB GiB RB)
    (sg : StrictEtaleExceptionalTransport a c SA SB TX TY TZ GA GB)
    (si : StrictEtaleExceptionalTransport a (c.precomp j) SiA SiB Ti TYi TZi GiA GiB)
    (r : StrictEtaleInverseTransport Ti TX RA.restriction RB.restriction
      RA.derivedRestriction.system RB.derivedRestriction.system) :
    Nonempty (ClopenStrictScalarSquare RA RB TX TY TZ Ti TYi TZi sg si r) := by
  sorry
end Strict

/-- The clopen component with its induced k-structure (an abbreviation of Over.mk).
Source: Zheng Construction 5.15
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
abbrev clopenScalarComponent (P : PurityFiniteSetting.{u})
    (X : Over (Spec (.of P.field.k))) {U : Scheme.{u}} (j : U ⟶ X.left) :
    Over (Spec (.of P.field.k)) := Over.mk (j ≫ (X.left ↘ Spec (.of P.field.k)))

/-- Finite type of the induced component structure follows by composition.
Source: Zheng Construction 5.15
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
instance clopenScalarComponent_finiteType (P : PurityFiniteSetting.{u})
    (X : Over (Spec (.of P.field.k))) {U : Scheme.{u}} (j : U ⟶ X.left)
    [IsOpenImmersion j] [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))] :
    LocallyOfFiniteType ((clopenScalarComponent P X j).left ↘ Spec (.of P.field.k)) :=
  inferInstanceAs (LocallyOfFiniteType (j ≫ (X.left ↘ Spec (.of P.field.k))))

/-- Quasi-compactness follows because the component immersion is closed.
Source: Zheng Construction 5.15
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
instance clopenScalarComponent_quasiCompact (P : PurityFiniteSetting.{u})
    (X : Over (Spec (.of P.field.k))) {U : Scheme.{u}} (j : U ⟶ X.left)
    [IsClosedImmersion j] [QuasiCompact (X.left ↘ Spec (.of P.field.k))] :
    QuasiCompact ((clopenScalarComponent P X j).left ↘ Spec (.of P.field.k)) :=
  inferInstanceAs (QuasiCompact (j ≫ (X.left ↘ Spec (.of P.field.k))))

/-- The canonical component inclusion over k.
Source: Zheng Construction 5.15
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
def clopenScalarInclusion (P : PurityFiniteSetting.{u})
    (X : Over (Spec (.of P.field.k))) {U : Scheme.{u}} (j : U ⟶ X.left) :
    clopenScalarComponent P X j ⟶ X := Over.homMk j (by rfl)

/-- The bundled inclusion is the given open immersion.
Source: Zheng Construction 5.15
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
instance clopenScalarInclusion_open (P : PurityFiniteSetting.{u})
    (X : Over (Spec (.of P.field.k))) {U : Scheme.{u}} (j : U ⟶ X.left)
    [IsOpenImmersion j] : IsOpenImmersion (clopenScalarInclusion P X j).left :=
  inferInstanceAs (IsOpenImmersion j)

/-- The bundled inclusion is the given closed immersion.
Source: Zheng Construction 5.15
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
instance clopenScalarInclusion_closed (P : PurityFiniteSetting.{u})
    (X : Over (Spec (.of P.field.k))) {U : Scheme.{u}} (j : U ⟶ X.left)
    [IsClosedImmersion j] : IsClosedImmersion (clopenScalarInclusion P X j).left :=
  inferInstanceAs (IsClosedImmersion j)

/-- A comparison between zero objects, including its unique-arrow assertion.
Source: the empty-cover sheaf axiom and Zheng Construction 5.15
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
def ClopenZeroComparison {C : Type v} [Category.{z} C] [HasZeroMorphisms C]
    {K L : C} (e : K ≅ L) : Prop :=
  IsZero K ∧ IsZero L ∧ ∀ f : K ⟶ L, f = e.hom

/-- Evaluate the scalar comparison at the coefficient unit, then use the canonical
balancing identification. This defines the dualizing scalar map without a new choice.
Source: blueprint def-pur-section-invariant, coefficient-unit clause
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
def clopenIntegralDualizingScalar (P : PurityFiniteSetting.{u})
    (L : Type u) [Field L] [Algebra (Padic P.coefficients.l) L]
    [FiniteDimensional (Padic P.coefficients.l) L]
    (ι : P.extension →ₐ[Padic P.coefficients.l] L) (U V : Scheme.{u})
    (G : sfIntegralConstructibleCategory P.coefficients.l P.extension V ⥤
      sfIntegralConstructibleCategory P.coefficients.l P.extension U)
    (H : sfIntegralConstructibleCategory P.coefficients.l L V ⥤
      sfIntegralConstructibleCategory P.coefficients.l L U)
    (s : G ⋙ sfConstructibleIntegralScalarExtension 0 P.coefficients.l
        (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) P.extension L ι U ≅
      sfConstructibleIntegralScalarExtension 0 P.coefficients.l
        (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) P.extension L ι V ⋙ H) :=
  s.app (P.clopenIntegralUnit V) ≪≫
    H.mapIso (constantCoefficientConstructibleScalarIso P.coefficients.l P.extension L ι V
      P.field P.coefficients.different)

/-- The same coefficient-unit evaluation after raw rationalization.
Source: blueprint def-pur-section-invariant, coefficient-unit clause
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
def clopenRationalDualizingScalar (P : PurityFiniteSetting.{u})
    (L : Type u) [Field L] [Algebra (Padic P.coefficients.l) L]
    [FiniteDimensional (Padic P.coefficients.l) L]
    (ι : P.extension →ₐ[Padic P.coefficients.l] L) (U V : Scheme.{u})
    (G : sfRationalConstructibleCategory P.coefficients.l P.extension V ⥤
      sfRationalConstructibleCategory P.coefficients.l P.extension U)
    (H : sfRationalConstructibleCategory P.coefficients.l L V ⥤
      sfRationalConstructibleCategory P.coefficients.l L U)
    (s : G ⋙ sfRationalScalarExtension P.coefficients.l P.extension U 0
        (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) L ι ≅
      sfRationalScalarExtension P.coefficients.l P.extension V 0
        (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) L ι ⋙ H) :=
  s.app (P.clopenRationalUnit V) ≪≫
    H.mapIso (constantCoefficientRationalScalarIso P.coefficients.l P.extension L ι V
      P.field P.coefficients.different)

section Fields
variable (P : PurityFiniteSetting.{u})
  (X Y Xi : Over (Spec (.of P.field.k)))
  [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
  [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Xi.left ↘ Spec (.of P.field.k))]
  [QuasiCompact (Xi.left ↘ Spec (.of P.field.k))]
  (g : X.left ⟶ Y.left) [g.IsOver (Spec (.of P.field.k))]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (c : Compactification g) (j : Xi ⟶ X)
  [IsOpenImmersion j.left] [IsClosedImmersion j.left]

/-- The canonical scalar/restriction comparison in the published stage coordinates.
Its middle factor is the actual rationalized integral pullback comparison.
Source: def-weil-derived-pullback-tensor-hom, common-stage paragraph
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
def clopenStageScalarRestriction
    (B C : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar)
    (h : B ≤ C) :
    clopenRationalRestriction P
        (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
        j ⋙ GeneralAlgebraicallyClosedCoefficients.stageTransition
          P.coefficients.l P.coefficients.Qbar Xi.left B C h ≅
      GeneralAlgebraicallyClosedCoefficients.stageTransition
          P.coefficients.l P.coefficients.Qbar X.left B C h ⋙
        clopenRationalRestriction P
          (AlgebraicallyClosedCoefficients.Coefficient.{u}
            P.coefficients.l P.coefficients.Qbar C) j :=
  Functor.isoWhiskerLeft _ (operationStageTransitionIso _ _ Xi.left B C h) ≪≫
    rationalPullbackScalarComparison P.coefficients.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar C)
      (AlgebraicallyClosedCoefficients.coefficientInclusion _ _ B C h) j.left ≪≫
    Functor.isoWhiskerRight (operationStageTransitionIso _ _ X.left B C h).symm _

/-- The literal inclusion E into E', expressed in the published small stage model.
Source: Zheng Construction 4.1
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
def clopenBaseInclusion
    (B : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar)
    (h : P.extension ≤ B.val) : P.extension →ₐ[Padic P.coefficients.l]
      AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B :=
  (Shrink.algEquiv (Padic P.coefficients.l) B.val).symm.toAlgHom.comp
    (IntermediateField.inclusion h)

/-- Integral scalar extension from the named field E to an actual finite stage.
Source: Zheng Construction 4.1
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
abbrev clopenBaseScalar
    (B : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar)
    (ι : P.extension →ₐ[Padic P.coefficients.l]
      AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
    (W : Scheme.{u}) :=
  sfConstructibleIntegralScalarExtension 0 P.coefficients.l
    (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) P.extension
    (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B) ι W

/-- The same extension on the raw rationalized category.
Source: Zheng Construction 4.1
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
abbrev clopenBaseRationalScalar
    (B : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar)
    (ι : P.extension →ₐ[Padic P.coefficients.l]
      AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
    (W : Scheme.{u}) :=
  sfRationalScalarExtension P.coefficients.l P.extension W 0
    (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime))
    (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B) ι

/-- Scalar data linking the named coefficient field to every common-stage field.
The left comparisons are normalized by the finite quotient tensor unit in the
separate laws, and the right comparisons by their prescribed adjunction mates.
Source: Zheng Construction 5.15 and Lemma 5.22
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
structure ClopenBaseScalars (R : ClopenExceptionalAllCoefficients P X Y Xi g c j)
    (B : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar)
    (ι : P.extension →ₐ[Padic P.coefficients.l]
      AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B) where
  left : sfCompactSupportFiniteIntegralFunctor P.coefficients.l P.field.k
      R.base.baseUnit c P.extension ⋙ clopenBaseScalar P B ι Y.left ≅
    clopenBaseScalar P B ι X.left ⋙ sfCompactSupportFiniteIntegralFunctor
      P.coefficients.l P.field.k (R.stage B).baseUnit c
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
  leftI : sfCompactSupportFiniteIntegralFunctor P.coefficients.l P.field.k
      R.base.baseUnit (c.precomp j.left) P.extension ⋙ clopenBaseScalar P B ι Y.left ≅
    clopenBaseScalar P B ι Xi.left ⋙ sfCompactSupportFiniteIntegralFunctor
      P.coefficients.l P.field.k (R.stage B).baseUnit (c.precomp j.left)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
  right : R.base.integral ⋙ clopenBaseScalar P B ι X.left ≅
    clopenBaseScalar P B ι Y.left ⋙ (R.stage B).integral
  rightI : R.base.integralI ⋙ clopenBaseScalar P B ι Xi.left ≅
    clopenBaseScalar P B ι Y.left ⋙ (R.stage B).integralI
  rational : R.base.rational ⋙ clopenBaseRationalScalar P B ι X.left ≅
    clopenBaseRationalScalar P B ι Y.left ⋙ (R.stage B).rational
  rationalI : R.base.rationalI ⋙ clopenBaseRationalScalar P B ι Xi.left ≅
    clopenBaseRationalScalar P B ι Y.left ⋙ (R.stage B).rationalI

/-- The scalar square from the given E, its ramified ideals, and raw localization.
Every finite E' in the closure is represented by its canonical Shrink stage; ι
includes its canonical coefficient-field identification, without a universe equality.
Source: Zheng 4.1, 5.15 and 5.22
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
def ClopenBaseScalarLaws (R : ClopenExceptionalAllCoefficients P X Y Xi g c j)
    (B : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar)
    (ι : P.extension →ₐ[Padic P.coefficients.l]
      AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
    (S : ClopenBaseScalars P X Y Xi g c j R B ι) : Prop :=
  SfCompactSupportIntegralBetaSpec P.coefficients.l P.field.k R.base.baseUnit c P.extension
    (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
    ι S.left ∧
  SfCompactSupportIntegralBetaSpec P.coefficients.l P.field.k R.base.baseUnit
    (c.precomp j.left) P.extension
    (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
    ι S.leftI ∧
  S.right.hom = (mateEquiv R.base.integralAdjunction (R.stage B).integralAdjunction
    (.mk _ _ _ _ S.left.inv)).natTrans ∧
  S.rightI.hom = (mateEquiv R.base.integralAdjunctionI (R.stage B).integralAdjunctionI
    (.mk _ _ _ _ S.leftI.inv)).natTrans ∧
  (∀ K, (clopenBaseScalar P B ι Xi.left).map (R.base.integralComparison.hom.app K) ≫
      S.rightI.hom.app K =
    (integralPullbackScalarComparison P.coefficients.l P.extension
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
      ι j.left (R.base.integral.obj K)).hom ≫
      (clopenIntegralRestriction P
        (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
        j).map (S.right.hom.app K) ≫
      (R.stage B).integralComparison.hom.app ((clopenBaseScalar P B ι Y.left).obj K)) ∧
  (∀ K, HEq (S.rational.hom.app K)
    ((sfRationalConstructibleLocalization P.coefficients.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
      X.left).map (S.right.hom.app K.obj))) ∧
  (∀ K, HEq (S.rationalI.hom.app K)
    ((sfRationalConstructibleLocalization P.coefficients.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
      Xi.left).map (S.rightI.hom.app K.obj))) ∧
  (∀ K, (clopenBaseRationalScalar P B ι Xi.left).map
      (R.base.rationalComparison.hom.app K) ≫ S.rationalI.hom.app K =
    (rationalPullbackScalarComparison P.coefficients.l P.extension
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
      ι j.left).hom.app (R.base.rational.obj K) ≫
      (clopenRationalRestriction P
        (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
        j).map (S.rational.hom.app K) ≫
      (R.stage B).rationalComparison.hom.app
        ((clopenBaseRationalScalar P B ι Y.left).obj K)) ∧
  (∃ e : ℕ, 0 < e ∧ ∀ n : ℕ, 1 ≤ n →
    (Ideal.span ({integralScalarIntegerInclusion P.coefficients.l P.extension
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B) ι
      (Padic.coefficientExtensionUniformizer P.coefficients.l P.extension)} : Set
      (Padic.coefficientExtensionIntegers P.coefficients.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u}
          P.coefficients.l P.coefficients.Qbar B)))) ^ n =
    Padic.coefficientExtensionIdeal P.coefficients.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
      (e * n))

/-- The integral arrow is the actual normalized DU and total-limit realization.
The heterogeneous equations only forget the full-subcategory wrapper.
Source: Zheng 5.22; clopen-system integral realization, displayed map equations
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
def ClopenBaseRealizationLaws (R : ClopenExceptionalAllCoefficients P X Y Xi g c j) : Prop :=
  ∃ T : ClopenSystemIntegralRealization P c j.left,
    HEq T.integral R.base.integral ∧ HEq T.integralI R.base.integralI ∧
    HEq T.transport.core.S R.base.S ∧ HEq T.transport.core.G R.base.G ∧
    HEq T.transport.core.Si R.base.Si ∧ HEq T.transport.core.Gi R.base.Gi ∧
    (∀ K, HEq (T.integralComparison.hom.app K)
      ((sfIntegralConstructible P.coefficients.l P.extension Xi.left).ι.map
        (R.base.integralComparison.hom.app K)))

/-- An empty component has only zero objects and the displayed arrows are unique.
Source: Zheng 5.15 and the empty-cover sheaf axiom
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
def ClopenEmptyScalarLaws (R : ClopenExceptionalAllCoefficients P X Y Xi g c j) : Prop :=
  IsEmpty Xi.left →
    (∀ K, ClopenZeroComparison (R.base.strict.system.comparison.app K)) ∧
    (∀ n K, ClopenZeroComparison ((R.base.finite n).app K)) ∧
    (∀ K, ClopenZeroComparison (R.base.system.app K)) ∧
    (∀ K, ClopenZeroComparison (R.base.integralComparison.app K)) ∧
    (∀ K, ClopenZeroComparison (R.base.rationalComparison.app K)) ∧
    (∀ B K, ClopenZeroComparison ((R.stage B).integralComparison.app K)) ∧
    (∀ B K, ClopenZeroComparison ((R.stage B).rationalComparison.app K)) ∧
    (∀ K, ClopenZeroComparison (R.commonStageComparison.app K))

/-- The integral coefficient mates for the already fixed clopen comparisons.
Their normalization and scalar equations are asserted separately, to share the
large concrete types in kernel checking.
Source: Zheng 5.15--5.22 and the blueprint coefficient-unit clause
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
structure ClopenIntegralScalars
    (R : ClopenExceptionalAllCoefficients P X Y Xi g c j) where
  integralScalar : ∀ {B C : AlgebraicallyClosedCoefficients.Index
      P.coefficients.l P.coefficients.Qbar} (h : B ≤ C),
    (R.stage B).integral ⋙ GeneralAlgebraicallyClosedCoefficients.integralTransition
        P.coefficients.l P.coefficients.Qbar X.left B C h ≅
      GeneralAlgebraicallyClosedCoefficients.integralTransition
        P.coefficients.l P.coefficients.Qbar Y.left B C h ⋙ (R.stage C).integral
  integralScalarI : ∀ {B C : AlgebraicallyClosedCoefficients.Index
      P.coefficients.l P.coefficients.Qbar} (h : B ≤ C),
    (R.stage B).integralI ⋙ GeneralAlgebraicallyClosedCoefficients.integralTransition
        P.coefficients.l P.coefficients.Qbar Xi.left B C h ≅
      GeneralAlgebraicallyClosedCoefficients.integralTransition
        P.coefficients.l P.coefficients.Qbar Y.left B C h ⋙ (R.stage C).integralI

/-- Linearity, integral scalar mates, the realized scalar square, and its raw
rationalized square. The inherited comparison record retains the full DU/total
limit formula and the precise common-stage representative map and inverse.
Source: Zheng 5.15--5.22 and the blueprint coefficient-unit clause
(blueprint: lem-pur-clopen-exceptional-scalar-descent). -/
def ClopenScalarLaws
    (R : ClopenExceptionalAllCoefficients P X Y Xi g c j)
    (S : ClopenIntegralScalars P X Y Xi g c j R) : Prop :=
  (R.base.integral.Linear (Padic.coefficientExtensionIntegers
    P.coefficients.l P.extension)) ∧
  (R.base.integralI.Linear (Padic.coefficientExtensionIntegers
    P.coefficients.l P.extension)) ∧
  (∀ B, (R.stage B).integral.Linear
    (Padic.coefficientExtensionIntegers P.coefficients.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B))) ∧
  (∀ B, (R.stage B).integralI.Linear
    (Padic.coefficientExtensionIntegers P.coefficients.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B))) ∧
  (∀ {B C} (h : B ≤ C),
    (S.integralScalar h).hom =
      (mateEquiv (R.stage B).integralAdjunction (R.stage C).integralAdjunction
        (.mk _ _ _ _ (R.support.integralBeta h).inv)).natTrans) ∧
  (∀ {B C} (h : B ≤ C),
    (S.integralScalarI h).hom =
      (mateEquiv (R.stage B).integralAdjunctionI (R.stage C).integralAdjunctionI
        (.mk _ _ _ _ (R.supportI.integralBeta h).inv)).natTrans) ∧
  (∀ {B C} (h : B ≤ C) K,
    (GeneralAlgebraicallyClosedCoefficients.integralTransition
        P.coefficients.l P.coefficients.Qbar Xi.left B C h).map
          ((R.stage B).integralComparison.hom.app K) ≫ (S.integralScalarI h).hom.app K =
      (integralPullbackScalarComparison P.coefficients.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar C)
        (AlgebraicallyClosedCoefficients.coefficientInclusion _ _ B C h) j.left
        ((R.stage B).integral.obj K)).hom ≫
      (clopenIntegralRestriction P
        (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar C)
        j).map ((S.integralScalar h).hom.app K) ≫
      (R.stage C).integralComparison.hom.app
        ((GeneralAlgebraicallyClosedCoefficients.integralTransition
          P.coefficients.l P.coefficients.Qbar Y.left B C h).obj K)) ∧
  (∀ {B C} (h : B ≤ C) K,
    HEq ((R.action.β h).hom.app K)
      ((sfRationalConstructibleLocalization P.coefficients.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar C)
        X.left).map ((S.integralScalar h).hom.app K.obj))) ∧
  (∀ {B C} (h : B ≤ C) K,
    HEq ((R.actionI.β h).hom.app K)
      ((sfRationalConstructibleLocalization P.coefficients.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar C)
        Xi.left).map ((S.integralScalarI h).hom.app K.obj))) ∧
  (∀ {B C} (h : B ≤ C) K,
    (GeneralAlgebraicallyClosedCoefficients.stageTransition
        P.coefficients.l P.coefficients.Qbar Xi.left B C h).map
          ((R.stageComparison B).hom.app K) ≫ (R.actionI.β h).hom.app K =
      (clopenStageScalarRestriction P (X := X) (Xi := Xi) j B C h).hom.app
        ((R.action.Φ B).obj K) ≫
      (clopenRationalRestriction P
        (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar C)
        j).map ((R.action.β h).hom.app K) ≫
      (R.stageComparison C).hom.app
        ((GeneralAlgebraicallyClosedCoefficients.stageTransition
          P.coefficients.l P.coefficients.Qbar Y.left B C h).obj K))

end Fields

/-- Scalar coherence and field descent of the prescribed clopen comparisons.
Source: Zheng Construction 5.15, Lemmas 5.16 and 5.22, pp. 35--36;
blueprint def-pur-section-invariant, coefficient-unit clause
(blueprint: lem-pur-clopen-exceptional-scalar-descent).

Proof, the ten node steps:
1. Use one O-basis of O' at every quotient. Extension is exact. Tensor preserves
zero insertion, its identity/zero counit and the sectionwise open compositor.
2. Transpose the compact-support scalar square under coefficient adjunction.
The proper part is shared, so the remaining open square is the one from step 1.
3. Take prescribed counit mates. Mate pasting gives the system equation stated
in clopenExceptionalScalarDescent_system, on actual system transformations.
4. Tensor units and associators give identity and successive extensions. The
ideal identity varpi^n O' = (varpi')^(en) O' identifies the same square with the
cofinal restriction; its coefficient comparisons preserve these counits.
5. Whisker by nu^* and R nu_* and precompose with actual derived reduction.
The balancing maps commute with quotient transitions and retain the same maps
under DU, the exact forgetting to completed-coefficient strict towers.
6. Finite-free tensor commutes naturally with the actual total derived limit.
Apply this natural comparison to the entire square and its inverse. The inherited
inverseLimitMap equation is precisely this realization, and all constituents are
O-linear. The resulting integralScalar is the prescribed counit mate.
7. Cofinal restriction has the exact left adjoint repeating entries in blocks,
so it preserves K-injectives. Compatible-family limits agree naturally. The total
limit cofinal comparison therefore preserves the square and successive restrictions.
8. Localize the integral maps and their equations. On a pure tensor a tensor u,
naturality is integral naturality multiplied by a. The inherited rationalMap and
rationalComparisonMap equations identify this raw localization, without Karoubi
completion; the rational scalar equations retain the same scalar mates.
9. The scalar square makes the classes of the stage comparisons natural on
common-stage representatives: substitute the two endpoint scalar squares and
cancel the conjugating comparisons. Equality after extension gives equality of
images, independently of representative and common field. The inherited
commonStageMap specifies those classes, and their inverses compose to identities.
10. Evaluate the very same maps at the coefficient unit. Its scalar identification
is the balancing map 1 tensor b to b. Empty component module categories, strict
systems and derived categories are zero, so all component arrows are unique;
an empty cover has no component assertion. No separatedness of Y is used.

Dependencies by step:
1. lem-pur-clopen-strict-system-support; lem-pur-local-field-coefficient-stages.
2. lem-pur-etale-system-coefficient-projection; def-weil-pbc-adjunction-mate.
3. lem-pur-clopen-counit-adjoint-comparison;
   lem-pur-etale-system-scalar-mate-coherence; lem-weil-pbc-mate-pasting.
4. lem-pur-etale-system-cofinal-mate and the coefficient-stage and scalar-mate nodes.
5. lem-pur-clopen-system-integral-realization; def-weil-exceptional-inverse-image.
6. lem-weil-finite-free-completed-scalar-comparison;
   lem-weil-pbc-finite-free-strict-tower-transport; the clopen realization nodes.
7. lem-weil-pbc-ringed-strict-tower-homotopy-limit.
8. lem-pur-semilinear-scalar-localization; def-weil-derived-pullback-tensor-hom.
9. def-weil-algebraically-closed-coefficients and both operation definitions.
10. lem-pur-finite-clopen-derived-decomposition and the same operation definitions. -/
theorem clopenExceptionalScalarDescent
    (P : PurityFiniteSetting.{u})
    (X Y : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
    (g : X ⟶ Y) [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    {I : Type w} [Finite I] (Xi : I → Scheme.{u}) (j : ∀ i, Xi i ⟶ X.left)
    [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (_hdisjoint : ∀ i k, i ≠ k → Disjoint (Set.range (j i)) (Set.range (j k)))
    (_hcover : (⋃ i, Set.range (j i)) = Set.univ) (c : Compactification g.left) :
    ∀ i : I, ∃ R : ClopenExceptionalAllCoefficients P X Y
      (clopenScalarComponent P X (j i)) g.left c (clopenScalarInclusion P X (j i)),
      ∃ S : ClopenIntegralScalars P X Y (clopenScalarComponent P X (j i))
        g.left c (clopenScalarInclusion P X (j i)) R,
        ClopenScalarLaws P X Y (clopenScalarComponent P X (j i)) g.left c
          (clopenScalarInclusion P X (j i)) R S ∧
        ClopenBaseRealizationLaws P X Y (clopenScalarComponent P X (j i)) g.left c
          (clopenScalarInclusion P X (j i)) R ∧
        ClopenEmptyScalarLaws P X Y (clopenScalarComponent P X (j i)) g.left c
          (clopenScalarInclusion P X (j i)) R ∧
        ∀ B (h : P.extension ≤ B.val),
          ∃ T : ClopenBaseScalars P X Y (clopenScalarComponent P X (j i)) g.left c
            (clopenScalarInclusion P X (j i)) R B (clopenBaseInclusion P B h),
          ClopenBaseScalarLaws P X Y (clopenScalarComponent P X (j i)) g.left c
            (clopenScalarInclusion P X (j i)) R B (clopenBaseInclusion P B h) T := by
  sorry

end WeilConjectures.PurityFiniteSetting
