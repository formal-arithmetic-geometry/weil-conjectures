module

public import Sheaf.Paper.SupportedHomPullback
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
public import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.SupportedCohomologyHom
public import Sheaf.AlgebraicGeometry.ClosedSupportHom
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.CategoryTheory.ExactDerivedAdjunctionBounds
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence

/-! # Closed-support restriction as an exceptional counit mate

Source: blueprint main-20261015, affine-line orientation proof, naturality and final
etale-origin comparison; Milne, Theorem 9.4 and Example 9.5, pp. 65--67, and closed
support adjunction, pp. 111--112 (blueprint: lem-pur-closed-support-exceptional-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a₀ a₁ h₀ h₁ d₀ d₁
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry

/-- Finiteness of the coefficient quotient from the finite-setting construction.
Source: purity conventions (blueprint: lem-pur-closed-support-exceptional-mate). -/
instance closedMateRingFinite (P : WeilConjectures.PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- The coefficient universe lift retains finiteness.
Source: purity conventions (blueprint: lem-pur-closed-support-exceptional-mate). -/
instance closedMateCoefficientFinite (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  @Finite.of_equiv (ULift.{u + 1} P.Ring) P.Ring (closedMateRingFinite P) Equiv.ulift.symm

namespace ClosedSupportExceptionalMate

universe c d c' d' v w v' w' p q r vp vq vr

/-- A typed record of the functors, adjunctions and canonical exchange occurring in the
counit-mate calculation. The geometric instance below supplies the actual closed functors.
Source: Stacks 0037 and 0959 (blueprint: lem-pur-closed-support-exceptional-mate). -/
structure Diagram (C : Type c) (D : Type d) (C' : Type c') (D' : Type d')
    [Category.{v} C] [Category.{w} D] [Category.{v'} C'] [Category.{w'} D'] where
  push : C ⥤ D
  push' : C' ⥤ D'
  pull : D ⥤ D'
  pull' : C ⥤ C'
  exceptional : D ⥤ C
  exceptional' : D' ⥤ C'
  adj : push ⊣ exceptional
  adj' : push' ⊣ exceptional'
  exchange : push ⋙ pull ≅ pull' ⋙ push'
  constant : C
  constant' : C'
  constantPullback : pull'.obj constant ≅ constant'

namespace Diagram
variable {C : Type c} {D : Type d} {C' : Type c'} {D' : Type d'}
  [Category.{v} C] [Category.{w} D] [Category.{v'} C'] [Category.{w'} D']
  (dgm : Diagram C D C' D')

/-- Finite exchange evaluated at the coefficient unit.
Source: Stacks 0959 (blueprint: lem-pur-closed-support-exceptional-mate). -/
def constantExchange :=
  dgm.exchange.app dgm.constant ≪≫ dgm.push'.mapIso dgm.constantPullback

/-- Pullback of the exceptional counit, precomposed with inverse finite exchange.
Source: Stacks 0037 and 0959 (blueprint: lem-pur-closed-support-exceptional-mate). -/
def pulledCounit (N : D) :=
  dgm.exchange.inv.app (dgm.exceptional.obj N) ≫ dgm.pull.map (dgm.adj.counit.app N)

/-- The exceptional mate is the actual adjunct of that pulled counit.
Source: Stacks 0037 (blueprint: lem-pur-closed-support-exceptional-mate). -/
def beta (N : D) := dgm.adj'.homEquiv _ _ (dgm.pulledCounit N)

/-- Pullback of M by the inverse coefficient exchange.
Source: Milne, Theorem 9.4 (blueprint: lem-pur-closed-support-exceptional-mate). -/
def pulledMorphism {N : D} (M : dgm.push.obj dgm.constant ⟶ N) :=
  dgm.constantExchange.inv ≫ dgm.pull.map M

/-- Pullback of u, with the source identified by the canonical constant comparison.
Source: Milne, Example 9.5 (blueprint: lem-pur-closed-support-exceptional-mate). -/
def pulledAdjunct {K : C} (u : dgm.constant ⟶ K) :=
  dgm.constantPullback.inv ≫ dgm.pull'.map u

/-- The four displayed equations, with the actual u, epsilon-prime and beta substituted.
Source: blueprint affine-line orientation, naturality
(blueprint: lem-pur-closed-support-exceptional-mate). -/
def Equations {N : D} (M : dgm.push.obj dgm.constant ⟶ N) : Prop :=
  M = dgm.push.map (dgm.adj.homEquiv _ _ M) ≫ dgm.adj.counit.app N ∧
  dgm.pulledMorphism M =
    dgm.push'.map (dgm.pulledAdjunct (dgm.adj.homEquiv _ _ M)) ≫ dgm.pulledCounit N ∧
  dgm.push'.map (dgm.beta N) ≫ dgm.adj'.counit.app (dgm.pull.obj N) = dgm.pulledCounit N ∧
  dgm.adj'.homEquiv _ _ (dgm.pulledMorphism M) =
    dgm.pulledAdjunct (dgm.adj.homEquiv _ _ M) ≫ dgm.beta N

/-- Both ordinary exceptional objects are bounded below; the shift is already in N.
Source: exact-adjoint lower-bound lemma
(blueprint: lem-pur-closed-support-exceptional-mate). -/
def Bounded (pa : ObjectProperty C) (pb : ObjectProperty C') (N : D) : Prop :=
  pa (dgm.exceptional.obj N) ∧ pb (dgm.exceptional'.obj (dgm.pull.obj N))

/-- The same four equations after applying the comparison inverse images. The last
one is the assertion that the compared restriction is the image of beta composed with g*u.
Source: blueprint affine-line orientation, final etale-origin comparison
(blueprint: lem-pur-closed-support-exceptional-mate). -/
def ImageEquations {DP : Type p} {DP' : Type q} {CP' : Type r}
    [Category.{vp} DP] [Category.{vq} DP'] [Category.{vr} CP']
    (cX : D ⥤ DP) (cX' : D' ⥤ DP') (cZ' : C' ⥤ CP')
    {N : D} (M : dgm.push.obj dgm.constant ⟶ N) : Prop :=
  cX.map M = cX.map (dgm.push.map (dgm.adj.homEquiv _ _ M)) ≫
    cX.map (dgm.adj.counit.app N) ∧
  cX'.map (dgm.pulledMorphism M) =
    cX'.map (dgm.push'.map (dgm.pulledAdjunct (dgm.adj.homEquiv _ _ M))) ≫
      cX'.map (dgm.pulledCounit N) ∧
  cX'.map (dgm.push'.map (dgm.beta N)) ≫
      cX'.map (dgm.adj'.counit.app (dgm.pull.obj N)) = cX'.map (dgm.pulledCounit N) ∧
  cZ'.map (dgm.adj'.homEquiv _ _ (dgm.pulledMorphism M)) =
    cZ'.map (dgm.pulledAdjunct (dgm.adj.homEquiv _ _ M)) ≫ cZ'.map (dgm.beta N)

end Diagram

variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- Transport of a transpose through the canonical uniqueness of right adjoints.
The inverse Hom formula reduces the identity to the counit characterization of
`rightAdjointUniq`, followed by naturality in the target.
Source: Stacks 0037 (blueprint: lem-pur-closed-support-exceptional-mate). -/
private theorem transpose_rightAdjointUniq
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{w} D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R')
    (e : L' ≅ L) {A : C} {N N' : D} (M : L.obj A ⟶ N) (η : N ⟶ N') :
    adj'.homEquiv _ _ (e.hom.app A ≫ M ≫ η) =
      adj.homEquiv _ _ M ≫ R.map η ≫
        ((adj.ofNatIsoLeft e.symm).rightAdjointUniq adj').hom.app N' := by
  let a := adj.ofNatIsoLeft e.symm
  have he : a.homEquiv _ _ (e.hom.app A ≫ M ≫ η) =
      adj.homEquiv _ _ (M ≫ η) := by
    rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
    simp
  calc
    _ = a.homEquiv _ _ (e.hom.app A ≫ M ≫ η) ≫
        (a.rightAdjointUniq adj').hom.app N' := by
      apply (adj'.homEquiv _ _).symm.injective
      rw [Equiv.symm_apply_apply]
      simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
        Adjunction.rightAdjointUniq_hom_app_counit]
      exact ((a.homEquiv _ _).symm_apply_apply _).symm.trans
        (a.homEquiv_counit _ _ _)
    _ = adj.homEquiv _ _ (M ≫ η) ≫ (a.rightAdjointUniq adj').hom.app N' := by rw [he]
    _ = _ := by rw [adj.homEquiv_naturality_right M η, Category.assoc]

variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- The unique ordinary etale closed right adjoint, with the exact-derived counit.
Source: Milne, pp. 111--112 (blueprint: lem-pur-closed-support-exceptional-mate). -/
def adjunction {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategory ⊣
      (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctor.rightAdjoint :=
  (Adjunction.ofIsLeftAdjoint
    (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctor).ofNatIsoLeft
      (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctorIsoMapDerivedCategory

/-- The degree-zero coefficient unit on a scheme.
Source: Milne, Example 9.5 (blueprint: lem-pur-closed-support-exceptional-mate). -/
def constant (Z : Scheme.{u}) : Etale.DerivedCategoryModule P.Coefficient Z :=
  (DerivedCategory.singleFunctor
    (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0).obj (P.constantEtale Z)

/-- Finite direct-image exchange descended to the derived category, with real canonical data.
Source: Stacks 0959 (blueprint: lem-pur-closed-support-exceptional-mate). -/
def exchange {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) (g : Z' ⟶ Z)
    (sq : ChosenCartesianSquare g i' i h) :
    (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategory ⋙
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h).mapDerivedCategory ≅
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).mapDerivedCategory ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i').mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso
      (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (@asIso _ _ _ _ (Etale.baseChangeMap (ModuleCat.{u + 1} P.Coefficient) sq.toCommSq)
        (Etale.isIso_baseChangeMap_of_isFinite _
          (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd))) ≪≫
    Functor.mapDerivedCategoryCompIso
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) g)
      (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i')

/-- Exact descent carries a chosen sheaf comparison to the corresponding singles.
This generic constructor keeps the canonical coefficient comparison explicit.
Source: Milne, Example 9.5 (blueprint: lem-pur-closed-support-exceptional-mate). -/
def singleComparison {A : Type a₀} {B : Type a₁}
    [Category.{h₀} A] [Category.{h₁} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{d₀} A] [HasDerivedCategory.{d₁} B] (L : A ⥤ B) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (a : A) (b : B) (e : L.obj a ≅ b) :
    L.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A 0).obj a) ≅
      (DerivedCategory.singleFunctor B 0).obj b :=
  (L.mapDerivedCategorySingleFunctor 0).app a ≪≫
    (DerivedCategory.singleFunctor B 0).mapIso e

/-- The geometric diagram uses the recorded functors and canonical coefficient comparison.
Source: Stacks 0959, 0037; Milne, Example 9.5
(blueprint: lem-pur-closed-support-exceptional-mate). -/
def diagram {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) (g : Z' ⟶ Z)
    (sq : ChosenCartesianSquare g i' i h) :
    Diagram (Etale.DerivedCategoryModule P.Coefficient Z)
      (Etale.DerivedCategoryModule P.Coefficient X)
      (Etale.DerivedCategoryModule P.Coefficient Z')
      (Etale.DerivedCategoryModule P.Coefficient X') where
  push := (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategory
  push' := (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i').mapDerivedCategory
  pull := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h).mapDerivedCategory
  pull' := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).mapDerivedCategory
  exceptional :=
    (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctor.rightAdjoint
  exceptional' :=
    (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i').rightDerivedFunctor.rightAdjoint
  adj := adjunction P i
  adj' := adjunction P i'
  exchange := exchange P i i' h g sq
  constant := constant P Z
  constant' := constant P Z'
  constantPullback :=
    singleComparison (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) g)
      (P.constantEtale Z) (P.constantEtale Z')
      ((Etale.constantSheafCompUpperStarIso P.Coefficient g).app
        (ModuleCat.of P.Coefficient P.Coefficient))

/-- Canonical comparison from exact closed pushforward to its single supported sheaf.
Source: Milne, Theorem 9.4 (blueprint: lem-pur-closed-support-exceptional-mate). -/
def supportedSingle {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategory.obj
        (constant P Z) ≅
      (DerivedCategory.singleFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0).obj
          (etaleSupportHomPair P i).supported :=
  singleComparison (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)
    (P.constantEtale Z) (etaleSupportHomPair P i).supported (Iso.refl _)

/-- Transport a morphism through its specified source comparison.
Source: Milne, Theorem 9.4 (blueprint: lem-pur-closed-support-exceptional-mate). -/
def sourceTransport {C : Type c} [Category.{v} C] {B B' N : C}
    (e : B ≅ B') (M : B' ⟶ N) : B ⟶ N :=
  e.hom ≫ M

/-- The normalized supported-Hom class in the exact closed direct-image coordinates.
Source: Milne, Theorem 9.4 (blueprint: lem-pur-closed-support-exceptional-mate). -/
def classMorphism {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (chi : (etaleSupportHomPair P i).Identification)
    (F : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (a : ℤ) (alpha : (etaleSupportHomPair P i).group F a) :
    (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategory.obj
        (constant P Z) ⟶ F.obj⟦a⟧ :=
  sourceTransport (supportedSingle P i) (chi.chi F a alpha)

/-- Exact comparison inverse image in the existing unbounded derived category.
Source: Stacks 099R (blueprint: lem-pur-closed-support-exceptional-mate). -/
abbrev comparison (X : Scheme.{u}) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory

/-- At the closed compactification (id,i), compact support is exact closed pushforward.
This is the existing identity extension normalization followed by the exact derived
comparison; no arbitrary compact-support isomorphism is supplied.
Source: blueprint affine-line orientation, final etale-origin comparison
(blueprint: lem-pur-closed-support-exceptional-mate). -/
def compactNormalization {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient)
        (Compactification.ofIsProper i) ≅
      (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (Etale.mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} P.Coefficient) Z)
      (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctor ≪≫
    Functor.leftUnitor _ ≪≫
    (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctorIsoMapDerivedCategory

/-- The finite transported exceptional inverse image, with the required existing adjoint
instance supplied rather than assumed. This is literally sfFiniteExceptionalAt.
Source: blueprint exceptional inverse image, finite formula
(blueprint: lem-pur-closed-support-exceptional-mate). -/
def transported {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} P.Coefficient)) :=
  haveI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
    P.Coefficient (Compactification.ofIsProper i)
  ProEtale.sfFiniteExceptionalAt P.Coefficient (Compactification.ofIsProper i)

/-- The canonical right adjoint at the closed compactification, in the recorded formula.
Source: blueprint finite exceptional inverse image
(blueprint: lem-pur-closed-support-exceptional-mate). -/
def compactRight {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Etale.DerivedCategoryModule P.Coefficient X ⥤
      Etale.DerivedCategoryModule P.Coefficient Z :=
  haveI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
    P.Coefficient (Compactification.ofIsProper i)
  (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient)
    (Compactification.ofIsProper i)).rightAdjoint

/-- The adjunction used in the recorded finite exceptional composite.
Source: blueprint finite exceptional formula
(blueprint: lem-pur-closed-support-exceptional-mate). -/
def compactAdjunction {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient)
        (Compactification.ofIsProper i) ⊣ compactRight P i :=
  @Adjunction.ofIsLeftAdjoint _ _ _ _
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient)
      (Compactification.ofIsProper i))
    (Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
      P.Coefficient (Compactification.ofIsProper i))

/-- The counit-normalized unique comparison of the two ordinary etale right adjoints.
Source: Stacks 0037; blueprint final closed-compactification comparison
(blueprint: lem-pur-closed-support-exceptional-mate). -/
def rightComparison {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctor.rightAdjoint ≅
      compactRight P i :=
  haveI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
    P.Coefficient (Compactification.ofIsProper i)
  ((adjunction P i).ofNatIsoLeft (compactNormalization P i).symm).rightAdjointUniq
    (@Adjunction.ofIsLeftAdjoint _ _ _ _
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient)
        (Compactification.ofIsProper i))
      (Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
        P.Coefficient (Compactification.ofIsProper i)))

/-- The etale-origin normalization of the recorded transported exceptional functor.
Its first factor is precisely the comparison-adjunction unit, and its second is
uniqueness of ordinary etale right adjoints with the specified compact normalization.
Source: Stacks 099R; blueprint affine-line orientation, final comparison
(blueprint: lem-pur-closed-support-exceptional-mate). -/
def originIso {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (N : Etale.DerivedCategoryModule P.Coefficient X)
    (hN : DerivedCategory.TStructure.t.plus N) :
    (comparison P Z).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctor.rightAdjoint.obj
          N) ≅
      (transported P i).obj ((comparison P X).obj N) :=
  ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctor.rightAdjoint ⋙
      comparison P Z).mapIso
        (@asIso _ _ _ _
          ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) X).unit.app N)
          (ProEtale.isIso_derivedComparisonAdjunction_unit_app _ _ N hN)) ≪≫
    (comparison P Z).mapIso ((rightComparison P i).app _)

/-- Transpose along the actual ordinary compact-support adjunction after inserting
its compactification comparison and the site-adjunction unit, then apply nu_Z^*.
This is the Hom chain defining the transported exceptional functor on etale inputs.
Source: blueprint exceptional inverse image and final etale-origin comparison
(blueprint: lem-pur-closed-support-exceptional-mate). -/
def originTranspose {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (N : Etale.DerivedCategoryModule P.Coefficient X)
    (M : (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategory.obj
      (constant P Z) ⟶ N) :
    (comparison P Z).obj (constant P Z) ⟶
      (transported P i).obj ((comparison P X).obj N) :=
  (comparison P Z).map ((compactAdjunction P i).homEquiv _ _
    ((compactNormalization P i).hom.app (constant P Z) ≫ M ≫
      (ProEtale.derivedComparisonAdjunction
        (ModuleCat.{u + 1} P.Coefficient) X).unit.app N))

end ClosedSupportExceptionalMate

open ClosedSupportExceptionalMate

/-- Closed supported-class restriction is the counit-defined exceptional mate, on all
ordinary etale bounded-below inputs and after exact site inverse image. The support
identifications retain their evaluation-at-one normalization. All transports retain the
constant-unit, closed-exchange, kernel-inclusion, shift and site-square comparisons.
In particular nothing here assumes that beta is invertible.

Source: blueprint main-20261015, thm-pur-affine-line-orientation.proof.md,
naturality and final etale-origin comparison; Milne, Theorem 9.4, Example 9.5 and
pp. 111--112 (blueprint: lem-pur-closed-support-exceptional-mate).

Proof:
1. Closed immersions and their base changes are finite. Apply finite exactness and
exchange (Stacks 03QP, 0959); inverse image is exact. The closed ambient adjoint and
exactDerivedAdjunction_isGE put its values in D+. Adjoint shift compatibility gives
Ri!(F[a]) = (Ri!F)[a], compatibly with the counits.
2. The inverse Hom bijection sends u to i_*u followed by the counit (Stacks 0037).
Apply it to u = adj(M) and beta = adj(epsilon-prime), giving equations one and three.
3. Naturality of finite exchange at u gives equation two after inverse cancellation.
4. Transpose equation two and use equation three and functoriality, giving equation four.
Only the finite exchange was inverted.
5. The normalized supportedHom_pullback theorem identifies the pulled M with the
supported pullback class, with its exact inverse-image shift comparison.
6. Comparison inverse image is exact; apply it to the four equations. Finite closed
pushforward is qcqs, so comparisonDirectImagePlus supplies the canonical endpoint
identifications. The comparison-pullback coherence and supported constant comparisons
cancel at the internal endpoints. The four Compatible clauses and SupportHomSquareCoherent
identify the resulting supported classes on both sites.
7. Naturality of comparison inverse image with g* identifies the restricted image of u
with the image of beta composed with g*u, as encoded by the last image equation.
8. For finite-type k-schemes, the closed compactification is (id,i). Remove identity
extension and use exactness to identify its compact support with i_*. Uniqueness of
right adjoints and the invertible comparison unit give originIso. Its naturality
identifies the restriction with the recorded transported functor. An arbitrary geometric
fibre uses the ordinary closed adjoint and its exact comparison image from steps 1--7;
no finite-type or ambient pro-etale adjoint hypothesis is used there. -/
theorem closedSupport_exceptional_mate (P : WeilConjectures.PurityFiniteSetting.{u}) :
    ∃ chiE : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
        (etaleSupportHomPair P i).Identification,
    ∃ chiP : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
        (proEtaleSupportHomPair P i).Identification,
    ∀ {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) (g : Z' ⟶ Z)
      (sq : ChosenCartesianSquare g i' i h),
    ∃ e : etaleSupportHomTransport P i i' h,
    ∃ p : proEtaleSupportHomTransport P i i' h,
    ∃ v : siteSupportHomTransport P i,
    ∃ v' : siteSupportHomTransport P i',
      SupportHomSquareCoherent P i i' h e p v v' ∧
      ∀ (F : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) (a : ℤ)
        (alpha : (etaleSupportHomPair P i).group F a),
        (diagram P i i' h g sq).Bounded
          DerivedCategory.TStructure.t.plus DerivedCategory.TStructure.t.plus (F.obj⟦a⟧) ∧
        (diagram P i i' h g sq).Equations (classMorphism P i (chiE i) F a alpha) ∧
        (diagram P i i' h g sq).ImageEquations
          (comparison P X) (comparison P X') (comparison P Z')
          (classMorphism P i (chiE i) F a alpha) ∧
        e.Compatible (hB := Etale.isContinuous_overPullback h) (chiE i) (chiE i') F a ∧
        p.Compatible (hB := Scheme.ProEt.isContinuous_overPullback h) (chiP i) (chiP i')
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategoryPlus.obj F) a ∧
        v.Compatible (hB := Scheme.isContinuous_toProEt X) (chiE i) (chiP i) F a ∧
        v'.Compatible (hB := Scheme.isContinuous_toProEt X') (chiE i') (chiP i')
          ((Etale.upperStar
            (ModuleCat.{u + 1} P.Coefficient) h).mapDerivedCategoryPlus.obj F) a ∧
        (diagram P i i' h g sq).pulledMorphism (classMorphism P i (chiE i) F a alpha) ≫
            ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h).mapDerivedCategory.commShiftIso
              a).hom.app F.obj =
          classMorphism P i' (chiE i')
            ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h).mapDerivedCategoryPlus.obj F) a
            ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) a).map
              ((e.derivedMap (hB := Etale.isContinuous_overPullback h)).app F) alpha) := by
  sorry

/-- On finite-type k-schemes the ordinary closed transpose, followed by comparison,
is the transpose for the recorded transported functor, through the specified originIso.
Consequently its restriction is the image restriction in closedSupport_exceptional_mate.
Source: blueprint affine-line orientation, final comparison; Stacks 099R
(blueprint: lem-pur-closed-support-exceptional-mate).
Proof: for the closed compactification (id,i), remove identity extension by zero and
identify exact derived direct image with termwise direct image. Uniqueness of right
adjoints through this canonical comparison gives rightComparison. Insert the comparison
unit in the target of M, transpose along the compact-support adjunction and apply nu_Z^*.
Naturality of rightComparison gives the stated equality. The comparison unit is invertible
on the bounded-below shifted F, giving originIso. Applying the four image equations of
the main statement then identifies restriction with the image of beta composed with g*u.
For an arbitrary fibre only the ordinary adjoint and its comparison image are used. -/
theorem closedSupport_exceptional_mate_origin (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of P.field.k))]
    (F : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) (a : ℤ)
    (M : (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategory.obj
      (constant P Z) ⟶ F.obj⟦a⟧) :
    originTranspose P i (F.obj⟦a⟧) M =
      (comparison P Z).map ((adjunction P i).homEquiv _ _ M) ≫
        (originIso P i (F.obj⟦a⟧)
          (DerivedCategory.TStructure.t.plus.le_shift a F.obj F.property)).hom := by
  dsimp only [originTranspose]
  change (comparison P Z).map
    ((compactAdjunction P i).homEquiv _ _
      ((compactNormalization P i).hom.app (constant P Z) ≫ M ≫
        (ProEtale.derivedComparisonAdjunction
          (ModuleCat.{u + 1} P.Coefficient) X).unit.app (F.obj⟦a⟧))) = _
  rw [transpose_rightAdjointUniq (adjunction P i) (compactAdjunction P i)]
  simp only [Functor.map_comp, originIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.comp_map, asIso_hom, rightComparison]
  rfl

end AlgebraicGeometry
