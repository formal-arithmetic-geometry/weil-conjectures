/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.DerivedPullbackTensorHom
public import WeilConjectures.Compactification.NagataCompactification
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorResolution

/-! # Symmetry of the concrete finite forward compact-support product

Source: Stacks, sites-cohomology.tex, Tag 0E48, remark-compatible-with-diagram,
and the preceding counit projection map; the forward-product consequence and its
compactification proof are the agent-formulated DAG node
(blueprint: def-pur-finite-forward-product).

The definitions are extracted without changing their bodies or signatures.
The same cartesian scheme represents both orders of the fibre product. Thus the
scheme-factor swap is the unique identification of these two cartesian cones;
after this identification its coefficient map is precisely the signed tensor symmetry.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u u'
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- Finiteness of the actual purity coefficient quotient, with its standard size lift.
Source: def-pur-conventions and the coefficient-extension finiteness theorem
(blueprint: def-pur-finite-forward-product). -/
instance finiteForwardCoefficient (C : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite C.Coefficient :=
  letI : Finite C.Ring := Padic.finite_coefficientExtensionRing
    C.coefficients.l C.extension C.level C.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} C.Ring))

section CoefficientCategory
variable (V : Type u') [Category.{u + 1} V] [Abelian V]
  [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V]
  [MonoidalPreadditive V] [SymmetricCategory V] [MonoidalClosed V]
  [Abelian.HasFunctorialFlatResolution V] [UpperStarPreservesFlat V]

/-- The derived symmetry is the unique lift of the signed homotopy-complex symmetry
through the left-derived tensor's comparison. Source: K-flat tensor localization
and def-weil-derived-pullback-tensor-hom
(blueprint: def-pur-finite-forward-tensor-symmetry). -/
def finiteForwardTensorSymmetryNat (T : Scheme.{u}) :
    (derivedTensor V T).flip ⟶ derivedTensor V T :=
  let μ := Functor.LaxMonoidal.μNatTrans
    (_root_.DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology T) V))
  let W := HomotopyCategory.quasiIso (Sheaf (Scheme.ProEt.topology T) V) (.up ℤ)
  (derivedTensor V T).leftDerived₂Lift μ W W (derivedTensor V T).flip
    ((flipFunctor _ _ _).map μ ≫
      Functor.whiskerRight ((flipFunctor _ _ _).map
        (BraidedCategory.curriedBraidingNatIso
          (HomotopyCategory (Sheaf (Scheme.ProEt.topology T) V) (.up ℤ))).hom)
        ((Functor.whiskeringRight
          (HomotopyCategory (Sheaf (Scheme.ProEt.topology T) V) (.up ℤ))
          (HomotopyCategory (Sheaf (Scheme.ProEt.topology T) V) (.up ℤ))
          (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) V))).obj
          _root_.DerivedCategory.Qh))

/-- The specified signed tensor symmetry on the small pro-etale site, evaluated
at its two objects. Source: the signed symmetry in the node's displayed Xi
(blueprint: def-pur-finite-forward-tensor-symmetry). -/
def finiteForwardTensorSymmetry (T : Scheme.{u})
    (K L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) V)) :
    ((derivedTensor V T).obj K).obj L ⟶ ((derivedTensor V T).obj L).obj K :=
  ((finiteForwardTensorSymmetryNat V T).app L).app K

variable {B X Z P : Scheme.{u}} {f : X ⟶ B} {g : Z ⟶ B}
  {p : P ⟶ X} {q : P ⟶ Z}

/-- Compact support for the second projection, with exactly the base-changed
compactification required by the concrete exchange map. Source: def-exchange-projection,
chosen compactification paragraph (blueprint: def-pur-finite-forward-product). -/
def finiteForwardProjectionSupport [HasCompactification f]
    (sq : IsPullback p q f g) :=
  rightDerivedLowerShriekOfCompactification V
    ((HasCompactification.compactification f).ofIsPullback sq)

/-- The existing counit-defined projection map with its two object components exposed.
This fixes no new transformation: it is literally the component of PF for c.
Source: def-exchange-projection, finite forward projection transformation
(blueprint: def-pur-finite-forward-product). -/
def finiteForwardProjectionMap {U W : Scheme.{u}} {t : U ⟶ W}
    (c : Compactification t)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) V))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology W) V)) :
    ((derivedTensor V W).obj
      ((rightDerivedLowerShriekOfCompactification V c).obj K)).obj L ⟶
      (rightDerivedLowerShriekOfCompactification V c).obj
        (((derivedTensor V U).obj K).obj (L(upperStar V t).obj L)) :=
  ((projectionMapOfCompactification V c).app K).app L

/-- The tensor-domain hypotheses for one order of the displayed composite.
Every field is a bounded-below etale-origin condition on an actual tensor object;
`external` is the condition needed to evaluate the normalized compositor.
The opposite order is required separately in the symmetry theorem.
Source: the tensor-domain paragraph of the node
(blueprint: def-pur-finite-forward-product). -/
structure FiniteForwardProductDomain [HasCompactification f] [HasCompactification g]
    (sq : IsPullback p q f g)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) V))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) V)) :
    Prop where
  input : DerivedCategory.plusEtaleOrigin V B
    (((derivedTensor V B).obj
      ((rightDerivedLowerShriek V f).obj M)).obj
      ((rightDerivedLowerShriek V g).obj N))
  firstProjection : DerivedCategory.plusEtaleOrigin V Z
    (((derivedTensor V Z).obj N).obj
      (L(upperStar V g).obj
        ((rightDerivedLowerShriek V f).obj M)))
  transposedProjection : DerivedCategory.plusEtaleOrigin V Z
    (((derivedTensor V Z).obj
      (L(upperStar V g).obj
        ((rightDerivedLowerShriek V f).obj M))).obj N)
  exchanged : DerivedCategory.plusEtaleOrigin V Z
    (((derivedTensor V Z).obj
      ((finiteForwardProjectionSupport V sq).obj
        (L(upperStar V p).obj M))).obj N)
  external : DerivedCategory.plusEtaleOrigin V P
    (((derivedTensor V P).obj
      (L(upperStar V p).obj M)).obj
      (L(upperStar V q).obj N))

/-- The first five arrows of Xi: symmetry, PF_g, symmetry under Rg_!, tensoring Ex_! with identity,
and PF_q, in that order. The compactification of q is exactly the base change of
that of f, so both occurrences of compact support use identical data.
Source: the displayed definition of Xi in the node, using def-exchange-projection
and thm-sf-comp-composition (blueprint: def-pur-finite-forward-product). -/
def finiteForwardProductPrefix [HasCompactification f] [HasCompactification g]
    (sq : IsPullback p q f g)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) V))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) V)) :
    ((derivedTensor V B).obj
        ((rightDerivedLowerShriek V f).obj M)).obj
        ((rightDerivedLowerShriek V g).obj N) ⟶
      (rightDerivedLowerShriek V g).obj
        ((finiteForwardProjectionSupport V sq).obj
        (((derivedTensor V P).obj
          (L(upperStar V p).obj M)).obj
          (L(upperStar V q).obj N))) :=
  (finiteForwardTensorSymmetry V B
      ((rightDerivedLowerShriek V f).obj M) ((rightDerivedLowerShriek V g).obj N)) ≫
    finiteForwardProjectionMap V (HasCompactification.compactification g) N
      ((rightDerivedLowerShriek V f).obj M) ≫
    (rightDerivedLowerShriek V g).map
      ((finiteForwardTensorSymmetry V Z N
        (L(upperStar V g).obj ((rightDerivedLowerShriek V f).obj M))) ≫
        ((derivedTensor V Z).map
          ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
            V sq (HasCompactification.compactification f)).app M)).app N) ≫
    (rightDerivedLowerShriek V g).map
      (finiteForwardProjectionMap V
        ((HasCompactification.compactification f).ofIsPullback sq)
        (L(upperStar V p).obj M) N)

/-- S in common cartesian coordinates: the equality of the two structure maps is
followed by Rh_! of the signed external tensor swap. The cone sq.flip represents
Z times_B X on P itself, so its unique scheme-factor identification is the identity.
Source: the factor-swap clause of the node
(blueprint: def-pur-finite-forward-product). -/
def finiteForwardProductSwap [HasCompactification (p ≫ f)] [HasCompactification (q ≫ g)]
    (sq : IsPullback p q f g)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) V))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) V)) :
    (rightDerivedLowerShriek V (p ≫ f)).obj
        (((derivedTensor V P).obj
          (L(upperStar V q).obj N)).obj
          (L(upperStar V p).obj M)) ⟶
      (rightDerivedLowerShriek V (q ≫ g)).obj
        (((derivedTensor V P).obj
          (L(upperStar V p).obj M)).obj
          (L(upperStar V q).obj N)) :=
  (rightDerivedLowerShriekCongr V sq.w).hom.app _ ≫
    (rightDerivedLowerShriek V (q ≫ g)).map
      (finiteForwardTensorSymmetry V P _ _)

end CoefficientCategory

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {B X Z P : Scheme.{u}} {f : X ⟶ B} {g : Z ⟶ B}
  {p : P ⟶ X} {q : P ⟶ Z}

/-- The canonical comparison of compactifications on the full bounded-below origin class.
It descends the specified etale common-refinement comparison through the canonical site
comparison, by full faithfulness; it chooses no arbitrary comparison morphism.
Source: thm-sf-comp-composition, normalized compactification comparisons
(blueprint: def-pur-finite-forward-product). -/
def finiteForwardCompactificationComparison {U V : Scheme.{u}} {t : U ⟶ V}
    [QuasiCompact t] (c e : Compactification t) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U).ι ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U).ι ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) e :=
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) U
  let model := compactSupportSiteComparison A c ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c e)
      (comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory ≪≫
    (compactSupportSiteComparison A e).symm
  (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso model

/-- Exactly Xi: symmetry, PF_g, symmetry under Rg_!, tensoring Ex_! with identity,
PF_q, and the normalized alpha_{g,q}, in that order. The compactification of q used
by PF_q is the base change of that of f. The last arrow includes the canonical
comparison from this compactification to the chosen one, before applying alpha.
Source: the displayed definition of Xi in the node, using def-exchange-projection
and thm-sf-comp-composition (blueprint: def-pur-finite-forward-product). -/
def finiteForwardProduct [HasCompactification f] [HasCompactification g]
    [HasCompactification q] [HasCompactification (q ≫ g)]
    [QuasiCompact q] [QuasiCompact g]
    (sq : IsPullback p q f g)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (hMN : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) P
      (((derivedTensor (ModuleCat.{u + 1} A) P).obj
        (L(upperStar (ModuleCat.{u + 1} A) p).obj M)).obj
        (L(upperStar (ModuleCat.{u + 1} A) q).obj N))) :
    ((derivedTensor (ModuleCat.{u + 1} A) B).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M)).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj N) ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (q ≫ g)).obj
        (((derivedTensor (ModuleCat.{u + 1} A) P).obj
          (L(upperStar (ModuleCat.{u + 1} A) p).obj M)).obj
          (L(upperStar (ModuleCat.{u + 1} A) q).obj N)) :=
  finiteForwardProductPrefix (ModuleCat.{u + 1} A) sq M N ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
      ((finiteForwardCompactificationComparison A
        ((HasCompactification.compactification f).ofIsPullback sq)
        (HasCompactification.compactification q)).hom.app ⟨_, hMN⟩) ≫
    (originCompositionAmbient A q g).hom.app ⟨_, hMN⟩

/-- The actual product symmetry equation, retaining both ordered tensor domains.
Source: the final displayed equality of the node
(blueprint: def-pur-finite-forward-product). -/
def FiniteForwardProductEquation [HasCompactification f] [HasCompactification g]
    [HasCompactification p] [HasCompactification q]
    [HasCompactification (p ≫ f)] [HasCompactification (q ≫ g)]
    [QuasiCompact p] [QuasiCompact q] [QuasiCompact f] [QuasiCompact g]
    (sq : IsPullback p q f g)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))) :
    Prop :=
  ∀ (d : FiniteForwardProductDomain (ModuleCat.{u + 1} A) sq M N)
    (d' : FiniteForwardProductDomain (ModuleCat.{u + 1} A) sq.flip N M),
    finiteForwardProduct A sq M N d.external =
      finiteForwardTensorSymmetry (ModuleCat.{u + 1} A) B _ _ ≫
        finiteForwardProduct A sq.flip N M d'.external ≫
        finiteForwardProductSwap (ModuleCat.{u + 1} A) sq M N

/-- The explicit equality of the two concrete products, on exactly the ordered tensor domains.
The specified input witnesses are retained as parameters; the canonical maps themselves
are independent of these choices. The finite-type structure maps provide the qcqs
instances needed by Nagata, without imposing additional hypotheses.
Source: the domain and equality in the node
(blueprint: def-pur-finite-forward-product). -/
def FiniteForwardPurityProductSymmetry
    (C : WeilConjectures.PurityFiniteSetting.{u})
    {B X Z : Scheme.{u}}
    [B.Over (Spec (CommRingCat.of C.field.k))]
    [X.Over (Spec (CommRingCat.of C.field.k))]
    [Z.Over (Spec (CommRingCat.of C.field.k))]
    [IsSeparated (B ↘ Spec (CommRingCat.of C.field.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of C.field.k))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of C.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (CommRingCat.of C.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of C.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of C.field.k))]
    [QuasiCompact (B ↘ Spec (CommRingCat.of C.field.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of C.field.k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of C.field.k))]
    (f : X ⟶ B) (g : Z ⟶ B)
    [f.IsOver (Spec (CommRingCat.of C.field.k))]
    [g.IsOver (Spec (CommRingCat.of C.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (M : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C.Coefficient)))
    (N : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} C.Coefficient)))
    (_wM : Scheme.FixedEtaleOriginWitness X C.Coefficient M)
    (_wN : Scheme.FixedEtaleOriginWitness Z C.Coefficient N) : Prop :=
  letI : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace
    (B ↘ Spec (CommRingCat.of C.field.k))
  letI : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated
    (B ↘ Spec (CommRingCat.of C.field.k))
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (CommRingCat.of C.field.k))
  letI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated
    (X ↘ Spec (CommRingCat.of C.field.k))
  letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace
    (Z ↘ Spec (CommRingCat.of C.field.k))
  letI : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated
    (Z ↘ Spec (CommRingCat.of C.field.k))
  FiniteForwardProductEquation C.Coefficient
    (IsPullback.of_hasPullback f g) M.obj N.obj

end AlgebraicGeometry.ProEtale
