/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.RingedCoefficientProjectionData
public import Sheaf.Paper.CommonQuotientTowerPresentation
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
public import Sheaf.Paper.RingedTopoiTensorSections
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.RingedTopoiTensorComparisonConstruction
import Sheaf.Paper.RingedTopoiTensorComparisonData
import Sheaf.Paper.FlatCommonQuotientReductionTower
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons

/-! # Common quotient reduction of geometric scalar insertion

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E, 0D6D;
sites-modules.tex, Tags 03D7, 03EK, 03EL.
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison).

The coefficient inverse image identifies R' with u^{-1}R and S'_n with u^{-1}S_n.
The latter identification is equivalent to the hypothesis that J'_n is generated
by u^{-1}J_n, by exactness of inverse image. Common quotients are specified by
locally surjective quotient projections and pushout squares, never by sectionwise
surjectivity. All comparisons retain their quotient-module action.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections (Mod D)
open SheafOfModules.RingedCoefficientProjection
open SheafOfModules.SuccessiveDerivedQuotient (restriction sectionTensor)
namespace SheafOfModules.CommonQuotientPullback

universe uA vA wA uB vB wB uE vE wE

/-- Computation data used to spell out the canonical pullback compositors. Every
instance below is built from the recorded localization counits or exact factorizations.
Source: Stacks 06YY (blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
structure Model (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] (B : Type uB) [Category.{vB} B] [Abelian B]
    [HasDerivedCategory.{wB} B] where
  ordinary : A ⥤ B
  [additive : ordinary.Additive]
  derived : DerivedCategory A ⥤ DerivedCategory B
  computation : ∀ H : HomotopyCategory A (.up ℤ),
    derived.obj (DerivedCategory.Qh.obj H) ⟶
      DerivedCategory.Qh.obj ((ordinary.mapHomotopyCategory (.up ℤ)).obj H)

attribute [instance] Model.additive

/-- Compose the actual computation maps, including the homotopy compositor.
Source: Stacks 06YY, 0D6D
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
def Model.comp {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasDerivedCategory.{wB} B] {E : Type uE} [Category.{vE} E] [Abelian E]
    [HasDerivedCategory.{wE} E] (F : Model A B) (G : Model B E) : Model A E where
  ordinary := F.ordinary ⋙ G.ordinary
  derived := F.derived ⋙ G.derived
  computation H := G.derived.map (F.computation H) ≫
    G.computation ((F.ordinary.mapHomotopyCategory (.up ℤ)).obj H) ≫
    DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (F.ordinary ⋙ G.ordinary)) (.up ℤ)).hom.app H)

/-- A compositor is fixed by its ordinary comparison and its K-flat computation
square. In particular this record does not assume any scalar-insertion coherence.
Source: Stacks 06YY, 0D6D
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
structure ModelIso {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasDerivedCategory.{wB} B] (F G : Model A B)
    (flat : CochainComplex A ℤ → Prop) where
  ordinary : F.ordinary ≅ G.ordinary
  derived : F.derived ≅ G.derived
  representative : ∀ P : CochainComplex A ℤ, flat P →
    derived.hom.app (DerivedCategory.Q.obj P) ≫
        G.computation ((HomotopyCategory.quotient _ _).obj P) =
      F.computation ((HomotopyCategory.quotient _ _).obj P) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory ordinary.hom (.up ℤ)).app
            ((HomotopyCategory.quotient _ _).obj P))

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}
  {uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
  {uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)} {adj : uInv ⊣ uPush}
  (g : Geometry uInv uPush adj)
  {pY : Scalars.{c, v, r} J} {pX : Scalars.{c, v, r} K}
  (nY : SuccessiveDerivedQuotient.Normalization (J := J) pY)
  (nX : SuccessiveDerivedQuotient.Normalization (J := K) pX)
  (e : Comparisons g nY nX)
  {R B : Sheaf J CommRingCat.{r}} (φ : R ⟶ B)
  {B' : Sheaf K CommRingCat.{r}} (a : g.rings.obj B ⟶ B')

/-- Ordinary ringed B-pullback: algebraic inverse image followed by actual scalar extension.
Source: Stacks 06YY (blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
abbrev ordinaryPullback := (g.inverse B).modules ⋙ (pX a).ordinary

/-- Its K-flat left derived functor; inverse image itself is exact.
Source: Stacks 06YY (blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
abbrev derivedPullback := g.left B ⋙ (pX a).derived

/-- The canonical homotopy-model computation map for ringed pullback.
Source: Stacks 06YY (blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
def pullbackComputation (P : HomotopyCategory (Mod J B) (.up ℤ)) :
    (derivedPullback g (pX := pX) a).obj (DerivedCategory.Qh.obj P) ⟶
      DerivedCategory.Qh.obj
        (((ordinaryPullback g (pX := pX) a).mapHomotopyCategory (.up ℤ)).obj P) :=
  (pX a).derived.map ((g.inverse B).modules.mapDerivedCategoryFactorsh.hom.app P) ≫
    (pX a).counit.app (((g.inverse B).modules.mapHomotopyCategory (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso
        (F := (g.inverse B).modules) (G := (pX a).ordinary)
        (Iso.refl (ordinaryPullback g (pX := pX) a)) (.up ℤ)).hom.app P)

/-- The unreduced source, using the exact R-coefficient inverse image.
Source: Stacks 06YY (blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
abbrev source := nY.right φ ⋙ g.left R

/-- The unreduced target, restricted along the commuting structural coefficient map.
Source: Stacks 06YY (blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
abbrev target := derivedPullback g (pX := pX) a ⋙ nX.right (g.rings.map φ ≫ a)

/-- The ordinary unreduced source functor.
Source: Stacks 03D7 (blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
abbrev ordinarySource := restriction φ ⋙ (g.inverse R).modules

/-- The ordinary unreduced target functor.
Source: Stacks 03D7 (blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
abbrev ordinaryTarget :=
  ordinaryPullback g (pX := pX) a ⋙ restriction (g.rings.map φ ≫ a)

/-- The exact source computation, with the canonical homotopy compositor included.
Source: Stacks 06YY (blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
def sourceComputation (H : HomotopyCategory (Mod J B) (.up ℤ)) :
    (source g nY φ).obj (DerivedCategory.Qh.obj H) ⟶
      DerivedCategory.Qh.obj (((ordinarySource g φ).mapHomotopyCategory (.up ℤ)).obj H) :=
  (g.left R).map ((nY.right_factors φ).hom.app H) ≫
    (g.inverse R).modules.mapDerivedCategoryFactorsh.hom.app
      (((restriction φ).mapHomotopyCategory (.up ℤ)).obj H) ≫
    DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso
        (F := restriction φ) (G := (g.inverse R).modules)
        (Iso.refl (ordinarySource g φ)) (.up ℤ)).inv.app H)

/-- The target computation, using scalar extension's universal counit and the exact
restriction factorization. This is invertible on the specified K-flat representatives.
Source: Stacks 06YY (blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
def targetComputation (H : HomotopyCategory (Mod J B) (.up ℤ)) :
    (target g nX φ a).obj (DerivedCategory.Qh.obj H) ⟶
      DerivedCategory.Qh.obj
        (((ordinaryTarget g (pX := pX) φ a).mapHomotopyCategory (.up ℤ)).obj H) :=
  (nX.right (g.rings.map φ ≫ a)).map (pullbackComputation g (pX := pX) a H) ≫
    (nX.right_factors (g.rings.map φ ≫ a)).hom.app
      (((ordinaryPullback g (pX := pX) a).mapHomotopyCategory (.up ℤ)).obj H) ≫
    DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso
        (F := ordinaryPullback g (pX := pX) a)
        (G := restriction (g.rings.map φ ≫ a))
        (Iso.refl (ordinaryTarget g (pX := pX) φ a)) (.up ℤ)).hom.app H)

/-- The normalized scalar-insertion comparison on ordinary sheaves and derived objects.
Its representative equation uses the universal counits, not an arbitrary derived lift.
Source: Stacks 03D7, 06YY
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
structure Insertion where
  ordinary : ordinarySource g φ ⟶ ordinaryTarget g (pX := pX) φ a
  sections : ∀ (M : Mod J B) (U : Xᵒᵖ)
    (x : ((g.inverse R).modules.obj ((restriction φ).obj M)).val.obj U),
    (ordinary.app M).val.app U x = sectionTensor (pX a) ((g.inverse B).modules.obj M) U 1
      (((g.inverse R).moduleUnderlying.hom.app ((restriction φ).obj M) ≫
        (g.inverse B).moduleUnderlying.inv.app M).hom.app U x)
  derived : source g nY φ ⟶ target g nX φ a
  representative : ∀ (P : CochainComplex (Mod J B) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := B) P →
    (∀ i : ℤ, IsFlatOnSite (J := J) (R := B) (P.X i)) →
    derived.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
        targetComputation g nX φ a ((HomotopyCategory.quotient _ _).obj P) =
      sourceComputation g nY φ ((HomotopyCategory.quotient _ _).obj P) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory ordinary (.up ℤ)).app
            ((HomotopyCategory.quotient _ _).obj P))

/-- The resolving class for all the compositor normalizations below.
Source: Stacks 06YS, 06YY
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
def flatTerms (P : CochainComplex (Mod J B) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := B) P ∧
    ∀ i : ℤ, IsFlatOnSite (J := J) (R := B) (P.X i)

/-- The recorded exact restriction model, with its actual factorization.
Source: Stacks 03D7, 06YY
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
def restrictionModel : Model (Mod J B) (Mod J R) where
  ordinary := restriction φ
  derived := nY.right φ
  computation H := (nY.right_factors φ).hom.app H

/-- The recorded exact inverse-image model.
Source: Stacks 07A6 (blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
def inverseModel : Model (Mod J R) (Mod K (g.rings.obj R)) where
  ordinary := (g.inverse R).modules
  derived := g.left R
  computation H := (g.inverse R).modules.mapDerivedCategoryFactorsh.hom.app H

/-- The unreduced source with its canonical computation.
Source: Stacks 06YY (blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
def sourceModel : Model (Mod J B) (Mod K (g.rings.obj R)) where
  ordinary := ordinarySource g φ
  derived := source g nY φ
  computation := sourceComputation g nY φ

/-- The unreduced target with its canonical computation.
Source: Stacks 06YY (blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
def targetModel : Model (Mod J B) (Mod K (g.rings.obj R)) where
  ordinary := ordinaryTarget g (pX := pX) φ a
  derived := target g nX φ a
  computation := targetComputation g nX φ a

/-- The ringed pullback model used in the successive geometric path.
Source: Stacks 06YY (blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
def pullbackModel : Model (Mod J B) (Mod K B') where
  ordinary := ordinaryPullback g (pX := pX) a
  derived := derivedPullback g (pX := pX) a
  computation := pullbackComputation g (pX := pX) a

/-- The actual ordinary pullback insertion, before any compositor is applied.
Source: Stacks 03D7 (blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
def pullbackInsertion (M : Mod J B) :
    uInv.obj ((underlying B).obj M) ⟶
      (underlying B').obj ((ordinaryPullback g (pX := pX) a).obj M) :=
  (g.inverse B).moduleUnderlying.inv.app M ≫
    RingedCoefficientProjection.insertion nX a ((g.inverse B).modules.obj M)

/-- Derived reduction followed by restriction, retaining the canonical quotient unit.
Source: Stacks 06YU, 07A6
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
abbrev restrictedReduction {A S : Sheaf K CommRingCat.{r}} (q : A ⟶ S) :=
  (pX q).derived ⋙ nX.right q

/-- The quotient transition, defined by the scalar-extension adjunction unit and the
normalized associators. No transition between derived objects is chosen independently.
Source: Stacks 03D7, 06YU
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
def reductionTransition {A S T : Sheaf K CommRingCat.{r}}
    (q : A ⟶ S) (t : S ⟶ T) (M : D K A) :
    (restrictedReduction nX q).obj M ⟶ (restrictedReduction nX (q ≫ t)).obj M :=
  (nX.right q).map ((nX.adjunction t).unit.app ((pX q).derived.obj M)) ≫
    (nX.rightComp q t).hom.app ((pX t).derived.obj ((pX q).derived.obj M)) ≫
    (nX.right (q ≫ t)).map ((nX.derived q t).hom.app M)

variable (Q : CommonQuotientTowerPresentation φ)
  (b : (Functor.const ℕᵒᵖ).obj B' ⟶ Q.S ⋙ g.rings)

/-- The quotient projection after the exact coefficient inverse image. Its kernel is
precisely the ideal generated by the inverse image of the original kernel ideal.
Source: Stacks 04JC, 03EL
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
abbrev quotient (n : ℕ) := g.rings.map (Q.projection n)

/-- Reduction of the source of scalar insertion, with the quotient action retained.
Source: Stacks 06YU, 06YY
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
abbrev finiteSource (n : ℕ) := source g nY φ ⋙ (pX (quotient g φ Q n)).derived

/-- Reduction of the target of scalar insertion in the same quotient-module category.
Source: Stacks 06YU, 06YY
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
abbrev finiteTarget (n : ℕ) := target g nX φ a ⋙ (pX (quotient g φ Q n)).derived

/-- Pullback of the original reduction, carrying its actual inverse-image quotient action.
Source: Stacks 03EL, 06YY
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
abbrev pulledReduction (n : ℕ) :=
  nY.right φ ⋙ (pY (Q.projection n)).derived ⋙ g.left (Q.S.obj (op n))

/-- The finite comparison and all its normalizations. Naturality is part of each natural
isomorphism. The inverse comparison is explicitly the inverse of reduced scalar insertion,
followed by the canonical inverse-image/tensor comparison. The quotient units and
transitions are those constructed from the normalized scalar adjunctions.

Source: Stacks 06YY, 0G7E, 0D6D, 03EL
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
structure Comparison where
  insertion : Insertion g nY nX φ a
  finite : ∀ n : ℕ, finiteSource g nY φ Q n ≅ finiteTarget g nX φ a Q n
  reduced_insertion : ∀ n : ℕ,
    (finite n).hom = Functor.whiskerRight insertion.derived
      (pX (quotient g φ Q n)).derived
  inverse : ∀ n : ℕ,
    finiteTarget g nX φ a Q n ≅ pulledReduction g nY φ Q n
  inverse_normalization : ∀ n : ℕ,
    inverse n = (finite n).symm ≪≫
      Functor.isoWhiskerLeft (nY.right φ) (e.derived (Q.projection n)).symm
  units : ∀ (n : ℕ) (M : D J B),
    (nX.adjunction (quotient g φ Q n)).unit.app ((source g nY φ).obj M) ≫
        (nX.right (quotient g φ Q n)).map ((finite n).hom.app M) =
      insertion.derived.app M ≫
        (nX.adjunction (quotient g φ Q n)).unit.app ((target g nX φ a).obj M)
  transitions : ∀ (n : ℕ) (M : D J B),
    (nX.right (quotient g φ Q (n + 1))).map ((finite (n + 1)).hom.app M) ≫
      reductionTransition nX (quotient g φ Q (n + 1))
        (g.rings.map (Q.S.map (homOfLE (Nat.le_succ n)).op))
        ((target g nX φ a).obj M) =
    reductionTransition nX (quotient g φ Q (n + 1))
        (g.rings.map (Q.S.map (homOfLE (Nat.le_succ n)).op))
        ((source g nY φ).obj M) ≫
      (nX.right (quotient g φ Q (n + 1) ≫
        g.rings.map (Q.S.map (homOfLE (Nat.le_succ n)).op))).map
          ((pX (quotient g φ Q (n + 1) ≫
            g.rings.map (Q.S.map (homOfLE (Nat.le_succ n)).op))).derived.map
              (insertion.derived.app M))
section Composition

variable {Z : Type c} [Category.{v} Z] [EssentiallySmall.{r} Z]
  {L : GrothendieckTopology Z}
  {vInv : Sheaf K (Type r) ⥤ Sheaf L (Type r)}
  {vPush : Sheaf L (Type r) ⥤ Sheaf K (Type r)} {vadj : vInv ⊣ vPush}
  {wInv : Sheaf J (Type r) ⥤ Sheaf L (Type r)}
  {wPush : Sheaf L (Type r) ⥤ Sheaf J (Type r)} {wadj : wInv ⊣ wPush}
  (g2 : Geometry vInv vPush vadj) (g12 : Geometry wInv wPush wadj)
  {pZ : Scalars.{c, v, r} L} (nZ : SuccessiveDerivedQuotient.Normalization (J := L) pZ)
  {B2 : Sheaf L CommRingCat.{r}} (a2 : g2.rings.obj B' ⟶ B2)
  (a12 : g12.rings.obj B ⟶ B2)
  (θ : wInv ≅ uInv ⋙ vInv) (ρ : g12.rings ≅ g.rings ⋙ g2.rings)

/-- The three geometric paths and their canonical ordinary and derived compositors.
The ordinary source map is the inverse-image compositor; the ordinary target map
is fixed on the scalar-extension insertion. Both derived maps have their explicit
flat-term K-flat computation squares. Ring transport is exact restriction along
the specified ring isomorphism, so all equations retain their coefficient action.
No field of this record asserts the insertion or finite-comparison coherence.
Source: Stacks 03EL, 06YY, 0D6D
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
structure CompositionData where
  coefficient : a12 = ρ.hom.app B ≫ g2.rings.map a ≫ a2
  rings : ∀ A : Sheaf J CommRingCat.{r},
    (g12.inverse A).ringUnderlying.hom ≫
        (sheafCompose L (CategoryTheory.forget CommRingCat.{r})).map (ρ.hom.app A) =
      θ.hom.app ((sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj A) ≫
        vInv.map (g.inverse A).ringUnderlying.hom ≫
        (g2.inverse (g.rings.obj A)).ringUnderlying.hom
  source : ModelIso (sourceModel g12 nY φ)
    (((sourceModel g nY φ).comp (inverseModel g2 (R := g.rings.obj R))).comp
      (restrictionModel nZ (ρ.hom.app R))) flatTerms
  source_sections : ∀ M : Mod J B,
    (underlying (g12.rings.obj R)).map (source.ordinary.hom.app M) ≫
        (g2.inverse (g.rings.obj R)).moduleUnderlying.hom.app
          ((g.inverse R).modules.obj ((restriction φ).obj M)) ≫
        vInv.map ((g.inverse R).moduleUnderlying.hom.app ((restriction φ).obj M)) =
      (g12.inverse R).moduleUnderlying.hom.app ((restriction φ).obj M) ≫
        θ.hom.app ((underlying R).obj ((restriction φ).obj M))
  target : ModelIso (targetModel g12 nZ φ a12)
    (((pullbackModel g (pX := pX) a).comp
      (targetModel g2 nZ (g.rings.map φ ≫ a) a2)).comp
        (restrictionModel nZ (ρ.hom.app R))) flatTerms
  target_sections : ∀ M : Mod J B,
    pullbackInsertion g12 nZ a12 M ≫
        (underlying (g12.rings.obj R)).map (target.ordinary.hom.app M) =
      θ.hom.app ((underlying B).obj M) ≫
        vInv.map (pullbackInsertion g nX a M) ≫
        pullbackInsertion g2 nZ a2 ((ordinaryPullback g (pX := pX) a).obj M)

/-- Actual composition equations, before reduction and in every quotient-module
category. The second equation reduces the same pasting of the g1 and g2 insertions,
with both canonical compositors included. It asserts equality of the finite forward
comparison with that pasting, not merely uniqueness for the fixed geometry.
Source: Stacks 03EL, 06YY, 0D6D
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
def CompositionLaw (c1 : Comparison g nY nX e φ a Q)
    (i2 : Insertion g2 nX nZ (g.rings.map φ ≫ a) a2)
    (e12 : Comparisons g12 nY nZ)
    (c12 : Comparison g12 nY nZ e12 φ a12 Q)
    (d : CompositionData g nY nX φ a g2 g12 nZ a2 a12 θ ρ) : Prop :=
  (∀ M : D J B,
    c12.insertion.derived.app M ≫ d.target.derived.hom.app M =
      d.source.derived.hom.app M ≫
        (nZ.right (ρ.hom.app R)).map
          ((g2.left (g.rings.obj R)).map (c1.insertion.derived.app M) ≫
            i2.derived.app ((derivedPullback g (pX := pX) a).obj M))) ∧
  ∀ (n : ℕ) (M : D J B),
    (c12.finite n).hom.app M ≫
        (pZ (quotient g12 φ Q n)).derived.map (d.target.derived.hom.app M) =
      (pZ (quotient g12 φ Q n)).derived.map
        (d.source.derived.hom.app M ≫
          (nZ.right (ρ.hom.app R)).map
            ((g2.left (g.rings.obj R)).map (c1.insertion.derived.app M) ≫
              i2.derived.app ((derivedPullback g (pX := pX) a).obj M)))

end Composition

section Identity

variable {iInv : Sheaf J (Type r) ⥤ Sheaf J (Type r)}
  {iPush : Sheaf J (Type r) ⥤ Sheaf J (Type r)} {iadj : iInv ⊣ iPush}
  (g0 : Geometry iInv iPush iadj) (a0 : g0.rings.obj B ⟶ B)
  (θ0 : iInv ≅ 𝟭 (Sheaf J (Type r)))
  (ρ0 : g0.rings ≅ 𝟭 (Sheaf J CommRingCat.{r}))

/-- Identity unitors are the ordinary inverse-image unitor and scalar
multiplication, with their canonical K-flat descents. This data fixes unitors only;
it does not assume the identity comparison equation.
Source: Stacks 03D7, 03EL, 06YY
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
structure IdentityData where
  coefficient : a0 = ρ0.hom.app B
  rings : ∀ A : Sheaf J CommRingCat.{r},
    (g0.inverse A).ringUnderlying.hom ≫
        (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).map (ρ0.hom.app A) =
      θ0.hom.app ((sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj A)
  source : ModelIso (sourceModel g0 nY φ)
    ((restrictionModel nY φ).comp (restrictionModel nY (ρ0.hom.app R))) flatTerms
  source_sections : ∀ M : Mod J B,
    (underlying (g0.rings.obj R)).map (source.ordinary.hom.app M) =
      (g0.inverse R).moduleUnderlying.hom.app ((restriction φ).obj M) ≫
        θ0.hom.app ((underlying R).obj ((restriction φ).obj M))
  target : ModelIso (targetModel g0 nY φ a0)
    ((restrictionModel nY φ).comp (restrictionModel nY (ρ0.hom.app R))) flatTerms
  target_sections : ∀ M : Mod J B,
    pullbackInsertion g0 nY a0 M ≫
        (underlying (g0.rings.obj R)).map (target.ordinary.hom.app M) =
      θ0.hom.app ((underlying B).obj M)

/-- After the normalized unitors the insertion and every finite comparison
are the identity, in the actual unchanged or quotient coefficient category.
Source: Stacks 03EL, 06YY, 0D6D
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
def IdentityLaw (e0 : Comparisons g0 nY nY)
    (c0 : Comparison g0 nY nY e0 φ a0 Q)
    (d : IdentityData nY φ g0 a0 θ0 ρ0) : Prop :=
  (∀ M : D J B,
    d.source.derived.inv.app M ≫ c0.insertion.derived.app M ≫
      d.target.derived.hom.app M = 𝟙 _) ∧
  ∀ (n : ℕ) (M : D J B),
    (pY (quotient g0 φ Q n)).derived.map (d.source.derived.inv.app M) ≫
      (c0.finite n).hom.app M ≫
      (pY (quotient g0 φ Q n)).derived.map (d.target.derived.hom.app M) = 𝟙 _

end Identity

/-- Identity and composition coherence for the comparison. The geometry g is
explicitly the first of two composable morphisms; g12 presents their composite.
All compositors are quantified with their ordinary and K-flat normalizations.
Source: Stacks 03EL, 06YY, 0D6D
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison). -/
structure Coherence (c1 : Comparison g nY nX e φ a Q) : Prop where
  composition : ∀ {Z : Type c} [Category.{v} Z] [EssentiallySmall.{r} Z]
    {L : GrothendieckTopology Z}
    {vInv : Sheaf K (Type r) ⥤ Sheaf L (Type r)}
    {vPush : Sheaf L (Type r) ⥤ Sheaf K (Type r)} {vadj : vInv ⊣ vPush}
    [PreservesFiniteLimits vInv]
    {wInv : Sheaf J (Type r) ⥤ Sheaf L (Type r)}
    {wPush : Sheaf L (Type r) ⥤ Sheaf J (Type r)} {wadj : wInv ⊣ wPush}
    (g2 : Geometry vInv vPush vadj) (g12 : Geometry wInv wPush wadj)
    {pZ : Scalars.{c, v, r} L}
    (nZ : SuccessiveDerivedQuotient.Normalization (J := L) pZ)
    {B2 : Sheaf L CommRingCat.{r}} (a2 : g2.rings.obj B' ⟶ B2)
    (a12 : g12.rings.obj B ⟶ B2)
    (θ : wInv ≅ uInv ⋙ vInv) (ρ : g12.rings ≅ g.rings ⋙ g2.rings)
    (i2 : Insertion g2 nX nZ (g.rings.map φ ≫ a) a2)
    (e12 : Comparisons g12 nY nZ) (c12 : Comparison g12 nY nZ e12 φ a12 Q)
    (d : CompositionData g nY nX φ a g2 g12 nZ a2 a12 θ ρ),
    CompositionLaw g nY nX e φ a Q g2 g12 nZ a2 a12 θ ρ c1 i2 e12 c12 d
  identity : ∀ {iInv : Sheaf J (Type r) ⥤ Sheaf J (Type r)}
    {iPush : Sheaf J (Type r) ⥤ Sheaf J (Type r)} {iadj : iInv ⊣ iPush}
    (g0 : Geometry iInv iPush iadj) (a0 : g0.rings.obj B ⟶ B)
    (θ0 : iInv ≅ 𝟭 (Sheaf J (Type r)))
    (ρ0 : g0.rings ≅ 𝟭 (Sheaf J CommRingCat.{r}))
    (e0 : Comparisons g0 nY nY) (c0 : Comparison g0 nY nY e0 φ a0 Q)
    (d : IdentityData nY φ g0 a0 θ0 ρ0),
    IdentityLaw nY φ Q g0 a0 θ0 ρ0 e0 c0 d

/-- The common-quotient comparison for an arbitrary geometric inverse image and flat
coefficient extensions. `R'` and `S'_n` have been identified with the inverse images
of `R` and `S_n`, as in the statement. The target quotient squares and the commuting
B-projections specify the compatible common quotients; no flatness of a is assumed.

Source: Stacks 06YY, 0G7E, 0D6D; sites-modules.tex 04JC, 03D7, 03EK, 03EL
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison).

Proof:
1. Choose one flat-term K-flat B-complex P representing M by the K-flat resolution
lemma. Flat scalar restriction makes its R-restriction K-flat with flat terms, and
exact restriction computes Res M. This single P works for every quotient level.
2. Exact inverse image transports the quotient and its kernel. Preservation of finite
products, coproducts and epimorphisms identifies the extended ideal with the ideal
of local finite sums of products. Thus the pulled-back common quotient is S'_n.
The coefficient R-pullback is exact and computes its derived functor on every complex.
3. Ringed pullback preserves K-flat complexes with flat terms (0G7E); the separate
flatness of R' to B' makes restriction of this pulled-back complex K-flat too.
4. Define ordinary insertion by r' tensor p mapping to its B'-image tensor p.
Balancing follows from the commuting structural square. The scalar-extension unit
is p mapping to 1 tensor p, and localization of the resolving class descends this
natural map with precisely the representative normalization in Insertion.
5. The source reduction is S'_n tensor over R' with the inverse image of Res P.
The canonical tensor/pullback comparison identifies this with pullback of the
original reduction, preserving its S'_n-action and its pure sections (03EL).
6. Flat common-quotient reduction identifies the target reduction with
S'_n tensor over B' with (B' tensor over inverse-image B with inverse-image P).
The collapse s tensor (b' tensor p) maps to s times b'-bar tensor p, with inverse
s tensor p mapping to s tensor (1 tensor p).
7. The remaining comparison identifies both sides with the quotient of inverse-image
P by the inverse-image ideal. All lifts are local. Reduced insertion is invertible,
and its inverse is S'_n-linear, in the actual quotient-module derived category.
8. The formulas commute with chain maps, and the K-flat localization equivalence
therefore gives independence of representative and naturality for every derived map.
9. Quotient transitions send s tensor p to t(s) tensor p; quotient units insert 1.
These formulas commute with insertion and its inverse by pure-tensor extensionality.
10. Canonical pullback compositors collapse b'' tensor (b' tensor p) to their product
tensor p. Twice inserting 1 and then collapsing equals inserting 1 once. For the
identity, the unitor sends 1 tensor p to p. Localization preserves these equalities;
the two normalized compositor squares give CompositionLaw explicitly. Scalar
extension to each quotient preserves this pasting equation. IdentityData gives
the ordinary multiplication unitors; their representative squares give IdentityLaw,
including the identity finite comparison. Inverting the finite comparisons and
using inverse_normalization preserves the same commuting diagrams. -/
theorem nonempty_comparison [PreservesFiniteLimits uInv]
    (hflat : IsFlatOnSite (J := J) (R := R)
      ((restriction φ).obj (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))))
    (hflat' : IsFlatOnSite (J := K) (R := g.rings.obj R)
      ((restriction (g.rings.map φ ≫ a)).obj
        (unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B'))))
    (hquotient : ∀ n : ℕ, IsPushout (g.rings.map φ ≫ a)
      (quotient g φ Q n) (b.app (op n)) (𝟙 _))
    (hcompatible : ∀ n : ℕ, a ≫ b.app (op n) = g.rings.map (Q.extensionProjection n)) :
    ∃ c1 : Comparison g nY nX e φ a Q, Coherence g nY nX e φ a Q c1 := by
  sorry

end SheafOfModules.CommonQuotientPullback
