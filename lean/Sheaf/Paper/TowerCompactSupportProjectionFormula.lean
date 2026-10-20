/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.Paper.SmoothPurityTowerShriekLevels
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.Algebra.Homology.KFlat
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Paper.OpenImmersionLocalizing
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.Algebra.Homology.RingedSiteTorFlatModel
import Sheaf.Paper.FiniteDiscreteCondensedRing
import Sheaf.Paper.FiniteDiscreteSchemeRing
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.CondensedConstantConstructibility
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence
import Sheaf.Paper.FiniteProperBaseChange
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Tower compact-support projection over an arbitrary standing field

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-integral-adjunction,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, paragraph (3)
(blueprint: lem-sp-tower-compact-support-projection-formula).

The section-site model, its tensor and all geometric operations are the recorded
SpTowerShriek operations. Constructibility is transported from the recorded full
subcategory of the ordinary derived category of coefficient towers. No normalization
or etale-origin witness is imposed. Index n always means positive exponent n+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerProjection

open SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Exact derived transport of the recorded sectionwise realization of towers.
Source: blueprint paragraph (3), ordinary tower category
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def realization (b : Base l E) (T : Scheme.{u})
    (A : SpCoefficientTowersAbelian l E T) :
    spDerivedCoefficientTowers l E T A ≌ D l E T :=
  letI := A.hasDerived
  letI := b.realizationAdditive T
  (b.realization T).mapDerivedCategory

/-- The existing Dctf predicate transported through the sectionwise derived equivalence.
This retains both independent uniform intervals and every finite-level constructibility
condition, and adds no cartesian condition.
Source: blueprint paragraph (3), Dctf inputs
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def constructibleTor (b : Base l E) (T : Scheme.{u})
    (A : SpCoefficientTowersAbelian l E T) (C : D l E T) : Prop :=
  spConstructibleTorTowers l E T A ((realization l E b T A).inverse.obj C)

/-- The proper counit transpose, formed before any finite-level test or Tor hypothesis.
Source: blueprint paragraph (3), pi_p
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def properMap (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (C : D l E X) (B : D l E Y) :
    (tensor l E b Y).obj ((F l E b o c).obj C, B) ⟶
      (push l E b (o.geometry c.g)).obj
        ((tensor l E b c.Z).obj ((openD l E b (o.openOp c.i)).obj C,
          (pull l E b (o.geometry c.g)).obj B)) :=
  ((adjunction l E b (o.geometry c.g)).homEquiv _ _)
    (((o.geometry c.g).tensorPullback).hom.app ((F l E b o c).obj C, B) ≫
      (tensor l E b c.Z).map (Prod.mkHom
        ((adjunction l E b (o.geometry c.g)).counit.app
          ((openD l E b (o.openOp c.i)).obj C)) (𝟙 _)))

/-- The open-unit transpose pi_j, then Rp_*. The dependency's openTensor_mate fixes
its inverse direction as exactly that transpose, including the pullback/tensor comparison.
Source: blueprint paragraph (3), Rp_*(pi_j)
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def openMap (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (C : D l E X) (B : D l E Y) :=
  (push l E b (o.geometry c.g)).map
    ((o.openTensor c.i C ((pull l E b (o.geometry c.g)).obj B)).inv)

/-- The source of the proper projection arrow, as a functor of both inputs.
Source: blueprint paragraph (3), naturality
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def source (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  ((F l E b o c).prod (𝟭 (D l E Y))) ⋙ tensor l E b Y

/-- The common target of the two arrows, as a functor of both inputs.
Source: blueprint paragraph (3), naturality
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def middle (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  ((openD l E b (o.openOp c.i)).prod (pull l E b (o.geometry c.g))) ⋙
    tensor l E b c.Z ⋙ push l E b (o.geometry c.g)

/-- The source of the open projection arrow, using j^{-1}p^{-1}=f^{-1}.
The comparison to the single pullback is the recorded o.comp followed by c.comm.
Source: blueprint paragraph (3), naturality
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def openSource (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  ((𝟭 (D l E X)).prod
    (pull l E b (o.geometry c.g) ⋙ pull l E b (o.geometry c.i))) ⋙
      tensor l E b X ⋙ F l E b o c

/-- Both constructed arrows are natural in both inputs in the ambient unbounded categories.
Source: blueprint paragraph (3), simultaneous section-model maps
(blueprint: lem-sp-tower-compact-support-projection-formula).
Proof: expand the proper counit transpose. Naturality of tensorPullback, the counit,
and the tensor bifunctor gives the first equation by the adjunction Hom equivalence.
For the second, apply Rp_* to the natural open-unit transpose. Its mate identity is
Operations.openTensor_mate; naturality of that unit and tensor gives the equation.
These are equations of actual tower maps, not equality detected by evaluations. -/
theorem maps_natural (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {C C' : D l E X} {B B' : D l E Y} (a : C ⟶ C') (d : B ⟶ B') :
    (source l E b o c).map (Prod.mkHom a d) ≫ properMap l E b o c C' B' =
      properMap l E b o c C B ≫ (middle l E b o c).map (Prod.mkHom a d) ∧
    (openSource l E b o c).map (Prod.mkHom a d) ≫ openMap l E b o c C' B' =
      openMap l E b o c C B ≫ (middle l E b o c).map (Prod.mkHom a d) := by
  sorry

/-- The finite-level tensor is the same recorded K-flat total tensor.
Source: blueprint paragraph (3), finite projection maps
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
abbrev levelTensor (b : Base l E) (T : Scheme.{u}) (n : ℕ) :=
  ((b.calculus T).levelClosed n).tensor

/-- The finite inverse-image/tensor comparison in the normalized evaluated coordinates.
Every factor is a specified comparison of the section model. Its representative map is
therefore the canonical pure-tensor pullback comparison by Geometry.tensorPullback_eq.
Source: blueprint paragraph (3), finite projection maps
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def levelPullTensor (b : Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : Geometry l E b f) (n : ℕ) (N B : D l E Y) :=
  (proEtaleConstantRingDerivedPullback (R l E n) f).mapIso
      (((b.calculus Y).tensorEvaluation n).app (N, B)).symm ≪≫
    ((g.pullEvaluation n).app ((tensor l E b Y).obj (N, B))).symm ≪≫
    (Ev l E X n).mapIso (g.tensorPullback.app (N, B)) ≪≫
    ((b.calculus X).tensorEvaluation n).app
      ((pull l E b g).obj N, (pull l E b g).obj B) ≪≫
    (levelTensor l E b X n).mapIso
      (((g.pullEvaluation n).app N).prod ((g.pullEvaluation n).app B))

/-- The finite derived inverse-image/direct-image adjunction, with its canonical
ordinary normalization. Source: blueprint paragraph (3), finite proper projection
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
abbrev levelAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (proEtaleConstantRingAdjunction (R l E n) f).mapDerivedCategoryRightDerivedAdjunction

/-- The finite proper projection map: the finite counit transpose of the canonical
finite pullback/tensor comparison. Evaluation comparisons only change coordinates;
the arrow is constructed by the finite adjunction, independently of properMap.
Source: blueprint paragraph (3), finite proper projection map
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def finiteProperMap (b : Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : Geometry l E b f) (n : ℕ) (N : D l E X) (B : D l E Y) :=
  ((levelAdjunction l E f n).homEquiv _ _)
    ((proEtaleConstantRingDerivedPullback (R l E n) f).map
        ((levelTensor l E b Y n).map
          (Prod.mkHom ((g.pushEvaluation n).inv.app N) (𝟙 _))) ≫
      (levelPullTensor l E b g n ((push l E b g).obj N) B).hom ≫
      (levelTensor l E b X n).map (Prod.mkHom
        ((proEtaleConstantRingDerivedPullback (R l E n) f).map
            ((g.pushEvaluation n).hom.app N) ≫
          (levelAdjunction l E f n).counit.app ((Ev l E X n).obj N))
        (𝟙 _)))

/-- The finite exact open adjunction, obtained by termwise localization of the
specified finite ordinary adjunction. No adjunction is chosen independently.
Source: blueprint paragraph (3), finite open projection map
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def levelOpenAdjunction (b : Base l E) {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (n : ℕ) :
    sfIntrinsicDerivedOpen (R l E n) j ⊣
      proEtaleConstantRingDerivedPullback (R l E n) j :=
  ((finiteOpenAdjunction l E b j n).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
    (proEtaleConstantRingPullback (R l E n) j).rightDerivedFunctorIsoMapDerivedCategory

/-- The finite open projection arrow is the finite unit transpose, using the same
normalized pullback/tensor comparison. It is constructed before comparing with the
open tower arrow. The occurrence of openEvaluation changes only the j_! coordinates.
Source: blueprint paragraph (3), finite open projection map
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def finiteOpenMap (b : Base l E) (o : Operations l E b)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ)
    (C : D l E U) (L : D l E T) :=
  ((levelOpenAdjunction l E b j n).homEquiv _ _).symm
    ((levelTensor l E b U n).map (Prod.mkHom
        ((levelOpenAdjunction l E b j n).unit.app ((Ev l E U n).obj C) ≫
          (proEtaleConstantRingDerivedPullback (R l E n) j).map
            ((openEvaluation l E b (o.openOp j) n).inv.app C)) (𝟙 _)) ≫
      (levelPullTensor l E b (o.geometry j) n
        ((openD l E b (o.openOp j)).obj C) L).inv ≫
      (proEtaleConstantRingDerivedPullback (R l E n) j).map
        ((levelTensor l E b T n).map
          (Prod.mkHom ((openEvaluation l E b (o.openOp j) n).hom.app C) (𝟙 _))))

/-- Evaluation of the proper arrow is the finite counit projection map, with all
specified tensor, pullback and direct-image comparisons displayed.
Source: blueprint paragraph (3), levelwise finite projection
(blueprint: lem-sp-tower-compact-support-projection-formula).
Proof: apply the generic Geometry.projectionEvaluation identity. Transport its
coefficients, target calculus and operations through Geometry.coefficients,
transitions, target, pull_eq, push_eq and tensorPullback_eq. The derived adjunction
is fixed by derivedAdjunction_eq and the finite adjunction by levelAdjunction_eq.
Expand levelPullTensor and finiteProperMap; naturality cancels the comparison and
inverse comparison pairs. This is the ordinary counit transpose at level n. -/
theorem properMap_evaluation (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (n : ℕ) (C : D l E X) (B : D l E Y) :
    (Ev l E Y n).map (properMap l E b o c C B) ≫
        ((o.geometry c.g).pushEvaluation n).hom.app
          ((tensor l E b c.Z).obj ((openD l E b (o.openOp c.i)).obj C,
            (pull l E b (o.geometry c.g)).obj B)) ≫
        (proEtaleConstantRingPushforward (R l E n) c.g).rightDerivedFunctor.map
          (((b.calculus c.Z).tensorEvaluation n).hom.app
              ((openD l E b (o.openOp c.i)).obj C,
                (pull l E b (o.geometry c.g)).obj B) ≫
            (levelTensor l E b c.Z n).map (Prod.mkHom (𝟙 _)
              (((o.geometry c.g).pullEvaluation n).hom.app B))) =
      ((b.calculus Y).tensorEvaluation n).hom.app ((F l E b o c).obj C, B) ≫
        (levelTensor l E b Y n).map
          (Prod.mkHom (((o.geometry c.g).pushEvaluation n).hom.app
            ((openD l E b (o.openOp c.i)).obj C)) (𝟙 _)) ≫
        finiteProperMap l E b (o.geometry c.g) n
          ((openD l E b (o.openOp c.i)).obj C) B := by
  sorry

/-- Evaluation of the open arrow is exactly the finite unit projection map.
Applying the proper direct-image evaluation comparison identifies evaluation of
openMap with Rp_* of this same finite map.
Source: blueprint paragraph (3), levelwise finite projection
(blueprint: lem-sp-tower-compact-support-projection-formula).
Proof: use Operations.openTensor_mate and the termwise localization of the open
unit. Evaluate this transpose using the ordinary unit_evaluation equation of Open,
its unit_termwise identity, tensorEvaluation, and the normalized pullEvaluation.
The finite exact adjunction is levelOpenAdjunction. Its Hom equivalence identifies
the evaluated arrow with finiteOpenMap. Naturality of pushEvaluation then applies
Rp_* to the equation, giving precisely the evaluation of openMap. -/
theorem openMap_evaluation (b : Base l E) (o : Operations l E b)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ)
    (C : D l E U) (L : D l E T) :
    (Ev l E T n).map ((o.openTensor j C L).inv) ≫
        ((b.calculus T).tensorEvaluation n).hom.app
          ((openD l E b (o.openOp j)).obj C, L) ≫
        (levelTensor l E b T n).map
          (Prod.mkHom ((openEvaluation l E b (o.openOp j) n).hom.app C) (𝟙 _)) =
      (openEvaluation l E b (o.openOp j) n).hom.app
          ((tensor l E b U).obj (C, (pull l E b (o.geometry j)).obj L)) ≫
        (sfIntrinsicDerivedOpen (R l E n) j).map
          (((b.calculus U).tensorEvaluation n).hom.app
              (C, (pull l E b (o.geometry j)).obj L) ≫
            (levelTensor l E b U n).map (Prod.mkHom (𝟙 _)
              (((o.geometry j).pullEvaluation n).hom.app L))) ≫
        finiteOpenMap l E b o j n C L := by
  sorry

/-- The tower projection formula over any field of positive characteristic different
from ell, for constructible finite-Tor towers with uniform bounds. Normalization is
not required. The two bounds put both tensor inputs in D+; the two IsIso clauses
refer to the actual proper and open adjunction transposes above. The final IsIso
clause uses the recorded pullback-composition comparison to identify j^{-1}p^{-1}
with f^{-1}.

The level-evaluation assertion is inherited from Geometry.projectionEvaluation,
Geometry.tensorPullback_eq and the ordinary unit/counit equations of Open, descended
termwise by Open.unit_termwise and Open.counit_termwise. Thus these are the finite
projection maps under the specified tensor and adjunction comparisons, rather than
unspecified levelwise isomorphisms.

Source: blueprint main-20261015, integral direct-image proof, paragraph (3)
(blueprint: lem-sp-tower-compact-support-projection-formula).

Proof:
1. At level n use ell = unit times uniformizer^e to identify the actual quotient
   with A_(E,e(n+1)). The finite-discrete condensed-ring and scheme-ring comparisons,
   followed by the internal-abelian-module equivalence, identify ordinary module
   sheaves with the finite coefficient module objects. The exact derived equivalence
   preserves tensor, constructibility and Tor intervals. Internal-module operations
   transport identifies inverse image, direct image and open extension together
   with their units and counits. The same holds for their derived adjunctions.
   Finite presented modules over a finite ring are exactly finite modules, so the
   recorded intrinsic Dctf tests are precisely the finite-coefficient ones.
2. Choose common cohomological bounds [a,b] for C and Tor bounds [v,w] for B.
   At each level the ringed-site Tor-flat-model lemma represents B by a flat complex
   in [v,w], hence K-flat by the bounded-above-flat K-flat lemma. Pullback preserves
   these flat K-flat complexes. Good truncation represents C in [a,b]; exact j_!
   retains those bounds. A flat-term K-flat resolution of either bounded complex
   computes its derived tensor with that model: the acyclic cone remains acyclic
   under tensor with a K-flat complex. Site-derived-tensor descent identifies this
   with the signed total tensor. It vanishes outside [a+v,b+w]. Exact evaluation and
   levelwise tower kernels and cokernels give both asserted lower bounds. These
   independent flat models test bounds and need not assemble to a strict tower.
3. On simultaneous section models form properMap by the counit transpose and
   openMap by applying Rp_* to the open-unit transpose. Evaluation preserves tensor,
   adjunctions, transposes and composition by semilinear-derived-sections, so these
   evaluate to the specified finite maps. Tower-shriek-levels identifies evaluation
   of F with Rp_*j_! on the bounded-below inputs just obtained. Naturality already
   holds before evaluation by maps_natural.
4. Exact open extension preserves the finite Dctf category. Apply finite proper
   projection to p, j_!C_n and B_n. It makes the evaluated properMap invertible.
   These finite-coefficient results require no algebraic closure or finiteness of k.
5. The finite open projection isomorphism has inverse the open-unit transpose:
   the unit/counit triangle identities identify its adjunct with unit tensor one.
   Its inverse is therefore the evaluated pi_j. Rp_* preserves this isomorphism,
   proving levelwise invertibility of openMap.
6. Joint conservativity in the ordinary unbounded tower derived category makes
   both actual maps invertible. Compose properMap with the inverse of openMap and
   the recorded pullback-composition identification. This is the recorded projection
   arrow, hence invertible. The inverse of a natural isomorphism is natural, giving
   canonicalIso and canonicalIso_natural below. No normalization, compatible finite
   flat resolutions or faithfulness of evaluation is used. -/
theorem tower_compact_support_projection_formula
    (b : Base l E) (o : Operations l E b)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hlp : l ≠ p)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (AX : SpCoefficientTowersAbelian l E X.left)
    (AY : SpCoefficientTowersAbelian l E Y.left)
    (C : D l E X.left) (B : D l E Y.left)
    (_hC : constructibleTor l E b X.left AX C)
    (_hB : constructibleTor l E b Y.left AY B) :
    (∃ m : ℤ, ((tensor l E b X.left).obj
      (C, (pull l E b (o.geometry f.left)).obj B)).IsGE m) ∧
    (∃ m : ℤ, ((tensor l E b c.Z).obj
      ((openD l E b (o.openOp c.i)).obj C,
        (pull l E b (o.geometry c.g)).obj B)).IsGE m) ∧
    IsIso (properMap l E b o c C B) ∧
    IsIso (openMap l E b o c C B) ∧
    IsIso (projection l E b o c C B) := by
  sorry

/-- The right side of the projection formula as a bifunctor, with f^{-1} explicit.
Source: blueprint paragraph (3), canonical natural isomorphism
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def target (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  ((𝟭 (D l E X)).prod (pull l E b (o.geometry f))) ⋙
    tensor l E b X ⋙ F l E b o c

/-- The canonical projection isomorphism, whose forward map is the specified mate
composite, not an independently selected isomorphism of evaluated towers.
Source: blueprint paragraph (3), final sentence
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def canonicalIso (b : Base l E) (o : Operations l E b)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hlp : l ≠ p)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (AX : SpCoefficientTowersAbelian l E X.left)
    (AY : SpCoefficientTowersAbelian l E Y.left)
    (C : D l E X.left) (B : D l E Y.left)
    (hC : constructibleTor l E b X.left AX C)
    (hB : constructibleTor l E b Y.left AY B) :
    (source l E b o c).obj (C, B) ≅ (target l E b o c).obj (C, B) :=
  letI := (tower_compact_support_projection_formula l E b o k p hlp X Y f c
    AX AY C B hC hB).2.2.2.2
  asIso (projection l E b o c C B)

/-- Naturality of the canonical isomorphism on the two full Dctf subcategories.
Source: blueprint paragraph (3), final sentence
(blueprint: lem-sp-tower-compact-support-projection-formula).
Proof: properMap and openMap are natural by maps_natural. Invert the latter natural
isomorphism, compose, and use naturality of the recorded pullback-composition map.
This identifies the composite with the forward map of canonicalIso, which is
projection by construction. Fullness means the input maps are arbitrary ambient
derived-tower morphisms. -/
theorem canonicalIso_natural (b : Base l E) (o : Operations l E b)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hlp : l ≠ p)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (AX : SpCoefficientTowersAbelian l E X.left)
    (AY : SpCoefficientTowersAbelian l E Y.left)
    {C C' : D l E X.left} {B B' : D l E Y.left}
    (hC : constructibleTor l E b X.left AX C)
    (hB : constructibleTor l E b Y.left AY B)
    (hC' : constructibleTor l E b X.left AX C')
    (hB' : constructibleTor l E b Y.left AY B')
    (a : C ⟶ C') (d : B ⟶ B') :
    (source l E b o c).map (Prod.mkHom a d) ≫
        (canonicalIso l E b o k p hlp X Y f c AX AY C' B' hC' hB').hom =
      (canonicalIso l E b o k p hlp X Y f c AX AY C B hC hB).hom ≫
        (target l E b o c).map (Prod.mkHom a d) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerProjection
