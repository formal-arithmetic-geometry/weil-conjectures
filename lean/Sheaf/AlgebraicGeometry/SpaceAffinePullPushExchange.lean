module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
public import Sheaf.AlgebraicGeometry.SpaceAffineModuleBaseChange
public import Sheaf.AlgebraicGeometry.SpaceDerivedModuleOperations
public import Sheaf.AlgebraicGeometry.SpaceModuleDerivedExchange
public import Sheaf.AlgebraicGeometry.SpaceAffineSectionsCompositors
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap
public import Sheaf.Paper.ProjectionMateExact

import Sheaf.AlgebraicGeometry.SpaceAffineModuleHigherImageVanishing
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization
import Sheaf.Paper.RingedSliceDerivedAdjunction

/-! # Normalized affine pull-push and the exchange factorization

Source: Stacks Project, spaces-perfect.tex, Tags 08IJ and 08IR
(blueprint: lem-sfb-space-affine-pullpush-exchange).

All objects use the recorded small affine model of the small étale ringed topos.
The coefficient algebra is the ordinary compatible-chart direct image. The maps below
retain the universal derived units and counits, including for nonflat morphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}

/-- The ordinary structure algebra a_* O, defined for any morphism.
Source: Stacks, Tag 08IJ (blueprint: lem-sfb-space-affine-pullpush-exchange). -/
def affinePullPushAlgebra (a : X ⟶ Y) : Y.Modules :=
  (moduleDirectImage a).obj (SheafOfModules.unit X.structureSheaf)

/-- An original-site module in degree zero on the existing equivalent small model.
Source: Stacks, Tags 039Z and 08IJ
(blueprint: lem-sfb-space-affine-pullpush-exchange). -/
def affinePullPushSingle (Y : AlgebraicSpace S) [HasDerivedCategory.{w} Y.SmallModules]
    (M : Y.Modules) : Y.DerivedModules :=
  (DerivedCategory.singleFunctor Y.SmallModules 0).obj (Y.smallModuleRestriction.obj M)

variable [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]

/-- The canonical ordinary-to-derived map alpha_a, with the structure module identified
by the actual restriction comparison, rather than a chosen isomorphism.
Source: Stacks, Tag 08IJ, first proof paragraph
(blueprint: lem-sfb-space-affine-pullpush-exchange). -/
def affinePullPushAlpha (a : X ⟶ Y) :
    affinePullPushSingle Y (affinePullPushAlgebra a) ⟶
      (derivedDirectImage a).obj X.derivedStructure :=
  (DerivedCategory.singleFunctor Y.SmallModules 0).map
      (Y.smallModuleRestriction.map ((moduleDirectImage a).map
        (X.smallModuleEquivalence.unitIso.hom.app (SheafOfModules.unit X.structureSheaf)))) ≫
    (DerivedCategory.singleFunctorIsoCompQ Y.SmallModules 0).hom.app _ ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (smallModuleDirectImage a) (.up ℤ) 0).inv.app _) ≫
    spaceRightDerivedComplexUnit (smallModuleDirectImage a)
      ((HomologicalComplex.single X.SmallModules (.up ℤ) (0 : ℤ)).obj
        (X.smallModuleRestriction.obj (SheafOfModules.unit X.structureSheaf))) ≫
    (derivedDirectImage a).map
      ((DerivedCategory.singleFunctorIsoCompQ X.SmallModules 0).inv.app _ ≫
        (DerivedCategory.singleFunctor X.SmallModules 0).map (smallModuleUnitIso X).inv)

/-- The specified lambda is the adjoint of tensor comparison, evaluation through alpha,
and the scalar-multiplication right unitor. No inverse of alpha is used in its definition.
Source: Stacks, Tag 08IJ, canonical arrow in the proof
(blueprint: lem-sfb-space-affine-pullpush-exchange). -/
def affinePullPushLambda (a : X ⟶ Y) (F : Y.DerivedModules) :
    Y.derivedDualityModel.closed.tensor.obj
        (F, affinePullPushSingle Y (affinePullPushAlgebra a)) ⟶
      (derivedDirectImage a).obj ((spaceDerivedPullback a).obj F) :=
  (spaceDerivedAdjunction a).homEquiv _ _
    ((moduleDerivedPullbackTensor a).hom.app
        (F, affinePullPushSingle Y (affinePullPushAlgebra a)) ≫
      X.derivedDualityModel.closed.tensor.map
        (Prod.mkHom (𝟙 _) ((spaceDerivedPullback a).map (affinePullPushAlpha a) ≫
          (spaceDerivedAdjunction a).counit.app X.derivedStructure)) ≫
      X.derivedDualityModel.closed.tensor.map
        (Prod.mkHom (𝟙 _) X.derivedDualityModel.unitIso.inv) ≫
      (X.derivedDualityModel.closed.monoidal.rightUnitor
        ((spaceDerivedPullback a).obj F)).hom)

/-- The affine coefficient algebra is quasi-coherent, alpha is invertible, and the
specified counit-defined lambda is invertible on every unbounded D_QCoh object.
Source: Stacks, Tags 08IJ and 073H
(blueprint: lem-sfb-space-affine-pullpush-exchange).

Proof:
1. The rank-one structure module is quasi-coherent. Apply affine module base change
to a and the identity to obtain quasi-coherence of its direct image. Affine higher-image
vanishing gives zero positive cohomology of Ra_* O; the degree-zero injective resolution
has zero negative cohomology and degree-zero image a_* O. The universal comparison alpha
is the identity there, so the cohomology criterion makes alpha invertible.
2. Restrict to an affine étale scheme covering of the target. Derived étale chart
calculus preserves adjunctions and tensor, ordinary affine base change preserves the
algebra and its evaluation, and affine locality makes the source charts affine schemes.
The restrictions of lambda are thus the corresponding normalized affine scheme maps.
Their being isomorphisms can be checked on the cover by the cohomology of the cone.
3. The derived étale--Zariski and affine QCoh equivalences identify pullback with
B tensor_A^L (-) and pushforward with restriction of scalars, preserving the counit.
Choose a module K-flat representative P for F, using the source-module resolution theorem.
Both sides become P tensor_A B. The transpose is the augmentation from
B tensor_A^L (P tensor_A B), followed by b tensor p tensor b' mapping to bb' tensor p.
Precomposing with the adjunction unit gives p tensor b' mapping to b' tensor p, an
isomorphism. The augmentation itself is never inverted. This includes nonflat A to B
and unbounded P. Descent gives invertibility of the precise lambda in the statement. -/
theorem affine_pullpush_normalized (a : X ⟶ Y)
    (ha : IsRepresentable a.hom.hom) (haa : MapIsAffine a)
    (F : Y.DerivedModules) (hF : Y.derivedQCohProperty F) :
    (affinePullPushAlgebra a).IsQuasicoherent ∧
      IsIso (affinePullPushAlpha a) ∧ IsIso (affinePullPushLambda a F) := by
  sorry

/-- Naturality of the specified pull-push map on D_QCoh.
Source: Stacks, Tag 08IJ (blueprint: lem-sfb-space-affine-pullpush-exchange).
Proof: tensor comparison, alpha, the derived counit and the scalar right unitor are
natural. Naturality of the adjunction bijection therefore gives the displayed equation,
independently of the K-flat representative chosen in the invertibility argument. -/
theorem affinePullPushLambda_naturality (a : X ⟶ Y)
    (ha : IsRepresentable a.hom.hom) (haa : MapIsAffine a)
    (F G : Y.DerivedModules) (hF : Y.derivedQCohProperty F)
    (hG : Y.derivedQCohProperty G) (q : F ⟶ G) :
    Y.derivedDualityModel.closed.tensor.map
        (Prod.mkHom q (𝟙 (affinePullPushSingle Y (affinePullPushAlgebra a)))) ≫
        affinePullPushLambda a G =
      affinePullPushLambda a F ≫ (derivedDirectImage a).map ((spaceDerivedPullback a).map q) :=
  by sorry

variable [HasDerivedCategory.{w} X'.SmallModules] [HasDerivedCategory.{w} Y'.SmallModules]

/-- The ordinary affine coefficient base-change identification, expressed as its
canonical map: ordinary base change on O followed by ordinary structure evaluation.
Its construction makes sense without an affineness assumption.
Source: Stacks, Tags 07U8 and 08IR
(blueprint: lem-sfb-space-affine-pullpush-exchange). -/
def affinePullPushOrdinaryCoefficient (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h : X' ⟶ X) (f' : X' ⟶ Y') (sq : h ≫ f = f' ≫ g) :
    (moduleTensorPullback f).obj (affinePullPushAlgebra g) ⟶ affinePullPushAlgebra h :=
  (moduleBaseChange g f f' h sq.symm).app (SheafOfModules.unit Y'.structureSheaf) ≫
    (moduleDirectImage h).map
      (((moduleTensorAdjunction f').homEquiv _ _).symm (moduleStructureMap f'))

/-- The ordinary coefficient map is the affine module base-change identification.
Source: Stacks, Tags 07U8 and 08IR
(blueprint: lem-sfb-space-affine-pullpush-exchange).
Proof: apply affine_moduleDirectImage_baseChange with affine arrow g, base map f,
and the structure module on Y'. Its canonical mate is invertible. Ordinary tensor
pullback of O is O: b tensor c maps to b times the pulled-back c, and the inverse
inserts the unit scalar. This is exactly the adjoint of moduleStructureMap f', by
its chart projections and the fixed scalar-one unit. Applying direct image preserves
that isomorphism; their composite is the stated ordinary coefficient map. -/
theorem affinePullPushOrdinaryCoefficient_isIso (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h : X' ⟶ X) (f' : X' ⟶ Y')
    (hg : IsRepresentable g.hom.hom) (hga : MapIsAffine g)
    (sq : IsPullback h f' f g) :
    IsIso (affinePullPushOrdinaryCoefficient f g h f' sq.w) := by
  sorry

/-- The coefficient c: derived-to-ordinary pullback, followed by ordinary affine module
base change. This uses the universal derived counit on the actual degree-zero complex.
Source: Stacks, Tag 08IR, before the Tor-independence step
(blueprint: lem-sfb-space-affine-pullpush-exchange). -/
def affinePullPushCoefficient (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h : X' ⟶ X) (f' : X' ⟶ Y') (sq : h ≫ f = f' ≫ g) :
    (spaceDerivedPullback f).obj (affinePullPushSingle Y (affinePullPushAlgebra g)) ⟶
      affinePullPushSingle X (affinePullPushAlgebra h) :=
  (spaceDerivedPullback f).map
      ((DerivedCategory.singleFunctorIsoCompQ Y.SmallModules 0).hom.app _) ≫
    (spaceDerivedPullbackCounit f).app
      ((HomologicalComplex.single Y.SmallModules (.up ℤ) 0).obj
        (Y.smallModuleRestriction.obj (affinePullPushAlgebra g))) ≫
    DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
      (smallModuleTensorPullback f) (.up ℤ) 0).hom.app _) ≫
    (DerivedCategory.singleFunctorIsoCompQ X.SmallModules 0).inv.app _ ≫
    (DerivedCategory.singleFunctor X.SmallModules 0).map
      ((smallRestrictionPullback f).hom.app (affinePullPushAlgebra g) ≫
        X.smallModuleRestriction.map (affinePullPushOrdinaryCoefficient f g h f' sq))

/-- The normalized comparison Rg_* Rf'_* to Rf_* Rh_* for a commuting square,
using precisely the right-adjoint conjugates of pullback composition.
Source: Stacks, Tags 0D6D, 0D6E and 08IR
(blueprint: lem-sfb-space-affine-pullpush-exchange). -/
def affinePullPushDirectImageSquare (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h : X' ⟶ X) (f' : X' ⟶ Y') (sq : h ≫ f = f' ≫ g) :
    derivedDirectImage f' ⋙ derivedDirectImage g ≅
      derivedDirectImage h ⋙ derivedDirectImage f :=
  spaceDerivedChartDirectImageComp g f' ≪≫
    eqToIso (congrArg (fun k : X' ⟶ Y ↦
      (derivedDirectImage k : X'.DerivedModules ⥤ Y.DerivedModules)) sq.symm) ≪≫
      (spaceDerivedChartDirectImageComp f h).symm

/-- The pushed-forward derived exchange factors through the counit-defined projection
map and the derived-to-ordinary affine coefficient map. No invertibility of exchange,
the coefficient map or the projection map is asserted.
Source: Stacks, Tag 08IR, proof before its Tor-independence step; Tag 08IJ
(blueprint: lem-sfb-space-affine-pullpush-exchange).

Proof:
4. Base change of the affine g makes h affine. Ordinary affine module base change
on O gives d:f^* A to B, with transpose evaluation after canonical pullback composition.
Compute c on one flat-term K-flat resolution of A[0]. Both iterated evaluations send
u tensor (v tensor z) to u times h-sharp(v) times the restricted evaluation of z.
Normalized K-flat word descent and the chain-map normalization of the derived adjunction
give t_h composed with Lh^*c equal to Lf'^*t_g. No augmentation is inverted.
5. Put M=Rf_*E. Transpose both arrows from M tensor^L A[0] under the composite
adjunction. Composition comparisons are mates. Expanding lambda and exchange gives
the tensor of the pulled f-counit and Lf'^*t_g; expanding the projection mate and lambda_h
gives the tensor of the same pulled counit and t_h composed with Lh^*c, followed by
the scalar unitor. Step 4 and tensor functoriality identify these transposes. Injectivity
of the adjunction bijection proves the displayed equality. The normalized affine
pull-push theorem applies to g,M and h,E by the two QCoh hypotheses. The calculation
uses no flatness, boundedness, Tor independence, properness or Noetherian assumption. -/
theorem affine_pullpush_exchange (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h : X' ⟶ X) (f' : X' ⟶ Y')
    (hg : IsRepresentable g.hom.hom) (hga : MapIsAffine g)
    (sq : IsPullback h f' f g)
    (E : X.DerivedModules) (hE : X.derivedQCohProperty E)
    (hfE : Y.derivedQCohProperty ((derivedDirectImage f).obj E)) :
    affinePullPushLambda g ((derivedDirectImage f).obj E) ≫
        (derivedDirectImage g).map (moduleDerivedExchange f f' g h sq.w E) ≫
        (affinePullPushDirectImageSquare f g h f' sq.w).hom.app
          ((spaceDerivedPullback h).obj E) =
      derivedProjectionFormulaMate (spaceDerivedPullback f) (derivedDirectImage f)
          (spaceDerivedAdjunction f) Y.derivedDualityModel.closed.tensor
          X.derivedDualityModel.closed.tensor (moduleDerivedPullbackTensor f)
          E (affinePullPushSingle Y (affinePullPushAlgebra g)) ≫
        (derivedDirectImage f).map (X.derivedDualityModel.closed.tensor.map
          (Prod.mkHom (𝟙 E) (affinePullPushCoefficient f g h f' sq.w))) ≫
        (derivedDirectImage f).map (affinePullPushLambda h E) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
