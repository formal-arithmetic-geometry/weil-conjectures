module

public import Sheaf.AlgebraicGeometry.SpaceZariskiDerivedComparison
public import Sheaf.AlgebraicGeometry.SpaceDerivedModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import Sheaf.AlgebraicGeometry.ProperSupportTensorPerfect
import Sheaf.AlgebraicGeometry.SpaceFlatComplexBaseChange
import WeilConjectures.AlgebraicGeometry.DerivedPullbackPreservesQCoh
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Perfect direct images and arbitrary base change for proper flat algebraic spaces

Source: Stacks Project, spaces-perfect.tex, Tags 0CTM, 071Q, 08H8, 08HG and 08GH
(blueprint: lem-sfb-proper-flat-space-derived-base-change).
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}
variable [∀ X : AlgebraicSpace S, HasDerivedCategory.{w} X.SmallModules]
variable [∀ T : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]

variable [∀ T : Scheme.{u}, ∀ U : T.Opens,
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over U))]

/-- A module in degree zero on its actual small model.
Source: Stacks 0CTM (blueprint: lem-sfb-proper-flat-space-derived-base-change). -/
def properFlatSpaceCoefficient (X : AlgebraicSpace S) (M : X.Modules) :=
  (DerivedCategory.singleFunctor X.SmallModules 0).obj (X.smallModuleRestriction.obj M)

/-- The direct-image functor followed by the actual right-derived Zariski restriction.
Source: Stacks 0CTM, 071Q and 08GH
(blueprint: lem-sfb-proper-flat-space-derived-base-change). -/
def properFlatSpaceImageFunctor {Y : Over S} {X : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) :=
  X.smallModuleRestriction ⋙ DerivedCategory.singleFunctor X.SmallModules 0 ⋙
    derivedDirectImage f ⋙
      (spaceZariskiRestriction Y).rightDerivedFunctor

/-- K_f(M) = R epsilon_* Rf_* M[0].
Source: Stacks 0CTM and 08GH
(blueprint: lem-sfb-proper-flat-space-derived-base-change). -/
abbrev properFlatSpaceImage {Y : Over S} {X : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (M : X.Modules) := (properFlatSpaceImageFunctor f).obj M

/-- The coefficient comparison is the universal derived-to-ordinary pullback map
on the degree-zero complex, followed by the actual single-complex comparison.
Source: Stacks 0A1K (blueprint: lem-sfb-proper-flat-space-derived-base-change). -/
def properFlatSpaceCoefficientMap {X X' : AlgebraicSpace S}
    (p : X' ⟶ X) (M : X.Modules) :
    (spaceDerivedPullback p).obj (properFlatSpaceCoefficient X M) ⟶
      properFlatSpaceCoefficient X' ((moduleTensorPullback p).obj M) :=
  (spaceDerivedPullback p).map
      ((DerivedCategory.singleFunctorIsoCompQ X.SmallModules 0).hom.app
        (X.smallModuleRestriction.obj M)) ≫
    (spaceDerivedPullbackCounit p).app
      ((HomologicalComplex.single X.SmallModules (.up ℤ) (0 : ℤ)).obj
        (X.smallModuleRestriction.obj M)) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (smallModuleTensorPullback p) (.up ℤ) (0 : ℤ)).hom.app
          (X.smallModuleRestriction.obj M)) ≫
    (DerivedCategory.singleFunctorIsoCompQ X'.SmallModules 0).inv.app _ ≫
    (DerivedCategory.singleFunctor X'.SmallModules 0).map
      ((smallRestrictionPullback p).hom.app M)

/-- The small-etale base-change map: exchange followed by the ordinary-coefficient map.
Source: Stacks 0A1K and 0CTM
(blueprint: lem-sfb-proper-flat-space-derived-base-change). -/
def properFlatSpaceEtaleBaseChange {Y Y' : Over S} {X X' : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (f' : X' ⟶ schemeSpace Y') (g : Y' ⟶ Y) (p : X' ⟶ X)
    (w : p ≫ f = f' ≫ traceSchemeMap g) (M : X.Modules) :
    (spaceDerivedPullback (traceSchemeMap g)).obj
        ((derivedDirectImage f).obj (properFlatSpaceCoefficient X M)) ⟶
      (derivedDirectImage f').obj
        (properFlatSpaceCoefficient X' ((moduleTensorPullback p).obj M)) :=
  moduleDerivedExchange f f' (traceSchemeMap g) p w (properFlatSpaceCoefficient X M) ≫
    (derivedDirectImage f').map (properFlatSpaceCoefficientMap p M)

/-- The canonical Zariski base-change map is the epsilon-adjoint of the pullback
comparison, the pulled epsilon counit, and the small-etale base-change map.
Source: Stacks 0CTM, 071Q and 08GH
(blueprint: lem-sfb-proper-flat-space-derived-base-change). -/
def properFlatSpaceBaseChange {Y Y' : Over S} {X X' : AlgebraicSpace S}
    (d : SpaceZariskiDerivedData Y) (d' : SpaceZariskiDerivedData Y')
    (g : Y' ⟶ Y) (r : SpaceZariskiDerivedSquare g d d')
    (f : X ⟶ schemeSpace Y) (f' : X' ⟶ schemeSpace Y') (p : X' ⟶ X)
    (w : p ≫ f = f' ≫ traceSchemeMap g) (M : X.Modules) :
    (AlgebraicGeometry.derivedPullback g.left).obj (properFlatSpaceImage f M) ⟶
      properFlatSpaceImage f' ((moduleTensorPullback p).obj M) :=
  d'.adjunction.homEquiv _ _
    ((spaceZariskiDerivedPullback g d d' r).hom.app (properFlatSpaceImage f M) ≫
      (spaceDerivedPullback (traceSchemeMap g)).map
        (d.adjunction.counit.app
          ((derivedDirectImage f).obj (properFlatSpaceCoefficient X M))) ≫
      properFlatSpaceEtaleBaseChange f f' g p w M)

/-- The scalar structure map into the direct image of O_X[0], including actual basis
restriction. Source: Stacks 0CTM and 08GH
(blueprint: lem-sfb-proper-flat-space-derived-base-change). -/
def properFlatSpaceEtaleScalar {Y : Over S} {X : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) : (schemeSpace Y).derivedStructure ⟶
      (derivedDirectImage f).obj
        (properFlatSpaceCoefficient X (SheafOfModules.unit X.structureSheaf)) :=
  (DerivedCategory.singleFunctor (schemeSpace Y).SmallModules 0).map
      (traceSmallStructureMap f) ≫
    traceDirectImageComparison f (SheafOfModules.unit X.smallStructureRings) ≫
    (derivedDirectImage f).map
      ((DerivedCategory.singleFunctor X.SmallModules 0).map (smallModuleUnitIso X).hom)

/-- The ordinary epsilon structure map, with the actual regular-function map on opens.
Source: Stacks 03FH (blueprint: lem-sfb-proper-flat-space-derived-base-change). -/
def properFlatSpaceEpsilonUnit (Y : Over S) :
    SheafOfModules.unit (moduleRings Y.left.toRingedSpace) ⟶
      (spaceZariskiRestriction Y).obj
        (SheafOfModules.unit (schemeSpace Y).smallStructureRings) :=
  letI : (schemeOpens (schemeSpace Y) (affineIdentityChart Y)).IsContinuous
      (Opens.grothendieckTopology Y.left) (schemeSpace Y).etaleTopology :=
    schemeOpens_isContinuous (schemeSpace Y) (affineIdentityChart Y)
  SheafOfModules.unitToPushforwardObjUnit
      (R := (schemeSpace Y).structureSheaf) (S := Y.left.ringCatSheaf)
      (F := schemeOpens (schemeSpace Y) (affineIdentityChart Y))
      ⟨schemeOpensRingHom (schemeSpace Y) (affineIdentityChart Y)⟩ ≫
    (schemeRestriction (schemeSpace Y) (affineIdentityChart Y)).map
      (fullModuleSection (schemeSpace Y)
        (SheafOfModules.unit (schemeSpace Y).smallStructureRings) (𝟙 _))

/-- The universal comparison from an ordinary direct image in degree zero to its
unbounded right derived image. Source: Stacks 079V
(blueprint: lem-sfb-proper-flat-space-derived-base-change). -/
def properFlatSpaceSingleRight
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ D) [F.Additive] (M : C) :
    (DerivedCategory.singleFunctor D 0).obj (F.obj M) ⟶
      F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M) :=
  (DerivedCategory.singleFunctorIsoCompQ D 0).hom.app _ ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) (0 : ℤ)).inv.app M) ≫
    spaceRightDerivedComplexUnit F
      ((HomologicalComplex.single C (.up ℤ) (0 : ℤ)).obj M) ≫
    F.rightDerivedFunctor.map ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app M)

/-- The derived scalar unit O_T[0] to K_f(O_X), using ordinary scalar insertion and
both universal right-derived units. Source: Stacks 0CTM, 071Q and 08GH
(blueprint: lem-sfb-proper-flat-space-derived-base-change). -/
def properFlatSpaceScalar {Y : Over S} {X : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) :
    (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.left.toRingedSpace)) 0).obj
      (SheafOfModules.unit (moduleRings Y.left.toRingedSpace)) ⟶
        properFlatSpaceImage f (SheafOfModules.unit X.structureSheaf) :=
  (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.left.toRingedSpace)) 0).map
      (properFlatSpaceEpsilonUnit Y) ≫
    properFlatSpaceSingleRight (spaceZariskiRestriction Y)
      (SheafOfModules.unit (schemeSpace Y).smallStructureRings) ≫
    (spaceZariskiRestriction Y).rightDerivedFunctor.map (properFlatSpaceEtaleScalar f)

/-- The canonical Zariski structure pullback, obtained by transposing the scalar map
and its universal right-derived comparison. Source: Stacks 08HY
(blueprint: lem-sfb-proper-flat-space-derived-base-change). -/
def properFlatSpaceZariskiStructure {Y Y' : Over S} (g : Y' ⟶ Y) :
    (AlgebraicGeometry.derivedPullback g.left).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.left.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings Y.left.toRingedSpace))) ⟶
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y'.left.toRingedSpace)) 0).obj
        (SheafOfModules.unit (moduleRings Y'.left.toRingedSpace)) :=
  ((canonicalSchemeDerivedAdjunction g.left).homEquiv _ _).symm
    ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.left.toRingedSpace)) 0).map
        (SheafOfModules.unitToPushforwardObjUnit g.left.toRingCatSheafHom) ≫
      properFlatSpaceSingleRight (RingedSpace.moduleDirectImage g.left.toLRSHom.toShHom)
        (SheafOfModules.unit (moduleRings Y'.left.toRingedSpace)))

/-- The canonical identity comparison already chosen with the derived-pullback
compositors. Source: Stacks 0D5S
(blueprint: lem-sfb-proper-flat-space-derived-base-change). -/
def properFlatSpacePullbackId (Y : Over S) :
    AlgebraicGeometry.derivedPullback (𝟙 Y.left) ≅ 𝟭 (schemeDerivedCategory Y.left) :=
  (Classical.choose
    ((Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))).2)) Y.left

/-- The ordinary structure pullback is the transpose of regular-function pullback.
Source: Stacks 03D7 (blueprint: lem-sfb-proper-flat-space-derived-base-change). -/
def properFlatSpaceOrdinaryStructure {X X' : AlgebraicSpace S} (p : X' ⟶ X) :
    (moduleTensorPullback p).obj (SheafOfModules.unit X.structureSheaf) ⟶
      SheafOfModules.unit X'.structureSheaf :=
  ((moduleTensorAdjunction p).homEquiv _ _).symm (moduleStructureMap p)

/-- All conclusions are imposed on the actual canonical arrows defined above.
The simultaneous data merely present epsilon on the equivalent small affine models;
no comparison arrow is arbitrary. Source: Stacks 0CTM, 071Q, 08H8, 08HG and 08GH
(blueprint: lem-sfb-proper-flat-space-derived-base-change). -/
structure ProperFlatSpaceDerivedBaseChangeSystem where
  data : ∀ Y : Over S, SpaceZariskiDerivedData Y
  square : ∀ {Y' Y : Over S} (g : Y' ⟶ Y),
    SpaceZariskiDerivedSquare g (data Y) (data Y')
  perfect : ∀ (Y : Over S) (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y),
    MapIsProper f → MapIsFlat f → MapIsLocallyOfFinitePresentation f →
    ∀ (M : X.Modules), M.IsQuasicoherent → M.IsFinitePresentation → ModuleIsFlatOver f M →
      Scheme.IsPerfect Y.left (properFlatSpaceImage f M)
  counit : ∀ (Y : Over S) (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y),
    MapIsProper f → MapIsFlat f → MapIsLocallyOfFinitePresentation f →
    ∀ (M : X.Modules), M.IsQuasicoherent → M.IsFinitePresentation → ModuleIsFlatOver f M →
      IsIso ((data Y).adjunction.counit.app
        ((derivedDirectImage f).obj (properFlatSpaceCoefficient X M)))
  baseChange : ∀ (Y Y' : Over S) (X X' : AlgebraicSpace S)
    (f : X ⟶ schemeSpace Y) (f' : X' ⟶ schemeSpace Y') (g : Y' ⟶ Y) (p : X' ⟶ X),
    MapIsProper f → MapIsFlat f → MapIsLocallyOfFinitePresentation f →
    ∀ (sq : IsPullback p f' f (traceSchemeMap g)) (M : X.Modules),
      M.IsQuasicoherent → M.IsFinitePresentation → ModuleIsFlatOver f M →
      IsIso (properFlatSpaceBaseChange (data Y) (data Y') g (square g) f f' p sq.w M)
  etaleIdentification : ∀ (Y Y' : Over S) (X X' : AlgebraicSpace S)
    (f : X ⟶ schemeSpace Y) (f' : X' ⟶ schemeSpace Y') (g : Y' ⟶ Y) (p : X' ⟶ X),
    MapIsProper f → MapIsFlat f → MapIsLocallyOfFinitePresentation f →
    ∀ (sq : IsPullback p f' f (traceSchemeMap g)) (M : X.Modules),
      M.IsQuasicoherent → M.IsFinitePresentation → ModuleIsFlatOver f M →
      (data Y').extension.map
          (properFlatSpaceBaseChange (data Y) (data Y') g (square g) f f' p sq.w M) ≫
        (data Y').adjunction.counit.app
          ((derivedDirectImage f').obj
            (properFlatSpaceCoefficient X' ((moduleTensorPullback p).obj M))) =
      (spaceZariskiDerivedPullback g (data Y) (data Y') (square g)).hom.app
          (properFlatSpaceImage f M) ≫
        (spaceDerivedPullback (traceSchemeMap g)).map
          ((data Y).adjunction.counit.app
            ((derivedDirectImage f).obj (properFlatSpaceCoefficient X M))) ≫
        properFlatSpaceEtaleBaseChange f f' g p sq.w M
  identity : ∀ (Y : Over S) (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y),
    MapIsProper f → MapIsFlat f → MapIsLocallyOfFinitePresentation f →
    ∀ (M : X.Modules), M.IsQuasicoherent → M.IsFinitePresentation → ModuleIsFlatOver f M →
    ∀ w : 𝟙 X ≫ f = f ≫ traceSchemeMap (𝟙 Y),
      properFlatSpaceBaseChange (data Y) (data Y) (𝟙 Y) (square (𝟙 Y)) f f (𝟙 X) w M ≫
        (properFlatSpaceImageFunctor f).map ((moduleTensorPullbackId X).hom.app M) =
      (properFlatSpacePullbackId Y).hom.app (properFlatSpaceImage f M)
  composition : ∀ (Y Y' Y'' : Over S) (g : Y' ⟶ Y) (k : Y'' ⟶ Y')
    (X X' X'' : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)
    (f' : X' ⟶ schemeSpace Y') (f'' : X'' ⟶ schemeSpace Y'') (p : X' ⟶ X) (q : X'' ⟶ X'),
    MapIsProper f → MapIsFlat f → MapIsLocallyOfFinitePresentation f →
    ∀ (sq : IsPullback p f' f (traceSchemeMap g))
      (sq' : IsPullback q f'' f' (traceSchemeMap k))
      (w : (q ≫ p) ≫ f = f'' ≫ traceSchemeMap (k ≫ g)) (M : X.Modules),
      M.IsQuasicoherent → M.IsFinitePresentation → ModuleIsFlatOver f M →
      (AlgebraicGeometry.derivedPullback k.left).map
          (properFlatSpaceBaseChange (data Y) (data Y') g (square g) f f' p sq.w M) ≫
        properFlatSpaceBaseChange (data Y') (data Y'') k (square k) f' f'' q sq'.w
          ((moduleTensorPullback p).obj M) ≫
        (properFlatSpaceImageFunctor f'').map ((moduleTensorComposition q p).hom.app M) =
      (canonicalDerivedPullbackComposition k.left g.left).hom.app
          (properFlatSpaceImage f M) ≫
        properFlatSpaceBaseChange (data Y) (data Y'') (k ≫ g) (square (k ≫ g))
          f f'' (q ≫ p) w M
  scalar : ∀ (Y Y' : Over S) (X X' : AlgebraicSpace S)
    (f : X ⟶ schemeSpace Y) (f' : X' ⟶ schemeSpace Y') (g : Y' ⟶ Y) (p : X' ⟶ X),
    MapIsProper f → MapIsFlat f → MapIsLocallyOfFinitePresentation f →
    ∀ sq : IsPullback p f' f (traceSchemeMap g),
      (AlgebraicGeometry.derivedPullback g.left).map (properFlatSpaceScalar f) ≫
        properFlatSpaceBaseChange (data Y) (data Y') g (square g) f f' p sq.w
          (SheafOfModules.unit X.structureSheaf) ≫
        (properFlatSpaceImageFunctor f').map (properFlatSpaceOrdinaryStructure p) =
      properFlatSpaceZariskiStructure g ≫ properFlatSpaceScalar f'

/-- Perfectness, the epsilon counit, arbitrary canonical derived base change and its
identity, composition and scalar-unit laws for proper flat finitely presented spaces.
Source: Stacks Project, spaces-perfect.tex, Tags 0CTM, 071Q, 08H8, 08HG and 08GH
(blueprint: lem-sfb-proper-flat-space-derived-base-change).

Proof:
1. Apply lem-sfb-proper-support-tensor-perfect with E = O_X[0] and G = M[0].
   The first is strictly perfect of rank one; the only coefficient term is finitely
   presented and relatively flat, and its annihilator support is closed in proper X.
   Thus A = Rf_*M[0] is etale perfect with quasi-coherent cohomology.
2. The derived etale--Zariski equivalence (lem-sfb-derived-etale-zariski-equivalence)
   supplies exact epsilon pullback and its invertible counit on A. The small affine
   basis equivalence transports that same comparison to SpaceZariskiDerivedData.
   Etale detection (lem-sfb-etale-detects-perfect) makes R epsilon_* A Zariski perfect.
3. Apply lem-sfb-space-flat-complex-base-change to O_X[0] and M[0]. Its exchange
   followed by the ordinary coefficient comparison is the displayed small-etale map.
   Scheme derived pullback preserves quasi-coherent cohomology; the comparison square
   then shows the target also has quasi-coherent cohomology.
4. Transport through the canonical epsilon counits. The mate definition and vertical
   pasting identify the transported map with exchange for the composite adjunctions.
   It is exactly properFlatSpaceBaseChange, and is invertible by full faithfulness.
5. Horizontal mate pasting proves composition. On coefficient representatives both
   paths send c tensor b tensor m to cb tensor m. Identity exchange and its coefficient
   map are the canonical unit comparisons. Faithfulness transfers these equations
   through epsilon; no assertion Lp*M = p*M is made from relative flatness alone.
6. For O_X, transpose the pulled scalar unit and exchange. The counit--unit triangle
   identity gives the identity of O_X'. Its transpose is the scalar unit for f'.
   Ordinary scalar insertion and the normalized derived units give the stated
   Zariski equality. These are the six proof steps of the node, with mate-pasting
   and def-weil-pbc-adjunction-mate supplying the canonical arrow calculations. -/
theorem properFlatSpace_derivedBaseChange :
    Nonempty (ProperFlatSpaceDerivedBaseChangeSystem (S := S)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
