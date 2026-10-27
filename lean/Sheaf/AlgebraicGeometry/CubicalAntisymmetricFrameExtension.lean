module

public import Sheaf.AlgebraicGeometry.RelativeMultiplicativeGroup
public import Sheaf.AlgebraicGeometry.CubicalRigidifiedLine
public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Sheaf.AlgebraicGeometry.SplitTorusTorsorFrameGeometry
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.SemiabelianGeometricPowerIntegrality
import Sheaf.AlgebraicGeometry.RelativeGroupUnitAxisFactorization
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.GroupScheme.ConnectedExtension
import Sheaf.AlgebraicGeometry.CommutativeMultiplicativeTypeExtension
import Sheaf.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

import Mathlib.AlgebraicGeometry.Morphisms.Separated

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import Mathlib.AlgebraicGeometry.Gluing

import Mathlib.CategoryTheory.Yoneda

import Mathlib.AlgebraicGeometry.Morphisms.Basic

import Mathlib.AlgebraicGeometry.Morphisms.Flat

import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # The antisymmetric cubical frame extension

Source: Moret-Bailly, Pinceaux de varietes abeliennes, I §2 and I §5; the explicit
agent construction in the DAG (blueprint: lem-sfb-cubical-antisymmetric-frame-extension).
The original source is WANTED. The cube restriction is specified in local frames on
arbitrary test schemes, including nonreduced schemes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.CubicalAntisymmetric

open Scheme.Modules SplitTorusFrames RelativeMultiplicativeGroup

/-- The antisymmetric line, with the actual internal-Hom dual.
Source: Moret-Bailly I §2, I §5
(blueprint: lem-sfb-cubical-antisymmetric-frame-extension). -/
def line {S : Scheme.{u}} {H : Over S} [CommGrpObj H]
    (L : CubicalRigidifiedLine H) : H.left.Modules :=
  L.line ⊗ dual ((tensorPullback (GrpObj.inv (X := H)).left).obj L.line)


/-- Evaluate the antisymmetric line in frames of the two factors, using evaluation
against the pulled-back dual. Source: Moret-Bailly I §2, I §5
(blueprint: lem-sfb-cubical-antisymmetric-frame-extension). -/
def frameMap {S : Scheme.{u}} {H : Over S} [CommGrpObj H]
    (L : CubicalRigidifiedLine H) {T : Scheme.{u}} (x : T ⟶ H.left)
    (b : CubicalLine.Frame T L.line) :
    (tensorPullback x).obj (line L) ⟶ 𝟙_ T.Modules :=
  (boundaryPullbackTensorIso x L.line
    (dual ((tensorPullback (GrpObj.inv (X := H)).left).obj L.line))).hom ≫
    ((b x).1 ⊗ₘ
      (CubicalLine.Word.factor (GrpObj.inv (X := H)).left true).frameMap x L.line b) ≫
    (λ_ _).hom


/-- Pull a multiplication isomorphism back to two generalized points, with the
normalized composition and tensor comparisons. Source: Moret-Bailly I §2, I §5
(blueprint: lem-sfb-cubical-antisymmetric-frame-extension). -/
def multiplicationAt {S : Scheme.{u}} {H : Over S} [CommGrpObj H]
    (L : CubicalRigidifiedLine H)
    (m : (tensorPullback (fst H H).left).obj (line L) ⊗
      (tensorPullback (snd H H).left).obj (line L) ≅
      (tensorPullback (μ[H]).left).obj (line L))
    (T : Over S) (x y : T ⟶ H) :
    (tensorPullback x.left).obj (line L) ⊗ (tensorPullback y.left).obj (line L) ≅
      (tensorPullback (x * y).left).obj (line L) :=
  (((eqToIso (congrArg (fun f ↦ (tensorPullback f).obj (line L))
      (congrArg Over.Hom.left (lift_fst x y)))).symm ≪≫
      (tensorPullbackSectionComp (lift x y).left (fst H H).left).app (line L)) ⊗ᵢ
    ((eqToIso (congrArg (fun f ↦ (tensorPullback f).obj (line L))
      (congrArg Over.Hom.left (lift_snd x y)))).symm ≪≫
      (tensorPullbackSectionComp (lift x y).left (snd H H).left).app (line L))) ≪≫
    (boundaryPullbackTensorIso (lift x y).left _ _).symm ≪≫
    (tensorPullback (lift x y).left).mapIso m ≪≫
    ((tensorPullbackSectionComp (lift x y).left (μ[H]).left).app (line L)).symm


/-- A frame evaluated at an arbitrary scheme point of its representing scheme.
This specializes the existing frame pullback, without a new frame functor.
Source: Stacks Tags 01M2, 01LX; Moret-Bailly I §2
(blueprint: lem-sfb-cubical-antisymmetric-frame-extension). -/
def frameAt {X : Scheme.{u}} {D : X.Modules} (F : FrameModel D)
    {T : Scheme.{u}} (x : T ⟶ F.space.left) :
    𝟙_ T.Modules ≅ (tensorPullback (x ≫ F.space.hom)).obj D :=
  pullFrame D F.space.hom F.frame x


/-- The actual frame scheme with its cube-induced group structure and all the
geometric and fppf exactness conclusions. Source: Moret-Bailly I §2, I §5;
Stacks Tags 01M2, 01LX
(blueprint: lem-sfb-cubical-antisymmetric-frame-extension). -/
structure Extension {S : Scheme.{u}} (H : Over S) [CommGrpObj H]
    (L : CubicalRigidifiedLine H) where
  /-- Actual scheme representing frames, with its universal frame. -/
  frames : FrameModel (line L)
  /-- Group law on that same frame scheme over S. -/
  [group : GrpObj ((Over.map H.hom).obj frames.space)]
  /-- Commutativity as a diagram of S-scheme morphisms. -/
  [commutative : IsCommMonObj ((Over.map H.hom).obj frames.space)]
  /-- The actual frame projection is a group homomorphism. -/
  [projectionHom : IsMonHom (Over.homMk frames.space.hom (by rfl) :
    (Over.map H.hom).obj frames.space ⟶ H)]
  /-- The multiplicative-line isomorphism on H times H. -/
  multiplication : (tensorPullback (fst H H).left).obj (line L) ⊗
    (tensorPullback (snd H H).left).obj (line L) ≅
      (tensorPullback (μ[H]).left).obj (line L)
  /-- Its exact scalar normalization: it is the inverse of the cube Hom frame. -/
  cube_formula (T : Over S) (x y : T ⟶ H) (b : CubicalLine.Frame T.left L.line)
      (hb : CubicalLine.Framed T ![x, y, (x * y)⁻¹] b) :
    (multiplicationAt L multiplication T x y).hom ≫ frameMap L (x * y).left b ≫
        CubicalLine.value L.sectionIso T ![x, y, (x * y)⁻¹] b =
      (frameMap L x.left b ⊗ₘ frameMap L y.left b) ≫ (λ_ _).hom
  /-- Multiplication of frames is induced by that sheaf isomorphism. Heterogeneous
  equality identifies the targets along the projection homomorphism law. -/
  frame_product (T : Over S) (x y : T ⟶ (Over.map H.hom).obj frames.space) :
    HEq (frameAt frames (x * y).left).hom
      ((λ_ _).inv ≫ ((frameAt frames x.left).hom ⊗ₘ (frameAt frames y.left).hom) ≫
        (multiplicationAt L multiplication T
          (x ≫ Over.homMk frames.space.hom (by rfl))
          (y ≫ Over.homMk frames.space.hom (by rfl))).hom)
  /-- The identity is the evaluation frame of e*L tensor its dual; the factors of
  the supplied rigidification cancel, so this formula is independent of its scale. -/
  identity_frame (b : CubicalLine.Frame S L.line)
      (hb : b.valid ((η[(Over.map H.hom).obj frames.space]).left ≫ frames.space.hom))
      (hi : b.valid (((η[(Over.map H.hom).obj frames.space]).left ≫ frames.space.hom) ≫
        (GrpObj.inv (X := H)).left)) :
    (frameAt frames (η[(Over.map H.hom).obj frames.space]).left).hom ≫
      frameMap L ((η[(Over.map H.hom).obj frames.space]).left ≫ frames.space.hom) b = 𝟙 _
  /-- The specified kernel inclusion. -/
  inclusion : multiplicative S ⟶ (Over.map H.hom).obj frames.space
  /-- The inclusion is a homomorphism. -/
  [inclusionHom : IsMonHom inclusion]
  /-- Its square is the scheme-theoretic kernel square. -/
  kernel : IsPullback inclusion (toUnit (multiplicative S))
    (Over.homMk frames.space.hom (by rfl)) η[H]
  /-- Fppf epimorphy of the quotient. -/
  locally_surjective : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
    (yoneda.map (Over.homMk frames.space.hom (by rfl) :
      (Over.map H.hom).obj frames.space ⟶ H))
  /-- The kernel action is precisely scalar multiplication on the universal frames. -/
  scaling (T : Over S) (a : T ⟶ multiplicative S)
      (x : T ⟶ (Over.map H.hom).obj frames.space) :
    HEq (frameAt frames ((a ≫ inclusion) * x).left).hom
      ((frameAt frames x.left).hom ≫
        ((tensorPullback (x.left ≫ frames.space.hom)).obj (line L)).smulHom (scalar a))
  /-- Smoothness over the original base. -/
  smooth : Smooth (frames.space.hom ≫ H.hom)
  /-- Separatedness over the original base. -/
  separated : IsSeparated (frames.space.hom ≫ H.hom)
  /-- Finite presentation over the original base. -/
  finitePresentation : LocallyOfFinitePresentation (frames.space.hom ≫ H.hom) ∧
    QuasiCompact (frames.space.hom ≫ H.hom) ∧ QuasiSeparated (frames.space.hom ≫ H.hom)
  /-- Semiabelian fibres for the supplied group law. -/
  semiabelian : HasSemiabelianGeometricFibres
    (Grp.mk ((Over.map H.hom).obj frames.space))
  /-- Affineness of the actual frame projection. -/
  affine : IsAffineHom frames.space.hom
  /-- Faithful flatness of that projection. -/
  faithfullyFlat : Flat frames.space.hom ∧ Surjective frames.space.hom
  /-- Finite presentation of that projection. -/
  projectionFinitePresentation : LocallyOfFinitePresentation frames.space.hom ∧
    QuasiCompact frames.space.hom ∧ QuasiSeparated frames.space.hom


/-- The antisymmetric part of a supplied cubical line has its multiplicative frame
extension, without positivity hypotheses or conclusions.

Source: Moret-Bailly I §2 and I §5, agent-formulated construction
(blueprint: lem-sfb-cubical-antisymmetric-frame-extension).
Proof:
1. Pullback, duality and tensor preserve lines (lem-weil-pbc-invertible-pullback-tensor).
   The rigidification and evaluation give the identity frame of D.
2. Restrict the eight-factor cube to (x,y,-x-y). Cancel the identity factors to
   obtain D_x tensor D_y tensor D_(x+y) dual. Its Hom frame has inverse mu.
   Symmetry and identity-slice normalization give commutativity and the unit laws.
3. The ratio of the two associative composites is a global unit on H cubed equal
   to one on its axes. The semiabelian-power integrality and geometric-connectedness
   criteria give geometrically connected fibres. The reduced-base alternative of
   lem-sfb-relative-group-unit-axis-factorization makes this ratio one.
4. Glue affine Laurent frame charts by their actual transition units
   (lem-weil-pbc-glue-schemes). The frame-product Laurent algebra proves affineness.
5. Multiply frames by mu. The inverse frame is obtained by its perfect pairing
   with the line over -x. Yoneda represents these natural operations as morphisms;
   the sheaf-map identities give all commutative group diagrams.
6. The fibre at the identity is exactly the scalar multiples of the identity frame,
   and kernel translation is frame scaling. Every pulled-back line has Zariski
   local frames; Zariski covers are fppf, giving the exact fppf sequence.
7. The Laurent charts make q smooth, flat and surjective, and finitely presented.
   Affineness gives quasi-compactness and separatedness, hence quasi-separatedness.
   Use smooth open restriction and source locality for smoothness and target
   open locality for finite presentation.
8. Composition of smooth, separated and finitely presented maps gives these
   properties for E over S.
9. On a geometric fibre pull the supplied torus back to E. This affine group is
   a smooth connected commutative extension of multiplicative-type groups, hence
   is multiplicative type and a torus by the largest-subtorus criterion. Its quotient
   is the given abelian variety, proving semiabelianity, including rank zero.
10. Evaluate the frame functor at its universal point: frames.frame is the
    tautological O_E isomorphism q*D; its inverse is the required trivialization.
-/
theorem cubical_antisymmetric_frame_extension {S : Scheme.{u}}
    [IsAffine S] [IsIntegral S] [IsNoetherian S]
    (hnormal : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (H : Over S) [CommGrpObj H] [Smooth H.hom] [IsSeparated H.hom]
    [LocallyOfFinitePresentation H.hom] [QuasiCompact H.hom]
    (hsemiabelian : HasSemiabelianGeometricFibres (Grp.mk H))
    (L : CubicalRigidifiedLine H) : Nonempty (Extension H L) := by
  sorry

end AlgebraicGeometry.CubicalAntisymmetric
