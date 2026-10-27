module

public import Sheaf.AlgebraicGeometry.LineBiextension
public import Sheaf.AlgebraicGeometry.CubicalRigidifiedLine
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.LineAlgebraicEquivalence
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.SplitTorusTorsorFrameGeometry
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.RelativeGroupUnitAxisFactorization
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
import Sheaf.AlgebraicGeometry.AbelianVariety.MultiplicationAlgebraicEquivalence
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure

/-! # Second difference on a semiabelian variety

Source: Moret-Bailly I §§2, 5, 7.2; Lan §§3.2.1--3.2.3 and §3.2.5;
Milne, Abelian Varieties, I Remark 10.19.
(blueprint: lem-sfb-semiabelian-second-difference-diagonal)

The line is the literal three-factor tensor from the node. The frame formula below fixes
its identity-axis trivializations from the supplied rigidification, without choosing a
cancellation isomorphism. The geometric quotient hypothesis is an exact fppf sequence
only after extension to the algebraic closure; it asserts no splitting over the base field.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
namespace AlgebraicGeometry
namespace SemiabelianSecondDifference

/-- The literal second-difference line, with pullback of the internal-Hom dual.
Source: Moret-Bailly I §2; Lan (3.2.2.3)
(blueprint: lem-sfb-semiabelian-second-difference-diagonal). -/
noncomputable def line {S : Scheme.{u}} (H : Over S) [CommGrpObj H]
    (L : H.left.Modules) : (H ⊗ H).left.Modules :=
  ((Scheme.Modules.tensorPullback (μ[H]).left).obj L ⊗
    (Scheme.Modules.tensorPullback (fst H H).left).obj (Scheme.Modules.dual L)) ⊗
      (Scheme.Modules.tensorPullback (snd H H).left).obj (Scheme.Modules.dual L)

/-- Evaluate the pullback of a dual factor in the inverse of a local frame of L.
Source: Moret-Bailly I §2, tensor cancellation
(blueprint: lem-sfb-semiabelian-second-difference-diagonal). -/
noncomputable def negativeFrame {X Y T : Scheme.{u}} (q : T ⟶ X) (a : X ⟶ Y)
    (L : Y.Modules) (b : CubicalLine.Frame T L) :
    (Scheme.Modules.tensorPullback q).obj
      ((Scheme.Modules.tensorPullback a).obj (Scheme.Modules.dual L)) ⟶ 𝟙_ T.Modules :=
  ((Scheme.Modules.tensorPullbackSectionComp q a).app (Scheme.Modules.dual L)).inv ≫
    (λ_ _).inv ≫ ((b (q ≫ a)).2 ▷
      (Scheme.Modules.tensorPullback (q ≫ a)).obj (Scheme.Modules.dual L)) ≫
    (Scheme.Modules.boundaryPullbackTensorIso (q ≫ a) L (Scheme.Modules.dual L)).inv ≫
    (Scheme.Modules.tensorPullback (q ≫ a)).map (Scheme.Modules.dualEvaluation L) ≫
    (LineBiextension.unit (q ≫ a)).hom

/-- Coordinate of the second-difference line in simultaneous partial local frames.
Source: Moret-Bailly I §2, tensor cancellation
(blueprint: lem-sfb-semiabelian-second-difference-diagonal). -/
noncomputable def frameMap {S : Scheme.{u}} (H : Over S) [CommGrpObj H]
    (L : H.left.Modules) {T : Over S} (q : T ⟶ H ⊗ H) (b : CubicalLine.Frame T.left L) :
    (Scheme.Modules.tensorPullback q.left).obj (line H L) ⟶ 𝟙_ T.left.Modules :=
  (Scheme.Modules.boundaryPullbackTensorIso q.left
    ((Scheme.Modules.tensorPullback (μ[H]).left).obj L ⊗
      (Scheme.Modules.tensorPullback (fst H H).left).obj (Scheme.Modules.dual L))
    ((Scheme.Modules.tensorPullback (snd H H).left).obj (Scheme.Modules.dual L))).hom ≫
  (((Scheme.Modules.boundaryPullbackTensorIso q.left
      ((Scheme.Modules.tensorPullback (μ[H]).left).obj L)
      ((Scheme.Modules.tensorPullback (fst H H).left).obj (Scheme.Modules.dual L))).hom ≫
    ((((Scheme.Modules.tensorPullbackSectionComp q.left (μ[H]).left).app L).inv ≫
        (b (q.left ≫ (μ[H]).left)).1) ⊗ₘ
      negativeFrame q.left (fst H H).left L b) ≫ (λ_ _).hom) ⊗ₘ
    negativeFrame q.left (snd H H).left L b) ≫ (λ_ _).hom

/-- The supplied rigidification pulled to an arbitrary test scheme at its identity point.
Source: Moret-Bailly I §2, rigidifications
(blueprint: lem-sfb-semiabelian-second-difference-diagonal). -/
noncomputable def identityFrame {S : Scheme.{u}} (H : Over S) [CommGrpObj H]
    (L : H.left.Modules)
    (r : (Scheme.Modules.tensorPullback (η[H]).left).obj L ≅ 𝟙_ S.Modules)
    (T : Over S) :
    (Scheme.Modules.tensorPullback (1 : T ⟶ H).left).obj L ≅ 𝟙_ T.left.Modules :=
  eqToIso (congrArg (fun a : T.left ⟶ H.left ↦
    (Scheme.Modules.tensorPullback a).obj L) (by rfl)) ≪≫
    (Scheme.Modules.tensorPullbackSectionComp T.hom (η[H]).left).app L ≪≫
    (Scheme.Modules.tensorPullback T.hom).mapIso r ≪≫ LineBiextension.unit T.hom

/-- Fix the axis maps by testing the cancellation formula in local frames. Only the three
factors occurring in the relevant word must be framed, and the identity frame is r.
Valid such frames exist locally since L is invertible. The two maps are therefore fixed
uniquely; no unrestricted isomorphism is substituted for either canonical axis.
Source: Moret-Bailly I §2; Lan §3.2.2
(blueprint: lem-sfb-semiabelian-second-difference-diagonal). -/
def AxesNormalized {S : Scheme.{u}} (H : Over S) [CommGrpObj H]
    (L : H.left.Modules)
    (r : (Scheme.Modules.tensorPullback (η[H]).left).obj L ≅ 𝟙_ S.Modules)
    (B : LineBiextension H H (line H L)) : Prop :=
  (∀ (T : Over S) (y : T ⟶ H) (b : CubicalLine.Frame T.left L),
    b.valid (lift (1 : T ⟶ H) y ≫ μ[H]).left →
    b.valid (lift (1 : T ⟶ H) y ≫ fst H H).left →
    b.valid (lift (1 : T ⟶ H) y ≫ snd H H).left →
    (b (1 : T ⟶ H).left).1 = (identityFrame H L r T).hom →
    (B.leftAxis T y).hom = frameMap H L (lift 1 y) b) ∧
  (∀ (T : Over S) (x : T ⟶ H) (b : CubicalLine.Frame T.left L),
    b.valid (lift x (1 : T ⟶ H) ≫ μ[H]).left →
    b.valid (lift x (1 : T ⟶ H) ≫ fst H H).left →
    b.valid (lift x (1 : T ⟶ H) ≫ snd H H).left →
    (b (1 : T ⟶ H).left).1 = (identityFrame H L r T).hom →
    (B.rightAxis T x).hom = frameMap H L (lift x 1) b)

end SemiabelianSecondDifference

/-- The second difference is a biextension with the prescribed axes, and its diagonal
class is twice the original class modulo geometric algebraic equivalence.
Source: Moret-Bailly I §§2, 5, 7.2; Lan §§3.2.1--3.2.3 and §3.2.5;
Milne, Abelian Varieties, I Remark 10.19
(blueprint: lem-sfb-semiabelian-second-difference-diagonal).

Proof:
1. Over the algebraic closure the kernel square and local surjectivity make the quotient
   a split-torus torsor. By lem-sfb-smooth-affine-group-torsor-representability and
   lem-sfb-split-torus-torsor-frame-geometry it is affine, smooth, surjective and open,
   locally a product of punctured line modules. Its fibres are connected, including rank
   zero. The open quotient to the connected abelian variety then makes H geometrically
   connected (lem-weil-geometrically-connected-algebraic-closure). Smoothness implies
   flatness (lem-pc-smooth-flat) and local finite presentation; separated finite type gives
   finite presentation (def-sbc-locally-finite-presentation).
2. The field base is normal and reduced. Apply case (b) of
   lem-sfb-semiabelian-cubical-rigidification to (L,r), obtaining its normalized cube
   section as in def-sfb-cubical-rigidified-line, over k itself.
3. Tensor and composition comparisons (lem-weil-pbc-invertible-pullback-tensor) identify
   E_(x+x',y) tensor E_(x,y)^dual tensor E_(x',y)^dual with the eight-factor cube,
   using r on its constant factor. The cube section gives the first law and permutation
   gives the second. The cube identity slices give exactly AxesNormalized and the units.
4. Associativity defects are units on H^4, commutativity defects units on H^3, and the
   interchange defect a unit on H^4. All equal one on every coordinate axis by step 3.
   Apply lem-sfb-relative-group-unit-axis-factorization to each defect. This proves every
   coherence equation of LineBiextension, over arbitrary test schemes, not only at points.
5. Over the algebraic closure apply lem-sfb-split-torus-torsor-line-pullback to the quotient
   to write L as q^*N for an invertible N on the abelian variety (def-sc-abelian-variety).
   Only surjectivity on line classes is used, without descending N or its isomorphism.
6. Pullback to the diagonal gives [2]^*L tensor (L^dual)^2. After another tensor factor
   (L^dual)^2 and base change, this is q^*([2]^*N tensor (N^dual)^4). The inside line is
   algebraically trivial by lem-sfb-abelian-multiplication-algebraic-equivalence with n=2.
   Pull each generating family back along q times the identity of its smooth connected
   parameter. Thus pullback preserves the generated equivalence relation and proves the
   displayed geometric algebraic triviality, equivalently the doubled Picard class.
-/
theorem semiabelian_second_difference_diagonal
    {k : Type u} [Field k] (H : Grp (Over (Spec (.of k))))
    [IsCommMonObj H.X] [Smooth H.X.hom] [IsSeparated H.X.hom]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    (hgeom : ∃ (r : ℕ) (A : Grp (Over (Spec (.of (AlgebraicClosure k)))))
      (i : MultiplicativeType.splitTorus (AlgebraicClosure k) r ⟶
        (MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj H)
      (q : (MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj H ⟶ A),
      IsCommMonObj A.X ∧ IsProper A.X.hom ∧ Smooth A.X.hom ∧
      GeometricallyConnected A.X.hom ∧
      IsPullback i.hom.hom
        (toUnit (MultiplicativeType.splitTorus (AlgebraicClosure k) r).X)
        q.hom.hom η[A.X] ∧
      Presheaf.IsLocallySurjective
        (Scheme.fppfTopology.over (Spec (.of (AlgebraicClosure k))))
        (yoneda.map q.hom.hom))
    (L : H.X.left.Modules) [L.IsInvertible]
    (r : (Scheme.Modules.tensorPullback (η[H.X]).left).obj L ≅
      𝟙_ (Spec (.of k)).Modules) :
    (∃ B : LineBiextension H.X H.X (SemiabelianSecondDifference.line H.X L),
      SemiabelianSecondDifference.AxesNormalized H.X L r B) ∧
    Scheme.Modules.AreAlgebraicallyEquivalent
      (Over.mk (pullback.snd H.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))
      ((Scheme.Modules.tensorPullback
        (pullback.fst H.X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))).obj
        ((Scheme.Modules.tensorPullback (lift (𝟙 H.X) (𝟙 H.X)).left).obj
          (SemiabelianSecondDifference.line H.X L) ⊗ (Scheme.Modules.dual L).tensorPow 2))
      (𝟙_ (pullback H.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))).Modules) := by
  sorry

end AlgebraicGeometry
