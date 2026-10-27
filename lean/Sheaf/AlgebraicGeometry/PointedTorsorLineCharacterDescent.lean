module

public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.Descent
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-! # Pointed torsor descent of line modules

Source: Stacks Project, descent.tex, Tag 023T,
proposition-fpqc-descent-quasi-coherent, and Tag 05B2,
lemma-finite-locally-free-descends; the pointed torsor specialization and its
character convention are the calculation in the DAG proof.
(blueprint: lem-sfb-pointed-torsor-line-character-descent).

The auxiliary declarations spell out the pairs K_q(T), their isomorphism classes,
tensor product, normalized frames, and their descent multipliers. The multiplier
is the character itself. All tests range over schemes, including nonreduced ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped MonObj

namespace AlgebraicGeometry.PointedTorsor

open Scheme.Modules

variable {k : Type u} [Field k]

/-- The canonical tensor-pullback identification with the structure module.
Source: Stacks, 0096 and 023T
(blueprint: lem-sfb-pointed-torsor-line-character-descent). -/
def unitComparison {A B : Scheme.{u}} (f : A ⟶ B) :
    (tensorPullback f).obj (𝟙_ B.Modules) ≅ 𝟙_ A.Modules :=
  (boundaryPullbackComparison f).app _ ≪≫ pullbackObjUnitIso f

/-- The pointed axis x₀ × id, with no chosen point on the parameter scheme.
Source: the pointed specialization of Stacks 023T
(blueprint: lem-sfb-pointed-torsor-line-character-descent). -/
def axis {X : Over (Spec (.of k))}
    (x₀ : 𝟙_ (Over (Spec (.of k))) ⟶ X) (T : Over (Spec (.of k))) : T ⟶ X ⊗ T :=
  lift (toUnit T ≫ x₀) (𝟙 T)

/-- Restrict a frame along a test morphism, with the normalized tensor compositor.
Source: Stacks 0096 and the pointed calculation in 023T
(blueprint: lem-sfb-pointed-torsor-line-character-descent). -/
def frameAt {A B S : Scheme.{u}} (q : A ⟶ B) (L : B.Modules)
    (τ : (tensorPullback q).obj L ≅ 𝟙_ A.Modules) (x : S ⟶ A) :
    (tensorPullback (x ≫ q)).obj L ≅ 𝟙_ S.Modules :=
  (tensorPullbackSectionComp x q).app L ≪≫
    (tensorPullback x).mapIso τ ≪≫ unitComparison x

/-- A pair (L,r) killed by q, with existence, rather than a choice, of a frame
restricting to r. The rigidification is on the composite q x₀, namely y₀.
Source: Stacks 023T, pointed torsor specialization
(blueprint: lem-sfb-pointed-torsor-line-character-descent). -/
structure Pair {A B S : Scheme.{u}} (q : A ⟶ B) (x₀ : S ⟶ A) where
  L : B.Modules
  invertible : L.IsInvertible
  r : (tensorPullback (x₀ ≫ q)).obj L ≅ 𝟙_ S.Modules
  trivial : ∃ τ : (tensorPullback q).obj L ≅ 𝟙_ A.Modules, frameAt q L τ x₀ = r

/-- Rigidification-preserving isomorphism, the equivalence relation defining K_q(T).
Source: Stacks 023T, pointed torsor specialization
(blueprint: lem-sfb-pointed-torsor-line-character-descent). -/
def Pair.Isomorphic {A B S : Scheme.{u}} {q : A ⟶ B} {x₀ : S ⟶ A}
    (P Q : Pair q x₀) : Prop :=
  ∃ i : P.L ≅ Q.L, (tensorPullback (x₀ ≫ q)).map i.hom ≫ Q.r.hom = P.r.hom

/-- Isomorphism classes of exactly the pairs in the statement, without choosing frames.
Source: Stacks 023T, pointed torsor specialization
(blueprint: lem-sfb-pointed-torsor-line-character-descent). -/
def Classes {A B S : Scheme.{u}} (q : A ⟶ B) (x₀ : S ⟶ A) :=
  Quot (Pair.Isomorphic (q := q) (x₀ := x₀))

/-- The class of a rigidified pair.
Source: Stacks 023T, pointed torsor specialization
(blueprint: lem-sfb-pointed-torsor-line-character-descent). -/
def classOf {A B S : Scheme.{u}} {q : A ⟶ B} {x₀ : S ⟶ A}
    (P : Pair q x₀) : Classes q x₀ := Quot.mk _ P

/-- The tensor product graph on pairs, including its specified tensor rigidification.
Source: Stacks 023T and Modules 01CD
(blueprint: lem-sfb-pointed-torsor-line-character-descent). -/
def IsTensor {A B S : Scheme.{u}} {q : A ⟶ B} {x₀ : S ⟶ A}
    (P Q R : Pair q x₀) : Prop :=
  ∃ i : R.L ≅ P.L ⊗ Q.L,
    (tensorPullback (x₀ ≫ q)).map i.hom ≫
        (boundaryPullbackTensorIso (x₀ ≫ q) P.L Q.L).hom ≫
        (P.r.hom ⊗ₘ Q.r.hom) ≫ (λ_ (𝟙_ S.Modules)).hom = R.r.hom

/-- The unit graph: a trivial line with its canonical pointed rigidification.
Source: Stacks 023T, pointed torsor specialization
(blueprint: lem-sfb-pointed-torsor-line-character-descent). -/
def IsUnit {A B S : Scheme.{u}} {q : A ⟶ B} {x₀ : S ⟶ A}
    (P : Pair q x₀) : Prop :=
  ∃ i : P.L ≅ 𝟙_ B.Modules,
    (tensorPullback (x₀ ≫ q)).map i.hom ≫ (unitComparison (x₀ ≫ q)).hom = P.r.hom

/-- Transport a specified rigidification through a commuting base-change square.
The comparison is fixed by tensor inverse image and multiplication on the unit.
Source: Stacks 0096 and 023T
(blueprint: lem-sfb-pointed-torsor-line-character-descent). -/
def restrictRigidification {B S B' S' : Scheme.{u}} (s : S ⟶ B) (s' : S' ⟶ B')
    (f : S' ⟶ S) (b : B' ⟶ B) (w : s' ≫ b = f ≫ s) (L : B.Modules)
    (r : (tensorPullback s).obj L ≅ 𝟙_ S.Modules) :
    (tensorPullback s').obj ((tensorPullback b).obj L) ≅ 𝟙_ S'.Modules :=
  ((tensorPullbackSectionComp s' b).app L).symm ≪≫
    (eqToIso (congrArg (fun h ↦ (tensorPullback h).obj L) w)) ≪≫
    (tensorPullbackSectionComp f s).app L ≪≫
    (tensorPullback f).mapIso r ≪≫ unitComparison f

/-- The base-change graph on pairs, with the actual pulled-back rigidification.
Source: Stacks 023T, pointed torsor specialization
(blueprint: lem-sfb-pointed-torsor-line-character-descent). -/
def IsPullback {A B S A' B' S' : Scheme.{u}}
    {q : A ⟶ B} {x₀ : S ⟶ A} {q' : A' ⟶ B'} {x₀' : S' ⟶ A'}
    (P : Pair q x₀) (P' : Pair q' x₀') (f : S' ⟶ S) (b : B' ⟶ B) : Prop :=
  ∃ (w : (x₀' ≫ q') ≫ b = f ≫ (x₀ ≫ q))
    (i : P'.L ≅ (tensorPullback b).obj P.L),
    (tensorPullback (x₀' ≫ q')).map i.hom ≫
      (restrictRigidification (x₀ ≫ q) (x₀' ≫ q') f b w P.L P.r).hom = P'.r.hom

/-- The genuine group of T-group-scheme morphisms G_T → Gₘ,T.
Source: Stacks 022U and the pointed specialization of 023T
(blueprint: lem-sfb-pointed-torsor-line-character-descent). -/
abbrev Characters (G : Over (Spec (.of k))) [GrpObj G] (T : Over (Spec (.of k))) :=
  (Over.pullback T.hom).mapGrp.obj (Grp.mk G) ⟶
    (Over.pullback T.hom).mapGrp.obj (Grp.mk (StandardGroupSchemes.multiplicative k))

/-- Evaluation of the Laurent coordinate of a character on a scheme-valued point.
Source: Stacks 022U and the pointed specialization of 023T
(blueprint: lem-sfb-pointed-torsor-line-character-descent). -/
def value {G : Over (Spec (.of k))} [GrpObj G] {T S : Over (Spec (.of k))}
    (χ : Characters G T) (g : S ⟶ G ⊗ T) : Γ(S.left, ⊤) :=
  (g.left ≫ χ.hom.hom.left ≫
    pullback.fst (StandardGroupSchemes.multiplicative k).hom T.hom).appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1))

/-- Right translation of a point in X_T by a point of G.
Source: Stacks 023T, pointed torsor specialization
(blueprint: lem-sfb-pointed-torsor-line-character-descent). -/
def translate {X G T S : Over (Spec (.of k))} (a : X ⊗ G ⟶ X)
    (x : S ⟶ X ⊗ T) (g : S ⟶ G) : S ⟶ X ⊗ T :=
  lift (lift (x ≫ fst X T) g ≫ a) (x ≫ snd X T)

/-- The descent multiplier equation on every test scheme. On the common pulled-back
line the second frame is χ(g) times the first frame; hence d = τ₂ c τ₁⁻¹ = χ.
The equality on all test schemes detects scheme-theoretic, not just reduced, data.
Source: Stacks 023T, pointed torsor calculation
(blueprint: lem-sfb-pointed-torsor-line-character-descent). -/
def HasMultiplier {X Y G : Over (Spec (.of k))} [GrpObj G]
    (q : X ⟶ Y) (a : X ⊗ G ⟶ X)
    {x₀ : 𝟙_ (Over (Spec (.of k))) ⟶ X} {T : Over (Spec (.of k))}
    (P : Pair (q ▷ T).left (axis x₀ T).left)
    (τ : (tensorPullback (q ▷ T).left).obj P.L ≅ 𝟙_ (X ⊗ T).left.Modules)
    (χ : Characters G T) : Prop :=
  ∀ (S : Over (Spec (.of k))) (x : S ⟶ X ⊗ T) (g : S ⟶ G)
    (h : (translate a x g).left ≫ (q ▷ T).left = x.left ≫ (q ▷ T).left)
    (m : Γ((tensorPullback (x.left ≫ (q ▷ T).left)).obj P.L, ⊤)),
    (frameAt (q ▷ T).left P.L τ (translate a x g).left).hom.app ⊤
        ((eqToIso (congrArg (fun f ↦ (tensorPullback f).obj P.L) h)).inv.app ⊤ m) =
      value χ (lift g (x ≫ snd X T)) •
        (frameAt (q ▷ T).left P.L τ x.left).hom.app ⊤ m

/-- K_q(T), with the parameter and its pointed axis displayed explicitly.
Source: Stacks 023T, pointed torsor specialization
(blueprint: lem-sfb-pointed-torsor-line-character-descent). -/
abbrev K {X Y : Over (Spec (.of k))} (q : X ⟶ Y)
    (x₀ : 𝟙_ (Over (Spec (.of k))) ⟶ X) (T : Over (Spec (.of k))) :=
  Classes (q ▷ T).left (axis x₀ T).left

/-- The complete classification interface: group bijections, tensor and unit graphs,
unique normalized frames, the character multiplier in both directions, and arbitrary
base change. Graphs specify canonical tensor and pullback operations without choosing
representatives of isomorphism classes.
Source: Stacks 023T and 05B2, pointed torsor specialization
(blueprint: lem-sfb-pointed-torsor-line-character-descent). -/
structure Classification {X Y G : Over (Spec (.of k))} [GrpObj G]
    (q : X ⟶ Y) (a : X ⊗ G ⟶ X)
    (x₀ : 𝟙_ (Over (Spec (.of k))) ⟶ X) where
  group : ∀ T : Over (Spec (.of k)), CommGroup (K q x₀ T)
  characterGroup : ∀ T : Over (Spec (.of k)), CommGroup (Characters G T)
  character_mul : ∀ (T S : Over (Spec (.of k))) (χ ψ : Characters G T)
    (z : S ⟶ G ⊗ T),
    value (@Mul.mul _ (characterGroup T).toMul χ ψ) z = value χ z * value ψ z
  equivalence : ∀ T : Over (Spec (.of k)),
    @MulEquiv (K q x₀ T) (Characters G T) (group T).toMul (characterGroup T).toMul
  tensor : ∀ (T : Over (Spec (.of k)))
    (P Q R : Pair (q ▷ T).left (axis x₀ T).left),
    classOf R = @Mul.mul _ (group T).toMul (classOf P) (classOf Q) ↔ IsTensor P Q R
  unit : ∀ (T : Over (Spec (.of k))) (P : Pair (q ▷ T).left (axis x₀ T).left),
    classOf P = @One.one _ (group T).toOne ↔ IsUnit P
  unique_frame : ∀ (T : Over (Spec (.of k)))
    (P : Pair (q ▷ T).left (axis x₀ T).left),
    ∃! τ : (tensorPullback (q ▷ T).left).obj P.L ≅ 𝟙_ (X ⊗ T).left.Modules,
      frameAt (q ▷ T).left P.L τ (axis x₀ T).left = P.r
  multiplier : ∀ (T : Over (Spec (.of k)))
    (P : Pair (q ▷ T).left (axis x₀ T).left) (χ : Characters G T),
    equivalence T (classOf P) = χ ↔
      ∃ τ : (tensorPullback (q ▷ T).left).obj P.L ≅ 𝟙_ (X ⊗ T).left.Modules,
        frameAt (q ▷ T).left P.L τ (axis x₀ T).left = P.r ∧ HasMultiplier q a P τ χ
  pullback_exists : ∀ (T T' : Over (Spec (.of k))) (f : T' ⟶ T)
    (P : Pair (q ▷ T).left (axis x₀ T).left),
    ∃ P' : Pair (q ▷ T').left (axis x₀ T').left,
      IsPullback P P' f.left (Y ◁ f).left
  frame_naturality : ∀ (T T' : Over (Spec (.of k))) (f : T' ⟶ T)
    (P : Pair (q ▷ T).left (axis x₀ T).left)
    (P' : Pair (q ▷ T').left (axis x₀ T').left)
    (i : P'.L ≅ (tensorPullback (Y ◁ f).left).obj P.L)
    (w : (q ▷ T').left ≫ (Y ◁ f).left = (X ◁ f).left ≫ (q ▷ T).left)
    (v : ((axis x₀ T').left ≫ (q ▷ T').left) ≫ (Y ◁ f).left =
      f.left ≫ ((axis x₀ T).left ≫ (q ▷ T).left))
    (τ : (tensorPullback (q ▷ T).left).obj P.L ≅ 𝟙_ (X ⊗ T).left.Modules),
    (tensorPullback ((axis x₀ T').left ≫ (q ▷ T').left)).map i.hom ≫
        (restrictRigidification ((axis x₀ T).left ≫ (q ▷ T).left)
          ((axis x₀ T').left ≫ (q ▷ T').left) f.left (Y ◁ f).left
          v P.L P.r).hom =
      P'.r.hom →
    frameAt (q ▷ T).left P.L τ (axis x₀ T).left = P.r →
    frameAt (q ▷ T').left P'.L
      ((tensorPullback (q ▷ T').left).mapIso i ≪≫
        restrictRigidification (q ▷ T).left (q ▷ T').left (X ◁ f).left
          (Y ◁ f).left w P.L τ) (axis x₀ T').left = P'.r
  naturality : ∀ (T T' : Over (Spec (.of k))) (f : T' ⟶ T)
    (P : Pair (q ▷ T).left (axis x₀ T).left)
    (P' : Pair (q ▷ T').left (axis x₀ T').left),
    IsPullback P P' f.left (Y ◁ f).left →
      ∀ (S : Over (Spec (.of k))) (z : S ⟶ G ⊗ T'),
        value (equivalence T' (classOf P')) z =
          value (equivalence T (classOf P)) (z ≫ (G ◁ f))

/-- Pointed torsor descent identifies exactly the rigidified lines killed by q with
characters, as groups naturally in every parameter scheme. The action is written as
an actual right-action morphism; its laws and the torsor isomorphism are tested by
Yoneda on all scheme-valued points. The latter is equivalent to the displayed
X × G → X ×[Y] X being an isomorphism.

Source: Stacks Project, descent.tex, 023T and 05B2; pointed torsor specialization
(blueprint: lem-sfb-pointed-torsor-line-character-descent).

Proof:
1. A finite flat surjection is fpqc: preimages of affine opens are affine and cover.
Fpqc covers remain covers after every base change (022D).
2. Two frames differ by a unit on X_T. Universal constancy of global functions
pulls this unit back from T, and restriction along x₀ makes it one. This proves
uniqueness of the normalized frame.
3. On the overlap the canonical descent isomorphism, in these frames, is a unit.
The torsor isomorphism identifies the overlap with X × G_T. Apply constancy with
S = G_T to descend this unit uniquely to G_T; restriction at x₀ computes it.
4. On the triple overlap the cocycle law is a(x,gh)=a(xg,h)a(x,g). Independence
of x gives the character law; its value at the identity is one and inversion
is respected. Thus the multiplier defines a group-scheme character, with no inverse.
5. Conversely a character supplies precisely this descent cocycle on the trivial
line. Effective fpqc descent (023T) and descent of finite local freeness (05B2)
give the line on Y_T. Restrict its frame at x₀ to obtain r.
6. Full faithfulness of descent identifies the two inverse constructions and
identifies rigidification-preserving isomorphisms with equal character classes.
7. The pullback-tensor comparison takes pure tensors to pure tensors. Hence the
tensored frame has multiplier χ₁χ₂, and the unit has multiplier one. Associators
and symmetry preserve r. Bijectivity gives inverses by descending χ⁻¹. These are
the asserted commutative groups and group bijections, with the stated tensor graph.
8. Pullback preserves the frames, their rigidifications and their scalar multipliers.
Uniqueness of normalized frames and full faithfulness of fpqc descent identify
both constructions after arbitrary base change, including nonreduced or empty bases.
-/
theorem classification {X Y G : Over (Spec (.of k))} [GrpObj G] [IsCommMonObj G]
    (hfinite : IsFinite G.hom) (q : X ⟶ Y)
    (hqfinite : IsFinite q.left) (hqflat : Flat q.left) (hqsurj : Surjective q.left)
    (a : X ⊗ G ⟶ X)
    (hunit : ∀ (S : Over (Spec (.of k))) (x : S ⟶ X), lift x 1 ≫ a = x)
    (hassoc : ∀ (S : Over (Spec (.of k))) (x : S ⟶ X) (g h : S ⟶ G),
      lift (lift x g ≫ a) h ≫ a = lift x (g * h) ≫ a)
    (hquot : a ≫ q = fst X G ≫ q)
    (htorsor : ∀ (S : Over (Spec (.of k))) (x x' : S ⟶ X),
      x ≫ q = x' ≫ q → ∃! g : S ⟶ G, lift x g ≫ a = x')
    (x₀ : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (hfunctions : ∀ S : Over (Spec (.of k)),
      Function.Bijective (snd X S).left.appTop) :
    Nonempty (Classification q a x₀) := by
  sorry

end AlgebraicGeometry.PointedTorsor
