module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Artinian.Defs
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import WeilConjectures.AlgebraicGeometry.Thickening
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.SmoothFixedResidueArtinianTest
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource

/-! # Versal base change over an affine Noetherian base

Source: Stacks Project, Artin's Axioms, Tag 0CXM, and Tag 0G2K, the section
associated to a first-order thickening
(blueprint: lem-sfb-artin-noetherian-versal-base-change).

The auxiliary predicates unpack the conditions introduced in this node over an arbitrary
base. Families are maps from representable discrete fibred groupoids, by 2-Yoneda;
no cleavage, isomorphism classes, or coefficient-field embeddings are chosen.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ArtinBaseChange

variable {S : Scheme.{u}}

/-- An arrow over the specified base map records its pullback identification.
Source: Stacks 003T; Artin, Tag 0CXM
(blueprint: lem-sfb-artin-noetherian-versal-base-change). -/
abbrev Lift {F : BasedCategory.{v, w} (Over S)} {T U : Over S}
    (a : T ⟶ U) (x y : F.obj) := {b : x ⟶ y // F.p.IsHomLift a b}

/-- Every object at the inverse limit descends to a stage.
Source: Stacks, Artin, limit preserving, axiom [1]
(blueprint: lem-sfb-artin-noetherian-versal-base-change). -/
def ObjectsDescend (F : BasedCategory.{v, w} (Over S)) : Prop :=
  ∀ (I : Type u) [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S) (c : Cone D),
    (∀ i : I, IsAffine (D.obj (op i)).left) → IsAffine c.pt.left →
    Nonempty (IsLimit c) → ∀ x : Functor.Fiber F.p c.pt,
      ∃ (i : I) (xi : Functor.Fiber F.p (D.obj (op i))),
        Nonempty (Lift (c.π.app (op i)) x.val xi.val)

/-- Arrows between stage objects descend after passage to a common later stage.
The two factorizations retain the specified identifications at the limit.
Source: Stacks, Artin, axiom [1]
(blueprint: lem-sfb-artin-noetherian-versal-base-change). -/
def ArrowsDescend (F : BasedCategory.{v, w} (Over S)) : Prop :=
  ∀ (I : Type u) [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S) (c : Cone D),
    (∀ i : I, IsAffine (D.obj (op i)).left) → IsAffine c.pt.left →
    Nonempty (IsLimit c) → ∀ (i : I) (xi yi : Functor.Fiber F.p (D.obj (op i)))
      (x y : Functor.Fiber F.p c.pt) (px : Lift (c.π.app (op i)) x.val xi.val)
      (py : Lift (c.π.app (op i)) y.val yi.val) (a : x ⟶ y),
      ∃ (j : I) (hij : i ≤ j) (xj yj : Functor.Fiber F.p (D.obj (op j)))
        (qx : Lift (D.map (homOfLE hij).op) xj.val xi.val)
        (qy : Lift (D.map (homOfLE hij).op) yj.val yi.val)
        (rx : Lift (c.π.app (op j)) x.val xj.val) (ry : Lift (c.π.app (op j)) y.val yj.val)
        (b : xj ⟶ yj),
        rx.val ≫ qx.val = px.val ∧ ry.val ≫ qy.val = py.val ∧
          a.val ≫ ry.val = rx.val ≫ b.val

/-- Equality of stage arrows detected at the limit holds at a later stage.
Source: Stacks, Artin, axiom [1]
(blueprint: lem-sfb-artin-noetherian-versal-base-change). -/
def ArrowEqualitiesDescend (F : BasedCategory.{v, w} (Over S)) : Prop :=
  ∀ (I : Type u) [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S) (c : Cone D),
    (∀ i : I, IsAffine (D.obj (op i)).left) → IsAffine c.pt.left →
    Nonempty (IsLimit c) → ∀ (i : I) (xi yi : Functor.Fiber F.p (D.obj (op i)))
      (a b : xi ⟶ yi) (x : Functor.Fiber F.p c.pt) (px : Lift (c.π.app (op i)) x.val xi.val),
      px.val ≫ a.val = px.val ≫ b.val →
      ∃ (j : I) (hij : i ≤ j) (xj : Functor.Fiber F.p (D.obj (op j)))
        (qx : Lift (D.map (homOfLE hij).op) xj.val xi.val), qx.val ≫ a.val = qx.val ≫ b.val

/-- Equivalence on directed affine 2-colimits, including arrows and their equalities.
Source: Stacks, Artin, axiom [1], Tag 07Y4
(blueprint: lem-sfb-artin-noetherian-versal-base-change). -/
def IsLimitPreserving (F : BasedCategory.{v, w} (Over S)) : Prop :=
  ObjectsDescend F ∧ ArrowsDescend F ∧ ArrowEqualitiesDescend F

/-- Square-zero affine gluing, including its universal property on arrows. In a fibred
in groupoids category a pushout of the two cartesian arrows over the affine pushout
is equivalent to the stated equivalence with the iso-fibre product of fibres.
There is no Artinian, local, or finite-type restriction on these rings.
Source: Stacks, Artin, (RS), Tag 0CXM
(blueprint: lem-sfb-artin-noetherian-versal-base-change). -/
def SquareZeroGluing (F : BasedCategory.{v, w} (Over S)) : Prop :=
  ∀ (A B B' : CommRingCat.{u}) (f : A ⟶ B) (g : B' ⟶ B),
    Function.Surjective g.hom → RingHom.ker g.hom ^ 2 = ⊥ →
    ∀ (sA : Spec A ⟶ S) (sB' : Spec B' ⟶ S)
      (hs : Spec.map f ≫ sA = Spec.map g ≫ sB')
      (P : Over S) (i : Over.mk sA ⟶ P) (j : Over.mk sB' ⟶ P),
      IsAffine P.left →
      IsPushout (Over.homMk (Spec.map f) rfl :
          Over.mk (Spec.map f ≫ sA) ⟶ Over.mk sA)
        (Over.homMk (Spec.map g) hs.symm :
          Over.mk (Spec.map f ≫ sA) ⟶ Over.mk sB') i j →
      ∀ (x : Functor.Fiber F.p (Over.mk (Spec.map f ≫ sA)))
        (y : Functor.Fiber F.p (Over.mk sA)) (z : Functor.Fiber F.p (Over.mk sB'))
        (a : Lift (Over.homMk (Spec.map f) rfl :
          Over.mk (Spec.map f ≫ sA) ⟶ Over.mk sA) x.val y.val)
        (b : Lift (Over.homMk (Spec.map g) hs.symm :
          Over.mk (Spec.map f ≫ sA) ⟶ Over.mk sB') x.val z.val),
        ∃ (q : Functor.Fiber F.p P) (c : Lift i y.val q.val) (d : Lift j z.val q.val),
          IsPushout a.val b.val c.val d.val

/-- Versality is the prescribed-isomorphism Artinian lifting property. A surjection
onto the actual residue field identifies the residue field of the Artinian local
ring; the composite identifies the residue field of the extension. The equality of
arrows requires extension of the specified isomorphism, not just its class.
Source: Stacks, Artin, definition-versal and equation-hat-x
(blueprint: lem-sfb-artin-noetherian-versal-base-change). -/
def IsVersalAt (F : BasedCategory.{v, w} (Over S)) (U : Over S)
    (x : BasedFunctor (discreteModuli (yoneda.obj U)) F) (u₀ : U.left) : Prop :=
  ∀ (A' A : CommRingCat.{u}) [IsArtinianRing A'] [IsLocalRing A']
    [IsArtinianRing A] [IsLocalRing A] (g : A' ⟶ A),
    Function.Surjective g.hom → IsNilpotent (RingHom.ker g.hom) →
    ∀ (r : A ⟶ U.left.residueField u₀), Function.Surjective r.hom →
    ∀ (s' : Spec A' ⟶ S) (a : Over.mk (Spec.map g ≫ s') ⟶ U),
      Spec.map r ≫ a.left = U.left.fromSpecResidueField u₀ →
    ∀ (y : Functor.Fiber F.p (Over.mk (Spec.map g ≫ s')))
      (y' : Functor.Fiber F.p (Over.mk s'))
      (b : Lift (Over.homMk (Spec.map g) rfl :
        Over.mk (Spec.map g ≫ s') ⟶ Over.mk s') y.val y'.val)
      (c : Lift a y.val (x.obj (CostructuredArrow.mk (𝟙 (yoneda.obj U))))),
      ∃ (a' : Over.mk s' ⟶ U)
        (d : Lift a' y'.val (x.obj (CostructuredArrow.mk (𝟙 (yoneda.obj U))))),
        Spec.map g ≫ a'.left = a.left ∧ b.val ≫ d.val = c.val

/-- The triples-space presentation retains both projections. The equivalence is to
the existing 2-fibre product, whose objects retain the specified fibre isomorphism.
Both projection comparisons lie over identities of test schemes.
Source: Stacks 0CXM, the displayed 2-fibre-product square
(blueprint: lem-sfb-artin-noetherian-versal-base-change). -/
structure TriplesPresentation (F : BasedCategory.{v, w} (Over S)) (U V : Over S)
    (x : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (y : BasedFunctor (discreteModuli (yoneda.obj V)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj U)
    (q : Z.obj.obj ⟶ yoneda.obj V) where
  /-- The equivalence with the actual 2-fibre product. -/
  equivalence : BasedFunctor (discreteModuli Z.obj.obj) (moduliTwoFiberProduct x y)
  /-- It is an equivalence, not a map of isomorphism classes. -/
  isEquivalence : equivalence.toFunctor.IsEquivalence
  /-- Comparison of the U projection over the identity of each test scheme. -/
  fst : ModuliTwoIso (equivalence.comp (moduliTwoFiberFst x y)) (discreteModuliMap p)
  /-- Comparison of the V projection. -/
  snd : equivalence.toFunctor ⋙ ObjectProperty.ι _ ⋙ Comma.snd x.toFunctor y.toFunctor ≅
    (discreteModuliMap q).toFunctor
  /-- The comparison fixes the test scheme. -/
  snd_over : ∀ t : (discreteModuli Z.obj.obj).obj,
    (discreteModuli (yoneda.obj V)).p.IsHomLift
      (𝟙 ((discreteModuli Z.obj.obj).p.obj t)) (snd.hom.app t)

/-- The specific triple attached to a map j and its specified fibre isomorphism.
Source: Stacks, Artin, Tag 0G2K, the triple defining i
(blueprint: lem-sfb-artin-noetherian-versal-base-change). -/
def sectionTriple {F : BasedCategory.{v, w} (Over S)} {U V : Over S}
    (x : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (y : BasedFunctor (discreteModuli (yoneda.obj V)) F) (j : U ⟶ V)
    (α : ModuliTwoIso x ((discreteModuliMap (yoneda.map j)).comp y)) :
    BasedFunctor (discreteModuli (yoneda.obj U)) (moduliTwoFiberProduct x y) where
  toFunctor :=
    { obj := fun t ↦ ⟨⟨t, (discreteModuliMap (yoneda.map j)).obj t, α.val.hom.app t⟩,
        ⟨inferInstance, α.property t⟩⟩
      map := fun f ↦ ObjectProperty.homMk
        { left := f
          right := (discreteModuliMap (yoneda.map j)).map f
          w := α.val.hom.naturality f } }
  w := rfl

/-- A finite-type space point admits a closed lift in an étale scheme neighbourhood.
Source: Stacks, Morphisms of Spaces, definition-finite-type-point, used in Tag 0CXM
(blueprint: lem-sfb-artin-noetherian-versal-base-change). -/
def FiniteTypeSpacePoint (Z : AlgebraicSpace S) (z : AlgebraicSpace.Point Z.obj.obj) :
    Prop :=
  ∃ (W : Over S) (e : yoneda.obj W ⟶ Z.obj.obj) (w₀ : W.left),
    AlgebraicSpace.IsEtale e ∧ IsClosed ({w₀} : Set W.left) ∧
      AlgebraicSpace.schemePointMap e w₀ = z

/-- The point lies over the given scheme point, in the field-valued point quotient.
Source: Stacks 0CXM, the condition that z_0 lies over u_0
(blueprint: lem-sfb-artin-noetherian-versal-base-change). -/
def LiesOver {Z : AlgebraicSpace S} {U : Over S}
    (p : Z.obj.obj ⟶ yoneda.obj U) (z : AlgebraicSpace.Point Z.obj.obj) (u₀ : U.left) :
    Prop :=
  ∃ a : AlgebraicSpace.PointRepresentative Z.obj.obj,
    Quot.mk _ a = z ∧
      Quot.mk _ (a.map p) = AlgebraicSpace.schemePointMap (𝟙 (yoneda.obj U)) u₀

/-- Smoothness on an open neighbourhood. The open is the existing actual subfunctor;
every étale scheme chart of that open has smooth composite to the target scheme.
Source: Stacks 0CXM, conclusion, and smoothness on étale charts
(blueprint: lem-sfb-artin-noetherian-versal-base-change). -/
def SmoothNear (Z : AlgebraicSpace S) (V : Over S) (q : Z.obj.obj ⟶ yoneda.obj V)
    (z : AlgebraicSpace.Point Z.obj.obj) : Prop :=
  ∃ O : AlgebraicSpace.OpenSubspace Z,
    z ∈ AlgebraicSpace.pointImage O.val.ι ∧
      ∀ (T : Over S) (a : yoneda.obj T ⟶ O.val.toFunctor),
        AlgebraicSpace.IsEtale a → Smooth (yoneda.preimage (a ≫ O.val.ι ≫ q)).left

/-- Versal base change is smooth near a finite-type point, including the section
associated to a compatible first-order thickening. The triples presentation exists
and the conclusions hold for every such presentation, hence no representative is chosen.
Source: Stacks Project, Artin's Axioms, Tag 0CXM, and Tag 0G2K, paragraph z_0=i(u_0)
(blueprint: lem-sfb-artin-noetherian-versal-base-change).

Proof:
1. By lem-sfb-limit-preserving-isom-space-lft, representability of the diagonal gives
Z, and limit preservation makes its projections locally of finite type. A scheme V
locally of finite type over a Noetherian ring is locally Noetherian, by
lem-weil-pbc-finite-type-algebra-noetherian and pqf-def-locnoeth.
2. Lift z_0 to a closed point w_0 of an étale scheme chart W and shrink W to affine.
By lem-trf-closed-point-residue-immersion, Spec κ(w_0) → W is finite type. Compose and
cancel by lem-sfb-stack-finite-type-calculus and
lemma-nagata-finite-type-to-separated-target. The resulting field algebra is finite
by lem-weil-pbc-zariski-lemma. Apply lem-sfb-artin-pointwise-versal-field-extension.
3. For a small extension and compatible maps to W and V, the latter gives an object
of F. Versality supplies a lift to U extending the inverse of the triples isomorphism.
Invert it to obtain a lifted triple. The étale chart lifts uniquely by
lem-sfb-etale-space-infinitesimal-lifting. Thus W → V satisfies the lifting test of
lem-sfb-smooth-fixed-residue-artinian-test and is smooth near w_0.
4. Its image is an open O by lem-a1-space-etale-open-image. Pulling its surjective
étale cover back to any chart of O gives a scheme by
lem-trf-space-fibre-products-etale-covers. Smoothness descends by
lem-sfb-stack-chartwise-smooth-etale-calculus and lem-trf-etale-source-smoothness.
5. The compatible thickening triple gives a unique section i of p with qi=j. Since
pi=id, lem-sfb-space-lft-cancellation makes i locally of finite type. Composition
with the finite-type residue-field point and
lem-sfb-space-finite-type-point-characterization show that i(u_0) is finite type.
It lies over u_0, and the first assertion gives the smooth neighbourhood. -/
theorem artin_noetherian_versal_base_change
    (Λ : CommRingCat.{u}) [IsNoetherianRing Λ]
    (F : BasedCategory.{v, w} (Over (Spec Λ)))
    (hFibred : IsFibredInGroupoids F) (hDiagonal : HasAlgebraicSpaceDiagonal F)
    (hGluing : SquareZeroGluing F) (hLimits : IsLimitPreserving F)
    (U V : Over (Spec Λ)) [LocallyOfFiniteType U.hom] [LocallyOfFiniteType V.hom]
    (x : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (y : BasedFunctor (discreteModuli (yoneda.obj V)) F) :
    (∃ (Z : AlgebraicSpace (Spec Λ)) (p : Z.obj.obj ⟶ yoneda.obj U)
      (q : Z.obj.obj ⟶ yoneda.obj V), Nonempty (TriplesPresentation F U V x y Z p q)) ∧
    ∀ (Z : AlgebraicSpace (Spec Λ)) (p : Z.obj.obj ⟶ yoneda.obj U)
      (q : Z.obj.obj ⟶ yoneda.obj V) (P : TriplesPresentation F U V x y Z p q),
      (∀ (u₀ : U.left) (z₀ : AlgebraicSpace.Point Z.obj.obj),
        (LocallyOfFiniteType (U.left.fromSpecResidueField u₀) ∧
          QuasiCompact (U.left.fromSpecResidueField u₀)) → IsVersalAt F U x u₀ →
        FiniteTypeSpacePoint Z z₀ → LiesOver p z₀ u₀ → SmoothNear Z V q z₀) ∧
      (∀ (j : U ⟶ V), IsFirstOrderThickening j.left →
        ∀ α : ModuliTwoIso x ((discreteModuliMap (yoneda.map j)).comp y),
        ∃ i : yoneda.obj U ⟶ Z.obj.obj,
          Nonempty (ModuliTwoIso ((discreteModuliMap i).comp P.equivalence)
            (sectionTriple x y j α)) ∧
          i ≫ p = 𝟙 _ ∧ i ≫ q = yoneda.map j ∧
          ∀ u₀ : U.left,
            (LocallyOfFiniteType (U.left.fromSpecResidueField u₀) ∧
              QuasiCompact (U.left.fromSpecResidueField u₀)) →
            FiniteTypeSpacePoint Z (AlgebraicSpace.schemePointMap i u₀) ∧
            LiesOver p (AlgebraicSpace.schemePointMap i u₀) u₀ ∧
            (IsVersalAt F U x u₀ → SmoothNear Z V q (AlgebraicSpace.schemePointMap i u₀))) := by
  sorry

end AlgebraicGeometry.ArtinBaseChange
