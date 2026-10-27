module

public import Sheaf.AlgebraicGeometry.AbelianSpacePoincareData
public import WeilConjectures.AlgebraicGeometry.Picard.DegreeMorphism
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import WeilConjectures.AlgebraicGeometry.Hilbert.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.AlgebraicGeometry.Picard.DegreeDecomposition
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum

/-! # Relative Picard presentations and geometric theta characterization

Source: Deligne, Le lemme de Gabber, Section 4.1; Milne, Abelian Varieties,
III Sections 6 and 8 (blueprint: def-sfb-relative-jacobian-theta-data).

Presentations use natural equivalences, allowing the two existing universe conventions.
The theta line is the dual ideal of the scheme-theoretic effective-divisor Abel image.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry.Scheme.Modules CategoryTheory.MonObj

namespace AlgebraicGeometry.AlgebraicSpace.JacobianTheta

open Poincare
variable {S : Scheme.{u}}

/-- Scheme tests over a represented base, in the ambient category of spaces.
Source: Deligne 4.1 (blueprint: def-sfb-relative-jacobian-theta-data). -/
abbrev test (B : Over S) (T : Over B.left) : AlgebraicSpace S :=
  schemeSpace ((Over.map B.hom).obj T)

/-- The actual test-scheme structure map to the represented base.
Source: Deligne 4.1 (blueprint: def-sfb-relative-jacobian-theta-data). -/
def testProjection (B : Over S) (T : Over B.left) : test B T ⟶ schemeSpace B :=
  groupSchemeMap (Over.homMk T.hom rfl)

/-- Representation of the degree-zero subfunctor of the existing Picard sheaf.
Naturality is stated using all commuting arrows, avoiding a chosen fibre-product model.
Source: Milne III Section 8; Deligne 4.1
(blueprint: def-sfb-relative-jacobian-theta-data). -/
structure Presentation {B : Over S} {C : Scheme.{u}} (f : C ⟶ B.left)
    (J : AlgebraicSpace S) (p : J ⟶ schemeSpace B) where
  classify (T : Over B.left) :
    {a : test B T ⟶ J // a ≫ p = testProjection B T} ≃
      {x : (picardFunctor f).obj.obj (op T) // ∀ t : T.left, picardDegree f x t = 0}
  naturality {T U : Over B.left} (q : U ⟶ T)
    (a : {a : test B T ⟶ J // a ≫ p = testProjection B T})
    (b : {b : test B U ⟶ J // b ≫ p = testProjection B U}) :
    groupSchemeMap ((Over.map B.hom).map q) ≫ a.val = b.val →
      (classify U b).val = (picardFunctor f).obj.map q.op (classify T a).val

/-- The group law is tensor product on every locally represented Picard class.
Source: Milne III Section 8 (blueprint: def-sfb-relative-jacobian-theta-data). -/
def TensorCompatible {C : Scheme.{u}} (f : C ⟶ S) (J : AlgebraicSpace S)
    (e : Presentation (B := Over.mk (𝟙 S)) f J (groupSpaceProjection J))
    (g : CommutativeSpaceGroup J) : Prop :=
  ∀ (T : Over S) (x y z : schemeSpace T ⟶ J)
    (hx : x ≫ groupSpaceProjection J = testProjection (Over.mk (𝟙 S)) T)
    (hy : y ≫ groupSpaceProjection J = testProjection (Over.mk (𝟙 S)) T)
    (hz : z ≫ groupSpaceProjection J = testProjection (Over.mk (𝟙 S)) T)
    (L M : (Limits.pullback f T.hom).Pic),
    (e.classify T ⟨x, hx⟩).val = (toPicardFunctor f).app (op T) L →
    (e.classify T ⟨y, hy⟩).val = (toPicardFunctor f).app (op T) M →
    (∀ U : (Over S)ᵒᵖ, ∀ t : (schemeSpace T).obj.obj.obj U,
      z.hom.hom.app U t = @Mul.mul _ (g.group U).toMul
        (x.hom.hom.app U t) (y.hom.hom.app U t)) →
    (e.classify T ⟨z, hz⟩).val = (toPicardFunctor f).app (op T) (L * M)

/-- The normalized difference of a fibre line is the restricted universal family.
Source: Milne III 6.6 (blueprint: def-sfb-relative-jacobian-theta-data). -/
def FibreDifference {B : AlgebraicSpace S} (A D : Pointed B)
    (P : (product A.p D.p).SmallModules)
    (B0 : Over S) {K : Type u} [Field K] (t : Spec (.of K) ⟶ B0.left)
    (Z : Over (Spec (.of K))) [GrpObj Z]
    (j : test B0 ((Over.map t).obj Z) ⟶ A.X) (lam : A.X ⟶ D.X)
    (L : Z.left.Modules) : Prop :=
  ∃ v : test B0 ((Over.map t).obj (Z ⊗ Z)) ⟶ product A.p D.p,
    v ≫ Poincare.fst A.p D.p = groupSchemeMap ((Over.map B0.hom).map ((Over.map t).map (fst Z Z))) ≫
      j ∧
    v ≫ Poincare.snd A.p D.p = groupSchemeMap ((Over.map B0.hom).map ((Over.map t).map (snd Z Z))) ≫
      j ≫ lam ∧
    Nonempty ((schemeModule ((Over.map B0.hom).obj ((Over.map t).obj (Z ⊗ Z)))).obj
      ((smallModuleTensorPullback v).obj P) ≅ abelianNormalizedDifference Z L)

/-- The geometric theta characterization: the Abel image after subtracting `(g-1)p`
provides an ample line whose normalized difference is the specified polarization.
All choices of point and all translations are included.
Source: Milne III Theorem 6.6 and Summary 6.11
(blueprint: def-sfb-relative-jacobian-theta-data). -/
def GeometricTheta {B : Over S} {C : Scheme.{u}} (f : C ⟶ B.left) (g : ℕ)
    (A D : Pointed (schemeSpace B)) (e : Presentation f A.X A.p)
    (P : (product A.p D.p).SmallModules) (lam : A.X ⟶ D.X) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ B.left),
    ∃ (Z : Over (Spec (.of K))) (_zGroup : GrpObj Z)
      (eZ : (picardFunctorDegree (Limits.pullback.snd f t) 0).obj.RepresentableBy Z)
      (j : test B ((Over.map t).obj Z) ⟶ A.X),
      IsAbelianVariety Z ∧ IsPicardZeroMul (Limits.pullback.snd f t) eZ ∧
      (∀ (U : Over (Spec (.of K))) (a : U ⟶ Z),
        ∃ w : (groupSchemeMap ((Over.map B.hom).map ((Over.map t).map a)) ≫ j) ≫
            A.p = testProjection B ((Over.map t).obj U),
          (picardFunctorIsoOfIsPullback (IsPullback.of_hasPullback f t)).hom.app (op U)
            (e.classify ((Over.map t).obj U)
              ⟨groupSchemeMap ((Over.map B.hom).map ((Over.map t).map a)) ≫ j, w⟩).val =
            (picardFunctorDegreeι (Limits.pullback.snd f t) 0).hom.app (op U)
              (eZ.homEquiv a)) ∧
      ∀ (p : Spec (.of K) ⟶ Limits.pullback f t)
        (_hp : p ≫ Limits.pullback.snd f t = 𝟙 _),
        ∃ (N : (Limits.pullback f t).Pic),
          Nonempty ((fromSkeleton _).obj N.val ≅ p.ker.toModules) ∧
          ∃ (H : Over (Spec (.of K)))
            (eH : (hilbertPresheaf (Limits.pullback.snd f t) (g - 1)).RepresentableBy H)
            (a : H ⟶ Z),
            (∀ (U : Over (Spec (.of K))) (v : U ⟶ H),
              ∃ (L : (Limits.pullback (Limits.pullback.snd f t) U.hom).Pic),
                Nonempty ((fromSkeleton _).obj L.val ≅ (eH.homEquiv v).val.toModulesᵛ) ∧
                ∃ hL : L * Scheme.Pic.map
                    (Limits.pullback.fst (Limits.pullback.snd f t) U.hom) (N ^ (g - 1)) ∈
                    (picardSubfunctorDegree (Limits.pullback.snd f t) 0).obj (op U),
                  eZ.homEquiv (v ≫ a) =
                    (toSheafify (Scheme.fppfTopology.over (Spec (.of K)))
                      (picardSubfunctorDegree (Limits.pullback.snd f t) 0).toFunctor).app
                      (op U) ⟨L * Scheme.Pic.map
                        (Limits.pullback.fst (Limits.pullback.snd f t) U.hom)
                          (N ^ (g - 1)), hL⟩) ∧
            a.left.ker.IsInvertible ∧
            ∃ (Ltheta : Z.left.Modules) (_hL : Ltheta.IsInvertible),
              Nonempty (Ltheta ≅ a.left.ker.toModulesᵛ) ∧
              Scheme.Modules.IsAmple Z.left Ltheta ∧
              FibreDifference A D P B t Z j lam Ltheta ∧
              ∀ (b : Z ⟶ Z),
                (∃ x : 𝟙_ (Over (Spec (.of K))) ⟶ Z,
                  b = lift (𝟙 Z) (toUnit Z ≫ x) ≫ μ[Z]) →
                FibreDifference A D P B t Z j lam ((Scheme.Modules.pullback b.left).obj Ltheta)

/-- Canonical Picard identification under base change, characterized on every test.
Source: Deligne 4.1; Milne III Section 8
(blueprint: def-sfb-relative-jacobian-theta-data). -/
def PicardBaseChange {C : Scheme.{u}} (f : C ⟶ S)
    (A : Pointed (groupSpaceBase S))
    (e : Presentation (B := Over.mk (𝟙 S)) f A.X A.p)
    (T : Over S)
    (eT : Presentation (B := T) (Limits.pullback.snd f T.hom)
      (A.baseChange (testProjection (Over.mk (𝟙 S)) T)).X
      (A.baseChange (testProjection (Over.mk (𝟙 S)) T)).p) : Prop :=
  ∀ (U : Over T.left)
    (a : {a : test T U ⟶ (A.baseChange (testProjection (Over.mk (𝟙 S)) T)).X //
      a ≫ (A.baseChange (testProjection (Over.mk (𝟙 S)) T)).p = testProjection T U})
    (b : {b : test (Over.mk (𝟙 S)) ((Over.map T.hom).obj U) ⟶ A.X //
      b ≫ A.p = testProjection (Over.mk (𝟙 S)) ((Over.map T.hom).obj U)}),
    a.val ≫ A.baseChangeMap (testProjection (Over.mk (𝟙 S)) T) = b.val →
    (eT.classify U a).val =
      (picardFunctorIsoOfIsPullback (IsPullback.of_hasPullback f T.hom)).hom.app (op U)
        (e.classify ((Over.map T.hom).obj U) b).val

/-- Pullback of the polarization is the theta polarization of the pulled-back curve.
Projection equations uniquely characterize the map, hence retain the identity and
iterated-pullback comparisons. Picard presentations are characterized on all tests too.
Source: Deligne 4.1 (blueprint: def-sfb-relative-jacobian-theta-data). -/
def UniversalThetaBaseChange {C : Scheme.{u}} (f : C ⟶ S) (g : ℕ)
    (A D : Pointed (groupSpaceBase S))
    (e : Presentation (B := Over.mk (𝟙 S)) f A.X A.p)
    (P : (product A.p D.p).SmallModules) (r : Axes A D P)
    (lam : A.X ⟶ D.X) : Prop :=
  ∀ (T : Over S) [IsLocallyNoetherian T.left],
    ∃ (eT : Presentation (B := T) (Limits.pullback.snd f T.hom)
        (A.baseChange (testProjection (Over.mk (𝟙 S)) T)).X
        (A.baseChange (testProjection (Over.mk (𝟙 S)) T)).p)
      (rT : Axes (A.baseChange (testProjection (Over.mk (𝟙 S)) T))
        (D.baseChange (testProjection (Over.mk (𝟙 S)) T))
        ((smallModuleTensorPullback
          (baseChangeProductMap A D (testProjection (Over.mk (𝟙 S)) T))).obj P)),
      PicardBaseChange f A e T eT ∧
      IsBaseChangedAxes A D (testProjection (Over.mk (𝟙 S)) T) P r rT ∧
      Represents (A.baseChange (testProjection (Over.mk (𝟙 S)) T))
        (D.baseChange (testProjection (Over.mk (𝟙 S)) T))
        ((smallModuleTensorPullback
          (baseChangeProductMap A D (testProjection (Over.mk (𝟙 S)) T))).obj P) rT ∧
      ∃! lamT : (A.baseChange (testProjection (Over.mk (𝟙 S)) T)).X ⟶
          (D.baseChange (testProjection (Over.mk (𝟙 S)) T)).X,
        lamT ≫ D.baseChangeMap (testProjection (Over.mk (𝟙 S)) T) =
          A.baseChangeMap (testProjection (Over.mk (𝟙 S)) T) ≫ lam ∧
        lamT ≫ (D.baseChange (testProjection (Over.mk (𝟙 S)) T)).p =
          (A.baseChange (testProjection (Over.mk (𝟙 S)) T)).p ∧
        IsIso lamT ∧
        GeometricTheta (Limits.pullback.snd f T.hom) g
          (A.baseChange (testProjection (Over.mk (𝟙 S)) T))
          (D.baseChange (testProjection (Over.mk (𝟙 S)) T)) eT
          ((smallModuleTensorPullback
            (baseChangeProductMap A D (testProjection (Over.mk (𝟙 S)) T))).obj P) lamT

/-- Picard transport induced by inverse pullback along an actual curve isomorphism.
Source: Milne III Sections 6 and 8; Deligne 4.1
(blueprint: def-sfb-relative-jacobian-theta-data). -/
def CurveTransport {C C' : Scheme.{u}} (f : C ⟶ S) (f' : C' ⟶ S)
    (u : C ≅ C') (hu : IsPullback u.inv f' f (𝟙 S))
    (J J' : AlgebraicSpace S)
    (e : Presentation (B := Over.mk (𝟙 S)) f J (groupSpaceProjection J))
    (e' : Presentation (B := Over.mk (𝟙 S)) f' J' (groupSpaceProjection J'))
    (a : J ⟶ J') : Prop :=
  ∀ (T : Over S)
    (x : {x : test (Over.mk (𝟙 S)) T ⟶ J //
      x ≫ groupSpaceProjection J = testProjection (Over.mk (𝟙 S)) T})
    (y : {y : test (Over.mk (𝟙 S)) T ⟶ J' //
      y ≫ groupSpaceProjection J' = testProjection (Over.mk (𝟙 S)) T}),
    x.val ≫ a = y.val →
      (e'.classify T y).val =
        (picardFunctorIsoOfIsPullback hu).hom.app (op T) (e.classify T x).val

/-- The polarized curve-isomorphism equation, with the dual map characterized by
pullback of the normalized universal line. This includes identity and composites,
since all curve isomorphisms and all normalized dual maps are quantified.
Source: Milne III Sections 6 and 8; Deligne 4.1
(blueprint: def-sfb-relative-jacobian-theta-data). -/
def CurveIsomorphismNaturality {C : Scheme.{u}} (f : C ⟶ S) (genus : ℕ)
    (J D : AlgebraicSpace S) (gJ : CommutativeSpaceGroup J) (gD : CommutativeSpaceGroup D)
    (e : Presentation (B := Over.mk (𝟙 S)) f J (groupSpaceProjection J))
    (P : (product (groupSpaceProjection J) (groupSpaceProjection D)).SmallModules)
    (lam : J ⟶ D) : Prop :=
  ∀ (C' : Scheme.{u}) (f' : C' ⟶ S) (u : C ≅ C')
    (hu : IsPullback u.inv f' f (𝟙 S))
    (J' D' : AlgebraicSpace S) (gJ' : CommutativeSpaceGroup J')
    (gD' : CommutativeSpaceGroup D')
    (e' : Presentation (B := Over.mk (𝟙 S)) f' J' (groupSpaceProjection J'))
    (Q : (product (groupSpaceProjection J') (groupSpaceProjection D')).SmallModules)
    (rQ : Axes (pointedGroup J' gJ') (pointedGroup D' gD') Q),
    TensorCompatible f' J' e' gJ' →
    IsAbelianFamily (groupSpaceProjection J') →
    IsAbelianFamily (groupSpaceProjection D') →
    Represents (pointedGroup J' gJ') (pointedGroup D' gD') Q rQ →
    ∀ (lam' : J' ⟶ D'), IsHom gJ' gD' lam' →
      GeometricTheta f' genus (pointedGroup J' gJ') (pointedGroup D' gD') e' Q lam' →
      ∀ (a : J ≅ J') (aDual : D' ⟶ D),
        CurveTransport f f' u hu J J' e e' a.hom →
        Dualizes J D J' D' gJ gD gJ' gD' P Q a.hom aDual →
        a.hom ≫ lam' ≫ aDual = lam

end AlgebraicGeometry.AlgebraicSpace.JacobianTheta


