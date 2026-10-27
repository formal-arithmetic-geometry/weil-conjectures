module

public import Sheaf.AlgebraicGeometry.SymmetricAbelImageGeometry
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.TraceFormula.SmoothComponentPureTranscendental
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed
import WeilConjectures.AlgebraicGeometry.DensePoints
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # The theta difference bundle and the normalized Picard family

Source: Milne, Abelian Varieties, Chapter III, Lemma 6.8(b), printed p.106
(blueprint: lem-sfb-theta-poincare-pullback).

## Main declarations

- `negativeThetaModule`: the line of the inversion pullback of the image divisor.
- `thetaDifferenceModule`: its three-factor difference module.
- `thetaAbelPullbackModule`: the pullback along the Abel map times inversion.
- `thetaZeroAxis`: the second normalization axis.
- `exists_theta_poincare_pullback_iso`: the isomorphism preserving both normalizations.

The Abel morphisms are specified on every test scheme by their divisor classes,
using the interfaces of `exists_pointedAbel_image_geometry`. Axis identifications
are the composites of the stipulated trivializations. Their compatibility at the
corner is expressed by heterogeneous equality after the canonical pullback
composition comparisons: the two composite scheme maps are equal.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Opposite MonObj
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The negative-theta line O([-1]*Theta), with Theta the scheme-theoretic image
of the specified symmetric Abel map. Source: Milne III, before Theorem 6.6 and
Lemma 6.8 (blueprint: lem-sfb-theta-poincare-pullback). -/
def negativeThetaModule {k : Type u} [Field k]
    {H J : Over (Spec (.of k))} [GrpObj J] (a : H ⟶ J) : J.left.Modules :=
  (Scheme.Modules.tensorPullback ι[J].left).obj a.left.ker.toModulesᵛ

/-- The three-factor difference bundle m*L tensor p1*L-dual tensor p2*L-dual.
Source: Milne III, before Theorem 6.6 and Lemma 6.8
(blueprint: lem-sfb-theta-poincare-pullback). -/
def thetaDifferenceModule {k : Type u} [Field k]
    {H J : Over (Spec (.of k))} [GrpObj J] (a : H ⟶ J) : (J ⊗ J).left.Modules :=
  ((Scheme.Modules.tensorPullback μ[J].left).obj (negativeThetaModule a) ⊗
    (Scheme.Modules.tensorPullback (fst J J).left).obj (negativeThetaModule a)ᵛ) ⊗
      (Scheme.Modules.tensorPullback (snd J J).left).obj (negativeThetaModule a)ᵛ

/-- Pull back the difference bundle along the Abel map times inversion.
Source: Milne III, Lemma 6.8(b)
(blueprint: lem-sfb-theta-poincare-pullback). -/
def thetaAbelPullbackModule {k : Type u} [Field k]
    {C : Scheme.{u}} {f : C ⟶ Spec (.of k)}
    {H J : Over (Spec (.of k))} [GrpObj J] (fP : Over.mk f ⟶ J) (a : H ⟶ J) :
    (pullback f J.hom).Modules :=
  (Scheme.Modules.tensorPullback (fP ⊗ₘ ι[J]).left).obj (thetaDifferenceModule a)

/-- The inclusion of C times the origin in C times J.
Source: Milne III, Lemma 6.8(b), identity-axis normalization
(blueprint: lem-sfb-theta-poincare-pullback). -/
def thetaZeroAxis {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (J : Over (Spec (.of k))) [GrpObj J] :
    C ⟶ pullback f J.hom :=
  (lift (𝟙 (Over.mk f)) (toUnit (Over.mk f) ≫ η[J])).left

/-- The normalized theta difference bundle pulls back to the identity Picard family.
Source: Milne III, Lemma 6.8(b), printed p.106
(blueprint: lem-sfb-theta-poincare-pullback).

Proof:
1. Projective-proper and smooth-component-pure-transcendental show C is proper and
geometrically integral. The Jacobian is smooth, proper, separated and finite type.
The projection C times J to J is proper by proper-base-change, flat by tensoring
k-vector spaces, and locally finitely presented by smoothness and base change.
2. Put A=(fP times inversion)*m*L. On a fibre a its map to J is t_(-a) composed
with fP. Generic-theta-Abel-Cartier-pullback identifies A_a with O(D(a)) on a dense
open, hence with M_a tensor O(gP), by symmetric-Abel-image-geometry and addition
of local divisor exponents.
3. Picard-fiber-triviality-closed applied to M tensor p*O(gP) tensor A-dual gives
a closed triviality locus. Rational-points-dense makes this locus all of J, so the
fibre identification holds everywhere.
4. At zero, M_0 is trivial, giving fP*L=O(gP). In the three-factor difference
bundle this cancels the first projection factor. The second projection factor is
a constant line on each curve fibre. Thus its pullback and M have isomorphic fibres.
5. Rigidified-product-seesaw extends the prescribed identification on P times J
to the global isomorphism. All its geometric hypotheses follow from step 1.
6. On C times zero the restricted isomorphism and the prescribed identification
agree at (P,0). Uniqueness in rigidified-product-seesaw, with parameter Spec k,
makes them equal. This gives precisely both normalization equations below.
The axis maps rP and r0 are obtained by composing the indicated trivializations;
the corner hypothesis says they agree at (P,0), via pullback composition.
-/
theorem exists_theta_poincare_pullback_iso
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsHProjective f]
    (g : ℕ) (hg : f.genus = g) (hgpos : 1 ≤ g)
    (P : Spec (.of k) ⟶ C) (hP : P ≫ f = 𝟙 _)
    (J : Over (Spec (.of k))) [GrpObj J]
    (hJ : @IsJacobian k _ C f _ _ _ (pointedAbelGeometricIntegrality f) J _)
    (eJ : (picardFunctorDegree f 0).obj.RepresentableBy J)
    (heJ : IsPicardZeroMul f eJ)
    (M : (pullback f J.hom).Pic)
    (hM : M ∈ (picardSubfunctorDegree f 0).obj (op J))
    (hMnorm : M ∈ (picardFunctorNormalized f P hP).obj (op J))
    (hMid : eJ.homEquiv (𝟙 J) =
      (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
        (picardSubfunctorDegree f 0).toFunctor).app (op J) ⟨M, hM⟩)
    (hMzero : Scheme.Pic.map (baseChangeMap f η[J]) M = 1)
    (N : C.Pic) (hN : Nonempty ((fromSkeleton C.Modules).obj N.val ≅ P.ker.toModules))
    (fP : Over.mk f ⟶ J)
    (hfP : ∀ (T : Over (Spec (.of k))) (Q : T ⟶ Over.mk f),
      ∃ (LQ : (pullback f T.hom).Pic),
        Nonempty ((fromSkeleton _).obj LQ.val ≅
          (pullback.lift Q.left (𝟙 T.left) Q.w).ker.toModulesᵛ) ∧
        ∃ hQ : LQ * Scheme.Pic.map (pullback.fst f T.hom) N ∈
            (picardSubfunctorDegree f 0).obj (op T),
          eJ.homEquiv (Q ≫ fP) =
            (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
              (picardSubfunctorDegree f 0).toFunctor).app (op T)
                ⟨LQ * Scheme.Pic.map (pullback.fst f T.hom) N, hQ⟩)
    (H : Over (Spec (.of k))) (eH : (hilbertPresheaf f (g - 1)).RepresentableBy H)
    (a : H ⟶ J)
    (ha : ∀ (T : Over (Spec (.of k))) (v : T ⟶ H),
      ∃ (L : (pullback f T.hom).Pic),
        Nonempty ((fromSkeleton _).obj L.val ≅ (eH.homEquiv v).val.toModulesᵛ) ∧
        ∃ hL : L * Scheme.Pic.map (pullback.fst f T.hom) (N ^ (g - 1)) ∈
            (picardSubfunctorDegree f 0).obj (op T),
          eJ.homEquiv (v ≫ a) =
            (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
              (picardSubfunctorDegree f 0).toFunctor).app (op T)
                ⟨L * Scheme.Pic.map (pullback.fst f T.hom) (N ^ (g - 1)), hL⟩)
    (rP : (Scheme.Modules.tensorPullback (sectionBaseChange f P hP J)).obj
        (thetaAbelPullbackModule fP a) ≅
      (Scheme.Modules.tensorPullback (sectionBaseChange f P hP J)).obj ((fromSkeleton _).obj M.val))
    (r0 : (Scheme.Modules.tensorPullback (thetaZeroAxis f J)).obj
        (thetaAbelPullbackModule fP a) ≅
      (Scheme.Modules.tensorPullback (thetaZeroAxis f J)).obj ((fromSkeleton _).obj M.val))
    (hcorner : HEq
      (((Scheme.Modules.tensorPullbackSectionComp η[J].left (sectionBaseChange f P hP J)).hom.app
          (thetaAbelPullbackModule fP a)) ≫
        (Scheme.Modules.tensorPullback η[J].left).map rP.hom ≫
        (Scheme.Modules.tensorPullbackSectionComp η[J].left (sectionBaseChange f P hP J)).inv.app
          ((fromSkeleton _).obj M.val))
      (((Scheme.Modules.tensorPullbackSectionComp P (thetaZeroAxis f J)).hom.app
          (thetaAbelPullbackModule fP a)) ≫
        (Scheme.Modules.tensorPullback P).map r0.hom ≫
        (Scheme.Modules.tensorPullbackSectionComp P (thetaZeroAxis f J)).inv.app
          ((fromSkeleton _).obj M.val))) :
    ∃ e : thetaAbelPullbackModule fP a ≅ (fromSkeleton _).obj M.val,
      (Scheme.Modules.tensorPullback (sectionBaseChange f P hP J)).map e.hom = rP.hom ∧
      (Scheme.Modules.tensorPullback (thetaZeroAxis f J)).map e.hom = r0.hom := by
  sorry

end AlgebraicGeometry
