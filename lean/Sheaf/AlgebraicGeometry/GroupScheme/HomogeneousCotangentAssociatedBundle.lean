/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.AssociatedVectorBundleFrame
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexExact
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree
import WeilConjectures.AlgebraicGeometry.Descent
import Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension

/-! # The cotangent bundle of a smooth homogeneous quotient

Source: Milne, Algebraic Groups (2017), Proposition 7.15, pp.142--143,
and Section 18c, pp.389--390; Stacks Tags 023T, 0B2C, 0B2F, 02G1, 02G2.
(blueprint: lem-sfb-homogeneous-cotangent-associated-bundle)

The bundle identifications are stated as descent frames for the actual relative
 differential sheaf and its exterior sheaf. The frame is normalized by the
canonical differential pairing and intertwines translations. Rational points
are used only to characterize morphisms of smooth algebraic groups over an
algebraically closed field; the representations and descent relations themselves
are scheme-theoretic, with the latter tested over every algebra.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry.HomogeneousCotangent

/-- The structural residue map at a point.
Source: Stacks 0B2C (blueprint: lem-sfb-homogeneous-cotangent-associated-bundle). -/
def residueScalar {F : Type u} [Field F] (X : Over (Spec (.of F))) (x : X.left) :
    F →+* X.left.residueField x :=
  (StructureSheaf.toStalk F (X.hom x) ≫ X.hom.stalkMap x ≫ X.left.residue x).hom

/-- The recorded dual-number tangent space, with scalars restricted along the
structural residue map. In particular no new tangent space or operation is chosen.
Source: Stacks 0B2C (blueprint: lem-sfb-homogeneous-cotangent-associated-bundle). -/
def tangentModule {F : Type u} [Field F] (X : Over (Spec (.of F))) (x : X.left) :
    ModuleCat.{u} F :=
  (ModuleCat.restrictScalars (residueScalar X x)).obj
    (ModuleCat.of (X.left.residueField x) (schemeTangentSpace F X.left X.hom x))

/-- The actual image of the subgroup tangent map.
Source: Stacks 0B2F (blueprint: lem-sfb-homogeneous-cotangent-associated-bundle). -/
abbrev lieImage {F : Type u} [Field F]
    {G H : Grp (Over (Spec (.of F)))} (i : H ⟶ G) : Submodule F (GrpObj.Lie G.X) :=
  LinearMap.range (GrpObj.differential i.hom.hom).toLinearMap

/-- The quotient of the actual tangent spaces at the identity.
Source: Milne, 7.15 (blueprint: lem-sfb-homogeneous-cotangent-associated-bundle). -/
abbrev quotientLie {F : Type u} [Field F]
    {G H : Grp (Over (Spec (.of F)))} (i : H ⟶ G) :=
  GrpObj.Lie G.X ⧸ lieImage i

/-- The canonical differential map with ordinary pullback and the given structural
map on its target; it is the recorded tensor differential map transported by
uniqueness of the pullback adjunction.
Source: Stacks 01UV (blueprint: lem-sfb-homogeneous-cotangent-associated-bundle). -/
def differentialMap {F : Type u} [Field F] {X Y : Over (Spec (.of F))} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f.left).obj Y.hom.relativeDifferentials ⟶
      X.hom.relativeDifferentials :=
  ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f.left)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction f.left)).inv.app Y.hom.relativeDifferentials ≫
    Scheme.Hom.relativeDifferentialsPullbackMap Y.hom f.left ≫
      (Scheme.Hom.relativeDifferentialsCongr (f.left ≫ Y.hom) (Over.w f)).hom

/-- Pulling the canonical differential map back to a specified point. The equality
h is precisely the commutative triangle defining the tangent map.
Source: Stacks 0B2F (blueprint: lem-sfb-homogeneous-cotangent-associated-bundle). -/
def differentialAt {F : Type u} [Field F] {X Y S : Over (Spec (.of F))}
    (f : X ⟶ Y) (x : S ⟶ X) (y : S ⟶ Y) (h : y = x ≫ f) :
    (Scheme.Modules.pullback y.left).obj Y.hom.relativeDifferentials ⟶
      (Scheme.Modules.pullback x.left).obj X.hom.relativeDifferentials :=
  (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).hom.app
      Y.hom.relativeDifferentials ≫
    (Scheme.Modules.pullbackComp x.left f.left).inv.app Y.hom.relativeDifferentials ≫
      (Scheme.Modules.pullback x.left).map (differentialMap f)

/-- Left translation on the quotient, as a genuine scheme map.
Source: Milne, Section 18c
(blueprint: lem-sfb-homogeneous-cotangent-associated-bundle). -/
def translation {F : Type u} [Field F] (G : Grp (Over (Spec (.of F))))
    (Q : Over (Spec (.of F))) (a : ModObj G.X Q)
    (k : 𝟙_ (Over (Spec (.of F))) ⟶ G.X) : Q ⟶ Q :=
  lift (toUnit Q ≫ k) (𝟙 Q) ≫ a.smul

/-- A representation matrix at a rational point, using the canonical map from the
chosen affine Spec F object to the terminal F-scheme.
Source: Milne, Section 4a
(blueprint: lem-sfb-homogeneous-cotangent-associated-bundle). -/
def matrixAt {F : Type u} [Field F] {H : Grp (Over (Spec (.of F)))}
    {I : Type u} [Fintype I] [DecidableEq I]
    (r : GeneralLinearGroup.RationalHom H.X I) [IsMonHom r]
    (h : 𝟙_ (Over (Spec (.of F))) ⟶ H.X) : Matrix I I F :=
  r.points F (toUnit ((Spec (.of F)).asOver (Spec (.of F))) ≫ h)

/-- A cotangent frame intertwines the canonical differential of each left
translation. The relation is one of sheaf maps, tested on all affine-valued
points and vectors; density of G(F), since G is smooth and F algebraically
closed, makes this equivalent to equivariance for the algebraic G-action.
Source: Milne, 18.14, and Stacks 01UV
(blueprint: lem-sfb-homogeneous-cotangent-associated-bundle). -/
def IsEquivariantFrame {F : Type u} [Field F]
    (G : Grp (Over (Spec (.of F)))) {Q : Over (Spec (.of F))}
    (q : G.X ⟶ Q) (a : ModObj G.X Q) (n : ℕ)
    (θ : (Scheme.Modules.pullback q.left).obj Q.hom.relativeDifferentials ≅
      AssociatedVectorBundle.free G.X.left n) : Prop :=
  ∀ (k : 𝟙_ (Over (Spec (.of F))) ⟶ G.X)
    (A : Type u) [CommRing A] [Algebra F A] (g : points G.X A),
    ∃ h : ((toUnit ((Spec (.of A)).asOver (Spec (.of F))) ≫ k) * g) ≫ q =
        (g ≫ q) ≫ translation G Q a k,
      ∀ v : ULift.{u} (Fin n) → A,
        (differentialAt (translation G Q a k) (g ≫ q) _ h).app ⊤
          (AssociatedVectorBundle.framedVector q Q.hom.relativeDifferentials n θ
            ((toUnit ((Spec (.of A)).asOver (Spec (.of F))) ≫ k) * g) v) =
          AssociatedVectorBundle.framedVector q Q.hom.relativeDifferentials n θ g v

/-- Smooth homogeneous quotients have the canonical equivariant cotangent
associated-bundle identification, including the top wedge and dimension clauses.

Source: Milne, Algebraic Groups (2017), Proposition 7.15, pp.142--143;
Section 18c, 18.11 and proof of 18.14, pp.389--390; Stacks 023T, 0B2C,
0B2F, 02G1, 02G2.
(blueprint: lem-sfb-homogeneous-cotangent-associated-bundle).

Proof for stage 3:
1. Left multiplication descends to Q on the fppf quotient. The torsor square
identifies the self-base-change of q with G times H -> G. Smooth base change
(lem-pc-proper-base-change), fpqc descent (lem-trf-smooth-fpqc-base-descent),
and smooth source descent (lem-sbc-smooth-flat-surjective-source-descent)
show first q and then Q smooth.
2. Its fibre at o is H. Dual-number lifts therefore identify the kernel of dq
with Lie H and show injectivity. Formal smoothness lifts every tangent vector
at o through e, giving surjectivity. This supplies the quotient equivalence
and its displayed dual-number formula. The canonical Lie/tangent equivalence
is the recorded def-sc-scheme-tangent-space interface.
3. Differentiate q(hxh inverse) = hq(x). Conjugation preserves Lie H, so
it induces the rational representation r on the quotient. The stabilizer
representation on T_o Q is transported through the quotient equivalence.
Dualizing gives the contragredient rV. The matrix identity is required after
every algebra extension. Smooth finite type gives finite-dimensional tangent
spaces (lem-ag-smooth-relative-differentials-finite-locally-free and
lem-sfb-rational-tangent-differential-fibre-duality).
4. The action automorphism (g,z) -> (g,gz), differential base change
(lem-trf-relative-differential-sheaf-base-change), and the canonical
relative differential map (def-a1-relative-differentials-pullback-map)
construct the cotangent linearization. Restrict along (g,o) and use the
finite-dimensional double-dual pairing to obtain θ. Its normalization is
exactly evaluation of lambda on the class of the tangent vector v.
5. θ_gh(w) = θ_g(hw) and θ_kg(w) = k θ_g(w) give the descent and
translation clauses, as identities of algebraic maps. Fully faithful
effective fpqc descent (lem-pc-fpqc-descent) identifies Ω with the
associated bundle and descends constant rank.
6. Exterior powers commute with pullback, checked on increasing basis wedges.
Taking wedges of θ gives θTop. Its displayed determinant formula on every
open characterizes the canonical comparison, and the descent relation
is the determinant of the original one. The empty determinant is 1,
so this also normalizes degree zero.
7. The differential rank equals smooth fibre dimension
(lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension), hence the
relative dimension is d everywhere. The identity image makes Q nonempty.
No argument divides by a characteristic or assumes H connected. -/
theorem homogeneous_cotangent_associated_bundle
    (F : Type u) [Field F] [IsAlgClosed F]
    (G H : Grp (Over (Spec (.of F)))) (i : H ⟶ G)
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth H.X.hom] [IsClosedSubgroupScheme i.hom.hom]
    (Q : Over (Spec (.of F))) [IsSeparated Q.hom] [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    (q : G.X ⟶ Q) [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    [QuasiCompact q.left] [QuasiSeparated q.left]
    (htorsor : IsPullback (fst G.X H.X)
      ((𝟙 G.X ⊗ₘ i.hom.hom) ≫ μ[G.X]) q q) :
    Smooth Q.hom ∧ Smooth q.left ∧
    Function.Injective (GrpObj.differential i.hom.hom) ∧
    ∃ (a : ModObj G.X Q)
      (d : ℕ) (b : Module.Basis (ULift.{u} (Fin d)) F (quotientLie i))
      (t : quotientLie i ≃ₗ[F]
        tangentModule Q (q.left (GrpObj.onePoint G.X)))
      (r rV : GeneralLinearGroup.RationalHom H.X (ULift.{u} (Fin d)))
      (_ : IsMonHom r) (_ : IsMonHom rV)
      (rTop : GeneralLinearGroup.RationalHom H.X (ULift.{u} (Fin 1)))
      (_ : IsMonHom rTop)
      (θ : (Scheme.Modules.pullback q.left).obj Q.hom.relativeDifferentials ≅
        AssociatedVectorBundle.free G.X.left d)
      (θTop : (Scheme.Modules.pullback q.left).obj
        (Scheme.Modules.exteriorSheaf Q.hom.relativeDifferentials d) ≅
          AssociatedVectorBundle.free G.X.left 1),
      (∀ (S : Over (Spec (.of F))) (g k : S ⟶ G.X),
        lift k (g ≫ q) ≫ a.smul = (k * g) ≫ q) ∧
      (∀ v : GrpObj.Lie G.X,
        (t ((lieImage i).mkQ v)).val =
          Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom
            (residueScalar Q (q.left (GrpObj.onePoint G.X))))) ≫
              (GrpObj.tangentPoint v).left ≫ q.left) ∧
      (∀ (h : 𝟙_ (Over (Spec (.of F))) ⟶ H.X) (v : GrpObj.Lie G.X),
        b.equivFun.symm ((matrixAt r h).mulVec (b.repr ((lieImage i).mkQ v))) =
          (lieImage i).mkQ
            (GrpObj.differential (GrpObj.conjBy G.X (h ≫ i.hom.hom)) v)) ∧
      (∀ (h : 𝟙_ (Over (Spec (.of F))) ⟶ H.X) (w : quotientLie i),
        (t (b.equivFun.symm ((matrixAt r h).mulVec (b.repr w)))).val =
          (t w).val ≫ (translation G Q a (h ≫ i.hom.hom)).left) ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A] (h : points H.X A),
        (rV.points A h : Matrix (ULift.{u} (Fin d)) (ULift.{u} (Fin d)) A) =
          (r.points A h⁻¹ : Matrix (ULift.{u} (Fin d)) (ULift.{u} (Fin d)) A).transpose) ∧
      AssociatedVectorBundle.IsDescentFrame G H i q d rV Q.hom.relativeDifferentials θ ∧
      IsEquivariantFrame G q a d θ ∧
      (∀ (ell : Module.Dual F (quotientLie i)) (v : GrpObj.Lie G.X),
        v.app ⊤
          ((differentialAt q (η[G.X]) (η[G.X] ≫ q) rfl).app ⊤
            ((AssociatedVectorBundle.frameAt q Q.hom.relativeDifferentials d θ η[G.X]).inv.app ⊤
              ((Scheme.Modules.freeSectionsEquiv (ULift.{u} (Fin d))).symm
                (fun j => (Scheme.ΓSpecIso (.of F)).inv ((b.dualBasis.repr ell) j))))) =
          (Scheme.ΓSpecIso (.of F)).inv (ell ((lieImage i).mkQ v))) ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A] (h : points H.X A),
        (rTop.points A h : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) A)
            (ULift.up 0) (ULift.up 0) =
          (rV.points A h : Matrix (ULift.{u} (Fin d)) (ULift.{u} (Fin d)) A).det) ∧
      AssociatedVectorBundle.IsDescentFrame G H i q 1 rTop
        (Scheme.Modules.exteriorSheaf Q.hom.relativeDifferentials d) θTop ∧
      (∀ (U : Q.left.Opens) (s : Fin d → Γ(Q.hom.relativeDifferentials, U)),
        Scheme.Modules.freeSectionsEquivOpens (q.left ⁻¹ᵁ U) (ULift.{u} (Fin 1))
          (θTop.hom.app (q.left ⁻¹ᵁ U)
            (Scheme.Modules.pullbackSection q.left
              (Scheme.Modules.exteriorSheafSection Q.hom.relativeDifferentials d U s)))
                (ULift.up 0) =
          Matrix.det (fun j k : ULift.{u} (Fin d) =>
            Scheme.Modules.freeSectionsEquivOpens (q.left ⁻¹ᵁ U) (ULift.{u} (Fin d))
              (θ.hom.app (q.left ⁻¹ᵁ U)
                (Scheme.Modules.pullbackSection q.left (s k.down))) j)) ∧
      Q.hom.relativeDifferentials.IsFiniteLocallyFreeOfRank d ∧
      SmoothOfRelativeDimension d Q.hom := by
  sorry

end AlgebraicGeometry.HomogeneousCotangent
