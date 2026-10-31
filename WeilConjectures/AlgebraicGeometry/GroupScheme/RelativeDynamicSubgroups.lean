/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeDynamicAttractionData
public import WeilConjectures.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import WeilConjectures.AlgebraicGeometry.SolvableGroupStructure
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.DirectSum.Internal
import WeilConjectures.AlgebraicGeometry.AffineFormallySmooth
import WeilConjectures.AlgebraicGeometry.GmRepresentationWeightBasis
import WeilConjectures.AlgebraicGeometry.TransverseSubgroupProductOpen
import WeilConjectures.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Smooth.Basic

/-! # Relative dynamic subgroups

Source: Conrad, Reductive group schemes, Theorem 4.1.7(1)--(4), pp.112--114,
and the base-change paragraph following Example 4.1.9, p.114
(blueprint: lem-sfb-relative-dynamic-subgroups).

Orbit extensions are morphisms of schemes. Fixed points are tested after every
extension of the test scheme. Weights use the universal Laurent coordinate, including
over nonreduced rings. Tangent vectors are the existing dual-number points of `Lie`.
The diagram below only packages witnesses to the theorem; no witness is chosen by a definition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite
open scoped MonObj TensorProduct

namespace AlgebraicGeometry.RelativeDynamic

section Orbit

variable {S : Scheme.{u}} (T : Grp (Over S)) (L : Over S)
  (j : T.X ⟶ L) (zero : 𝟙_ (Over S) ⟶ L)
  (G : Grp (Over S)) (act : T.X ⊗ G.X ⟶ G.X)

/-- P consists of points with an orbit extension. Source: Conrad, Theorem 4.1.7, p.112
(blueprint: lem-sfb-relative-dynamic-subgroups). -/
def parabolicPoints (W : Over S) : Set (W ⟶ G.X) :=
  {g | ∃ p, IsOrbitExtension T L j G act W g p}

/-- U consists of points whose orbit extends with value one at zero.
Source: Conrad, Theorem 4.1.7, p.112 (blueprint: lem-sfb-relative-dynamic-subgroups). -/
def unipotentPoints (W : Over S) : Set (W ⟶ G.X) :=
  {g | ∃ p, IsOrbitExtension T L j G act W g p ∧
    lift (𝟙 W) (toUnit W ≫ zero) ≫ p = 1}

/-- Z consists of points fixed on every further test scheme, including nonreduced tests.
Source: Conrad, Theorem 4.1.7, p.112 (blueprint: lem-sfb-relative-dynamic-subgroups). -/
def fixedPoints (W : Over S) : Set (W ⟶ G.X) :=
  {g | ∀ (V : Over S) (f : V ⟶ W) (t : V ⟶ T.X), lift t (f ≫ g) ≫ act = f ≫ g}

/-- Reverse the action by inversion on G_m. Source: Conrad, p.111
(blueprint: lem-sfb-relative-dynamic-subgroups). -/
def oppositeAction : T.X ⊗ G.X ⟶ G.X := (ι[T.X] ⊗ₘ 𝟙 G.X) ≫ act

end Orbit

/-- The represented groups and maps occurring in Theorem 4.1.7. The order of factors
in the product is Z times U. Source: Conrad, pp.112--113
(blueprint: lem-sfb-relative-dynamic-subgroups). -/
structure Diagram {S : Scheme.{u}} (G : Grp (Over S)) where
  /-- The nonnegative limit group. -/
  P : Grp (Over S)
  /-- The positive contraction group. -/
  U : Grp (Over S)
  /-- The fixed group. -/
  Z : Grp (Over S)
  /-- The contraction group for the opposite action. -/
  V : Grp (Over S)
  /-- Inclusion of P into G. -/
  iP : P ⟶ G
  /-- Inclusion of U into G. -/
  iU : U ⟶ G
  /-- Inclusion of Z into G. -/
  iZ : Z ⟶ G
  /-- Inclusion of the opposite contraction group into G. -/
  iV : V ⟶ G
  /-- Inclusion of U into P. -/
  uP : U ⟶ P
  /-- Inclusion of Z into P. -/
  zP : Z ⟶ P
  /-- Evaluation at zero. -/
  q : P ⟶ Z
  /-- The scheme isomorphism (z,u) maps to zu. -/
  productIso : Z.X ⊗ U.X ≅ P.X
  /-- The conjugation (z,u) maps to z^-1 u z. -/
  conjugation : Z.X ⊗ U.X ⟶ U.X

/-- Pull back every object and arrow of the dynamic diagram, using the canonical
product comparison for pullback. Source: Conrad, paragraph after Example 4.1.9, p.114
(blueprint: lem-sfb-relative-dynamic-subgroups). -/
def Diagram.baseChange {S S' : Scheme.{u}} {G : Grp (Over S)}
    (D : Diagram G) (f : S' ⟶ S) : Diagram ((Over.pullback f).mapGrp.obj G) where
  P := (Over.pullback f).mapGrp.obj D.P
  U := (Over.pullback f).mapGrp.obj D.U
  Z := (Over.pullback f).mapGrp.obj D.Z
  V := (Over.pullback f).mapGrp.obj D.V
  iP := (Over.pullback f).mapGrp.map D.iP
  iU := (Over.pullback f).mapGrp.map D.iU
  iZ := (Over.pullback f).mapGrp.map D.iZ
  iV := (Over.pullback f).mapGrp.map D.iV
  uP := (Over.pullback f).mapGrp.map D.uP
  zP := (Over.pullback f).mapGrp.map D.zP
  q := (Over.pullback f).mapGrp.map D.q
  productIso := Functor.Monoidal.μIso (Over.pullback f) D.Z.X D.U.X ≪≫
    (Over.pullback f).mapIso D.productIso
  conjugation := Functor.LaxMonoidal.μ (Over.pullback f) D.Z.X D.U.X ≫
    (Over.pullback f).map D.conjugation

section Weights

variable {R : Type u} [CommRing R] (T G : Grp (Over (Spec (.of R))))
  (chi : ℤ → Γ(T.X.left, ⊤)) (act : T.X ⊗ G.X ⟶ G.X)

/-- The ideal generated by the negative-degree functions. Source: Conrad, p.113
(blueprint: lem-sfb-relative-dynamic-subgroups). -/
def parabolicIdeal : Ideal Γ(G.X.left, ⊤) :=
  Ideal.span {f | ∃ n : ℤ, n < 0 ∧ f ∈ homogeneous T G chi act n}

/-- The ideal generated by every nonzero-degree function. Source: Conrad, p.113
(blueprint: lem-sfb-relative-dynamic-subgroups). -/
def fixedIdeal : Ideal Γ(G.X.left, ⊤) :=
  Ideal.span {f | ∃ n : ℤ, n ≠ 0 ∧ f ∈ homogeneous T G chi act n}

/-- The negative functions together with f-epsilon(f) in degree zero.
Source: Conrad, proof of Theorem 4.1.7, p.113
(blueprint: lem-sfb-relative-dynamic-subgroups). -/
def unipotentIdeal : Ideal Γ(G.X.left, ⊤) :=
  parabolicIdeal T G chi act ⊔
    Ideal.span {g | ∃ f ∈ homogeneous T G chi act 0,
      g = f - G.X.hom.appTop ((GrpObj.unitSection G.X).appTop f)}

/-- The actual tangent image under an inclusion, characterized by dual-number points.
The span equals the image, since the map is a group homomorphism.
Source: Conrad, Theorem 4.1.7(4), p.113
(blueprint: lem-sfb-relative-dynamic-subgroups). -/
def tangentImage {H : Grp (Over (Spec (.of R)))} (i : H ⟶ G) :
    Submodule R (GrpObj.Lie G.X) :=
  Submodule.span R {v | ∃ w : GrpObj.Lie H.X,
    GrpObj.tangentPoint w ≫ i.hom.hom = GrpObj.tangentPoint v}

end Weights

/-- Representability and all structural maps, on every test scheme. In particular this
includes every commutative test algebra and every further algebra extension. All schemes
involved are affine, so this is equivalent to their functors on test algebras.
Source: Conrad, Theorem 4.1.7(1),(3),(4), pp.112--114
(blueprint: lem-sfb-relative-dynamic-subgroups). -/
def Structural {S : Scheme.{u}} (T : Grp (Over S)) (L : Over S)
    (j : T.X ⟶ L) (zero : 𝟙_ (Over S) ⟶ L)
    (G : Grp (Over S)) (act : T.X ⊗ G.X ⟶ G.X) (D : Diagram G) : Prop :=
  IsClosedImmersion D.iP.hom.hom.left ∧ IsClosedImmersion D.iU.hom.hom.left ∧
  IsClosedImmersion D.iZ.hom.hom.left ∧ IsClosedImmersion D.iV.hom.hom.left ∧
  (∀ (W : Over S) (g : W ⟶ G.X),
    ((∃ p, p ≫ D.iP.hom.hom = g) ↔ g ∈ parabolicPoints T L j G act W) ∧
    ((∃ p, p ≫ D.iU.hom.hom = g) ↔ g ∈ unipotentPoints T L j zero G act W) ∧
    ((∃ p, p ≫ D.iZ.hom.hom = g) ↔ g ∈ fixedPoints T G act W) ∧
    ((∃ p, p ≫ D.iV.hom.hom = g) ↔
      g ∈ unipotentPoints T L j zero G (oppositeAction T G act) W)) ∧
  D.uP ≫ D.iP = D.iU ∧ D.zP ≫ D.iP = D.iZ ∧ D.zP ≫ D.q = 𝟙 D.Z ∧
  (∀ (W : Over S) (p : W ⟶ D.P.X) (b : W ⊗ L ⟶ G.X),
    IsOrbitExtension T L j G act W (p ≫ D.iP.hom.hom) b →
      lift (𝟙 W) (toUnit W ≫ zero) ≫ b = p ≫ D.q.hom.hom ≫ D.iZ.hom.hom) ∧
  (∀ (W : Over S) (p : W ⟶ D.P.X),
    p ≫ D.q.hom.hom = 1 ↔ ∃ v, v ≫ D.uP.hom.hom = p) ∧
  (∀ W : Over S, (IsMonHom.monoidHom D.uP.hom.hom W).range.Normal) ∧
  D.productIso.hom ≫ D.iP.hom.hom =
    (fst D.Z.X D.U.X ≫ D.iZ.hom.hom) * (snd D.Z.X D.U.X ≫ D.iU.hom.hom) ∧
  D.conjugation ≫ D.iU.hom.hom =
    (fst D.Z.X D.U.X ≫ D.iZ.hom.hom)⁻¹ *
      (snd D.Z.X D.U.X ≫ D.iU.hom.hom) * (fst D.Z.X D.U.X ≫ D.iZ.hom.hom) ∧
  (∀ (W : Over S) (z z' : W ⟶ D.Z.X) (v v' : W ⟶ D.U.X),
    (lift z v ≫ D.productIso.hom) * (lift z' v' ≫ D.productIso.hom) =
      lift (z * z') ((lift z' v ≫ D.conjugation) * v') ≫ D.productIso.hom) ∧
  IsOpenImmersion ((D.iV.hom.hom ⊗ₘ D.iP.hom.hom) ≫ μ[G.X]).left

/-- Smooth affine finite presentation, geometric connectedness and geometric unipotence.
A faithful representation is required separately on every geometric fibre, without
assuming any faithful representation over the original ring.
Source: Conrad, Theorem 4.1.7(1),(2),(4), pp.112--114
(blueprint: lem-sfb-relative-dynamic-subgroups). -/
def Geometric {S : Scheme.{u}} {G : Grp (Over S)} (D : Diagram G) : Prop :=
  (∀ H ∈ ({D.P, D.U, D.Z, D.V} : Set (Grp (Over S))),
    IsAffine H.X.left ∧ Smooth H.X.hom ∧ LocallyOfFinitePresentation H.X.hom) ∧
  GeometricallyConnected D.U.X.hom ∧
  (GeometricallyConnected G.X.hom →
    GeometricallyConnected D.P.X.hom ∧ GeometricallyConnected D.Z.X.hom) ∧
  ∀ (F : Type u) [Field F] [IsAlgClosed F] (s : Spec (.of F) ⟶ S),
    SolvableGroupStructure.IsUnipotent ((Over.pullback s).mapGrp.obj D.U)

/-- The coordinate ideals and the three actual tangent inclusions into Lie(G).
Source: Conrad, Theorem 4.1.7(4) and its proof, pp.113--114
(blueprint: lem-sfb-relative-dynamic-subgroups). -/
def CoordinatesAndTangents {R : Type u} [CommRing R]
    (T : Grp (Over (Spec (.of R)))) (chi : ℤ → Γ(T.X.left, ⊤))
    (G : Grp (Over (Spec (.of R)))) (act : T.X ⊗ G.X ⟶ G.X)
    (D : Diagram G) : Prop :=
  RingHom.ker D.iP.hom.hom.left.appTop.hom = parabolicIdeal T G chi act ∧
  RingHom.ker D.iZ.hom.hom.left.appTop.hom = fixedIdeal T G chi act ∧
  RingHom.ker D.iU.hom.hom.left.appTop.hom = unipotentIdeal T G chi act ∧
  DirectSum.IsInternal (weightSpace T G chi act) ∧
  tangentImage G D.iZ = weightSpace T G chi act 0 ∧
  tangentImage G D.iU = ⨆ (n : ℤ) (_ : 0 < n), weightSpace T G chi act n ∧
  tangentImage G D.iP = ⨆ (n : ℤ) (_ : 0 ≤ n), weightSpace T G chi act n

/-- Base change of the action is its pullback preceded by the canonical product comparison.
Source: Conrad, paragraph following Example 4.1.9, p.114
(blueprint: lem-sfb-relative-dynamic-subgroups). -/
def baseChangeAction {S S' : Scheme.{u}} (T G : Grp (Over S))
    (act : T.X ⊗ G.X ⟶ G.X) (f : S' ⟶ S) :
    ((Over.pullback f).mapGrp.obj T).X ⊗ ((Over.pullback f).mapGrp.obj G).X ⟶
      ((Over.pullback f).mapGrp.obj G).X :=
  Functor.LaxMonoidal.μ (Over.pullback f) T.X G.X ≫ (Over.pullback f).map act

/-- Pull back the Laurent characters as regular functions.
Source: Conrad, pp.113--114 (blueprint: lem-sfb-relative-dynamic-subgroups). -/
def baseChangeCharacters {S S' : Scheme.{u}} (T : Grp (Over S))
    (chi : ℤ → Γ(T.X.left, ⊤)) (f : S' ⟶ S) (n : ℤ) :
    Γ(((Over.pullback f).mapGrp.obj T).X.left, ⊤) :=
  (pullback.fst T.X.hom f).appTop (chi n)

/-- All conclusions, formulated so the same predicates can be applied after any pullback.
Source: Conrad, Theorem 4.1.7 and paragraph after Example 4.1.9, pp.112--114
(blueprint: lem-sfb-relative-dynamic-subgroups). -/
def Conclusions {R : Type u} [CommRing R]
    (T : Grp (Over (Spec (.of R)))) (L : Over (Spec (.of R)))
    (j : T.X ⟶ L) (zero : 𝟙_ (Over (Spec (.of R))) ⟶ L)
    (chi : ℤ → Γ(T.X.left, ⊤)) (G : Grp (Over (Spec (.of R))))
    (act : T.X ⊗ G.X ⟶ G.X) (D : Diagram G) : Prop :=
  Structural T L j zero G act D ∧ Geometric D ∧ CoordinatesAndTangents T chi G act D

/-- Pulling back the displayed diagram satisfies exactly the same conclusions, for the
pulled-back action, line, zero section and characters. Inclusions, q, conjugation and the
semidirect product isomorphism are the actual pullbacks supplied by `Diagram.baseChange`.
Source: Conrad, paragraph after Example 4.1.9, p.114
(blueprint: lem-sfb-relative-dynamic-subgroups). -/
def BaseChangeConclusions {R B : Type u} [CommRing R] [CommRing B]
    (T : Grp (Over (Spec (.of R)))) (L : Over (Spec (.of R)))
    (j : T.X ⟶ L) (zero : 𝟙_ (Over (Spec (.of R))) ⟶ L)
    (chi : ℤ → Γ(T.X.left, ⊤)) (G : Grp (Over (Spec (.of R))))
    (act : T.X ⊗ G.X ⟶ G.X) (D : Diagram G) (f : Spec (.of B) ⟶ Spec (.of R)) : Prop :=
  Conclusions ((Over.pullback f).mapGrp.obj T) ((Over.pullback f).obj L)
    ((Over.pullback f).map j)
    (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map zero)
    (baseChangeCharacters T chi f) ((Over.pullback f).mapGrp.obj G)
    (baseChangeAction T G act f) (D.baseChange f)

/-- Scalar extension identifies every weight module, and supplies the canonical tangent
comparison for G and each subgroup. The point characterization also makes these
comparisons commute with the inclusions and with successive extensions: both composites
have the same dual-number point on every pure tensor.
Source: Conrad, Theorem 4.1.7(4) and base-change paragraph, pp.113--114
(blueprint: lem-sfb-relative-dynamic-subgroups). -/
def TangentBaseChange {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (T : Grp (Over (Spec (.of R)))) (chi : ℤ → Γ(T.X.left, ⊤))
    (G : Grp (Over (Spec (.of R)))) (act : T.X ⊗ G.X ⟶ G.X)
    (D : Diagram G) : Prop :=
  (∃ e : B ⊗[R] GrpObj.Lie G.X ≃ₗ[B]
      GrpObj.Lie ((Over.pullback (Spec.map
        (CommRingCat.ofHom (algebraMap R B)))).mapGrp.obj G).X,
    IsTangentComparison G e ∧
    ∀ n : ℤ, Submodule.map e.toLinearMap
      (Submodule.span B {x | ∃ v ∈ weightSpace T G chi act n, x = 1 ⊗ₜ[R] v}) =
        weightSpace
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).mapGrp.obj T)
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).mapGrp.obj G)
          (baseChangeCharacters T chi (Spec.map (CommRingCat.ofHom (algebraMap R B))))
          (baseChangeAction T G act (Spec.map (CommRingCat.ofHom (algebraMap R B)))) n) ∧
  ∀ H ∈ ({D.P, D.U, D.Z} : Set (Grp (Over (Spec (.of R))))),
    ∃ e : B ⊗[R] GrpObj.Lie H.X ≃ₗ[B]
        GrpObj.Lie ((Over.pullback (Spec.map
          (CommRingCat.ofHom (algebraMap R B)))).mapGrp.obj H).X,
      IsTangentComparison H e

/-- Arbitrary and successive base changes preserve the entire specified diagram and its
coordinate and tangent identifications. The twice-pulled diagram is used literally,
so the comparison with one pullback is the canonical `Over.pullbackComp`, rather than
an unspecified isomorphism. Identity and nonflat base changes are included.
Source: Conrad, paragraph after Example 4.1.9, p.114
(blueprint: lem-sfb-relative-dynamic-subgroups). -/
def StableUnderBaseChange {R : Type u} [CommRing R]
    (T : Grp (Over (Spec (.of R)))) (L : Over (Spec (.of R)))
    (j : T.X ⟶ L) (zero : 𝟙_ (Over (Spec (.of R))) ⟶ L)
    (chi : ℤ → Γ(T.X.left, ⊤)) (G : Grp (Over (Spec (.of R))))
    (act : T.X ⊗ G.X ⟶ G.X) (D : Diagram G) : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra R B],
    BaseChangeConclusions T L j zero chi G act D
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) ∧
    TangentBaseChange (B := B) T chi G act D ∧
    ∀ (C : Type u) [CommRing C] [Algebra B C],
      BaseChangeConclusions
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).mapGrp.obj T)
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj L)
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map j)
        (Functor.LaxMonoidal.ε
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))) ≫
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map zero)
        (baseChangeCharacters T chi (Spec.map (CommRingCat.ofHom (algebraMap R B))))
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).mapGrp.obj G)
        (baseChangeAction T G act (Spec.map (CommRingCat.ofHom (algebraMap R B))))
        (D.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R B))))
        (Spec.map (CommRingCat.ofHom (algebraMap B C))) ∧
      TangentBaseChange (B := C)
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).mapGrp.obj T)
        (baseChangeCharacters T chi (Spec.map (CommRingCat.ofHom (algebraMap R B))))
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).mapGrp.obj G)
        (baseChangeAction T G act (Spec.map (CommRingCat.ofHom (algebraMap R B))))
        (D.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R B))))

/-- Relative dynamic subgroups for any smooth affine finitely presented group scheme,
with any multiplicative-group action by automorphisms; no connectedness, reductivity,
Noetherian or characteristic hypothesis is imposed.

Source: Conrad, Reductive group schemes, Theorem 4.1.7(1)--(4), pp.112--114, and
paragraph after Example 4.1.9, p.114 (blueprint: lem-sfb-relative-dynamic-subgroups).

Proof for stage 3, following the node's twelve steps:
1. The coaction gives the integer grading (lem-sfb-group-algebra-coaction-grading).
   Comparing Laurent coefficients, including after arbitrary algebra extension,
   identifies P and Z with the negative and nonzero homogeneous quotient ideals.
   Orbit extensions are unique because B[t] embeds in B[t,t^-1]. Products and
   inverses of orbit extensions give subgroup functors (def-weil-closed-immersion).
2. Evaluation at zero lands in Z and is a group homomorphism retracting Z into P.
   Its kernel ideal is the negative ideal plus f-epsilon(f) for degree-zero f.
   Choose finitely many homogeneous algebra generators. The negative generators,
   all nonzero generators, and the negative and adjusted zero generators generate
   the respective ideals. Thus all three coordinate quotients are finitely presented.
3. The kernel is normal. The mutually inverse morphisms (z,u) maps to zu and
   p maps to (q(p),q(p)^-1 p) give the specified semidirect product and conjugation law.
4. Use lem-sfb-graded-square-zero-smooth-lifting with B[t] to lift P-points, and
   with B in degree zero to lift Z-points. The affine infinitesimal criterion
   lem-weil-pbc-affine-formally-smooth-iff-ring-lifting, with finite presentation,
   gives smoothness (def-sbc-smooth-morphisms).
5. Lift a U-point first into P, then replace p by q(p)^-1 p to get a U-lift.
   The same criterion proves U smooth. Apply the construction to the opposite action.
6. The nonnegative grading of R[U], with degree-zero part R, defines an affine-line
   contraction. Every geometric-fibre point, including nonclosed points, is joined
   to the identity by the image of an affine line over its residue field.
7. Over a geometric field form G semidirect G_m. The embeddings g maps to (g,1)
   and t maps to (1,t) realize the action as conjugation.
8. Embed this field group faithfully in GL_n
   (lem-sfb-affine-group-faithful-linear-representation), and diagonalize G_m
   (lem-sfb-gm-representation-weight-basis). Orbit extension with limit one forces
   strictly upper unitriangular matrices, proving geometric unipotence.
9. Write tangent vectors as epsilon plus derivations using
   def-weil-pbc-kahler-differentials. Restriction to homogeneous functions is the
   full integer-character decomposition. The three coordinate ideals remove the
   negative, nonzero and nonpositive tangent weights, respectively.
10. The opposite U and P have trivial intersection and complementary tangent images.
    Apply lem-sfb-transverse-subgroup-product-open on geometric fibres; the source
    is smooth, hence flat by lem-weil-pbc-smooth-ring-map-base-change-composition
    and lem-weil-pbc-smooth-ring-map-iff-smooth-affine. Apply
    lem-sfb-flat-geometric-fibre-open-criterion to obtain the relative open immersion.
11. In a connected smooth geometric fibre, the big cell and translations, together
    with lem-sfb-locally-algebraic-group-identity-component, give connectedness of P.
    Its retraction to Z gives connectedness of Z.
12. The quotient ideals, orbit extensions and evaluation maps commute with every
    base change. Smoothness makes the identity cotangent module finite projective;
    lem-weil-pbc-kahler-differentials-base-change identifies its dual after scalar
    extension. Homogeneous summands and inclusions are preserved, with the stated
    dual-number normalization. Pullback and tensor composition give successive
    compatibility for all maps and tangent identifications.
-/
theorem relative_dynamic_subgroups
    (R : Type u) [CommRing R] (G : Grp (Over (Spec (.of R))))
    [IsAffine G.X.left] [Smooth G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [ModObj (RingGroupSchemes.multiplicative R).X G.X]
    (hAut : ∀ (W : Over (Spec (.of R)))
      (t : W ⟶ (RingGroupSchemes.multiplicative R).X) (x y : W ⟶ G.X),
      t • (x * y) = (t • x) * (t • y)) :
    ∃ D : Diagram G,
      Conclusions (RingGroupSchemes.multiplicative R) (affineLine R)
        (puncturedLine R) (zeroSection R) (characters R) G
        (ModObj.smul (M := (RingGroupSchemes.multiplicative R).X) (X := G.X)) D ∧
      StableUnderBaseChange (RingGroupSchemes.multiplicative R) (affineLine R)
        (puncturedLine R) (zeroSection R) (characters R) G
        (ModObj.smul (M := (RingGroupSchemes.multiplicative R).X) (X := G.X)) D := by
  sorry

end AlgebraicGeometry.RelativeDynamic
