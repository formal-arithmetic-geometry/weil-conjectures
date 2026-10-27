/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ParameterRootBoundaryData
public import Sheaf.AlgebraicGeometry.SNCUniversalResidualCharts
public import Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Sheaf.RingTheory.MonicTensorPresentation
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Integral parameter-root projections and their nil closed fibres

Source: blueprint main-20261015, ctf-stability direct-images proof, paragraph (3),
extracted returned step 2 of the root-tower boundary argument.
(blueprint: lem-sfb-parameter-root-integral-nil-fibre).

The existing compatible-root quotient is the presentation of the filtered colimit:
its power relations give the finite stages and its compatibility relations give exactly
the divisibility transitions. All coordinate-ring assertions below use actual global
sections of the affine fibre product, so no identification of its nil thickening with
the reduced root quotient is made.

## Main statements

* `colimit_presentation`: the specified transitions and colimit universal property.
* `integral_nil_fibre`: the power basis, integral projection and nil closed fibre.
* `finiteStage_baseChange`: finite stages, roots and transitions under base change.
* `baseChange_naturality`: cartesian root and stratum squares and parameter naturality.
* `profinite_naturality`: iterated tests and simultaneous continuous parameter maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

namespace ParameterRootNilFibre

open RootBoundary
open AlgebraicGeometry.Scheme.UniversalCover

variable (p : ℕ) {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R)

/-- The finite-stage equations vanish under the divisibility substitution.
Source: direct-images proof (3), the transition x_(i,n) to x_(i,m)^(m/n)
(blueprint: lem-sfb-parameter-root-integral-nil-fibre).
Proof: on each generator, raising x_(i,m)^(m/n) to n gives x_(i,m)^m,
since n divides m; the defining relation at m makes this t_i. -/
theorem stageRelations_transition (n m : TameRootOrder p) (h : n.val ∣ m.val) :
    Ideal.span (Set.range (fun i : Fin r ↦
      MvPolynomial.X i ^ n.val - MvPolynomial.C (t i))) ≤
      RingHom.ker (MvPolynomial.aeval
        (fun i : Fin r ↦ sncRootCoordinate t m.val i ^ (m.val / n.val))).toRingHom := by
  sorry

/-- The actual transition homomorphism between finite root stages.
Source: direct-images proof (3), divisibility transition maps
(blueprint: lem-sfb-parameter-root-integral-nil-fibre). -/
def transition (n m : TameRootOrder p) (h : n.val ∣ m.val) :
    sncRootLevel t n.val →ₐ[R] sncRootLevel t m.val :=
  Ideal.Quotient.liftₐ _
    (MvPolynomial.aeval (fun i : Fin r ↦ sncRootCoordinate t m.val i ^ (m.val / n.val)))
    (stageRelations_transition p t n m h)

/-- The finite-stage equations vanish on the named roots of the full tower.
Source: direct-images proof (3), the stage-to-colimit maps
(blueprint: lem-sfb-parameter-root-integral-nil-fibre).
Proof: each evaluated generator is precisely the image of the corresponding
power relation among tameRootRelations, so vanishes in their quotient. -/
theorem stageRelations_tower (n : TameRootOrder p) :
    Ideal.span (Set.range (fun i : Fin r ↦
      MvPolynomial.X i ^ n.val - MvPolynomial.C (t i))) ≤
      RingHom.ker (MvPolynomial.aeval (fun i : Fin r ↦
        sncFullRootCoordinate p t n i)).toRingHom := by
  sorry

/-- The finite-stage coprojection into the actual compatible-root presentation.
Source: direct-images proof (3), the canonical maps into A
(blueprint: lem-sfb-parameter-root-integral-nil-fibre). -/
def stageInclusion (n : TameRootOrder p) : sncRootLevel t n.val →ₐ[R] tameRootAlgebra p t :=
  Ideal.Quotient.liftₐ _
    (MvPolynomial.aeval (fun i : Fin r ↦
      sncFullRootCoordinate p t n i))
    (stageRelations_tower p t n)

/-- The recorded compatible-root algebra has exactly the displayed divisibility
colimit universal property. The statement writes the cocone and its unique
factorization explicitly, rather than choosing another model for the same algebra.
Source: direct-images proof (3), A as the filtered colimit of A_n
(blueprint: lem-sfb-parameter-root-integral-nil-fibre).

Proof: transitions send roots to the specified powers; identity and composition
are checked on roots using positive divisibility, then on all polynomials and
quotients. The tower compatibility relations make the stage inclusions a cocone.
For a compatible family c_n, evaluate every root variable x_(i,n) at
c_n(sncRootCoordinate t n.val i). Each power equation vanishes because c_n is an algebra map.
Each transition equation vanishes by compatibility of the family c_n with the
transition map. Quotient evaluation therefore gives an algebra map from the
full tower. Its composite on a finite stage is c_n since they agree on roots
and coefficients. Uniqueness follows since every full-tower variable lies in
one of these finite-stage images. Positive prime-to-p orders are filtered:
1 belongs and nm is a common divisible order for n and m. -/
theorem colimit_presentation (hp : p.Prime) :
    (∀ n : TameRootOrder p,
      transition p t n n (dvd_refl n.val) = AlgHom.id R (sncRootLevel t n.val)) ∧
    (∀ (n m l : TameRootOrder p) (hnm : n.val ∣ m.val) (hml : m.val ∣ l.val),
      (transition p t m l hml).comp (transition p t n m hnm) =
        transition p t n l (dvd_trans hnm hml)) ∧
    (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
      (stageInclusion p t m).comp (transition p t n m h) = stageInclusion p t n) ∧
    ∀ (D : Type (max u v)) [CommRing D] [Algebra R D]
      (c : ∀ n : TameRootOrder p, sncRootLevel t n.val →ₐ[R] D),
      (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
        (c m).comp (transition p t n m h) = c n) →
      ∃! f : tameRootAlgebra p t →ₐ[R] D,
        ∀ n : TameRootOrder p, f.comp (stageInclusion p t n) = c n := by
  sorry

/-- Coefficient change respects the finite-stage equations.
Source: direct-images proof (3), base change of A_n
(blueprint: lem-sfb-parameter-root-integral-nil-fibre).
Proof: polynomial coefficient change sends X_i^n-C(t_i) to X_i^n-C(f(t_i)).
Each generator therefore belongs to the inverse image of the target ideal. -/
theorem stageRelations_map (n : TameRootOrder p)
    {R' : Type u} [CommRing R'] (f : R →+* R') :
    Ideal.span (Set.range (fun i : Fin r ↦
      MvPolynomial.X i ^ n.val - MvPolynomial.C (t i))) ≤
      (Ideal.span (Set.range (fun i : Fin r ↦
        MvPolynomial.X i ^ n.val - MvPolynomial.C (f (t i))))).comap
          (MvPolynomial.map f) := by
  sorry

/-- The actual coefficient-change map of finite root algebras.
Source: direct-images proof (3), applying f to coefficients and fixing the roots
(blueprint: lem-sfb-parameter-root-integral-nil-fibre). -/
def stageMap (n : TameRootOrder p) {R' : Type u} [CommRing R'] (f : R →+* R') :
    sncRootLevel t n.val →+* sncRootLevel (fun i ↦ f (t i)) n.val :=
  Ideal.quotientMap _ (MvPolynomial.map f) (stageRelations_map p t n f)

/-- The actual cartesian closed fibre of the parametrized tower projection.
Source: direct-images proof (3), B_P
(blueprint: lem-sfb-parameter-root-integral-nil-fibre). -/
abbrev fibre (P : Profinite.{u}) : Scheme.{u} :=
  pullback (qP p t P) (stratumInclusion t)

/-- The canonical factorization of the zero-root map through the cartesian fibre.
Source: direct-images proof (3), a_P, fixed by the two structural projections
(blueprint: lem-sfb-parameter-root-integral-nil-fibre). -/
def inclusion (P : Profinite.{u}) : (test (stratumScheme t) P).left ⟶ fibre p t P :=
  pullback.lift (testMap (boundary p t) P) (test (stratumScheme t) P).hom
    (test_boundary_square p t P)

/-- A named root in the coordinate ring of the actual cartesian fibre.
Source: direct-images proof (3), images of x_(i,n)
(blueprint: lem-sfb-parameter-root-integral-nil-fibre). -/
def root (P : Profinite.{u}) (i : Fin r) (n : TameRootOrder p) :
    Γ(fibre p t P, ⊤) :=
  ((pullback.fst (qP p t P) (stratumInclusion t) ≫
    (test (tower p t) P).hom).appTop).hom
      ((Scheme.ΓSpecIso (.of (tameRootAlgebra p t))).inv
        (sncFullRootCoordinate p t n i))

/-- The ideal generated by every compatible root, with no uniform exponent specified.
Source: direct-images proof (3), J_P
(blueprint: lem-sfb-parameter-root-integral-nil-fibre). -/
def rootIdeal (P : Profinite.{u}) : Ideal Γ(fibre p t P, ⊤) :=
  Ideal.span (Set.range (fun k : Fin r × TameRootOrder p ↦ root p t P k.1 k.2))

/-- Base change preserves the ideal of all compatible-root relations.
Source: direct-images proof (3), arbitrary coefficient-ring base change
(blueprint: lem-sfb-parameter-root-integral-nil-fibre).
Proof: polynomial coefficient change sends a power relation to the power relation
for f(t_i), and sends every transition relation to that same transition relation.
The inverse image of the target ideal therefore contains every generator. -/
theorem relations_map {R' : Type u} [CommRing R'] (f : R →+* R') :
    Ideal.span (tameRootRelations p t) ≤
      (Ideal.span (tameRootRelations p (fun i ↦ f (t i)))).comap (MvPolynomial.map f) := by
  sorry

/-- The actual coefficient-change homomorphism of compatible-root algebras.
Source: direct-images proof (3), fixing named roots and applying f to coefficients
(blueprint: lem-sfb-parameter-root-integral-nil-fibre). -/
def algebraMapOf {R' : Type u} [CommRing R'] (f : R →+* R') :
    tameRootAlgebra p t →+* tameRootAlgebra p (fun i ↦ f (t i)) :=
  Ideal.quotientMap _ (MvPolynomial.map f) (relations_map p t f)

/-- The original parameter ideal maps into the parameter ideal after coefficient change.
Source: direct-images proof (3), the induced map of zero loci
(blueprint: lem-sfb-parameter-root-integral-nil-fibre).
Proof: f sends each generating parameter t_i to the corresponding f(t_i).
The inverse image of the target parameter ideal contains their span. -/
theorem parameters_map {R' : Type u} [CommRing R'] (f : R →+* R') :
    Ideal.span (Set.range t) ≤
      (Ideal.span (Set.range (fun i ↦ f (t i)))).comap f := by
  sorry

/-- The canonical quotient map on stratum coordinate rings after base change.
Source: direct-images proof (3), the quotient of f
(blueprint: lem-sfb-parameter-root-integral-nil-fibre). -/
def stratumMapOf {R' : Type u} [CommRing R'] (f : R →+* R') :
    stratumRing t →+* stratumRing (fun i ↦ f (t i)) :=
  Ideal.quotientMap _ f (parameters_map t f)

/-- The actual map of root towers induced by coefficient change.
Source: direct-images proof (3), Spec of the coefficient-and-root map
(blueprint: lem-sfb-parameter-root-integral-nil-fibre). -/
def towerMap {R' : Type u} [CommRing R'] (f : R →+* R') :
    tower p (fun i ↦ f (t i)) ⟶ tower p t :=
  Spec.map (CommRingCat.ofHom (algebraMapOf p t f))

/-- The actual map of strata induced by coefficient change.
Source: direct-images proof (3), Spec of the quotient map
(blueprint: lem-sfb-parameter-root-integral-nil-fibre). -/
def stratumMap {R' : Type u} [CommRing R'] (f : R →+* R') :
    stratumScheme (fun i ↦ f (t i)) ⟶ stratumScheme t :=
  Spec.map (CommRingCat.ofHom (stratumMapOf t f))

/-- The stratum map commutes with its closed inclusion into the affine base.
Source: direct-images proof (3), base-change square
(blueprint: lem-sfb-parameter-root-integral-nil-fibre).
Proof: both contravariant composites are the quotient map after f on each base
coefficient. The quotient universal property identifies them; apply Spec. -/
theorem stratum_square {R' : Type u} [CommRing R'] (f : R →+* R') :
    stratumMap t f ≫ stratumInclusion t =
      stratumInclusion (fun i ↦ f (t i)) ≫ Spec.map (CommRingCat.ofHom f) := by
  sorry

/-- The canonical map of tower tests commutes with the map of affine bases.
Source: direct-images proof (3), ring and continuous parameter changes together
(blueprint: lem-sfb-parameter-root-integral-nil-fibre).
Proof: the profinite product map commutes with its projection. On constants the
coefficient-change map of root algebras is f. Contravariance of Spec and composition
therefore give the square for every continuous map of profinite parameters. -/
theorem test_square {R' : Type u} [CommRing R'] (f : R →+* R')
    {P P' : Profinite.{u}} (v : P' ⟶ P) :
    profiniteProductMap (towerMap p t f) v ≫ qP p t P =
      qP p (fun i ↦ f (t i)) P' ≫ Spec.map (CommRingCat.ofHom f) := by
  sorry

/-- The canonical map of cartesian fibres under a ring map and a parameter map.
Source: direct-images proof (3), induced fibre-product map
(blueprint: lem-sfb-parameter-root-integral-nil-fibre). -/
def fibreMap {R' : Type u} [CommRing R'] (f : R →+* R')
    {P P' : Profinite.{u}} (v : P' ⟶ P) :
    fibre p (fun i ↦ f (t i)) P' ⟶ fibre p t P :=
  pullback.map _ _ _ _ (profiniteProductMap (towerMap p t f) v) (stratumMap t f)
    (Spec.map (CommRingCat.ofHom f)) (test_square p t f v).symm
    (stratum_square t f).symm

/-- The canonical collapse of iterated profinite tests, with labels ordered Q times P.
It uses the product comparison of the existing finite-limit-preserving profinite functor
in schemes over Spec Z. In particular the map is fixed before invertibility is stated.
Source: direct-images proof (3), further profinite parametrization
(blueprint: lem-sfb-parameter-root-integral-nil-fibre). -/
def collapse (X : Scheme.{u}) (P Q : Profinite.{u}) :
    (test (test X P).left Q).left ⟶ (test X (Q ⨯ P)).left := by
  let F := profiniteToProEt ⋙ Scheme.ProEt.forget specZ
  let Z := (test (test X P).left Q).left
  let a : Over.mk (toSpecZ Z) ⟶ F.obj Q :=
    Over.homMk (pullback.fst _ _) (specULiftZIsTerminal.hom_ext _ _)
  let b : Over.mk (toSpecZ Z) ⟶ F.obj P :=
    Over.homMk ((test (test X P).left Q).hom ≫ pullback.fst _ _)
      (specULiftZIsTerminal.hom_ext _ _)
  exact pullback.lift
    ((Limits.prod.lift a b ≫ inv (Limits.prodComparison F Q P)).left)
    ((test (test X P).left Q).hom ≫ (test X P).hom)
    (specULiftZIsTerminal.hom_ext _ _)

/-- Simultaneous continuous reparametrization on the entire iterated test scheme.
Source: direct-images proof (3), a map Q times P' to P, together with ring base change
(blueprint: lem-sfb-parameter-root-integral-nil-fibre). -/
def familyTowerMap {R' : Type u} [CommRing R'] (f : R →+* R')
    (P P' Q : Profinite.{u}) (w : Q ⨯ P' ⟶ P) :
    (test (test (tower p (fun i ↦ f (t i))) P').left Q).left ⟶
      (test (tower p t) P).left :=
  collapse (tower p (fun i ↦ f (t i))) P' Q ≫
    profiniteProductMap (towerMap p t f) w

/-- The simultaneous parameter map respects the affine-base projection.
Source: direct-images proof (3), the structural square for Q times P' to P
(blueprint: lem-sfb-parameter-root-integral-nil-fibre).
Proof: the collapse map preserves the projection to the original scheme by its
pullback-lift definition. The product test map preserves that projection as well.
Apply test_square and associate the compositions. -/
theorem family_square {R' : Type u} [CommRing R'] (f : R →+* R')
    (P P' Q : Profinite.{u}) (w : Q ⨯ P' ⟶ P) :
    testMap (pullback.fst (qP p (fun i ↦ f (t i)) P')
        (stratumInclusion (fun i ↦ f (t i)))) Q ≫
        familyTowerMap p t f P P' Q w ≫ qP p t P =
      (test (fibre p (fun i ↦ f (t i)) P') Q).hom ≫
        pullback.snd (qP p (fun i ↦ f (t i)) P')
          (stratumInclusion (fun i ↦ f (t i))) ≫
        stratumMap t f ≫ stratumInclusion t := by
  sorry

/-- The canonical map from a whole Q-parametrized source fibre into the target fibre.
Source: direct-images proof (3), simultaneous parameter and base changes
(blueprint: lem-sfb-parameter-root-integral-nil-fibre). -/
def familyFibreMap {R' : Type u} [CommRing R'] (f : R →+* R')
    (P P' Q : Profinite.{u}) (w : Q ⨯ P' ⟶ P) :
    (test (fibre p (fun i ↦ f (t i)) P') Q).left ⟶ fibre p t P :=
  pullback.lift
    (testMap (pullback.fst (qP p (fun i ↦ f (t i)) P')
      (stratumInclusion (fun i ↦ f (t i)))) Q ≫ familyTowerMap p t f P P' Q w)
    ((test (fibre p (fun i ↦ f (t i)) P') Q).hom ≫
      pullback.snd (qP p (fun i ↦ f (t i)) P')
        (stratumInclusion (fun i ↦ f (t i))) ≫ stratumMap t f)
    (family_square p t f P P' Q w)

/-- Every finite stage is finite free with exactly its monomial basis, and each
parametrized tower projection is integral. The zero-root map is a surjective closed
immersion into the actual cartesian fibre, with exactly the stated nil kernel and
structural triangles. The ideal is only elementwise nilpotent.
Source: blueprint main-20261015, ctf-stability direct-images proof, paragraph (3),
extracted returned step 2
(blueprint: lem-sfb-parameter-root-integral-nil-fibre).

Proof: (1) Positive prime-to-p orders form a filtered divisibility system: 1 is an
order and nm is a common upper bound. Substitution x_(i,n) -> x_(i,m)^(m/n)
respects the power equations; iterated substitutions compose since the positive
orders divide one another. The existing all-root quotient imposes exactly these
transition identifications, hence presents this colimit by the polynomial and
quotient universal properties (`def-weil-pbc-category-colimit`).
(2) For R nonzero apply `lem-weil-pbc-monic-tensor-presentation` to X^n-t_i.
The maps between its finite tensor algebra and sncRootLevel send each root to its
namesake; both composites fix every root and coefficient, hence are identities.
Transport the tensor power basis to the displayed monomials. For the zero ring,
the zero free module on the same finite index set gives the basis. Finite indexing
gives Module.Finite and Module.Free, including r=0.
(3) By `lem-weil-pbc-fibre-product-affine-spectra`, tower[P] has coordinate ring
A tensor_Z LC(P,Z). Compactness makes each locally constant function finite-image.
Finitely many such functions admit a common finite clopen partition with orthogonal
characteristic idempotents summing to 1. Write an element as a finite sum of pure
tensors. `lem-weil-pbc-filtered-colimit-algebras-elementwise` lifts all its A entries
to a common finite stage. The finite product of that stage over the partition maps
unitally to the tensor algebra and contains the chosen element in its image.
`lem-weil-pbc-finite-algebra-is-integral` gives a monic equation, hence the same
equation in the target. `lem-weil-pbc-spec-integral-ring-map-integral` proves
integrality of qP. For empty P the zero ring satisfies the equation X=0.
(4) The fibre has coordinate ring E=(A tensor_Z LC(P,Z)) tensor_R R/(t_i).
The map of inclusion is exactly evaluation of every root at zero. It has the
section b tensor f -> (1 tensor f) tensor b, hence is a quotient. Its two
projection equations are those of the defining pullback lift.
(5) Let J be the span of all root images. In E/J every finite-stage polynomial
equals its constant term modulo the parameter ideal. Every colimit element comes
from a stage by the elementwise-colimit lemma. Expanding pure tensors therefore
gives y congruent to sigma(epsilon(y)) modulo J. Thus ker(epsilon)=J exactly;
no pre-existing nilpotent of R/(t_i) is additionally killed.
(6) Every root u_(i,n) has u^n=t_i=0 in E. An element of J involves finitely
many such generators u_j with exponents n_j. Its power with exponent
1+sum_j(n_j-1) vanishes by expansion and the pigeonhole principle; the empty sum
uses exponent 1. Every prime contains all roots, so the quotient is surjective
on spectra. This proves the closed immersion and surjectivity, without a common
nilpotence exponent for J. The fibre is never identified with the zero-root
quotient as a scheme. These arguments include the zero ring, r=0 and empty P. -/
theorem integral_nil_fibre (hp : p.Prime) :
    (∀ n : TameRootOrder p,
      (∃ b : Module.Basis (Fin r → Fin n.val) R (sncRootLevel t n.val),
        ∀ e : Fin r → Fin n.val, b e = ∏ i : Fin r, sncRootCoordinate t n.val i ^ (e i).val) ∧
      Module.Free R (sncRootLevel t n.val) ∧ Module.Finite R (sncRootLevel t n.val)) ∧
    ∀ P : Profinite.{u},
      IsIntegralHom (qP p t P) ∧
      IsClosedImmersion (stratumInclusion t) ∧
      IsClosedImmersion (inclusion p t P) ∧ Surjective (inclusion p t P) ∧
      Function.Surjective ((inclusion p t P).appTop).hom ∧
      RingHom.ker ((inclusion p t P).appTop).hom = rootIdeal p t P ∧
      (∀ y : Γ(fibre p t P, ⊤), y ∈ rootIdeal p t P → IsNilpotent y) ∧
      inclusion p t P ≫ pullback.fst (qP p t P) (stratumInclusion t) =
        testMap (boundary p t) P ∧
      inclusion p t P ≫ pullback.snd (qP p t P) (stratumInclusion t) =
        (test (stratumScheme t) P).hom := by
  sorry

/-- The ring-base-change and continuous-parameter descriptions commute on the actual
schemes, coordinate maps and root ideals. In particular arbitrary base change is
cartesian, not merely a map into an unrelated tower.
Source: direct-images proof (3), the final base-change and parameter-map clause
(blueprint: lem-sfb-parameter-root-integral-nil-fibre).

Proof: the root presentation commutes with tensor base change by the polynomial,
quotient and tensor universal properties, fixing coefficients and all named roots
(`lem-sfb-root-tower-profinite-base-change`). The parameter quotient has the same
property. This proves the two cartesian squares. Evaluation at zero before or
after coefficient change agrees on every coefficient and root, so it agrees on
the quotient. Pulling a locally constant function back along v replaces f by
f composed with v and fixes every root. Thus the zero-root square commutes.
The two projections defining the fibre map identify both composites with that
same square, proving the inclusion equality. Pulling back a root global section
sends it to the corresponding root. The ideal-map-of-span formula then gives
equality of the generated ideals, even when the coefficient map is not flat.
The identity and composite rules follow on polynomial coefficients and roots,
then on the quotient and on pullback projections. No nonemptiness is used. -/
theorem baseChange_naturality (hp : p.Prime)
    {R' : Type u} [CommRing R'] (f : R →+* R') :
    IsPullback (towerMap p t f) (parameterRootProjection p (fun i ↦ f (t i)))
      (parameterRootProjection p t) (Spec.map (CommRingCat.ofHom f)) ∧
    IsPullback (stratumMap t f) (stratumInclusion (fun i ↦ f (t i)))
      (stratumInclusion t) (Spec.map (CommRingCat.ofHom f)) ∧
    (stratumMap t f ≫ boundary p t =
      boundary p (fun i ↦ f (t i)) ≫ towerMap p t f) ∧
    ∀ (P P' : Profinite.{u}) (v : P' ⟶ P),
      inclusion p (fun i ↦ f (t i)) P' ≫ fibreMap p t f v =
        profiniteProductMap (stratumMap t f) v ≫ inclusion p t P ∧
      (∀ (i : Fin r) (n : TameRootOrder p),
        ((fibreMap p t f v).appTop).hom (root p t P i n) =
          root p (fun i ↦ f (t i)) P' i n) ∧
      Ideal.map ((fibreMap p t f v).appTop).hom (rootIdeal p t P) =
        rootIdeal p (fun i ↦ f (t i)) P' := by
  sorry

/-- Finite-stage algebras, their monomial generators, transitions and colimit maps
commute with arbitrary coefficient-ring base change.
Source: direct-images proof (3), base-change compatibility of the finite presentations
(blueprint: lem-sfb-parameter-root-integral-nil-fibre).

Proof: tensoring the polynomial quotient with R' gives the same polynomial
quotient with coefficients f(t_i), by the polynomial and tensor universal
properties. The resulting ring map is stageMap, since both maps agree on every
coefficient and root. This proves the cartesian square. Its value on a root is
that root, so its value on each basis monomial is the corresponding basis
monomial. Both paths through a transition send a root to the same power of the
same target root. Both paths into the full tower also fix named roots and send
coefficients by f. Quotient extensionality proves the remaining equalities. -/
theorem finiteStage_baseChange (hp : p.Prime)
    {R' : Type u} [CommRing R'] (f : R →+* R') :
    (∀ n : TameRootOrder p,
      IsPullback (Spec.map (CommRingCat.ofHom (stageMap p t n f)))
        (Spec.map (CommRingCat.ofHom
          (algebraMap R' (sncRootLevel (fun i ↦ f (t i)) n.val))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (sncRootLevel t n.val))))
        (Spec.map (CommRingCat.ofHom f)) ∧
      (∀ i : Fin r, stageMap p t n f (sncRootCoordinate t n.val i) =
        sncRootCoordinate (fun i ↦ f (t i)) n.val i) ∧
      (algebraMapOf p t f).comp (stageInclusion p t n).toRingHom =
        (stageInclusion p (fun i ↦ f (t i)) n).toRingHom.comp (stageMap p t n f)) ∧
    ∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
      (stageMap p t m f).comp (transition p t n m h).toRingHom =
        (transition p (fun i ↦ f (t i)) n m h).toRingHom.comp (stageMap p t n f) := by
  sorry

/-- Further profinite parametrization preserves the complete quotient and its nil
ideal, and simultaneous Q times P' to P maps commute on the whole schemes.
Source: direct-images proof (3), further profinite parametrization and families
(blueprint: lem-sfb-parameter-root-integral-nil-fibre).

Proof: the finite-limit-preserving profinite functor identifies the product of its
Q and P objects with its Q times P object in schemes over Spec Z. The canonical
collapse is the resulting pullback comparison, so is an isomorphism, preserving
projection to the original scheme. Tensoring the zero-root quotient with LC(Q,Z)
preserves its quotient and sends its kernel to the extended root ideal. Each
generator remains nilpotent; the finite-sum exponent from integral_nil_fibre
proves elementwise nilpotence there. The prime-ideal argument again gives the
surjective closed immersion. For w:Q times P' -> P, coefficient functions become
f composed with w, and the named roots and zero-root substitutions remain fixed.
The actual collapse and fibre-product lifts therefore give the displayed equality,
by checking both projections. The same computation sends each generating root
to its further pullback and proves the ideal equality. This includes arbitrary
ring base change at the same time, and includes empty Q or P'. -/
theorem profinite_naturality (hp : p.Prime) :
    (∀ P Q : Profinite.{u},
      IsIso (collapse (tower p t) P Q) ∧
      IsIso (collapse (stratumScheme t) P Q) ∧
      collapse (tower p t) P Q ≫ (test (tower p t) (Q ⨯ P)).hom =
        (test (test (tower p t) P).left Q).hom ≫ (test (tower p t) P).hom ∧
      IsClosedImmersion (testMap (inclusion p t P) Q) ∧
      Surjective (testMap (inclusion p t P) Q) ∧
      RingHom.ker ((testMap (inclusion p t P) Q).appTop).hom =
        Ideal.map ((test (fibre p t P) Q).hom.appTop).hom (rootIdeal p t P) ∧
      (∀ y : Γ((test (fibre p t P) Q).left, ⊤),
        y ∈ Ideal.map ((test (fibre p t P) Q).hom.appTop).hom (rootIdeal p t P) →
          IsNilpotent y)) ∧
    ∀ (R' : Type u) [CommRing R'] (f : R →+* R')
      (P P' Q : Profinite.{u}) (w : Q ⨯ P' ⟶ P),
      testMap (inclusion p (fun i ↦ f (t i)) P') Q ≫ familyFibreMap p t f P P' Q w =
        collapse (stratumScheme (fun i ↦ f (t i))) P' Q ≫
          profiniteProductMap (stratumMap t f) w ≫ inclusion p t P ∧
      Ideal.map ((familyFibreMap p t f P P' Q w).appTop).hom (rootIdeal p t P) =
        Ideal.map ((test (fibre p (fun i ↦ f (t i)) P') Q).hom.appTop).hom
          (rootIdeal p (fun i ↦ f (t i)) P') := by
  sorry

end ParameterRootNilFibre
end AlgebraicGeometry.ProEtale
