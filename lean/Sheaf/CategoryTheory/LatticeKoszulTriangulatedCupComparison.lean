/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.CondensedActionModule
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.LatticeAlgebraDerivedCup
public import Sheaf.CategoryTheory.LatticeRestrictionCupComparison
public import Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Mathlib.Algebra.Homology.TotalComplexShift
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Action.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Sheaf.CategoryTheory.DerivedTensorRightExact
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

import Sheaf.Algebra.Homology.BoundedBelowTotalComparison
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.ModelCategory.Injective
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Sheaf.AlgebraicTopology.IntegralLatticeCubicalContraction
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
import Sheaf.SixFunctors.ResolvingDerivedAdjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.AlgebraicTopology.IntegralCubicalChainDiagonal
import Sheaf.CategoryTheory.InternalActionSitePresentation
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk

/-! # Triangulated lattice Koszul comparison and twisted cup pairing

Source: main-20261015 direct-image proof, paragraph (3), agent expansion of the
ordinary internal discrete-lattice calculation
(blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison).

## Main definitions and statements

* `total`: the Koszul-first signed total on actual bounded-below complexes.
* `TriangulatedModel`: its descent and shift-compatible derived comparison.
* `CupComparison`: the twisted pairing, K-flat model, and canonical cup/unit equations.
* `lattice_koszul_triangulated_cup_comparison`: the simultaneous comparison theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace Profinite.DiscreteLattice
namespace TriangulatedCup
open DerivedCup

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ)

/-- The total coproducts exist in the original internal-module category.
Source: paragraph (3) (blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison). -/
instance moduleHasTotal (K : HomologicalComplex₂ (Modules R) (.up ℤ) (.up ℤ)) :
    K.HasTotal (.up ℤ) := fun _ ↦ inferInstance

/-- The finite Koszul functor is additive in its original coordinates.
Source: paragraph (3), proof step 1
(blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison).
Proof: its map matrix is diagonal with the original coefficient map on every diagonal
entry. Finite biproduct extensionality therefore proves preservation of sums. -/
@[instance] theorem koszulAdditive (K : KoszulModel R r) : K.functor.Additive := by
  sorry

/-- First put Koszul degree on the outside, then use the standard signed total.
Its differential is d_K + (-1)^a d_P in Koszul degree a.
Source: paragraph (3), proof steps 1--3
(blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison). -/
def total (K : KoszulModel R r) :
    CochainComplex (Equivariant R r) ℤ ⥤ CochainComplex (Modules R) ℤ :=
  K.functor.mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex₂.flipFunctor (Modules R) (.up ℤ) (.up ℤ) ⋙
      HomologicalComplex₂.totalFunctor (Modules R) (.up ℤ) (.up ℤ) (.up ℤ)

/-- A finite nonnegative Koszul strip preserves a lower bound on complex terms.
Source: paragraph (3), proof steps 1 and 2
(blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison).
Proof: Koszul coordinates vanish outside 0 through r. In total degree n below the
input bound, every surviving summand has input degree n-a below that bound and is zero. -/
theorem totalBoundedBelow (K : KoszulModel R r) (P : CochainComplex.Plus (Equivariant R r)) :
    CochainComplex.plus (Modules R) ((total R r K).obj P.obj) := by
  sorry

/-- The actual signed total restricted to bounded-below complexes.
Source: paragraph (3) (blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison). -/
def totalPlus (K : KoszulModel R r) :
    CochainComplex.Plus (Equivariant R r) ⥤ CochainComplex.Plus (Modules R) :=
  ObjectProperty.lift _ (CochainComplex.Plus.ι _ ⋙ total R r K)
    (totalBoundedBelow R r K)

/-- The actual Koszul-first bicomplex underlying the signed total.
Source: paragraph (3) (blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison). -/
def bicomplex (K : KoszulModel R r) (P : CochainComplex (Equivariant R r) ℤ) :=
  HomologicalComplex₂.flip ((K.functor.mapHomologicalComplex (.up ℤ)).obj P)

/-- The canonical total shift is degreewise functoriality followed by Mathlib's
second-index total shift. Its Koszul-degree a component has sign (-1)^(a*n).
Source: paragraph (3), proof steps 2 and 3
(blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison). -/
def totalShiftIsoApp (K : KoszulModel R r)
    (P : CochainComplex (Equivariant R r) ℤ) (n : ℤ) :
    (total R r K).obj (P⟦n⟧) ≅ ((total R r K).obj P)⟦n⟧ :=
  (HomologicalComplex₂.totalFunctor (Modules R) (.up ℤ) (.up ℤ) (.up ℤ)).mapIso
    ((HomologicalComplex₂.flipFunctor (Modules R) (.up ℤ) (.up ℤ)).mapIso
      ((K.functor.mapCochainComplexShiftIso n).app P)) ≪≫
    (bicomplex R r K P).totalShift₂Iso n

/-- The canonical total shift is natural in the original complex.
Source: paragraph (3), proof step 3
(blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison).
Proof: apply the flip and total functors to naturality of mapCochainComplexShiftIso,
then use totalShift₂Iso_hom_naturality. Both are the same signed map on each summand. -/
theorem totalShiftNaturality (K : KoszulModel R r) (n : ℤ)
    {P Q : CochainComplex (Equivariant R r) ℤ} (f : P ⟶ Q) :
    (total R r K).map (f⟦n⟧') ≫ (totalShiftIsoApp R r K Q n).hom =
      (totalShiftIsoApp R r K P n).hom ≫ ((total R r K).map f)⟦n⟧' := by
  sorry

/-- The canonical natural shift comparison for the signed Koszul total.
Source: paragraph (3), proof step 3
(blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison). -/
def totalShiftIso (K : KoszulModel R r) (n : ℤ) :
    shiftFunctor _ n ⋙ total R r K ≅ total R r K ⋙ shiftFunctor _ n :=
  NatIso.ofComponents (fun P ↦ totalShiftIsoApp R r K P n)
    (fun f ↦ totalShiftNaturality R r K n f)

/-- The signed comparisons satisfy the zero and addition shift laws.
Source: paragraph (3), proof step 3
(blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison).
Proof: test on each Koszul/input summand. At zero both component maps are identities;
for successive shifts the signs multiply as (-1)^(a*n) (-1)^(a*m) = (-1)^(a*(n+m)).
The index reassociations are the canonical complex shift reassociations on both sides. -/
theorem totalShiftCoherence (K : KoszulModel R r) :
    totalShiftIso R r K 0 = Functor.CommShift.isoZero (total R r K) ℤ ∧
      ∀ n m : ℤ, totalShiftIso R r K (n + m) =
        Functor.CommShift.isoAdd (totalShiftIso R r K n) (totalShiftIso R r K m) := by
  sorry

/-- The total has its constructed signed shift structure, independently of derived invariants.
Source: paragraph (3), proof step 3
(blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison). -/
instance totalCommShift (K : KoszulModel R r) : (total R r K).CommShift ℤ where
  commShiftIso := totalShiftIso R r K
  commShiftIso_zero := (totalShiftCoherence R r K).1
  commShiftIso_add := (totalShiftCoherence R r K).2

/-- The augmentation to the total is the original invariant inclusion in Koszul degree zero.
Source: paragraph (3), proof steps 4--6
(blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison). -/
def totalInclusionF (K : KoszulModel R r) (P : CochainComplex (Equivariant R r) ℤ) (n : ℤ) :
    ((invariants R r).obj (P.X n)) ⟶ ((total R r K).obj P).X n :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 ((invariants R r).obj (P.X n))).inv ≫
    (K.augmentation.app (P.X n)).f 0 ≫
      (bicomplex R r K P).ιTotal (.up ℤ) 0 n n (zero_add n)

/-- The degree-zero invariant inclusion commutes with both total differentials.
Source: paragraph (3), proof steps 4--6
(blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison).
Proof: the horizontal differential kills invariant sections. In Koszul degree zero
there is no vertical sign. Naturality of the original augmentation identifies the
vertical composites, so the displayed components form a chain map. -/
theorem totalInclusionComm (K : KoszulModel R r) (P : CochainComplex (Equivariant R r) ℤ)
    (a b : ℤ) :
    (((invariants R r).mapHomologicalComplex (.up ℤ)).obj P).d a b ≫
        totalInclusionF R r K P b =
      totalInclusionF R r K P a ≫ ((total R r K).obj P).d a b := by
  sorry

/-- The chain map from the actual invariant complex to the signed total.
Source: paragraph (3) (blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison). -/
def totalInclusion (K : KoszulModel R r) (P : CochainComplex (Equivariant R r) ℤ) :
    ((invariants R r).mapHomologicalComplex (.up ℤ)).obj P ⟶ (total R r K).obj P where
  f := totalInclusionF R r K P
  comm' := fun i j _ ↦ (totalInclusionComm R r K P i j).symm

/-- A module as an actual bounded-below single complex.
Source: paragraph (3) (blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison). -/
def moduleComplex (P : Equivariant R r) : CochainComplex.Plus (Equivariant R r) :=
  ⟨(HomologicalComplex.single _ (.up ℤ) 0).obj P, ⟨0, inferInstance⟩⟩

/-- The bounded-below localization has the shift induced by its quotient and Qh.
Source: paragraph (3), proof step 3
(blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison). -/
instance plusQCommShift :
    (DerivedCategory.Plus.Q (C := Equivariant R r)).CommShift ℤ := by
  unfold DerivedCategory.Plus.Q HomotopyCategory.Plus.quotient
  infer_instance

attribute [irreducible] totalShiftIsoApp totalShiftIso totalCommShift plusQCommShift

/-- A triangulated descent of the actual signed total, with a shift-compatible comparison.
The single-complex identification is fixed on the only nonzero input row, so it does
not allow replacing the module-level Koszul model by a different complex.
Source: paragraph (3), proof steps 1--6
(blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison). -/
structure TriangulatedModel (K : KoszulModel R r) where
  functor : DerivedCategory.Plus (Equivariant R r) ⥤ DerivedCategory.Plus (Modules R)
  [commShift : functor.CommShift ℤ]
  triangulated : functor.IsTriangulated
  factor : CochainComplex.Plus.ι _ ⋙ total R r K ⋙ DerivedCategory.Q.{u + 2} ≅
    DerivedCategory.Plus.Q ⋙ functor ⋙ DerivedCategory.Plus.ι
  factorShiftCompatibility : NatTrans.CommShift factor.hom ℤ
  iso : functor ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ derivedInvariants R r
  shiftCompatibility : NatTrans.CommShift iso.hom ℤ
  singleIso : ∀ P : Equivariant R r,
    (total R r K).obj (moduleComplex R r P).obj ≅ K.functor.obj P
  singleCoordinates : ∀ (P : Equivariant R r) (a : ℤ),
    (bicomplex R r K (moduleComplex R r P).obj).ιTotal (.up ℤ) a 0 a (add_zero a) ≫
      (singleIso P).hom.f a =
    (K.functor.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).hom).f a

/-- The comparison on an actual complex, transported from D-plus to its Q representative.
Source: paragraph (3) (blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison). -/
def onComplex {K : KoszulModel R r} (M : TriangulatedModel R r K)
    (P : CochainComplex.Plus (Equivariant R r)) :
    DerivedCategory.Q.{u + 2}.obj ((total R r K).obj P.obj) ⟶
      (derivedInvariants R r).obj (DerivedCategory.Q.{u + 2}.obj P.obj) :=
  M.factor.hom.app P ≫ M.iso.hom.app (DerivedCategory.Plus.Q.obj P) ≫
    (derivedInvariants R r).map ((DerivedCategory.quotientCompQhIso _).hom.app P.obj)

/-- The same comparison extends the module comparison, preserves invariant inclusions,
and identifies the actual connecting arrows of the Koszul short exact sequences.
Source: paragraph (3), proof steps 4--6
(blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison). -/
structure ComparisonProperties (K : KoszulModel R r) (M : TriangulatedModel R r K)
    (c : Comparison R r K) : Prop where
  normalization : ∀ P : CochainComplex.Plus (Equivariant R r),
    DerivedCategory.Q.{u + 2}.map (totalInclusion R r K P.obj) ≫ onComplex R r M P =
      derivedUnit R r P.obj
  extendsModules : ∀ P : Equivariant R r,
    DerivedCategory.Q.{u + 2}.map (M.singleIso P).inv ≫ onComplex R r M (moduleComplex R r P) =
      c.iso.hom.app P
  connecting : ∀ (S : ShortComplex (Equivariant R r)) (_ : S.ShortExact),
    ∃ (hK : (S.map K.functor).ShortExact)
      (hS : (S.map (HomologicalComplex.single (Equivariant R r) (.up ℤ) 0)).ShortExact),
      DerivedCategory.triangleOfSESδ hK ≫
        (shiftFunctor (DerivedCategory.{u + 2} (Modules R)) (1 : ℤ)).map (c.iso.hom.app S.X₁) =
      c.iso.hom.app S.X₃ ≫ (derivedInvariants R r).map (DerivedCategory.triangleOfSESδ hS) ≫
        ((derivedInvariants R r).commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor.{u + 2} _ 0).obj S.X₁)

/-- Twisted chain multiplication, its exact subset matrix, K-flatness, and the derived
cup and unit equations for this same natural module comparison. The matrix formulation
is the stated sum over ordered disjoint partitions, tested on every input summand.
Source: paragraph (3), proof steps 7--14
(blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison). -/
structure CupComparison (K : KoszulModel R r) (c : Comparison R r K)
    (B : DerivedCup.Algebra R r) where
  kflat : ∀ X : CochainComplex (Modules R) ℤ,
    X.Acyclic → (K.functor.obj B.X ⊗ X).Acyclic
  star : K.functor.obj B.X ⊗ K.functor.obj B.X ⟶ K.functor.obj B.X
  coordinates : ∀ (p q : ℤ) (A : Subsets r p) (C : Subsets r q)
    (I : Subsets r (p + q)),
    ((biproduct.ι _ A ≫ (K.coordinates B.X p).inv) ⊗ₘ
        (biproduct.ι _ C ≫ (K.coordinates B.X q).inv)) ≫
      HomologicalComplex.ιTensorObj _ _ p q (p + q) rfl ≫ star.f (p + q) ≫
      (K.coordinates B.X (p + q)).hom ≫ biproduct.π _ I =
    if Disjoint A.val C.val ∧ A.val ∪ C.val = I.val then
      ((-1 : ℤ) ^ ((A.val.product C.val).filter (fun ac ↦ ac.2 < ac.1)).card) •
        ((𝟙 B.X.V ⊗ₘ B.X.ρ (∏ i ∈ A.val, generator i)) ≫
          (MonObj.mul (X := B.X)).hom)
    else 0
  unit : (HomologicalComplex.single (Modules R) (.up ℤ) 0).obj (𝟙_ (Modules R)) ⟶
    K.functor.obj B.X
  unitCoordinates : ∀ I : Subsets r 0,
    unit.f 0 ≫ (K.coordinates B.X 0).hom ≫ biproduct.π _ I =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (Modules R))).hom ≫
        (MonObj.one (X := B.X)).hom
  tensorModel : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q.{u + 2}
    (K.functor.obj B.X) (K.functor.obj B.X))
  cupEquation : Functor.LaxMonoidal.μ DerivedCategory.Q.{u + 2}
      (K.functor.obj B.X) (K.functor.obj B.X) ≫ DerivedCategory.Q.{u + 2}.map star ≫
        c.iso.hom.app B.X =
    (c.iso.hom.app B.X ⊗ₘ c.iso.hom.app B.X) ≫ DerivedCup.cup R r B
  unitEquation : DerivedCategory.Q.{u + 2}.map unit ≫ c.iso.hom.app B.X =
    DerivedCup.cupUnit R r B

/-- At rank zero the total and invariants are the underlying complex, and the comparison
is the identity under precisely those identifications. This includes all bounded-below
complexes, rather than only modules in degree zero.
Source: paragraph (3), proof steps 6 and 14
(blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison). -/
def IsRankZero (K : KoszulModel R 0) (M : TriangulatedModel R 0 K) : Prop :=
  ∀ P : CochainComplex.Plus (Equivariant R 0),
    ∃ (e : ((invariants R 0).mapHomologicalComplex (.up ℤ)).obj P.obj ≅
        ((Action.forget (Modules R) (Group 0)).mapHomologicalComplex (.up ℤ)).obj P.obj)
      (k : (total R 0 K).obj P.obj ≅
        ((Action.forget (Modules R) (Group 0)).mapHomologicalComplex (.up ℤ)).obj P.obj),
      (∀ n : ℤ, e.hom.f n = limit.π
        ((Action.functorCategoryEquivalence (Modules R) (Group 0)).functor.obj (P.obj.X n))
          PUnit.unit) ∧
      (∀ n : ℤ,
        (bicomplex R 0 K P.obj).ιTotal (.up ℤ) 0 n n (zero_add n) ≫ k.hom.f n =
          (K.coordinates (P.obj.X n) 0).hom ≫ biproduct.π _ ⟨∅, rfl⟩) ∧
      onComplex R 0 M P = DerivedCategory.Q.{u + 2}.map k.hom ≫
        DerivedCategory.Q.{u + 2}.map e.inv ≫ derivedUnit R 0 P.obj

/-- A simultaneous triangulated Koszul comparison with the canonical twisted cup pairing.
Coefficients are arbitrary commutative condensed rings on the small coherent profinite
site, in the original universe convention. Only the algebra B is required to be flat.
The same c extends to all bounded-below complexes and satisfies all cup equations.

Source: main-20261015 direct-image stability proof, paragraph (3), agent-formulated
ordinary internal lattice input (blueprint: lem-sfb-lattice-koszul-triangulated-cup-comparison).

Proof, following the fourteen DAG steps:
1. The action-site description gives Grothendieck abelian categories and exact forgetting.
Each Koszul degree is a finite biproduct of forgetting, hence exact; natural differentials
and the displayed total convention give the functor on complexes.
2. Multiply a homotopy in Koszul degree a by (-1)^a. Horizontal terms cancel and vertical
terms give the original homotopy equation. Finite-strip column comparison proves that
quasi-isomorphisms between bounded-below complexes remain quasi-isomorphisms.
3. The shift comparison multiplies degree a by (-1)^a. For Cone(f), use identity on KQ
and (-1)^a on KP[1]; the off-diagonal f and both differentials then have the prescribed
cone signs. This preserves the cone triangle, including its negative projection.
4. Choose monomorphic bounded-below injective resolutions P -> J. For each injective
module, the normalized lattice comparison makes the invariant inclusion a quasi-isomorphism.
The row total comparison gives b_J : Gamma(J) -> K(J). Set lambda_P = Q(b_J)^(-1) Q(Ks).
5. Lift maps along those monomorphic resolutions. Uniqueness up to homotopy and step 2
prove naturality and independence. Cone comparisons commute with b_J and its degree-zero
inclusion, so lambda is triangulated and identifies the actual SES connecting arrows.
6. Both inclusions of invariant sections into K(J) agree. This gives the original
invariant normalization and a simultaneous module comparison. At rank zero b_J is the
identity, so lambda is the identity on all bounded-below complexes.
7. Internalize the integral cubical contraction in the augmented lattice resolution L.
Tensoring the contraction gives L tensor X -> X as a quasi-isomorphism and proves L K-flat.
8. For x in Koszul degree a and input degree b, evaluation on [v,I] is
(-1)^(ab) (-1)^(a(a+1)/2) T^v x_I. These signs identify the Hom differential with the
stated total differential; translation gives equivariance and invariants give the augmentation.
9. The normalized resolving derived adjunction identifies the evaluation roof with the
derived counit after trivial inflation of lambda, first on injectives, then on P by naturality.
10. Flat B gives finite-sum flat Koszul terms. Transport the bounded-flat K-flat criterion
through the internal/section tensor equivalence. The same argument works equivariantly.
11. Internalize the integral cubical chain diagonal. The identity
(T_i-1)(x T_A y) = (T_i-1)x T_(A union {i}) y + x T_A (T_i-1)y
and the ordered partition signs prove the twisted Leibniz equation, hence the chain pairing.
12. Compare evaluation after star with multiplication after the diagonal. On an ordered
partition (A,C), the tensor interchange contributes (-1)^(pq), while the evaluation signs
satisfy c_(p+q) = (-1)^(pq)c_p c_q. Both maps therefore agree on each summand; the counit
identity for the diagonal identifies their augmentation roofs.
13. The small action-site tensor is the balanced-pure-tensor diagonal tensor. Its closedness
and functorial flat resolutions give the canonical derived tensor. Exact trivial inflation
has the normalized strong derived tensor comparison. Transpose the step-12 equality through
the invariant-inclusion derived adjunction to obtain the cup equation. Evaluation of 1_B
is augmentation followed by the algebra unit, proving the unit equation. For trivial B=R
this is the same tensor-of-counits cup as in the recorded restriction calculus.
Explicitly, constant sections identify ordinary lattice actions with condensed discrete
actions; extend back by gluing along the finite clopen fibres of each section. This is
an exact equivalence on the same underlying modules. The invariant inclusions pin the
underived comparison, and computation units on every complex pin its derived comparison.
The exact identity coefficient functor supplies the localization-universe transport.
Its tensorator is pinned on flat K-flat representatives and its unit on R[0]. Taking
mates of the same tensor of counits gives Compatible's binary and unit equations.
14. At r=0 only the empty subset occurs and every map is identity or multiplication.
At r=1 the two mixed products are xy and xT_1(y); their Leibniz rule fixes the twist.
No division occurs, so zero rings, zero modules and characteristic two are all included. -/
theorem lattice_koszul_triangulated_cup_comparison :
    ∃ (K : ∀ r : ℕ, KoszulModel R r)
      (M : ∀ r : ℕ, TriangulatedModel R r (K r))
      (c : ∀ r : ℕ, Comparison R r (K r)),
      (∀ r : ℕ, ComparisonProperties R r (K r) (M r) (c r)) ∧
      IsRankZero R (K 0) (M 0) ∧
      (∀ r : ℕ, ∃ E : RestrictionCup.Bridge R r, RestrictionCup.Compatible R r E) ∧
      ∀ (r : ℕ) (B : DerivedCup.Algebra R r), IsCommMonObj B.X → ObjectProperty.flat B.X.V →
        Nonempty (CupComparison R r (K r) (c r) B) := by
  sorry

end TriangulatedCup
end Profinite.DiscreteLattice
