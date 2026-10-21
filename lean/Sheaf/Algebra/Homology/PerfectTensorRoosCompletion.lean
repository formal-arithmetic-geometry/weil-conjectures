/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Homology.AdicShortComplexCohomologyML
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.StrictRoosAdditiveComparison
public import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionDefs
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import Sheaf.Algebra.Homology.KFlatScalarTowerRealization
import Sheaf.Algebra.Homology.ExactProductsRoosComparison
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import Sheaf.CategoryTheory.CompactSupportRoosCofinality
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.RingTheory.Flat.Basic
import Sheaf.Algebra.Homology.SurjectiveModuleComplexTowerLimit

/-! # Perfect tensor quotient coaugmentation

Source: Stacks Project, Tag 0941 (lemma-derived-limit-is-ok), and Tag 031B;
the finite-retract and quotient-coordinate proof in the DAG.
(blueprint: lem-sf-perfect-tensor-roos-completion).

The published Roos coordinates are (y,x). The coordinates of the node are
(x,-y); thus their differential is (dx,(1-t)x-dy). In particular the normalized
augmentation has the prescribed quotient coordinate and zero shifted coordinate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.StrictTowerArithmetic
open scoped TensorProduct ChangeOfRings

namespace CochainComplex.PerfectTensorRoos

variable {R : Type u} [CommRing R]

/-- The quotient functors form the strict positive-power tower, with level n meaning n+1.
Source: Tag 0941, quotient tower (blueprint: lem-sf-perfect-tensor-roos-completion). -/
def towerFunctor (I : Ideal R) : ModuleCat.{u} R ⥤ (ℕᵒᵖ ⥤ ModuleCat.{u} R) :=
  (Functor.ofOpSequence (X := fun n : ℕ ↦ AdicCohomology.quotient I (n + 1))
    (fun n ↦ AdicCohomology.transition I (Nat.le_succ (n + 1)))).flip

/-- The quotient tower functor is additive.
Source: Tag 0941 (blueprint: lem-sf-perfect-tensor-roos-completion).
Proof: evaluate at every level and use additivity of the ordinary quotient functor. -/
theorem towerFunctor_additive (I : Ideal R) : (towerFunctor I).Additive := by
  sorry

attribute [instance] towerFunctor_additive

/-- The strict quotient tower of a cochain complex, with the original R-action retained.
Source: Tag 0941 (blueprint: lem-sf-perfect-tensor-roos-completion). -/
def tower (I : Ideal R) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ ModuleCat.{u} R) ℤ :=
  (towerFunctor I).mapHomologicalComplex (.up ℤ)

/-- The actual quotient projection at a positive level.
Source: Tag 0941 (blueprint: lem-sf-perfect-tensor-roos-completion). -/
def quotient (I : Ideal R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    K ⟶ ((tower I).obj K).asFunctor.obj (op n) :=
  (NatTrans.mapHomologicalComplex (AdicCohomology.projection I (n + 1)) (.up ℤ)).app K

/-- The quotient projections are compatible with the strict transitions.
Source: Tag 0941 (blueprint: lem-sf-perfect-tensor-roos-completion).
Proof: on the class of x both composites are its class modulo I^(n+1). -/
theorem quotient_compatible (I : Ideal R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℕ) :
    quotient I K (n + 1) ≫ ((tower I).obj K).asFunctor.map
      (homOfLE (Nat.le_succ n)).op = quotient I K n := by
  sorry

/-- The coaugmentation with actual quotient projections and zero shifted coordinate.
Source: Tag 0941 (blueprint: lem-sf-perfect-tensor-roos-completion). -/
def augmentation (I : Ideal R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    K ⟶ roosF.obj ((tower I).obj K) :=
  roosAugment (quotient I K) (quotient_compatible I K)

/-- The completion functor on complexes, before localization.
Source: Tag 0941 (blueprint: lem-sf-perfect-tensor-roos-completion). -/
def completion (I : Ideal R) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  tower I ⋙ roosF

/-- Scalar extension on cochain complexes; Mathlib uses the equivalent order S tensor P.
Source: quotient/scalar formulas, Tag 0941
(blueprint: lem-sf-perfect-tensor-roos-completion). -/
def extend {S : Type u} [CommRing S] (f : R →+* S) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} S) ℤ :=
  (ModuleCat.extendScalars.{u} f).mapHomologicalComplex (.up ℤ)

/-- The actual quotient tensor over R/I^(n+1), with scalars restricted back to R.
Source: quotient/scalar formulas, Tag 0941
(blueprint: lem-sf-perfect-tensor-roos-completion). -/
def quotientTensor (I : Ideal R) (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :=
  ((ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex
    (.up ℤ)).obj
      ((extend (Ideal.Quotient.mk (I ^ (n + 1)))).obj P ⊗
        (extend (Ideal.Quotient.mk (I ^ (n + 1)))).obj Q)

/-- The finite projective model condition, expressed using the recorded perfectness data.
Source: def-pc-perfect-ring-complex (blueprint: lem-sf-perfect-tensor-roos-completion). -/
def FiniteProjective (P : CochainComplex (ModuleCat.{u} R) ℤ) : Prop :=
  (∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b) ∧
    ∀ i : ℤ, Module.Projective R (P.X i) ∧ Module.Finite R (P.X i)

/-- The normalized completion diagram for any cochain map. This is also the form used
for associators, Koszul symmetry, unitors and changes of projective models.
Source: Tag 0941, DAG steps 7--9 (blueprint: lem-sf-perfect-tensor-roos-completion). -/
def Square (I : Ideal R) {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) : Prop :=
  f ≫ augmentation I L = augmentation I K ≫ (completion I).map f

/-- The natural quotient cone with vertex the original complex.
Source: Tag 0941 (blueprint: lem-sf-perfect-tensor-roos-completion).
Proof: the all-level compatibility follows by composing consecutive quotient transitions. -/
theorem quotient_natural (I : Ideal R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∀ (n m : ℕᵒᵖ) (f : n ⟶ m), quotient I K n.unop ≫
      ((tower I).obj K).asFunctor.map f = quotient I K m.unop := by
  sorry

/-- The quotient cone whose vertex is the specified complex, rather than an arbitrary limit.
Source: Tag 0941 (blueprint: lem-sf-perfect-tensor-roos-completion). -/
def quotientCone (I : Ideal R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    Cone ((tower I).obj K).asFunctor where
  pt := K
  π :=
    { app := fun n ↦ quotient I K n.unop
      naturality := fun n m f ↦ by
        simpa using (quotient_natural I K n m f).symm }

/-- The finite-projective tensor/completion assertions, including the actual kernel
and the coordinate formulas, without choosing bases.

Source: Stacks Tags 0941 and 031B (blueprint: lem-sf-perfect-tensor-roos-completion).
Proof:
1. Split finite free surjections onto every term of P and Q. Tensor the splittings,
   then take the finite sum in each total degree. The support intervals add.
2. The balanced quotient isomorphism sends (a tensor x) tensor (b tensor y) to
   the quotient class of ab times (x tensor y), with inverse obtained by placing 1
   in the first scalar factor. Both commute with the signed differentials.
3. A compatible quotient family in a finite-projective term embeds in the finite
   free completion. Its image is fixed by the retract idempotent, so it comes from
   the given term. This proves the limit assertion and injectivity of the quotient map.
4. Recursively lift a_n-b_n along each surjective transition; this solves (1-t)a=b.
   The kernel consists precisely of compatible families. The quotient augmentation
   has zero shifted coordinate and is a chain map.
5. For a fibre cycle (x,y), choose a with (1-t)a=y and subtract d(a,0). This leaves
   a cycle (c(v),0). For a boundary, solve (1-t)z=b and subtract dz to obtain c(w);
   injectivity then gives v=dw. Thus the specified augmentation is a quasi-isomorphism.
6. Projective terms are flat; bounded flat complexes are K-flat. The derived monoidal
   and scalar-tower computations identify this with ordinary derived tensor and its
   actual quotient units. Exact module products and the normalized Roos comparison
   identify it with the canonical derived-limit augmentation.
7. Cochain-map naturality follows on pure tensors. K-projective Hom bijectivity and
   the fibre homotopy (hx,-hy) descend it to all derived maps independently of models.
8. Associators give x tensor (y tensor z), symmetry gives (-1)^(ij)y tensor x,
   unitors multiply, and the coefficient unit reduces 1; all shifted coordinates vanish.
9. Reduction from any further quotient preserves products and the zero coordinate.
10. Finite-free extension commutes with the product by the projection comparison,
    and with the quotient tensor by balancing. Both coaugmentation routes have the
    same quotient coordinates and zero shifted coordinate.
11. A local finite-free extension has pi=u sigma^e with e positive. Arithmetic Roos
    restriction selects levels ej and sums transitions on the shifted coordinate;
    it is a quasi-isomorphism and carries the zero coordinate to zero.
12. Identity and composite scalar tensorators multiply the same scalar entries;
    arithmetic restrictions compose by multiplying e. Their augmentation squares agree. -/
theorem perfect_tensor_roos_completion [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) [IsAdicComplete (Ideal.span {π}) R]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : FiniteProjective P) (hQ : FiniteProjective Q) :
    FiniteProjective (P ⊗ Q) ∧
    (∀ n : ℕ, ∃ φ : quotientTensor (Ideal.span {π}) P Q n ≅
        ((tower (Ideal.span {π})).obj (P ⊗ Q)).asFunctor.obj (op n),
      ∀ (p q : ℤ) (x : P.X p) (y : Q.X q)
        (a b : R),
      φ.hom.f (p + q)
        ((HomologicalComplex.ιTensorObj
          ((extend (Ideal.Quotient.mk ((Ideal.span {π}) ^ (n + 1)))).obj P)
          ((extend (Ideal.Quotient.mk ((Ideal.span {π}) ^ (n + 1)))).obj Q)
          p q (p + q) rfl)
          (((Ideal.Quotient.mk ((Ideal.span {π}) ^ (n + 1)) a)
            ⊗ₜ[R, Ideal.Quotient.mk ((Ideal.span {π}) ^ (n + 1))] x) ⊗ₜ[_]
            ((Ideal.Quotient.mk ((Ideal.span {π}) ^ (n + 1)) b)
              ⊗ₜ[R, Ideal.Quotient.mk ((Ideal.span {π}) ^ (n + 1))] y))) =
        a • b • ((AdicCohomology.power (Ideal.span {π}) _ (n + 1)).mkQ
          ((HomologicalComplex.ιTensorObj P Q p q (p + q) rfl) (x ⊗ₜ[R] y)))) ∧
    (∀ (n : ℕ) (q : ℤ), Function.Surjective
      ((((tower (Ideal.span {π})).obj (P ⊗ Q)).asFunctor.map
        (homOfLE (Nat.le_succ n)).op).f q)) ∧
    Nonempty (IsLimit (quotientCone (Ideal.span {π}) (P ⊗ Q))) ∧
    (∀ q : ℤ, Function.Surjective ((roosU ((tower (Ideal.span {π})).obj (P ⊗ Q))).f q)) ∧
    (∀ q : ℤ, Function.Injective
      ((Pi.lift (quotient (Ideal.span {π}) (P ⊗ Q))).f q) ∧
      LinearMap.range ((Pi.lift (quotient (Ideal.span {π}) (P ⊗ Q))).f q).hom =
        LinearMap.ker ((roosU ((tower (Ideal.span {π})).obj (P ⊗ Q))).f q).hom) ∧
    QuasiIso (augmentation (Ideal.span {π}) (P ⊗ Q)) := by
  sorry


/-- Both actual coordinates, strict naturality, homotopy invariance, and every further
quotient of the completion augmentation. These equations hold before localization.
Source: Tag 0941, DAG steps 4, 7--9
(blueprint: lem-sf-perfect-tensor-roos-completion).
Proof: projection gives the quotient class, and the shifted projection gives zero.
A strict map commutes with reduction. A homotopy h induces (h,-h) in the node's
coordinate order (x,y), hence completion preserves homotopies. A transition between
any two levels is the quotient map sending the class of x to the class of x. -/
theorem augmentation_coordinates (I : Ideal R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (∀ q : ℤ, (augmentation I K).f (q + 1) ≫ (roosχ ((tower I).obj K) q).hom =
      biprod.lift 0 ((Pi.lift (quotient I K)).f (q + 1))) ∧
    (∀ (n : ℕ), augmentation I K ≫ roosEval ((tower I).obj K) n = quotient I K n) ∧
    (∀ (L : CochainComplex (ModuleCat.{u} R) ℤ) (f : K ⟶ L), Square I f) ∧
    (∀ (L : CochainComplex (ModuleCat.{u} R) ℤ) (f g : K ⟶ L),
      Homotopy f g → Nonempty (Homotopy ((completion I).map f) ((completion I).map g))) ∧
    (∀ (n m : ℕ) (h : n ≤ m), quotient I K m ≫
      (NatTrans.mapHomologicalComplex
        (AdicCohomology.transition I (Nat.add_le_add_right h 1)) (.up ℤ)).app K =
      quotient I K n) := by
  sorry

/-- The tensor coaugmentation intertwines associators, Koszul symmetry, both unitors
and the coefficient unit. The functor on the bottom sides is the actual quotient
Roos functor, so the equations retain both coordinates, including the zero one.
Source: Tag 0941, DAG steps 8--9
(blueprint: lem-sf-perfect-tensor-roos-completion).
Proof: the associator sends (x tensor y) tensor z to x tensor (y tensor z).
Symmetry sends x tensor y in degrees p,q to (-1)^(pq)y tensor x. Both unitors
multiply the scalar. Reduction sends the coefficient 1 to 1 at every level.
Each formula commutes with reduction; the shifted coordinates are all zero. -/
theorem tensor_coherence (I : Ideal R)
    (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    Square I (α_ P Q T).hom ∧ Square I (β_ P Q).hom ∧
    Square I (λ_ P).hom ∧ Square I (ρ_ P).hom ∧
    (∀ n : ℕ, augmentation I (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) ≫
      roosEval ((tower I).obj (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))) n =
      quotient I (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) n) := by
  sorry

/-- Localization identifies the specified tensor completion with ordinary derived tensor,
and gives naturality and independence for every derived morphism of the perfect models.
The last clause identifies this very map with the normalized total derived-limit unit,
for any presentation of total right derived inverse limit. Its displayed normalization
uniquely determines the comparison because the augmentation is invertible.
Source: Tag 0941, DAG steps 5--7
(blueprint: lem-sf-perfect-tensor-roos-completion).
Proof: bounded projective complexes are K-flat and K-projective. K-flat computation
makes the localization tensor comparison invertible. Apply the canonical cochain
quasi-isomorphism and K-projective Hom bijectivity. Strict naturality descends to all
derived morphisms and all model isomorphisms. Exact products identify the normalized
Roos augmentation with the derived-limit unit; this is the exact-products Roos
comparison, including its ordinary-limit normalization. -/
theorem derived_completion [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (_hπ : Irreducible π) [IsAdicComplete (Ideal.span {π}) R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ModuleCat.{u} R)]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (_hP : FiniteProjective P) (_hQ : FiniteProjective Q) :
    DerivedCategory.IsPerfectRingComplex (DerivedCategory.Q.{w}.obj (P ⊗ Q)) ∧
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q.{w} P Q) ∧
    IsIso (DerivedCategory.Q.{w}.map (augmentation (Ideal.span {π}) (P ⊗ Q))) ∧
    (∀ (P' Q' : CochainComplex (ModuleCat.{u} R) ℤ),
      FiniteProjective P' → FiniteProjective Q' →
      ∀ a : DerivedCategory.Q.{w}.obj (P ⊗ Q) ⟶ DerivedCategory.Q.{w}.obj (P' ⊗ Q'),
      ∃! b : DerivedCategory.Q.{w}.obj ((completion (Ideal.span {π})).obj (P ⊗ Q)) ⟶
          DerivedCategory.Q.{w}.obj ((completion (Ideal.span {π})).obj (P' ⊗ Q')),
        a ≫ DerivedCategory.Q.{w}.map (augmentation (Ideal.span {π}) (P' ⊗ Q')) =
          DerivedCategory.Q.{w}.map (augmentation (Ideal.span {π}) (P ⊗ Q)) ≫ b) ∧
    (∀ (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ ModuleCat.{u} R) ⥤
        DerivedCategory.{w} (ModuleCat.{u} R))
      (η : roosLimitFunctor (A := ModuleCat.{u} R) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RF),
      RF.IsRightDerivedFunctor η
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ModuleCat.{u} R) (.up ℤ)) →
      (∀ Z : CochainComplex (ℕᵒᵖ ⥤ ModuleCat.{u} R) ℤ,
        Z.IsKInjective → IsIso (η.app Z)) →
      ∃ σ : DerivedCategory.Q.{w}.obj ((completion (Ideal.span {π})).obj (P ⊗ Q)) ≅
          RF.obj (DerivedCategory.Q.{w}.obj ((tower (Ideal.span {π})).obj (P ⊗ Q))),
        DerivedCategory.Q.{w}.map (augmentation (Ideal.span {π}) (P ⊗ Q)) ≫ σ.hom =
          DerivedCategory.Q.{w}.map (roosAugmentLimit
            (quotient (Ideal.span {π}) (P ⊗ Q))
            (quotient_compatible (Ideal.span {π}) (P ⊗ Q))) ≫
              η.app ((tower (Ideal.span {π})).obj (P ⊗ Q))) := by
  sorry


/-- The canonical levelwise quotient/base-change identification is uniquely determined
by the quotient projection. This supplies canonically determined data.
Source: Tag 0941, DAG step 10 (blueprint: lem-sf-perfect-tensor-roos-completion).
Proof: extension preserves cokernels. Balancing identifies S tensor (M/IM) with
(S tensor M)/(IS)(S tensor M). The quotient projection is epic, proving uniqueness;
apply the construction degreewise, where it commutes with the differential. -/
theorem scalarQuotientIso_existsUnique {S : Type u} [CommRing S]
    (f : R →+* S) (I : Ideal R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    ∃! β : (extend f).obj (((tower I).obj K).asFunctor.obj (op n)) ≅
        ((tower (I.map f)).obj ((extend f).obj K)).asFunctor.obj (op n),
      (extend f).map (quotient I K n) ≫ β.hom =
        quotient (I.map f) ((extend f).obj K) n := by
  sorry

/-- The uniquely specified balanced quotient/base-change isomorphism at a level.
Source: Tag 0941, DAG step 10 (blueprint: lem-sf-perfect-tensor-roos-completion). -/
def scalarQuotientIso {S : Type u} [CommRing S]
    (f : R →+* S) (I : Ideal R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    (extend f).obj (((tower I).obj K).asFunctor.obj (op n)) ≅
      ((tower (I.map f)).obj ((extend f).obj K)).asFunctor.obj (op n) :=
  Classical.choose (scalarQuotientIso_existsUnique f I K n)

/-- The canonical product comparison, using the extended product projections followed
by their balanced quotient identifications. This is piComparison expressed by projections.
Source: Tag 0941, DAG step 10 (blueprint: lem-sf-perfect-tensor-roos-completion). -/
def scalarProduct {S : Type u} [CommRing S]
    (f : R →+* S) (I : Ideal R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extend f).obj (roosP ((tower I).obj K)) ⟶
      roosP ((tower (I.map f)).obj ((extend f).obj K)) :=
  Pi.lift (fun n ↦ (extend f).map
    (Pi.π (fun j : ℕ ↦ ((tower I).obj K).asFunctor.obj (op j)) n) ≫
      (scalarQuotientIso f I K n).hom)

/-- Both product coordinates specify the canonical scalar map of the actual Roos cones.
Source: Tag 0941, DAG step 10 (blueprint: lem-sf-perfect-tensor-roos-completion). -/
def ScalarCoordinates {S : Type u} [CommRing S]
    (f : R →+* S) (I : Ideal R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (c : (extend f).obj ((completion I).obj K) ⟶
      (completion (I.map f)).obj ((extend f).obj K)) : Prop :=
  ∀ q : ℤ, c.f (q + 1) ≫ (roosχ ((tower (I.map f)).obj ((extend f).obj K)) q).hom =
    (ModuleCat.extendScalars f).map (roosχ ((tower I).obj K) q).hom ≫
      (ModuleCat.extendScalars f).biprodComparison
        ((roosP ((tower I).obj K)).X q) ((roosP ((tower I).obj K)).X (q + 1)) ≫
      biprod.map ((scalarProduct f I K).f q) ((scalarProduct f I K).f (q + 1))

/-- There is a unique scalar Roos map with the prescribed two product coordinates.
Source: Tag 0941, DAG step 10 (blueprint: lem-sf-perfect-tensor-roos-completion).
Proof: use the additive comparison for the mapping cone with its projection product
map. Balancing makes the Roos differential square commute. Both cone projections
are jointly monic, proving uniqueness. No flatness or completeness is required. -/
theorem scalarComparison_existsUnique {S : Type u} [CommRing S]
    (f : R →+* S) (I : Ideal R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃! c : (extend f).obj ((completion I).obj K) ⟶
      (completion (I.map f)).obj ((extend f).obj K), ScalarCoordinates f I K c := by
  sorry

/-- The actual scalar Roos comparison, specified by its two canonical product coordinates.
Source: Tag 0941, DAG step 10 (blueprint: lem-sf-perfect-tensor-roos-completion). -/
def scalarComparison {S : Type u} [CommRing S]
    (f : R →+* S) (I : Ideal R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extend f).obj ((completion I).obj K) ⟶
      (completion (I.map f)).obj ((extend f).obj K) :=
  Classical.choose (scalarComparison_existsUnique f I K)

/-- The scalar tensorator is the ordinary balanced map, totalized with the same signs.
Source: Tag 0941, DAG step 10 (blueprint: lem-sf-perfect-tensor-roos-completion). -/
def scalarTensorator {S : Type u} [CommRing S] (f : R →+* S)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extend f).obj P ⊗ (extend f).obj Q ⟶ (extend f).obj (P ⊗ Q) :=
  letI := (ModuleCat.extendRestrictScalarsAdj f).left_adjoint_additive
  inv (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
    (ModuleCat.extendScalars f)).app P).app Q)

/-- Finite-free extension preserves the canonical product and Roos comparisons.
The augmentation square, followed by the balanced tensorator, is the scalar-extension
square for the two perfect tensor factors. All maps are the specified canonical maps.
Source: Tag 0941, DAG step 10 (blueprint: lem-sf-perfect-tensor-roos-completion).
Proof: finite-free extension commutes with products, independently of a basis.
The quotient/base-change isomorphism is balanced multiplication on pure tensors.
Apply its product comparison to both cone coordinates. The two routes on a
quotient augmentation agree and have zero shifted coordinate; naturality gives
the square after the balanced scalar tensorator. -/
theorem scalar_extension {S : Type u} [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S]
    (I : Ideal R) (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (_hP : FiniteProjective P) (_hQ : FiniteProjective Q) :
    IsIso (scalarProduct (algebraMap R S) I (P ⊗ Q)) ∧
    IsIso (scalarComparison (algebraMap R S) I (P ⊗ Q)) ∧
    ScalarCoordinates (algebraMap R S) I (P ⊗ Q)
      (scalarComparison (algebraMap R S) I (P ⊗ Q)) ∧
    (extend (algebraMap R S)).map (augmentation I (P ⊗ Q)) ≫
      scalarComparison (algebraMap R S) I (P ⊗ Q) =
        augmentation (I.map (algebraMap R S)) ((extend (algebraMap R S)).obj (P ⊗ Q)) ∧
    scalarTensorator (algebraMap R S) P Q ≫
      (extend (algebraMap R S)).map (augmentation I (P ⊗ Q)) ≫
      scalarComparison (algebraMap R S) I (P ⊗ Q) =
        augmentation (I.map (algebraMap R S))
          ((extend (algebraMap R S)).obj P ⊗ (extend (algebraMap R S)).obj Q) ≫
        (completion (I.map (algebraMap R S))).map
          (scalarTensorator (algebraMap R S) P Q) := by
  sorry


/-- The canonical arithmetic Roos map, formed using the existing selection/block square.
Source: Tags 0941 and 0H9K, DAG steps 11--12
(blueprint: lem-sf-perfect-tensor-roos-completion). -/
def arithmetic (X : CochainComplex (ℕᵒᵖ ⥤ ModuleCat.{u} R) ℤ)
    (e : ℕ) (he : 1 ≤ e) :
    roosF.obj X ⟶ roosF.obj ((complexRestriction (ModuleCat.{u} R) e).obj X) :=
  strictRoosMapOfSquare (selection e X.asFunctor) (block e X.asFunctor)
    (strictRoosBlock_comm X e he)

/-- The cofinal comparison has its selection/block coordinates, preserves every strict
augmentation, and satisfies the identity and iterated restriction equations.
Source: Tags 0941 and 0H9K, DAG steps 11--12
(blueprint: lem-sf-perfect-tensor-roos-completion).
Proof: finite telescoping makes selection and block commute with 1-t. The discarded
finite intervals contract, so the cone comparison is a quasi-isomorphism. Selection
of a compatible family is its restricted family, and block sends zero to zero.
One-term blocks give identity, and successive block sums concatenate; this proves
composition, including the canonical index transports expressed by HEq. -/
theorem arithmetic_coherence (X : CochainComplex (ℕᵒᵖ ⥤ ModuleCat.{u} R) ℤ) :
    (∀ (e : ℕ) (he : 1 ≤ e), QuasiIso (arithmetic X e he) ∧
      ∀ q : ℤ, (arithmetic X e he).f (q + 1) ≫
        (roosχ ((complexRestriction (ModuleCat.{u} R) e).obj X) q).hom =
        (roosχ X q).hom ≫ biprod.map
          ((block e X.asFunctor).f q) ((selection e X.asFunctor).f (q + 1))) ∧
    HEq (arithmetic X 1 (Nat.le_refl 1)) (𝟙 (roosF.obj X)) ∧
    (∀ (e f : ℕ) (he : 1 ≤ e) (hf : 1 ≤ f),
      HEq (arithmetic X e he ≫
          arithmetic ((complexRestriction (ModuleCat.{u} R) e).obj X) f hf)
        (arithmetic X (e * f) (one_le_mul he hf))) ∧
    (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ)
      (γ : ∀ n : ℕ, K ⟶ X.asFunctor.obj (op n))
      (hγ : ∀ n : ℕ, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
      (e : ℕ) (he : 1 ≤ e),
      ∃ hγe : ∀ n : ℕ, γ (e * (n + 1 + 1) - 1) ≫
          X.asFunctor.map ((index e).map (homOfLE (Nat.le_succ n)).op) =
            γ (e * (n + 1) - 1),
        roosAugment γ hγ ≫ arithmetic X e he =
          roosAugment (fun n ↦ γ (e * (n + 1) - 1)) hγe) := by
  sorry

/-- Ramified finite-free local extension: the completion comparison uses the cofinal
quotient maps, rather than identifying the two indexed uniformizer towers.
The comparison θ is fixed by its quotient maps. The derived isomorphism δ is fixed
by the actual scalar Roos comparison followed by inverse arithmetic restriction.
Source: Tag 0941, DAG steps 10--12
(blueprint: lem-sf-perfect-tensor-roos-completion).
Proof: positive finite-free rank implies pi has nonzero image in S. Locality makes
that image a nonunit, so DVR factorization writes it as u sigma^e with e positive.
The ideals (pi)^j and (sigma)^(ej) coincide. Their quotient maps give θ, independent
of a choice of generators or bases. Arithmetic restriction is a quasi-isomorphism
and sends quotient/zero coordinates to quotient/zero coordinates. The finite-free
scalar comparison is an isomorphism, with the same augmentation coordinates.
Localize and invert arithmetic restriction to obtain δ. Its defining equation and
the augmentation identity give the displayed balanced tensor square. -/
theorem ramified_extension {S : Type u} [CommRing S] [Algebra R S]
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
    [IsLocalHom (algebraMap R S)] [Module.Free R S] [Module.Finite R S]
    (π : R) (_hπ : Irreducible π) (σ : S) (_hσ : Irreducible σ)
    [IsAdicComplete (Ideal.span {π}) R] [IsAdicComplete (Ideal.span {σ}) S]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (_hP : FiniteProjective P) (_hQ : FiniteProjective Q) :
    ∃ (e : ℕ) (he : 1 ≤ e) (uS : Sˣ), algebraMap R S π = uS * σ ^ e ∧
      ∃ θ :
          (complexRestriction (ModuleCat.{u} S) e).obj
            ((tower (Ideal.span {σ})).obj ((extend (algebraMap R S)).obj (P ⊗ Q))) ≅
          (tower ((Ideal.span {π}).map (algebraMap R S))).obj
            ((extend (algebraMap R S)).obj (P ⊗ Q)),
        (∀ n : ℕ,
          quotient (Ideal.span {σ}) ((extend (algebraMap R S)).obj (P ⊗ Q))
              (e * (n + 1) - 1) ≫
            (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map θ.hom).app (op n) =
          quotient ((Ideal.span {π}).map (algebraMap R S))
            ((extend (algebraMap R S)).obj (P ⊗ Q)) n) ∧
        (∀ [HasDerivedCategory.{w} (ModuleCat.{u} S)],
          ∃ δ : DerivedCategory.Q.{w}.obj
              ((extend (algebraMap R S)).obj
                ((completion (Ideal.span {π})).obj (P ⊗ Q))) ≅
            DerivedCategory.Q.{w}.obj ((completion (Ideal.span {σ})).obj
              ((extend (algebraMap R S)).obj (P ⊗ Q))),
            δ.hom ≫ DerivedCategory.Q.{w}.map
                (arithmetic ((tower (Ideal.span {σ})).obj
                  ((extend (algebraMap R S)).obj (P ⊗ Q))) e he ≫ roosF.map θ.hom) =
              DerivedCategory.Q.{w}.map
                (scalarComparison (algebraMap R S) (Ideal.span {π}) (P ⊗ Q)) ∧
            DerivedCategory.Q.{w}.map
                ((extend (algebraMap R S)).map
                  (augmentation (Ideal.span {π}) (P ⊗ Q))) ≫ δ.hom =
              DerivedCategory.Q.{w}.map
                (augmentation (Ideal.span {σ}) ((extend (algebraMap R S)).obj (P ⊗ Q))) ∧
            DerivedCategory.Q.{w}.map (scalarTensorator (algebraMap R S) P Q ≫
                (extend (algebraMap R S)).map
                  (augmentation (Ideal.span {π}) (P ⊗ Q))) ≫ δ.hom =
              DerivedCategory.Q.{w}.map
                (augmentation (Ideal.span {σ})
                    ((extend (algebraMap R S)).obj P ⊗ (extend (algebraMap R S)).obj Q) ≫
                  (completion (Ideal.span {σ})).map
                    (scalarTensorator (algebraMap R S) P Q))) := by
  sorry

/-- Transport of the completion functor along an equality of ideals.
Source: Tag 0941, quotient ideal identification
(blueprint: lem-sf-perfect-tensor-roos-completion). -/
def idealCongr {I J : Ideal R} (h : I = J) : completion I ≅ completion J :=
  eqToIso (congrArg completion h)

/-- The canonical identity extension on cochain complexes.
Source: Tag 0941, DAG step 12 (blueprint: lem-sf-perfect-tensor-roos-completion). -/
def extendId : extend (RingHom.id R) ≅ 𝟭 (CochainComplex (ModuleCat.{u} R) ℤ) :=
  NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId R) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (ModuleCat.{u} R) (.up ℤ)

/-- The canonical iterated extension associator on cochain complexes.
Source: Tag 0941, DAG step 12 (blueprint: lem-sf-perfect-tensor-roos-completion). -/
def extendComp {S T : Type u} [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) : extend (g.comp f) ≅ extend f ⋙ extend g :=
  letI := (ModuleCat.extendRestrictScalarsAdj f).left_adjoint_additive
  letI := (ModuleCat.extendRestrictScalarsAdj g).left_adjoint_additive
  letI := (ModuleCat.extendRestrictScalarsAdj (g.comp f)).left_adjoint_additive
  NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g)) (.up ℤ)).symm

/-- The actual scalar completion maps satisfy the identity and composition squares.
Together with arithmetic_coherence these are the identity and iterated-extension
squares for ramified completion comparisons, since the latter are the uniquely
specified composites with inverse arithmetic restriction. The scalar tensorator
is the balanced tensorator and its own associativity is the monoidal functor law.
Source: Tag 0941, DAG step 12 (blueprint: lem-sf-perfect-tensor-roos-completion).
Proof: project to each quotient/product coordinate. Both composites multiply the
same scalar entries, and the shifted coordinate stays zero. Product uniqueness
and the two cone coordinates give equality. Canonical scalar extension associators
and ideal-map equalities supply exactly the displayed transports. -/
theorem scalar_identity_composition (I : Ideal R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    scalarComparison (RingHom.id R) I K ≫
      (idealCongr (Ideal.map_id (I := I))).hom.app ((extend (RingHom.id R)).obj K) ≫
      (completion I).map (extendId.hom.app K) = extendId.hom.app ((completion I).obj K) ∧
    ∀ (S T : Type u) [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T),
      scalarComparison (g.comp f) I K =
        (extendComp f g).hom.app ((completion I).obj K) ≫
          (extend g).map (scalarComparison f I K) ≫
          scalarComparison g (I.map f) ((extend f).obj K) ≫
          (idealCongr (Ideal.map_map f g)).hom.app ((extend g).obj ((extend f).obj K)) ≫
          (completion (I.map (g.comp f))).map ((extendComp f g).inv.app K) := by
  sorry


/-- The A-linear balanced tensorator, including its pure-tensor multiplication formula.
At f=R→R/(pi^(n+1)) this is exactly the canonical isomorphism U_n ≅ V tensor A_n.
Source: Tag 0941, DAG steps 2 and 10
(blueprint: lem-sf-perfect-tensor-roos-completion).
Proof: the inverse inserts 1 in the first scalar factor. Balancing checks the two
composites on pure tensors. Both differentials are d_P tensor 1 + (-1)^p 1 tensor d_Q,
so these degreewise maps form inverse cochain maps. -/
theorem scalar_tensorator_formula {S : Type u} [CommRing S] (f : R →+* S)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso (scalarTensorator f P Q) ∧
    ∀ (p q : ℤ) (x : P.X p) (y : Q.X q) (a b : S),
      (scalarTensorator f P Q).f (p + q)
        ((HomologicalComplex.ιTensorObj ((extend f).obj P) ((extend f).obj Q)
          p q (p + q) rfl) ((a ⊗ₜ[R, f] x) ⊗ₜ[S] (b ⊗ₜ[R, f] y))) =
        (a * b) ⊗ₜ[R, f] ((HomologicalComplex.ιTensorObj P Q p q (p + q) rfl)
          (x ⊗ₜ[R] y)) := by
  sorry

/-- The canonical scalar completion comparison is natural in maps of representatives.
Source: Tag 0941, DAG steps 7 and 10
(blueprint: lem-sf-perfect-tensor-roos-completion).
Proof: apply the quotient maps and product projections. Both sides send a pure
scalar tensor to its image under the map, and agree on both cone coordinates.
The scalar homotopies and K-projective Hom bijection descend this equation to
all derived maps of perfect models. -/
theorem scalar_naturality {S : Type u} [CommRing S] (f : R →+* S)
    (I : Ideal R) {K L : CochainComplex (ModuleCat.{u} R) ℤ} (a : K ⟶ L) :
    (extend f).map ((completion I).map a) ≫ scalarComparison f I L =
      scalarComparison f I K ≫ (completion (I.map f)).map ((extend f).map a) := by
  sorry

end CochainComplex.PerfectTensorRoos
