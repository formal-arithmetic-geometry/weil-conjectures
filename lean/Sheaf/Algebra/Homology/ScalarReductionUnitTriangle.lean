/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Algebra.Homology.ScalarAdjunctionUnitCoefficientNormalization
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.DivisibleExtensionDerivedReduction
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.CategoryTheory.TorsionSheafConstantModule
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Scalar reduction, its quotient unit, and its multiplication triangle

Source: blueprint main-20261015, Cartier proof paragraph 4, live V2 steps 2–3;
Stacks Project, Tags 093J, 03CY, 03D7, 03ER, 06YY, 06YU and 0152.
(blueprint: lem-sfb-scalar-reduction-unit-triangle).

The quotient is specified by its cokernel universal property in module sheaves.
The comparison and the boundary are fixed by the supplied resolution, rather than
by an arbitrary isomorphism to an object with the same cohomology.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r wZ wR

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ChangeOfRings

namespace SheafOfModules.ScalarAdjunctionNormalization

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [EssentiallySmall.{r} C]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasDerivedCategory.{wZ} (IntegerModules J)]
  (n : ℕ) [HasDerivedCategory.{wR} (ResidueModules J n)]
  (M : DerivedChangeOfRingsCochainModel (quotient J n))
  (N : Normalization J n M)

/-- The full scalar-reduction assertion, for the actual tensor functor and normalized unit.
Source: Cartier proof paragraph 4, live V2 steps 2–3; Stacks 093J, 03CY, 03D7,
03ER, 06YY and 0152 (blueprint: lem-sfb-scalar-reduction-unit-triangle).
The torsion essential-image and full-faithfulness clauses express uniqueness of the
residue action on a fixed abelian sheaf, including linearity of every additive map.
The resolution clauses quantify over every flat-term K-flat resolution. -/
structure ScalarReductionUnitTriangle where
  /-- Exact restriction, inherited from the supplied normalization. -/
  [restriction_limits : PreservesFiniteLimits (restriction J n)]
  [restriction_colimits : PreservesFiniteColimits (restriction J n)]
  /-- Exactness of the actual coefficient sequence. -/
  coefficient_zero : (n • 𝟙 (integerUnit J)) ≫ coefficientQuotient J n = 0
  coefficient_exact : (ShortComplex.mk (n • 𝟙 (integerUnit J))
    (coefficientQuotient J n) coefficient_zero).ShortExact
  /-- All residue modules, and precisely the torsion abelian sheaves, occur. -/
  residue_killed : ∀ (T : ResidueModules J n) (U : Cᵒᵖ) (x : T.val.obj U), n • x = 0
  torsion_lift : ∀ (F : Sheaf J AddCommGrpCat.{r}),
    (∀ (U : Cᵒᵖ) (x : F.obj.obj U), n • x = 0) →
    ∃ T : ResidueModules J n,
      Nonempty ((toSheaf.{r} (derivedChangeRingIndependentCoefficients J (residues J n))).obj T ≅ F)
  /-- Every additive map is residue-linear, and its lift is unique. -/
  additive_maps : (toSheaf.{r}
    (derivedChangeRingIndependentCoefficients J (residues J n))).FullyFaithful
  /-- Constant residue sections act by their integer representatives. -/
  integer_action : ∀ (T : ResidueModules J n) (U : Cᵒᵖ) (z : ℤ) (x : T.val.obj U),
    @SMul.smul ((residues J n).obj.obj U) (T.val.obj U) inferInstance
        ((toSheafify J ((Functor.const Cᵒᵖ).obj
          (CommRingCat.of (ULift.{r} (ZMod n))))).app U (ULift.up (z : ZMod n))) x = z • x
  /-- Restriction of residue modules to integer modules is fully faithful. -/
  restriction_fullyFaithful : (restriction J n).FullyFaithful
  /-- Natural quotient comparison, including the pure-tensor and unit formulas. -/
  quotient_comparison : ∃ (Q : IntegerModules J ⥤ ResidueModules J n)
    (π : 𝟭 (IntegerModules J) ⟶ Q ⋙ restriction J n)
    (w : ∀ A : IntegerModules J, (n • 𝟙 A) ≫ π.app A = 0),
    (∀ A : IntegerModules J, Nonempty (IsColimit (CokernelCofork.ofπ (π.app A) (w A)))) ∧
    ∃ e : M.E ≅ Q,
      (∀ A : IntegerModules J,
        N.ordinary.unit.app A ≫ (restriction J n).map (e.hom.app A) = π.app A) ∧
      ∀ (A : IntegerModules J) (U : Cᵒᵖ) (x : A.val.obj U)
        (a : (residues J n).obj.obj U),
        (eqToHom (M.obj_eq A).symm ≫ e.hom.app A).val.app U
          ((toSheafify J (changeOfRingsPresheaf (quotient J n) A).presheaf).app U
            (a ⊗ₜ[(integers J).obj.obj U, ((quotient J n).hom.app U).hom] x)) =
          @SMul.smul ((residues J n).obj.obj U) ((Q.obj A).val.obj U) inferInstance
            a ((π.app A).val.app U x)
  /-- The actual unit of every other ordinary left adjoint is also a cokernel. -/
  all_ordinary_units : ∀ (E : IntegerModules J ⥤ ResidueModules J n)
    (a : E ⊣ restriction J n) (A : IntegerModules J),
    ∃ w : (n • 𝟙 A) ≫ a.unit.app A = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (a.unit.app A) w))
  /-- Flat terms have monic multiplication, with no condition on their complex's homology. -/
  flat_terms_mono : ∀ P : CochainComplex (IntegerModules J) ℤ,
    (∀ i : ℤ, IsFlatOnSite (R := integers J) (P.X i)) →
    ∀ i : ℤ, Mono (n • 𝟙 (P.X i))
  /-- The genuine residue complex, its canonical comparison, short exact sequence,
  and the triangle transported by `(p,p,Res(c_A)⁻¹)`. -/
  resolution_triangle : ∀ (A : IntegerModules J)
    (P : CochainComplex (IntegerModules J) ℤ)
    (p : P ⟶ (CochainComplex.singleFunctor (IntegerModules J) 0).obj A),
    CochainComplex.IsKFlatResolutionIndependentCoefficients (R := integers J) p →
    (∀ i : ℤ, IsFlatOnSite (R := integers J) (P.X i)) →
    ∃ (w : (n • 𝟙 P) ≫ (N.ordinary.mapHomologicalComplex (.up ℤ)).unit.app P = 0)
      (hS : (ShortComplex.mk (n • 𝟙 P)
        ((N.ordinary.mapHomologicalComplex (.up ℤ)).unit.app P) w).ShortExact)
      (c : M.T.obj (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (IntegerModules J) 0).obj A)) ≅
        DerivedCategory.Q.obj ((M.E.mapHomologicalComplex (.up ℤ)).obj P)),
      M.T.map (DerivedCategory.Q.map p) ≫ c.hom = M.ε.app P ∧
      (∀ i : ℤ, ∃ wᵢ : (n • 𝟙 (P.X i)) ≫ N.ordinary.unit.app (P.X i) = 0,
        Nonempty (IsColimit (CokernelCofork.ofπ (N.ordinary.unit.app (P.X i)) wᵢ))) ∧
      ∃ δ : (restriction J n).mapDerivedCategory.obj
          (M.T.obj (DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (IntegerModules J) 0).obj A))) ⟶
        (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (IntegerModules J) 0).obj A))⟦(1 : ℤ)⟧,
        δ = (restriction J n).mapDerivedCategory.map c.hom ≫
          (restriction J n).mapDerivedCategoryFactors.hom.app
            ((M.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.triangleOfSESδ hS ≫ (DerivedCategory.Q.map p)⟦(1 : ℤ)⟧' ∧
        Triangle.mk
          (n • 𝟙 (DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (IntegerModules J) 0).obj A)))
          (N.derived.unit.app (DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (IntegerModules J) 0).obj A))) δ ∈
          distTriang (DerivedCategory (IntegerModules J)) ∧
        ∃ e : DerivedCategory.triangleOfSES hS ≅ Triangle.mk
          (n • 𝟙 (DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (IntegerModules J) 0).obj A)))
          (N.derived.unit.app (DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (IntegerModules J) 0).obj A))) δ,
          e.hom.hom₁ = DerivedCategory.Q.map p ∧
          e.hom.hom₂ = DerivedCategory.Q.map p ∧
          e.hom.hom₃ = (restriction J n).mapDerivedCategoryFactors.inv.app
            ((M.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
            (restriction J n).mapDerivedCategory.map c.inv
  /-- Every extension with epic first and monic last multiplication has the specified
  residue kernel and quotient presentation. -/
  presentations : ∀ (S : ShortComplex (IntegerModules J)) (_ : S.ShortExact),
    Epi (n • 𝟙 S.X₁) → Mono (n • 𝟙 S.X₃) →
    ∃ D : SheafOfModules.DivisibleReduction.Presentation (J := J) n, D.S = S

/-- Scalar reduction has its quotient unit and its canonical multiplication triangle.
Source: Cartier proof paragraph 4, live V2 steps 2–3; Stacks 093J, 03CY, 03D7,
0B65, 03ER, 06YY and 0152 (blueprint: lem-sfb-scalar-reduction-unit-triangle).

Proof:
1. Sheafify the exact constant coefficient sequence, using
   `lem-weil-pbc-sheafification-exact`, and identify its terms by
   `def-weil-pbc-constant-sheaf`. Module kernels and cokernels have the underlying
   abelian-sheaf kernels and cokernels (`def-weil-sheaf-of-modules-category`).
2. Apply `lem-pur-torsion-sheaf-constant-module`: torsion sheaves have the unique
   residue action and every additive map is linear. This proves full faithfulness
   of restriction (`def-pc-sheaf-restrict-scalars`).
3. Give coker(n on A) its residue action. The quotient is adjunct to a map from E(A).
   The inverse is induced by the ordinary unit, which kills n by balancing. Their
   composites are identities by the cokernel universal property and the adjunction
   bijection. The tensor formulas in
   `lem-sfb-scalar-adjunction-unit-coefficient-normalization` identify the map on pure
   tensors; cokernel uniqueness proves naturality.
4. Unit-compatible uniqueness of left adjoints
   (`lem-weil-pbc-conjugate-iso-unit-equation`) identifies every other unit with this
   cokernel, followed by an isomorphism.
5. Apply exact tensor with a flat module to the coefficient sequence. The tensor
   unit and symmetry identify its first map with n and its last with the quotient.
   Hence n is monic in each flat term, independently of boundedness or cohomology
   (`def-pc-flat-sheaf-modules`, `def-pur-sheaf-tensor-product`).
6. The K-flat computation of `lem-pur-derived-change-of-rings` identifies Lq(A)
   with the actual residue complex E(P). The termwise quotient units give a
   degreewise short exact sequence, since each term of P is flat.
7. Apply `lem-weil-pbc-complex-ses-triangle` to this sequence. Its boundary is
   `DerivedCategory.triangleOfSESδ`, with the fixed sign of Stacks 0152.
8. The resolution comparison satisfies Lq(p) followed by c_A equals c_P. The
   normalized unit on P is its ordinary quotient unit, by
   `lem-sfb-scalar-adjunction-unit-coefficient-normalization`. Naturality identifies
   the transported middle arrow with eta_A. Transport by p,p,Res(c_A) inverse;
   the boundary is Res(c_A), then the canonical boundary, then p[1]. These three
   equations give the triangle isomorphism; `def-weil-triangulated-category`
   preserves distinguishedness under that isomorphism.
9. For an extension with epic n on its first term and monic n on its last term,
   its kernel and cokernel are killed by n. Their unique residue actions give
   precisely the two extra short exact sequences and all the vanishing equations
   of `def-sfb-scalar-reduction-presentation`.
No flatness of the residue coefficient ring over the integers is assumed. -/
theorem scalarReductionUnitTriangle [HasTerminal C] (hn : 1 ≤ n) :
    Nonempty (ScalarReductionUnitTriangle J n M N) := by
  sorry

end SheafOfModules.ScalarAdjunctionNormalization
