/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

/-! # Tensor transport along an isomorphism of ring sheaves

Source: Stacks Project, Modules on Sites, Section 03EK, and Cohomology on Sites,
Tags 06YN, 06YP, 06YS and 06YT
(blueprint: lem-sfb-ring-isomorphism-tensor-transport).

The derived clause supplies symmetric derived tensors whose
monoidal localization maps are invertible on K-flat pairs. The normalization square
uses the same total-complex comparison as the ordinary transport.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r wR wS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}

/-- The existing monoidal structure on module cochain complexes, cached for elaboration.
Source: Stacks 03EK and 06YT
(blueprint: lem-sfb-ring-isomorphism-tensor-transport). -/
noncomputable instance (priority := 2000) ringIsoCochainMonoidal
    (A : Sheaf J CommRingCat.{r}) :
    MonoidalCategory (CochainComplex (scalarModules J A) ℤ) := inferInstance

/-- The underlying structure of the existing total tensor, cached for elaboration.
Source: Stacks 03EK and 06YT
(blueprint: lem-sfb-ring-isomorphism-tensor-transport). -/
noncomputable instance (priority := 2000) ringIsoCochainMonoidalStruct
    (A : Sheaf J CommRingCat.{r}) :
    MonoidalCategoryStruct (CochainComplex (scalarModules J A) ℤ) :=
  (ringIsoCochainMonoidal A).toMonoidalCategoryStruct

/-- Localization of termwise restriction, allowing independent localization universes.
Source: Stacks 04VG and 06YP
(blueprint: lem-sfb-ring-isomorphism-tensor-transport). -/
noncomputable def ringIsoDerivedRestriction (c : R ≅ S)
    [HasDerivedCategory.{wR} (scalarModules J R)]
    [HasDerivedCategory.{wS} (scalarModules J S)]
    (h : exactFunctor _ _ (scalarRestriction c.hom)) :
    DerivedCategory (scalarModules J S) ⥤ DerivedCategory (scalarModules J R) :=
  letI : PreservesFiniteLimits (scalarRestriction c.hom) := h.1
  letI : PreservesFiniteColimits (scalarRestriction c.hom) := h.2
  (scalarRestriction c.hom).mapDerivedCategory

/-- The canonical localization comparison for termwise scalar restriction.
Source: Stacks 04VG and 06YP
(blueprint: lem-sfb-ring-isomorphism-tensor-transport). -/
noncomputable def ringIsoRestrictionComparison (c : R ≅ S)
    [HasDerivedCategory.{wR} (scalarModules J R)]
    [HasDerivedCategory.{wS} (scalarModules J S)]
    (h : exactFunctor _ _ (scalarRestriction c.hom)) :
    DerivedCategory.Q ⋙ ringIsoDerivedRestriction c h ≅
      (scalarRestriction c.hom).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  letI : PreservesFiniteLimits (scalarRestriction c.hom) := h.1
  letI : PreservesFiniteColimits (scalarRestriction c.hom) := h.2
  (scalarRestriction c.hom).mapDerivedCategoryFactors

/-- The derived symmetric tensors and the representative normalization of their comparison.
The existential presentations include their localization maps, invertible on K-flat pairs
and at the unit. Thus they present the actual derived tensor, rather than impose
additional tensor hypotheses on the input categories or derived objects.
Source: Stacks 06YS, 06YT and 06YP
(blueprint: lem-sfb-ring-isomorphism-tensor-transport). -/
def RingIsoDerivedTensorCompatible
    (c : R ≅ S)
    [HasDerivedCategory.{wR} (scalarModules J R)]
    [HasDerivedCategory.{wS} (scalarModules J S)]
    (h : exactFunctor _ _ (scalarRestriction c.hom))
    (t : ∀ P Q : CochainComplex (scalarModules J S) ℤ,
      ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
        ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj P ⊗
          ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj Q) : Prop :=
  ∃ (mR : MonoidalCategory (DerivedCategory (scalarModules J R)))
    (mS : MonoidalCategory (DerivedCategory (scalarModules J S))),
    letI := mR
    letI := mS
    ∃ (bR : SymmetricCategory (DerivedCategory (scalarModules J R)))
      (bS : SymmetricCategory (DerivedCategory (scalarModules J S))),
      letI := bR
      letI := bS
      ∃ (qR : (DerivedCategory.Q (C := scalarModules J R)).LaxBraided)
        (qS : (DerivedCategory.Q (C := scalarModules J S)).LaxBraided),
        letI := qR
        letI := qS
        IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := scalarModules J R))) ∧
        IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := scalarModules J S))) ∧
        (∀ P Q : CochainComplex (scalarModules J R) ℤ,
          P.IsKFlatIndependentCoefficients → Q.IsKFlatIndependentCoefficients →
            IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)) ∧
        (∀ P Q : CochainComplex (scalarModules J S) ℤ,
          P.IsKFlatIndependentCoefficients → Q.IsKFlatIndependentCoefficients →
            IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)) ∧
        ∃ d : (ringIsoDerivedRestriction c h).Braided,
          ∀ (P Q : CochainComplex (scalarModules J S) ℤ),
            P.IsKFlatIndependentCoefficients → Q.IsKFlatIndependentCoefficients →
            d.toMonoidal.toOplaxMonoidal.δ
                (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
              ((ringIsoRestrictionComparison c h).hom.app P ⊗ₘ
                (ringIsoRestrictionComparison c h).hom.app Q) ≫
              Functor.LaxMonoidal.μ DerivedCategory.Q
                (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj P)
                (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj Q) =
            (ringIsoDerivedRestriction c h).map
                (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
              (ringIsoRestrictionComparison c h).hom.app (P ⊗ Q) ≫
              DerivedCategory.Q.map (t P Q).hom

/-- All clauses of scalar-coordinate tensor transport, with the tensor and unit maps
normalized on sections and the total-complex map normalized on every summand.
Source: Stacks 03EK, 06YN and 06YP
(blueprint: lem-sfb-ring-isomorphism-tensor-transport). -/
structure RingIsoTensorTransport (c : R ≅ S)
    [HasDerivedCategory.{wR} (scalarModules J R)]
    [HasDerivedCategory.{wS} (scalarModules J S)] where
  /-- The ordinary equivalence is the given restriction in both directions. -/
  equivalence : scalarModules J S ≌ scalarModules J R
  functor_eq : equivalence.functor = scalarRestriction c.hom
  inverse_eq : equivalence.inverse = scalarRestriction c.inv
  /-- Restriction is additive and exact. -/
  additive : (scalarRestriction c.hom).Additive
  exact : exactFunctor _ _ (scalarRestriction c.hom)
  /-- Strong symmetric tensor coherence, including associators and both unitors. -/
  monoidal : (scalarRestriction c.hom).Braided
  /-- The forward tensor map is the identity on local pure tensors. -/
  pure_hom : ∀ (M N : scalarModules J S) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U),
    (monoidal.toMonoidal.toOplaxMonoidal.δ M N).val.app U
        (ScalarHomOrdinary.pure S M N U x y) =
      ScalarHomOrdinary.pure R ((scalarRestriction c.hom).obj M)
        ((scalarRestriction c.hom).obj N) U x y
  /-- The inverse tensor map has exactly the same generator formula. -/
  pure_inv : ∀ (M N : scalarModules J S) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U),
    (monoidal.toMonoidal.toLaxMonoidal.μ M N).val.app U
        (ScalarHomOrdinary.pure R ((scalarRestriction c.hom).obj M)
          ((scalarRestriction c.hom).obj N) U x y) =
      ScalarHomOrdinary.pure S M N U x y
  /-- On the regular module the unit map is the inverse ring-sheaf isomorphism. -/
  unit_hom : ∀ (U : Cᵒᵖ) (s : S.obj.obj U),
    monoidal.toMonoidal.toOplaxMonoidal.η.val.app U s = c.inv.hom.app U s
  /-- Termwise restriction identifies the actual direct-sum total tensor complexes. -/
  totalIso : ∀ P Q : CochainComplex (scalarModules J S) ℤ,
    ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
      ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj Q
  /-- Naturality in both complex variables. -/
  total_naturality : ∀ {P P' Q Q' : CochainComplex (scalarModules J S) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q'),
    ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).map (f ⊗ₘ g) ≫
        (totalIso P' Q').hom =
      (totalIso P Q).hom ≫
        (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).map f ⊗ₘ
          ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).map g)
  /-- Its degree-n summand is precisely the ordinary tensor map. -/
  total_summand : ∀ (P Q : CochainComplex (scalarModules J S) ℤ)
    (p q n : ℤ) (h : p + q = n),
    (scalarRestriction c.hom).map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
        ((totalIso P Q).hom.f n) =
      monoidal.toMonoidal.toOplaxMonoidal.δ (P.X p) (Q.X q) ≫
        HomologicalComplex.ιTensorObj
          (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj P)
          (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj Q) p q n h
  /-- Preservation and reflection of acyclicity, without boundedness assumptions. -/
  acyclic_iff : ∀ P : CochainComplex (scalarModules J S) ℤ,
    (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj P).Acyclic ↔ P.Acyclic
  /-- Preservation and reflection of sheaf flatness. -/
  flat_iff : ∀ M : scalarModules J S,
    IsFlatOnSite (R := R) ((scalarRestriction c.hom).obj M) ↔ IsFlatOnSite (R := S) M
  /-- Preservation and reflection of the acyclic-tensor definition of K-flatness. -/
  kflat_iff : ∀ P : CochainComplex (scalarModules J S) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients
      (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj P) ↔
        P.IsKFlatIndependentCoefficients
  /-- On R-complexes the two definitions of K-flatness agree. -/
  kflat_test_R : ∀ P : CochainComplex (scalarModules J R) ℤ,
    P.IsKFlatIndependentCoefficients ↔ P.IsKFlatForTotalTensor
  /-- On S-complexes the same equivalence includes both tensor orders. -/
  kflat_test_S : ∀ P : CochainComplex (scalarModules J S) ℤ,
    P.IsKFlatIndependentCoefficients ↔ P.IsKFlatForTotalTensor
  /-- The coherent derived comparison is computed by this same total tensor map. -/
  derived : RingIsoDerivedTensorCompatible c exact totalIso

/-- Restriction along a ring-sheaf isomorphism transports tensor, flatness and K-flatness,
and its unbounded derived extension has the coherent normalized tensor comparison.
Source: Stacks 03EK, 03CY, 06YN, 06YP, 06YS and 06YT
(blueprint: lem-sfb-ring-isomorphism-tensor-transport).

Proof:
1. Restrict back along the inverse. Both composites are identity on abelian sheaves;
   the scalar actions agree by c inverse c = id. This gives the additive exact equivalence.
2. On section tensors send x tensor y to x tensor y in both directions. Surjectivity
   of c makes the S-balanced relation R-balanced. Sheafification extends these maps
   uniquely. The unit is c inverse. On pure tensors the associator, unitor and symmetry
   diagrams commute, hence they commute on the sheafified tensor.
3. Sum the comparisons in each degree over p+q=n. Naturality commutes with both
   differential terms; additivity preserves the sign (-1)^p. This yields totalIso.
4. Exactness identifies cohomology; the inverse equivalence reflects zero objects.
   Tensor the inverse image of a short exact sequence to transport flatness.
5. For any acyclic R-complex A, its inverse image is acyclic. Tensor it with the
   S-K-flat P and transport the total tensor back. Interchange c and its inverse
   to obtain reflection and the corresponding assertion for the inverse functor.
6. Tensor commutes with mapping cones. The acyclic-cone criterion proves that the
   acyclic-tensor test preserves quasi-isomorphisms on either side (06YP), using
   signed symmetry for the other order. Conversely apply tensor to zero -> A.
7. Localize the exact termwise equivalence. K-flat resolutions correspond by steps
   4-5, and step 3 gives the derived comparison on them. The resolving-subcategory
   descent theorem extends it uniquely and naturally to all derived pairs.
8. Check derived coherence on three K-flat resolutions, whose pairwise tensors are
   K-flat. The diagrams are those of step 2 summed over triple degrees; symmetry
   includes (-1)^(pq). Faithfulness of restriction to resolutions proves coherence
   for all derived objects. The displayed derived square records the computation
   on every corresponding pair of K-flat resolutions, independently of choices. -/
theorem ringIso_tensor_transport (c : R ≅ S)
    [HasDerivedCategory.{wR} (scalarModules J R)]
    [HasDerivedCategory.{wS} (scalarModules J S)] :
    Nonempty (RingIsoTensorTransport c) := by
  sorry

end SheafOfModules
