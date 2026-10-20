/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.IntegralDerivedCoefficientData
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Paper.FormalClosedSupportDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
import WeilConjectures.Algebra.Homology.LowerTruncationStepTriangle
import Sheaf.Paper.CoefficientHeartCommonStratification
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.ImmersionFiberDegreeOne
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.IntegralModelSurjectiveClosedReflection
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.Paper.LocalizingAdmissibleCoefficients
import Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.FilteredColimitsTensor
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Sheaf.Paper.IntegralConstructibleHeart
import Sheaf.Paper.IntegralHeartDualizable

/-!
# Integral stratum filtrations and the global derived Hom formula

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-ext,
det-lem-int-ext-formula.md and its proof, clauses (1)--(2)
(blueprint: det-lem-int-ext-formula).

The coefficients, constructibility, ordinary relative derived tensor and internal Hom
are the recorded constructions. Global sections are Hom from the regular module,
as in the ringed-site hypercohomology definition, here in the module-object encoding.
The inverse-limit clause uses strict towers of complexes and the recorded Roos triangle.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Global sections are Hom from the regular integral module. This is the same
`Hom(O,-)` construction as def-pur-ringed-site-zeroth-hypercohomology, specialized
using preadditiveCoyoneda to the recorded module-object category.
Source: blueprint det-lem-int-ext-formula, opening convention for global derived Hom
(blueprint: det-lem-int-ext-formula). -/
abbrev integralStratumSections (X : Scheme.{u}) :
    pulledBackModuleObjects (integralCoefficientRing l E) X ⥤ Ab.{u + 1} :=
  preadditiveCoyoneda.obj (op (Mod.regular (condensedRingObj (integralCoefficientRing l E) X)))

/-- Full derived sections, computed by the canonical K-injective replacement, before
applying any homology functor. Source: blueprint det-lem-int-ext-formula, opening convention;
Stacks Project, Section 07A5 (blueprint: det-lem-int-ext-formula). -/
def integralStratumDerivedSections (X : Scheme.{u}) :
    integralDerived l E X ⥤ DerivedCategory Ab.{u + 1} :=
  (integralStratumSections l E X).rightDerivedFunctor

/-- The derived dual of a stratum sheaf, including torsion sheaves, with values in the
ordinary uncompleted module derived category.
Source: blueprint det-lem-int-ext-formula, clause (2)
(blueprint: det-lem-int-ext-formula). -/
def integralStratumDual (S : Scheme.{u})
    (L : pulledBackModuleObjects (integralCoefficientRing l E) S) : integralDerived l E S :=
  ((derivedHom (integralCoefficientRing l E) S).obj
    (op ((DerivedCategory.singleFunctor _ 0).obj L))).obj (𝟙_ (integralDerived l E S))

/-- Tensoring by the recorded derived dual, using the existing uncompleted relative tensor.
Source: blueprint det-lem-int-ext-formula, clause (2)
(blueprint: det-lem-int-ext-formula). -/
def integralStratumDualTensor (S : Scheme.{u})
    (L : pulledBackModuleObjects (integralCoefficientRing l E) S) :
    integralDerived l E S ⥤ integralDerived l E S :=
  (derivedTensor (integralCoefficientRing l E) S).obj (integralStratumDual l E S L)

/-- Finite distinguished-triangle filtration by shifts of integral stratum sheaves;
if the input is a sheaf in degree zero, every shift can be zero.
Source: blueprint det-lem-int-ext-formula, clause (1)
(blueprint: det-lem-int-ext-formula).

Proof, following DAG steps 1--7:
1. sk-lem-int-integral-heart gives boundedness and constructible cohomology. The finitely
many lower-truncation triangles of lem-pc-derived-lower-truncation-step-triangle reduce
C to finitely many shifted cohomology sheaves.
2. Finite type over the field gives Noetherian affine charts
(lem-wf-affine-noetherian-components). Apply only the topological ordered-refinement
clause of det-lem-coefficient-heart-common-stratification to a common adapted partition.
The reduced-induced-closed-subscheme lemma realizes its open prefixes and closed tails.
3. For a refined stratum S and an old stratum T containing its image, S times_X T -> S
is an immersion by base change and is surjective by
lem-weil-pbc-immersion-fibre-degree-one. Hence it is a surjective closed immersion.
4. Cartesian coefficients and exact pullback transport the finite scalar matrices
unchanged, with their cokernels and torsion, to this fibre product. Composition of
module inverse images identifies the two restrictions of the original sheaf.
5. lem-sfb-integral-model-surjective-closed-reflection descends these models to S.
The one-stratum definition gives constructibility on S.
6. Apply the ringed open/closed exact sequence on each successive closed tail and push
it to X by exact closed direct image. The resulting short exact sequences have kernels
a_!L, and lem-weil-pbc-complex-ses-triangle gives distinguished triangles. For a sheaf
all vertices and pieces lie in degree zero.
7. Refine the finitely many truncation triangles by these sheaf filtrations. For a
triangle A -> B -> D -> A[1], pull each filtration step D_j -> D back as
Cone(D_j -> A[1])[-1]; the octahedral axiom gives successive triangles with the same
graded pieces. Append a filtration of A and induct. Use a common refinement for all
cohomology sheaves. The zero object and the empty scheme allow the empty filtration. -/
theorem integral_stratum_filtration
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (C : integralDerived l E X)
    (hC : constantModelBoundedConstructible (integralCoefficientRing l E) X C) :
    ∃ (S : X.FiniteLocallyClosedStratification) (m : ℕ)
      (F : Fin (m + 1) → integralDerived l E X)
      (T : Fin m → Triangle (integralDerived l E X)),
      IsZero (F 0) ∧ Nonempty (F (Fin.last m) ≅ C) ∧
      ∀ r : Fin m,
        T r ∈ Pretriangulated.distinguishedTriangles ∧
        (T r).obj₁ = F r.castSucc ∧ (T r).obj₂ = F r.succ ∧
        ∃ (a : Fin S.n) (Z : Scheme.{u}) (v : S.domain a ⟶ Z) (i : Z ⟶ X)
          (_ : IsOpenImmersion v) (_ : IsClosedImmersion i),
          v ≫ i = S.immersion a ∧
          ∃ (L : pulledBackModuleObjects (integralCoefficientRing l E) (S.domain a)) (n : ℤ),
            IsConstantModelConstructible (integralCoefficientRing l E) (S.domain a) L ∧
            HasFiniteConstantLocalModel (integralCoefficientRing l E) (S.domain a) L ∧
            (DerivedCategory.homologyConcentratedIn 0 0 C → n = 0) ∧
            Nonempty ((T r).obj₃ ≅
              ((DerivedCategory.singleFunctor _ 0).obj
                ((lowerStar (integralCoefficientRing l E) i).obj
                  ((openImmersionLowerShriek (integralCoefficientRing l E) v).obj L))) ⟦n⟧) := by
  sorry

/-- Global derived Hom from a stratum extension is derived sections of the tensor of
its derived dual with restricted derived support. The dual has Tor amplitude [0,1],
and tensoring with it preserves small filtered degreewise colimits and countable
strict derived inverse limits, with their projection maps.
Source: blueprint det-lem-int-ext-formula, clause (2)
(blueprint: det-lem-int-ext-formula).

Proof, following DAG steps 8--12:
8. det-lem-formal-closed-support-derived gives the support adjunction for the admissible
integral coefficient ring. The K-injective global-Hom model of
lem-sfb-derived-internal-hom-sections-model identifies its Hom complexes with RΓ RHom.
9. Cartesian coefficients identify open inverse image with transported ringed inverse
image. The exact adjunction u_! adjoint to u^* preserves K-injectives on the right.
Termwise adjunction of global Hom complexes therefore gives the natural open-adjunction
comparison, with no boundedness assumption on K.
10. det-prop-sfb-qlbar-colimit-x-integral-limit identifies the coefficient with the
completed integral sheaf. det-lem-int-integral-heart-dualizable gives dualizability and
Tor amplitude [0,1] of D = L^vee. The dual tensor adjunction and uniqueness of right
adjoints identify D tensor - with RHom(L,-), compatibly with evaluation. Apply derived
sections and compose the two support/open adjunction comparisons.
11. For a filtered diagram choose a flat-term K-flat representative of D
(lem-pc-kflat-resolution). Tensor totalization commutes with degreewise filtered colimits
by lem-pc-module-filtered-colimits-tensor. Exact filtered colimits identify the localized
colimit with the derived filtered colimit. The statement gives a K-flat model P,
its natural comparison with D tensor -, and preservation of degreewise filtered colimits
by P tensor -. No ordinary categorical colimit in a triangulated category is invoked.
12. Dualizability makes D tensor - a right adjoint, so it preserves countable products;
it is exact and preserves shifts. Apply it to the strict-tower Roos triangle from
lem-weil-pbc-ringed-strict-tower-homotopy-limit. Product comparison commutes with each
projection and hence with 1-shift. Cone totalizations agree with standard Koszul signs
(-1)^p in degree p; this gives the asserted triangle and its canonical projection map. -/
theorem integral_stratum_hom_formula
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {X Z S V : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] (v : S ⟶ Z) [IsOpenImmersion v]
    (j : V ⟶ X) [IsOpenImmersion j] (hij : Set.range j = (Set.range i)ᶜ)
    (L : pulledBackModuleObjects (integralCoefficientRing l E) S)
    (hL : IsConstantModelConstructible (integralCoefficientRing l E) S L)
    (hmodel : HasFiniteConstantLocalModel (integralCoefficientRing l E) S L) :
    ∃ (_ : (closedModuleSectionsWithSupport (integralCoefficientRing l E) i j).Additive),
      Nonempty
        ((derivedHom (integralCoefficientRing l E) X).obj
            (op ((DerivedCategory.singleFunctor _ 0).obj
              ((lowerStar (integralCoefficientRing l E) i).obj
                ((openImmersionLowerShriek (integralCoefficientRing l E) v).obj L)))) ⋙
              integralStratumDerivedSections l E X ≅
          (closedModuleSectionsWithSupport (integralCoefficientRing l E) i j).rightDerivedFunctor ⋙
            (upperStar (integralCoefficientRing l E) v).mapDerivedCategory ⋙
              integralStratumDualTensor l E S L ⋙
                integralStratumDerivedSections l E S) ∧
      DerivedCategory.torAmplitudeIn _ 0 1 (integralStratumDual l E S L) ∧
      (∃ P : CochainComplex.KFlat
          (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
            (condensedRingObj (integralCoefficientRing l E) S)),
        Nonempty (DerivedCategory.Q.obj P.obj ≅ integralStratumDual l E S L) ∧
        Nonempty (DerivedCategory.Q ⋙
            integralStratumDualTensor l E S L ≅
          (curriedTensor (CochainComplex
            (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
              (condensedRingObj (integralCoefficientRing l E) S)) ℤ)).obj P.obj ⋙
              DerivedCategory.Q) ∧
        ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I],
          PreservesColimitsOfShape I
            ((curriedTensor (CochainComplex
              (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
                (condensedRingObj (integralCoefficientRing l E) S)) ℤ)).obj P.obj)) ∧
      (∀ (B : ℕᵒᵖ ⥤ CochainComplex
          (pulledBackModuleObjects (integralCoefficientRing l E) S) ℤ)
        [HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n)))]
        [HasProduct (fun n : ℕ ↦
          (integralStratumDualTensor l E S L).obj
            (DerivedCategory.Q.obj (B.obj (op n))))]
        (A : integralDerived l E S)
        (p : A ⟶ ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n))))
        (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n)))) ⟶ A⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle
          (fun n : ℕ ↦ DerivedCategory.Q.map (B.map (homOfLE (Nat.le_succ n)).op)) A p δ →
        ∃ ε : (∏ᶜ (fun n : ℕ ↦
            (integralStratumDualTensor l E S L).obj (DerivedCategory.Q.obj (B.obj (op n))))) ⟶
          ((integralStratumDualTensor l E S L).obj A) ⟦(1 : ℤ)⟧,
          IsDerivedLimitTriangle
            (fun n : ℕ ↦
              (integralStratumDualTensor l E S L).map
                (DerivedCategory.Q.map (B.map (homOfLE (Nat.le_succ n)).op)))
            ((integralStratumDualTensor l E S L).obj A)
            (Pi.lift (fun n : ℕ ↦
              (integralStratumDualTensor l E S L).map
                (p ≫ Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n))) n))) ε) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
