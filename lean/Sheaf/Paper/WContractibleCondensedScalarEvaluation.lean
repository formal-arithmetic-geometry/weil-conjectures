/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.CondensedScalarRealization
import Sheaf.Paper.CondensedPointBasisEvaluation
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsDerived
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
import Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsExact
import WeilConjectures.RingTheory.ProEtale.WContractible

/-!
# Condensed scalar extension on w-contractible affines

Source: Hemo–Richarz–Scholbach, Section 3, equations (3.1), (3.2), Remark 3.2;
Lemma 4.1(1), Proposition 4.3(1)
(blueprint: lem-zl-wcontractible-condensed-scalar-evaluation).

The scalar ring, canonical scalar map and scalar realization are imported from
`Sheaf.AlgebraicGeometry.CondensedScalarRealization`. The only coefficient transport
is the existing equivalence between internal and sectionwise module sheaves.

## Main definitions

- `condensedCoefficientRing`: section rings of the recorded internal coefficient object.
- `condensedSectionModuleTransport`: the existing module equivalence on derived categories.
- `condensedDerivedSections`: the existing unbounded K-injective section functor.
- `scalarAffineComponents`: the actual profinite component quotient.

## Main statements

- `wContractible_condensed_scalar_evaluation`: coefficient and derived comparisons,
  naturality on D(R), and t-exactness of derived sections on the affine.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u wS wB
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Section rings of the existing internal coefficient pullback Λ_X.
Source: HRS, Section 3; Stacks, Tag 00YV
(blueprint: lem-zl-wcontractible-condensed-scalar-evaluation). -/
abbrev condensedCoefficientRing (X : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (condensedRingObj.{u} Λ X))

/-- The existing exact internal/sectionwise module equivalence, localized termwise.
This changes only the presentation of modules, not the scalar realization.
Source: Stacks, Tag 00YV; HRS, equation (3.1)
(blueprint: lem-zl-wcontractible-condensed-scalar-evaluation). -/
def condensedSectionModuleTransport (X : Scheme.{u})
    [HasDerivedCategory.{wS} (SheafOfModules.{u + 1} (condensedCoefficientRing Λ X))] :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj.{u} Λ X)) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (condensedCoefficientRing Λ X)) :=
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj.{u} Λ X)
  haveI := Functor.additive_of_preserves_binary_products e.functor
  e.functor.mapDerivedCategory

/-- Unbounded derived sections at a site object, defined by the existing K-injective
right-derived construction. This is RΓ(U,-|_U): restriction to the slice followed by
sections has precisely this sectionwise evaluation functor.
Source: HRS, Section 3, equation (3.2)
(blueprint: lem-zl-wcontractible-condensed-scalar-evaluation). -/
def condensedDerivedSections (X : Scheme.{u}) (U : X.ProEt)
    [HasDerivedCategory.{wS} (SheafOfModules.{u + 1} (condensedCoefficientRing Λ X))]
    [HasDerivedCategory.{wB}
      (ModuleCat.{u + 1} ((condensedCoefficientRing Λ X).obj.obj (op U)))] :
    DerivedCategory (SheafOfModules.{u + 1} (condensedCoefficientRing Λ X)) ⥤
      DerivedCategory (ModuleCat.{u + 1}
        ((condensedCoefficientRing Λ X).obj.obj (op U))) :=
  haveI := Scheme.ProEt.moduleEvaluation_additive.{u, u + 1, 0}
    X (condensedCoefficientRing Λ X) U
  Functor.rightDerivedFunctorOfQuasiIsoResolutions
    (SheafOfModules.evaluation.{u + 1} (condensedCoefficientRing Λ X) (op U))
      (Scheme.ProEt.moduleQuasiIsoKInjectiveResolutions.{u, u + 1, 0}
        X (condensedCoefficientRing Λ X))

/-- The component quotient of an affine scheme, with its quotient topology.
Source: HRS, Proposition 4.3; Bhatt–Scholze, Lemma 2.4.8
(blueprint: lem-zl-wcontractible-condensed-scalar-evaluation). -/
def scalarAffineComponents (A : Type u) [CommRing A] : Profinite.{u} :=
  Profinite.of (ConnectedComponents (PrimeSpectrum A))

/-- The scalar map R = Λ(*) → Λ(S) induced by the unique map S → *.
Source: HRS, Definition 3.5 (blueprint: lem-zl-wcontractible-condensed-scalar-evaluation). -/
def condensedComponentScalar (A : Type u) [CommRing A] :
    condensedScalarRing Λ ⟶ (condensedSectionRing Λ).obj.obj (op (scalarAffineComponents A)) :=
  (condensedSectionRing Λ).obj.map (terminal.from (scalarAffineComponents A)).op

/-- Evaluation of the actual coefficient section-ring sheaf on a site object.
Source: HRS, Proposition 4.3(1)
(blueprint: lem-zl-wcontractible-condensed-scalar-evaluation). -/
abbrev scalarCoefficientEvaluation (X : Scheme.{u}) (U : X.ProEt) :=
  (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj.{u} Λ X)).obj.obj (op U)

/-- Evaluation of the existing condensed section-ring sheaf on the component quotient.
Source: HRS, Proposition 4.3(1)
(blueprint: lem-zl-wcontractible-condensed-scalar-evaluation). -/
abbrev scalarComponentEvaluation (A : Type u) [CommRing A] :=
  (condensedSectionRing Λ).obj.obj (op (scalarAffineComponents A))

/-- Additivity of the prescribed ordinary scalar extension, at the explicit module size.
It follows directly from its actual extension/restriction adjunction.
Source: HRS, Remark 3.2; Stacks, Tag 06YY
(blueprint: lem-zl-wcontractible-condensed-scalar-evaluation). -/
instance condensedComponentExtension_additive (A : Type u) [CommRing A] :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (condensedComponentScalar Λ A).hom).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1}
    (condensedComponentScalar Λ A).hom).left_adjoint_additive

universe wV wBV wBT

/-- Evaluation of ordinary condensed scalar extension on a w-contractible affine,
with no t-admissibility hypothesis. The coefficients are the recorded internal ring objects.
The existing scalar realization is used without a second construction.
The universal left-derived pair E, ε means ordinary derived tensor over R;
the comparison is a natural isomorphism on all of D(R), without boundedness.
The last two clauses give both halves of t-exactness of RΓ(V,-).

Source: Hemo–Richarz–Scholbach, equations (3.1), (3.2), Remark 3.2,
Lemma 4.1(1), Proposition 4.3(1); Bhatt–Scholze, Lemma 2.4.8
(blueprint: lem-zl-wcontractible-condensed-scalar-evaluation).

Proof for stage 3:
1. The geometric w-contractibility of Spec A gives weak contractibility of the site
object (lem-weil-pbc-source-affine-wcontractible-evaluation). Apply
lem-weil-pbc-condensed-point-basis-evaluation on T and V to identify coefficient
sections with Λ(pi_0 V). The comparison respects R because restriction along S → *
defines constants. IsWContractibleRing supplies extremal disconnectedness.
2. det-pe-wc-sections-exact makes evaluation exact, and det-pe-wc-sections-derived
computes its unbounded right derived functor termwise. Kernels and images are preserved,
so H^n Γ(V,C) = Γ(V,H^n C). Thus both cohomological truncation bounds are preserved.
lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits also gives all colimits.
3. For an R-module M, the scalar-extension/sections comparison sends m tensor b to
b times (1 tensor the constant section m). Both functors preserve coproducts and
cokernels: use lem-weil-pbc-ringed-topoi-module-adjunction for scalar extension,
and step 2 for evaluation. It is the identity on R, hence an isomorphism on free
modules, and then on every module by a free presentation. No flatness of Λ(S) is used.
4. Use lem-pc-kflat-resolution on the point to represent Q by a K-flat complex P
with flat terms. lem-weil-pbc-ringed-pullback-preserves-kflat applies to exact constant
realization (def-sfb-site-derived-constant-module-functor). By
lem-pur-derived-change-of-rings, termwise ordinary scalar extension of the constant
complex P represents L_T(Q); P tensor Λ(S) represents Q tensor^L_R Λ(S).
5. Step 3 is natural for every differential of P, so yields a chain isomorphism from
P tensor Λ(S) to sections of L_T(P). Step 2 computes derived sections by those sections.
The chain formula commutes with chain maps; lem-weil-pbc-site-derived-tensor-descent
and the universal counits descend it to a natural isomorphism on all of D(R).
6. lem-weil-proetale-weakly-etale-localization identifies the slice at V with V_proet.
def-weil-pbc-ringed-derived-restriction evaluates there on the same complexes, and
def-sfb-alpha-bundled identifies restricted coefficients with Λ_V. Hence the first
functor in the comparison is exactly RΓ(V,L_T(-)|_V). None of these steps uses
t-admissibility or boundedness. -/
theorem wContractible_condensed_scalar_evaluation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (T : Scheme.{u})
    (A : Type u) [CommRing A] [IsWContractibleRing A]
    (f : Spec (CommRingCat.of A) ⟶ T) [WeaklyEtale f]
    [HasDerivedCategory.{wS} (SheafOfModules.{u + 1} (condensedCoefficientRing Λ T))]
    [HasDerivedCategory.{wV} (SheafOfModules.{u + 1}
      (condensedCoefficientRing Λ (Spec (CommRingCat.of A))))]
    [HasDerivedCategory.{wBT} (ModuleCat.{u + 1}
      ((condensedCoefficientRing Λ T).obj.obj (op (Scheme.ProEt.mk f))))]
    [HasDerivedCategory.{wBV} (ModuleCat.{u + 1}
      ((condensedCoefficientRing Λ (Spec (CommRingCat.of A))).obj.obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (CommRingCat.of A)))))))]
    [HasDerivedCategory.{wB} (ModuleCat.{u + 1} (scalarComponentEvaluation Λ A))] :
    ∃ (eT : scalarCoefficientEvaluation Λ T (Scheme.ProEt.mk f) ≅
        scalarComponentEvaluation Λ A)
      (eV : scalarCoefficientEvaluation Λ (Spec (CommRingCat.of A))
        (Scheme.ProEt.mk (𝟙 (Spec (CommRingCat.of A)))) ≅ scalarComponentEvaluation Λ A),
      (∃ (E : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)) ⥤
          DerivedCategory (ModuleCat.{u + 1} (scalarComponentEvaluation Λ A)))
        (ε : DerivedCategory.Q ⋙ E ⟶
          (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
            (condensedComponentScalar Λ A).hom).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
        E.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (.up ℤ)) ∧
        Nonempty (condensedScalarRealization Λ T ⋙ condensedSectionModuleTransport Λ T ⋙
          condensedDerivedSections Λ T (Scheme.ProEt.mk f) ⋙
          Functor.mapDerivedCategory.{wBT, wB}
            (C₁ := ModuleCat.{u + 1}
              ((condensedCoefficientRing Λ T).obj.obj (op (Scheme.ProEt.mk f))))
            (C₂ := ModuleCat.{u + 1} (scalarComponentEvaluation Λ A))
            (ModuleCat.restrictScalars.{u + 1} eT.inv.hom) ≅ E)) ∧
      (∀ (M : DerivedCategory (SheafOfModules.{u + 1}
          (condensedCoefficientRing Λ (Spec (CommRingCat.of A))))) (n : ℤ),
        M.IsLE n → ((condensedDerivedSections Λ (Spec (CommRingCat.of A))
          (Scheme.ProEt.mk (𝟙 (Spec (CommRingCat.of A)))) ⋙
          Functor.mapDerivedCategory.{wBV, wB}
            (C₁ := ModuleCat.{u + 1}
              ((condensedCoefficientRing Λ (Spec (CommRingCat.of A))).obj.obj
                (op (Scheme.ProEt.mk (𝟙 (Spec (CommRingCat.of A)))))))
            (C₂ := ModuleCat.{u + 1} (scalarComponentEvaluation Λ A))
            (ModuleCat.restrictScalars.{u + 1} eV.inv.hom)).obj M).IsLE n) ∧
      (∀ (M : DerivedCategory (SheafOfModules.{u + 1}
          (condensedCoefficientRing Λ (Spec (CommRingCat.of A))))) (n : ℤ),
        M.IsGE n → ((condensedDerivedSections Λ (Spec (CommRingCat.of A))
          (Scheme.ProEt.mk (𝟙 (Spec (CommRingCat.of A)))) ⋙
          Functor.mapDerivedCategory.{wBV, wB}
            (C₁ := ModuleCat.{u + 1}
              ((condensedCoefficientRing Λ (Spec (CommRingCat.of A))).obj.obj
                (op (Scheme.ProEt.mk (𝟙 (Spec (CommRingCat.of A)))))))
            (C₂ := ModuleCat.{u + 1} (scalarComponentEvaluation Λ A))
            (ModuleCat.restrictScalars.{u + 1} eV.inv.hom)).obj M).IsGE n) := by
  sorry

end AlgebraicGeometry.ProEtale
