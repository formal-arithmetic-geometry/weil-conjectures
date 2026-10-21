/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.AlgebraicGeometry.ProEtaleStalkConservative
import Sheaf.Paper.ProEtaleLisseFiniteModelsFromLisse
import Sheaf.AlgebraicGeometry.ProEtalePullbackLocallyConstant
import Sheaf.Paper.ProEtaleFiniteModelStalks

/-! # Internal Hom from a finite local system over a finite field

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.7.13,
finite-coefficient local-system case; Stacks Project, Tag 0FNY, example-dual
(blueprint: lem-sfb-finite-field-lisse-internal-hom).

The two functors below spell out the two sides of the cohomology formula, including
all maps. The theorem asserts bounded constructibility in the original interval and
an isomorphism natural contravariantly in the local system and covariantly in the complex.
All derived categories are the ordinary, uncompleted localizations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- The existing locally bijective criterion in the fixed finite-coefficient universe.
This specializes the general coefficient-universe instance explicitly, so that an
unrelated completed-coefficient instance cannot leave a free universe metavariable.
Source: Stacks Project, Modules on Sites, Section 03DA
(blueprint: lem-sfb-finite-field-lisse-internal-hom). -/
instance finiteFieldInternalHom_locallyBijective (S : Scheme.{u}) :
    (ProEt.topology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}


/-- The bifunctor `(L,N) ↦ H^r RHom(L[0],N)` on the ordinary constant-ring module
category. The first variable is contravariant. Source: the K-injective construction
in Stacks, Cohomology on Sites, Section 08J7
(blueprint: lem-sfb-finite-field-lisse-internal-hom). -/
def finiteFieldInternalHomCohomology (S : Scheme.{u}) (A : Type u) [Field A] (r : ℤ) :
    (proEtaleRingModules S (proEtaleConstantRing S A))ᵒᵖ ×
      DerivedCategory.{u + 2} (proEtaleRingModules S (proEtaleConstantRing S A)) ⥤
        proEtaleRingModules S (proEtaleConstantRing S A) :=
  ((DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2}
      (proEtaleRingModules S (proEtaleConstantRing S A)) 0).op.prod
    (𝟭 (DerivedCategory.{u + 2} (proEtaleRingModules S (proEtaleConstantRing S A))))) ⋙
    derivedInternalHomOfUniverses.{u + 1, u, u + 1, u + 2}
      (ProEt.topology S) (proEtaleConstantRing S A) ⋙
    DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2}
      (proEtaleRingModules S (proEtaleConstantRing S A)) r

/-- The bifunctor `(L,N) ↦ Hom(L,A_S) ⊗ H^r(N)`, using the existing sheaf Hom and
sheafification tensor product; its first variable acts by precomposition.
Source: Stacks Project, Tag 0FNY, example-dual, finite-free evaluation formula
(blueprint: lem-sfb-finite-field-lisse-internal-hom). -/
def finiteFieldDualTensorCohomology (S : Scheme.{u}) (A : Type u) [Field A] (r : ℤ) :
    (proEtaleRingModules S (proEtaleConstantRing S A))ᵒᵖ ×
      DerivedCategory.{u + 2} (proEtaleRingModules S (proEtaleConstantRing S A)) ⥤
        proEtaleRingModules S (proEtaleConstantRing S A) :=
  (((SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1}
      (proEtaleConstantRing S A)).flip.obj
        (SheafOfModules.unit ((sheafCompose (ProEt.topology S)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing S A)))).prod
    (DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2}
      (proEtaleRingModules S (proEtaleConstantRing S A)) r)) ⋙
      Functor.uncurry.obj
        (curriedTensor (proEtaleRingModules S (proEtaleConstantRing S A)))

/-- Internal Hom from a finite-dimensional local system preserves constructible
cohomology and the same finite cohomological interval. The second conjunct supplies
cohomology isomorphisms natural in both variables on the full subcategory of pairs
consisting of a finite local system and a bounded constructible complex.

Source: Bhatt--Scholze, Lemma 6.7.13, finite-coefficient local-system case;
Stacks Project, Tag 0FNY, example-dual
(blueprint: lem-sfb-finite-field-lisse-internal-hom).

Proof:
1. On the given pro-etale covering, choose a basis of each finite-dimensional model
of L. Both L and its sheaf dual are finite free on that slice. Evaluation identifies
Hom(L,M) with L dual tensor M: the inverse sends f to the sum of the dual basis
vectors tensor f evaluated on the basis. These mutually inverse maps glue and are
natural in both variables. Restriction commutes with tensor by
lem-sfb-proetale-object-inverse-image-restriction and
lem-weil-pbc-ringed-topoi-module-pullback-tensor. Rank zero uses empty sums.
2. Hom(L,-) is exact: slice restriction is exact by
lem-pur-site-restriction-module-adjunction-exact and the local functor is a finite
direct sum. Its kernel, homology and cokernel vanish after restriction to the
cover, hence globally by clause 1 of lem-cbc-proetale-stalk-conservative and the
slice comparison lem-sfb-proetale-object-inverse-image-restriction.
3. Compute ambient RHom using a K-injective representative I of N. Since L is in
degree zero, the Hom complex is Hom(L,I), with the differential induced by I.
Exactness commutes with kernels, images and their quotient, giving
H^r RHom(L,N) = Hom(L,H^r N). Apply the evaluation inverse from step 1. All
comparisons are functorial, so the resulting isomorphisms are natural in L and N.
4. Use the finite constructible stratification of each H^r N. On each stratum,
lem-sf-proetale-lisse-finite-models gives finite constant models. Pull the finite
dual models back to that stratum by lem-exc-proetale-pullback-locally-constant.
The tensor comparison lem-weil-pbc-ringed-topoi-module-pullback-tensor and the
slice comparison identify their tensor on the common covering with a finite direct
sum of the second constant model. Thus it has finite constant models, and
lem-weil-pbc-proetale-finite-model-stalks gives finite geometric stalks. This proves
constructibility on the original stratification.
5. Outside [a,b], H^r N is zero and its tensor with the dual is zero. This proves
the same interval and bounded constructibility. Empty S, zero L or N, and a=b
are included in this calculation. -/
theorem finiteField_lisse_internalHom
    (S : Scheme.{u}) [IsLocallyNoetherian S] [CompactSpace S]
    (A : Type u) [Field A] [Finite A] :
    (∀ (L : proEtaleRingModules S (proEtaleConstantRing S A)),
      IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
        (fun M ↦ Module.Finite (ULift.{u + 1, u} A) M) L →
      ∀ (a b : ℤ), a ≤ b →
      ∀ (N : DerivedCategory.{u + 2} (proEtaleRingModules S (proEtaleConstantRing S A))),
        (∀ r : ℤ, IsConstructibleProEtaleModuleSheaf S A
          ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ r).obj N)) →
        (∀ r : ℤ, r < a ∨ b < r →
          IsZero ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2}
      (proEtaleRingModules S (proEtaleConstantRing S A)) r).obj N)) →
        ∀ r : ℤ,
          IsConstructibleProEtaleModuleSheaf S A
            ((finiteFieldInternalHomCohomology S A r).obj (op L, N)) ∧
          (r < a ∨ b < r →
            IsZero ((finiteFieldInternalHomCohomology S A r).obj (op L, N)))) ∧
    ∀ r : ℤ, Nonempty (
      (ObjectProperty.ι (fun P :
          (proEtaleRingModules S (proEtaleConstantRing S A))ᵒᵖ ×
            DerivedCategory.{u + 2} (proEtaleRingModules S (proEtaleConstantRing S A)) ↦
        IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
          (fun M ↦ Module.Finite (ULift.{u + 1, u} A) M) P.1.unop ∧
        (∀ q : ℤ, IsConstructibleProEtaleModuleSheaf S A
          ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ q).obj P.2)) ∧
        ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
          IsZero ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ q).obj P.2))) ⋙
            finiteFieldInternalHomCohomology S A r ≅
      (ObjectProperty.ι (fun P :
          (proEtaleRingModules S (proEtaleConstantRing S A))ᵒᵖ ×
            DerivedCategory.{u + 2} (proEtaleRingModules S (proEtaleConstantRing S A)) ↦
        IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
          (fun M ↦ Module.Finite (ULift.{u + 1, u} A) M) P.1.unop ∧
        (∀ q : ℤ, IsConstructibleProEtaleModuleSheaf S A
          ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ q).obj P.2)) ∧
        ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
          IsZero ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ q).obj P.2))) ⋙
            finiteFieldDualTensorCohomology S A r) := by
  sorry

end AlgebraicGeometry.Scheme
