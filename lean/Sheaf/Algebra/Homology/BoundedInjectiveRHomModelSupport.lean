/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q92
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.Algebra.Homology.HomComplex
public import Sheaf.Algebra.Homology.ModuleHomPrecompHomotopy
public import Sheaf.Paper.RingComplexGodementConstruction
public import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap

/-! # Bounded injective models and upper support of derived Hom

Source: Stacks Project, dualizing.tex, Tag 0G4H,
lemma-finite-ext-into-bounded-injective, proof; sites-cohomology.tex, Tags 08J7,
0A95 and 0A8X (blueprint: lem-trf-bounded-injective-rhom-model-support).

Ordinary module complexes are embedded by the existing constant-module functor
on the one-object identity-covering site. Its derived category is the specified
presentation of D(A). The complex comparison is normalized on every Hom coordinate;
the derived comparison is normalized by the fixed K-injective resolution unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The existing constant-module embedding applied termwise.
Source: Stacks, Tag 0A8X, evaluated on the one-object site
(blueprint: lem-trf-bounded-injective-rhom-model-support). -/
abbrev ringModuleComplex (A : Type u) [CommRing A] :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (RingSiteModules A) ℤ := by
  letI := AlgebraicGeometry.ringComplexConstant_additive (CommRingCat.of A)
  exact (AlgebraicGeometry.ringComplexConstant (CommRingCat.of A)).mapHomologicalComplex (.up ℤ)

/-- The actual fixed K-injective resolution unit applied inside the sheaf Hom complex.
Source: Stacks, Tags 08J7 and 0A95
(blueprint: lem-trf-bounded-injective-rhom-model-support). -/
def ringHomResolutionMap {A : Type u} [CommRing A]
    (L K : CochainComplex (RingSiteModules A) ℤ) :
    homComplex (R := CochainComplex.onePointRingSheaf A) L K ⟶
      homComplex (R := CochainComplex.onePointRingSheaf A) L
        ((CochainComplex.kInjectiveResolutionFunctor.{u} (RingSiteModules A)).obj K) :=
  ((homComplexFunctor (R := CochainComplex.onePointRingSheaf A)).obj (op L)).map
    ((CochainComplex.toKInjectiveResolution.{u} (RingSiteModules A)).app K)

/-- The localization factorization comparison for exactly the fixed resolution used
by the recorded derived internal Hom, with no choice of an objectwise isomorphism.
Source: Stacks, Tag 08J7 and derived.tex, Tag 05RN
(blueprint: lem-trf-bounded-injective-rhom-model-support). -/
def ringHomResolutionComparison {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (RingSiteModules A)]
    (L K : CochainComplex (RingSiteModules A) ℤ) :
    (derivedInternalHomOfUniverses.{u, u, u, w} ⊥
      (CochainComplex.onePointRingSheaf A)).obj
        (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (homComplex (R := CochainComplex.onePointRingSheaf A) L
          ((CochainComplex.kInjectiveResolutionFunctor.{u} (RingSiteModules A)).obj K)) :=
  (Localization.fac
    ((𝟭 _).prod (CochainComplex.kInjectiveResolutionFunctor.{u} (RingSiteModules A)) ⋙
      Functor.uncurry.obj (homComplexFunctor (R := CochainComplex.onePointRingSheaf A)) ⋙
        DerivedCategory.Q)
    (derivedInternalHomOfUniverses_inverts.{u, u, u, w} ⊥
      (CochainComplex.onePointRingSheaf A) _
      (CochainComplex.toKInjectiveResolution.{u} (RingSiteModules A))
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u}
        (RingSiteModules A) M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u}
          (RingSiteModules A) M⟩))
    (DerivedCategory.Q.op.prod DerivedCategory.Q)).app (op L, K)

/-- A bounded injective target computes module-valued derived Hom, naturally in the
source, with zero terms and zero derived cohomology above the difference of bounds.
The coordinate equation specifies the identity comparison between the sheaf and
module Hom complexes. The resolution equation specifies the canonical theta:
theta = (localization of the identity comparison) composed with the inverse of
the Hom map induced by the fixed resolution unit and the localization comparison.
Source: Stacks, dualizing.tex, Tag 0G4H, proof; sites-cohomology.tex, Tags 0A8X,
08J7 and 0A95; derived.tex, Tag 070J
(blueprint: lem-trf-bounded-injective-rhom-model-support).

Proof:
1. On the one-object site every restriction is the identity. Evaluating each
   projection of def-pur-hom-complex gives the linear maps M^p -> I^(p+r).
   These are exactly def-sc-module-total-hom-complex, with the same signed
   differential and componentwise A-action. This defines e and its coordinate formula.
2. The lower support bound a and termwise injectivity imply K-injectivity by
   lem-weil-pbc-bounded-below-injectives-kinjective. The fixed resolution unit is
   a quasi-isomorphism between K-injectives. Applying lem-pur-rhom-well-defined
   and localizing makes ringHomResolutionMap invertible. Compose the localization
   comparison with its inverse and Q(e). This gives theta and its normalization.
3. Precomposition commutes componentwise with postcomposition by that unit.
   The localization comparison is natural by def-pur-derived-internal-hom.
   Multiplying the resulting square by the inverted resolution maps proves
   the asserted naturality for every chain map, without a quasi-isomorphism assumption.
4. For r > b-n, each factor Hom(M^p,I^(p+r)) is zero: if p<n its source is zero,
   otherwise p+r>b and its target is zero. The product term is therefore zero.
   Its cohomology is zero by def-weil-abstract-derived-category, and applying
   cohomology to theta proves the derived cohomology bound. No finiteness is used.
-/
theorem boundedInjective_rhom_model_support
    (A : Type u) [CommRing A] [HasDerivedCategory.{w} (RingSiteModules A)]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) (hab : a ≤ b)
    (hI : ∀ q : ℤ, Injective (I.X q))
    (hIb : ∀ q : ℤ, q < a ∨ b < q → IsZero (I.X q)) :
    ∃ (e : ∀ M : CochainComplex (ModuleCat.{u} A) ℤ,
        homComplex (R := CochainComplex.onePointRingSheaf A)
          ((ringModuleComplex A).obj M) ((ringModuleComplex A).obj I) ≅
            (ringModuleComplex A).obj (CochainComplex.moduleHomComplex M I))
      (θ : ∀ M : CochainComplex (ModuleCat.{u} A) ℤ,
        (derivedInternalHomOfUniverses.{u, u, u, w} ⊥
          (CochainComplex.onePointRingSheaf A)).obj
            (op (DerivedCategory.Q.obj ((ringModuleComplex A).obj M)),
              DerivedCategory.Q.obj ((ringModuleComplex A).obj I)) ≅
          DerivedCategory.Q.obj
            ((ringModuleComplex A).obj (CochainComplex.moduleHomComplex M I))),
      (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (r p : ℤ)
        (z : (homComplex (R := CochainComplex.onePointRingSheaf A)
          ((ringModuleComplex A).obj M) ((ringModuleComplex A).obj I)).X r |>.val.obj
            (op ⟨PUnit.unit⟩)) (x : M.X p),
        (((e M).hom.f r).val.app (op ⟨PUnit.unit⟩) z).v p (p + r) rfl x =
          ringHomEvaluate ((ringModuleComplex A).obj M) ((ringModuleComplex A).obj I)
            r p (op ⟨PUnit.unit⟩) z x) ∧
      (∀ M : CochainComplex (ModuleCat.{u} A) ℤ,
        (θ M).hom ≫ DerivedCategory.Q.map (e M).inv ≫
          DerivedCategory.Q.map (ringHomResolutionMap
            ((ringModuleComplex A).obj M) ((ringModuleComplex A).obj I)) =
          (ringHomResolutionComparison
            ((ringModuleComplex A).obj M) ((ringModuleComplex A).obj I)).hom) ∧
      (∀ (M' M : CochainComplex (ModuleCat.{u} A) ℤ) (f : M' ⟶ M),
        (θ M).hom ≫ DerivedCategory.Q.map
          ((ringModuleComplex A).map (CochainComplex.moduleHomPrecomp I f)) =
        (derivedInternalHomOfUniverses.{u, u, u, w} ⊥
          (CochainComplex.onePointRingSheaf A)).map
            ((DerivedCategory.Q.map ((ringModuleComplex A).map f)).op,
              𝟙 (DerivedCategory.Q.obj ((ringModuleComplex A).obj I))) ≫ (θ M').hom) ∧
      (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ),
        (∀ p : ℤ, p < n → IsZero (M.X p)) →
        ∀ r : ℤ, b - n < r →
          IsZero ((CochainComplex.moduleHomComplex M I).X r) ∧
          IsZero ((DerivedCategory.homologyFunctor (RingSiteModules A) r).obj
            ((derivedInternalHomOfUniverses.{u, u, u, w} ⊥
              (CochainComplex.onePointRingSheaf A)).obj
                (op (DerivedCategory.Q.obj ((ringModuleComplex A).obj M)),
                  DerivedCategory.Q.obj ((ringModuleComplex A).obj I))))) := by
  sorry

end CategoryTheory
