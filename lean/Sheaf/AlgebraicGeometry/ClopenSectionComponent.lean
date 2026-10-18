/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleOpenTensor
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# The clopen component description for a section of an open immersion

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-sf-operations,
lem-weil-pbc-clopen-section-direct-image.proof.md, disjoint-open-cover description
and displayed section formula; Stacks Project, `proetale.tex`, Tags 098K and 09AE
(blueprint: lem-sp-clopen-section-component).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

/-- The open complement of a closed-range open immersion, with the closed immersion
instance obtained canonically from its open-immersion and closed-range hypotheses.
Source: Stacks Project, Definition 098K and Weil blueprint
(blueprint: lem-sp-clopen-section-component). -/
noncomputable def clopenComplement {X V : Scheme.{u}} (s : X ⟶ V)
    [IsOpenImmersion s] (hclosed : IsClosed (Set.range s.base)) : V.Opens :=
  @openComplementOfIsClosedImmersion V X s
    (IsClosedImmersion.of_isPreimmersion s hclosed)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The inclusion of the section component of `W ×[X] V`. Its projections are
`𝟙 W` and `W.hom ≫ s`, so it identifies that component with `W` over `X`.
Source: blueprint main-20261015, clopen-section-direct-image proof, displayed section formula
(blueprint: lem-sp-clopen-section-component). -/
noncomputable def clopenSectionComponentArrow {X V : Scheme.{u}} (q : V ⟶ X)
    (s : X ⟶ V) [IsOpenImmersion s] (hsection : s ≫ q = 𝟙 X) (W : X.ProEt) :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale s)).obj W ⟶
      (proEtaleBaseChange q).obj W :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 W.left) (W.hom ≫ s)
      (by
        change (𝟙 W.left) ≫ W.hom = (W.hom ≫ s) ≫ q
        exact (Category.id_comp W.hom).trans
          ((Category.comp_id W.hom).symm.trans
            ((congrArg (fun f : X ⟶ X ↦ W.hom ≫ f) hsection).symm.trans
              (Category.assoc W.hom s q).symm))))
    (by simp) trivial

/-- Sectionwise normalization of the comparison `q_* s_! → 𝟭`. On scalar-unit
sections, after the canonical realization counit, its composite with the open unit
is precisely restriction along `W → W ×[X] V`. The open unit identifies
`s^* s_! M` with `M`. Scalar-unit sections locally generate the intrinsic module
sheaf, so this equation fixes the comparison on all sections, with no arbitrary
coefficient identification.
Source: blueprint main-20261015, clopen-section-direct-image proof, displayed section formula
(blueprint: lem-sp-clopen-section-component). -/
def ClopenSectionComparisonOnSections {X V : Scheme.{u}} (q : V ⟶ X)
    (s : X ⟶ V) [IsOpenImmersion s] (hsection : s ≫ q = 𝟙 X)
    (A : Type u) [CommRing A] [Finite A]
    (e : sfIntrinsicExtensionByZero s A ⋙ proEtaleConstantModuleDirectImage q A ⟶
      𝟭 (proEtaleRingModules X (proEtaleConstantRing X A))) : Prop :=
  ∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (W : X.ProEtᵒᵖ)
    (m : (((sfIntrinsicModuleEquivalence V A).inverse.obj
      ((sfIntrinsicExtensionByZero s A).obj M)).obj.obj
        ((proEtaleBaseChange q).op.obj W))),
    ((sfIntrinsicExtensionByZeroAdjunction s A).unit.app M).val.app W
      ((e.app M).val.app W
        (((proEtaleConstantModuleDirectImage q A).map
          ((sfIntrinsicModuleEquivalence V A).counitIso.hom.app
            ((sfIntrinsicExtensionByZero s A).obj M))).val.app W
          (sfIntrinsicRealizationUnit V A
            ((sfIntrinsicModuleEquivalence V A).inverse.obj
              ((sfIntrinsicExtensionByZero s A).obj M))
            ((proEtaleBaseChange q).op.obj W) m))) =
      sfIntrinsicRealizationUnit X A
        ((ProEtale.openImmersionRestriction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) s).obj
            ((sfIntrinsicModuleEquivalence V A).inverse.obj
              ((sfIntrinsicExtensionByZero s A).obj M))) W
        ((((sfIntrinsicModuleEquivalence V A).inverse.obj
          ((sfIntrinsicExtensionByZero s A).obj M)).obj.map
            (clopenSectionComponentArrow q s hsection W.unop).op) m)

/-- For a clopen section, module sheaves, complexes, K-injectives and direct images split
into the section component and its open complement.
Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-sf-operations,
lem-weil-pbc-clopen-section-direct-image.proof.md, disjoint-open-cover description
and displayed section formula; Stacks Project, `proetale.tex`, Tags 098K and 09AE
(blueprint: lem-sp-clopen-section-component).

Proof plan, following all eight DAG steps:
1. Open-immersion base change splits every test object into the section and complementary
   opens. Weakly-etale base change and localization identify their pro-etale sites
   (`lem-weil-pbc-open-immersion-base-change`,
   `lem-weil-pbc-weakly-etale-composition-base-change`,
   `lem-weil-proetale-weakly-etale-localization`, `sk-def-pe-site`).
2. The sheaf equalizer for this two-open cover gives the sectionwise product decomposition:
   cross intersections are empty and the empty-cover condition gives zero sections there.
   The restriction maps are additive, linear, and natural (`def-weil-pbc-sites-and-cohomology`).
3. Glue a pair by `G(M,N)(W) = M(W_X) × N(W_Z)` with scalar action through coefficient
   restrictions. Matching families glue coordinatewise. Restriction and gluing are inverse
   on objects and morphisms (`def-weil-sheaf-of-modules-category`).
4. Kernels and cokernels in the product are coordinatewise. The equivalence preserves
   their universal properties, hence is exact; so are both coordinate restrictions.
5. In the product, insertion `(M,0)` is left adjoint to the first restriction. Uniqueness
   of left adjoints identifies the recorded extension by zero with that insertion, and its
   unit with the canonical component identification (`lem-weil-extension-by-zero-adjunction`).
6. Apply the additive equivalence in every integer degree. Differentials, chain maps,
   kernels/images and homotopy equations are componentwise; thus acyclicity and homotopies
   are componentwise (`def-pc-cochain-complex-modules`, `def-pc-acyclic-complex-modules`).
7. A map from an acyclic complex to the inserted K-injective has components `(a_X,0)`.
   A null homotopy of `a_X` extends by the zero homotopy on the complement. This proves
   K-injectivity without a degree bound (`def-pur-kinjective-complex`).
8. For `W → X`, direct image evaluates at `W ×[X] V`. The section component is `W`
   since `s ≫ q = 𝟙 X`. Restrict along `clopenSectionComponentArrow`, then use the inverse
   open unit. This is exactly `ClopenSectionComparisonOnSections`: the realization
   counit and scalar-unit maps express the same restriction in intrinsic coefficients.
   The coefficient composite is the identity on constant sections and hence on the
   sheafification, so the map is linear. Restriction and maps of sheaves commute with
   it, giving the natural isomorphism (`def-weil-proetale-module-direct-image`). Apply
   that same map in every degree; its naturality gives the differential, chain-map
   and degree-minus-one homotopy compatibilities displayed in the conclusion.
-/
theorem clopenSectionComponent {X V : Scheme.{u}} (q : V ⟶ X) (s : X ⟶ V)
    [IsOpenImmersion s] (hclosed : IsClosed (Set.range s.base))
    (hsection : s ≫ q = 𝟙 X) (A : Type u) [CommRing A] [Finite A] :
    ((Functor.prod'
        (sfIntrinsicOpenRestriction s A)
        (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A)).IsEquivalence ∧
      PreservesFiniteLimits
        (Functor.prod'
          (sfIntrinsicOpenRestriction s A)
          (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A)) ∧
      PreservesFiniteColimits
        (Functor.prod'
          (sfIntrinsicOpenRestriction s A)
          (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A))) ∧
      (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)),
        Nonempty
          ((Functor.prod'
              (sfIntrinsicOpenRestriction s A)
              (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A)).obj
            ((sfIntrinsicExtensionByZero s A).obj M) ≅
            ((M, 0) :
              proEtaleRingModules X (proEtaleConstantRing X A) ×
                proEtaleRingModules (clopenComplement s hclosed).toScheme
                  (proEtaleConstantRing (clopenComplement s hclosed).toScheme A)))) ∧
      (Functor.prod'
        ((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ))
        ((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
          (.up ℤ))).IsEquivalence ∧
      (∀ (K : CochainComplex
          (proEtaleRingModules V (proEtaleConstantRing V A)) ℤ),
        HomologicalComplex.Acyclic K ↔
          (HomologicalComplex.Acyclic
              (((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ)).obj K) ∧
            HomologicalComplex.Acyclic
              (((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
                (.up ℤ)).obj K))) ∧
      (∀ {E F : CochainComplex
          (proEtaleRingModules V (proEtaleConstantRing V A)) ℤ} (f g : E ⟶ F),
        Nonempty (Homotopy f g) ↔
          (Nonempty (Homotopy
              (((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ)).map f)
              (((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ)).map g)) ∧
            Nonempty (Homotopy
              (((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
                (.up ℤ)).map f)
              (((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
                (.up ℤ)).map g)))) ∧
      (∀ (I : CochainComplex
          (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ),
        CochainComplex.IsKInjective I →
          CochainComplex.IsKInjective
            (((sfIntrinsicExtensionByZero s A).mapHomologicalComplex (.up ℤ)).obj I)) ∧
      (∃ e : sfIntrinsicExtensionByZero s A ⋙ proEtaleConstantModuleDirectImage q A ≅
          𝟭 (proEtaleRingModules X (proEtaleConstantRing X A)),
        ClopenSectionComparisonOnSections q s hsection A e.hom ∧
        ∃ eC : (sfIntrinsicExtensionByZero s A).mapHomologicalComplex (.up ℤ) ⋙
            (proEtaleConstantModuleDirectImage q A).mapHomologicalComplex (.up ℤ) ≅
          𝟭 (CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ),
          (∀ (K : CochainComplex
              (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ) (n : ℤ),
            (eC.hom.app K).f n = e.hom.app (K.X n)) ∧
          (∀ {E F : CochainComplex
              (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ} (f : E ⟶ F),
            ((sfIntrinsicExtensionByZero s A).mapHomologicalComplex (.up ℤ) ⋙
                (proEtaleConstantModuleDirectImage q A).mapHomologicalComplex (.up ℤ)).map f ≫
              eC.hom.app F = eC.hom.app E ≫ f) ∧
          (∀ {E F : CochainComplex
              (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ}
              {f g : E ⟶ F} (h : Homotopy f g) (i j : ℤ),
            (sfIntrinsicExtensionByZero s A ⋙ proEtaleConstantModuleDirectImage q A).map
                (h.hom i j) ≫ e.hom.app (F.X j) =
              e.hom.app (E.X i) ≫ h.hom i j)) := by
  sorry

end AlgebraicGeometry.Scheme
