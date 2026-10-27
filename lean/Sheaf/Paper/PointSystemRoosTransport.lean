/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Paper.PointSystemRoosTransportData

import Sheaf.Paper.PointSystemRoosComparisonAssembly
import Sheaf.Paper.PointSystemRoosRestrictionAssembly
import Sheaf.Paper.PointSystemRoosTransportRepresentative

/-! Whole-Roos transport assembled from canonical comparisons and strict restriction. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.pointReductionModuleDerived
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard

universe t u a b a' b'
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointSystemRoos

variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] roosF

private theorem comparison_transport
    {C₀ : Type a} {C₁ : Type b} {C₂ : Type a'} {C₃ : Type b'}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    {V W : C₀} {F : C₀ ⥤ C₁} {H : C₀ ⥤ C₂} {R : C₁ ⥤ C₃} {Q : C₂ ⥤ C₃}
    (θ : F ⋙ R ≅ H ⋙ Q) (u : V ⟶ W) {A B : C₁}
    (α : A ≅ F.obj V) (β : B ≅ F.obj W) (I : A ⟶ B)
    (hI : I ≫ β.hom = α.hom ≫ F.map u) :
    R.map α.inv ≫ R.map I ≫ R.map β.hom ≫ θ.hom.app W =
      θ.hom.app V ≫ Q.map (H.map u) := by
  rw [← R.map_comp_assoc, ← R.map_comp_assoc, Category.assoc, hI,
    Iso.inv_hom_id_assoc]
  exact θ.hom.naturality u

/-- Whole-Roos normalization of point-system transport and sections, with no restrictions
on the realized ambient object. All comparisons and the transport equality concern whole
towers and are natural for every morphism in the ordinary unbounded derived category.

Source: literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-d-weil/
prop-trf-rational-frobenius-integral-model.proof.md, (3), integral maps as derived limits;
agent-formulated whole-cone refinement; Stacks Tag 0941
(blueprint: lem-trf-point-system-roos-transport).

Proof, following the eight steps of the node:
1. Restrict the actual quotient-linear systems along the completed projections. The
coefficient identity pi_n c_hat = c_n F(pi_n) identifies U(G M) with F(U M), including
all original transitions and the finite tensor insertions j from the descent lemma.
The site reindexing equivalence is additive, exact and preserves the canonical products.
2. Sections at the point are exact by lem-weil-point-proetale-sections-exact. Products
are sectionwise by lem-weil-proetale-countable-products-exact; scalar restriction keeps
those products and exactness. Products of R-modules are exact by coordinatewise choice.
3. Apply lem-weil-strict-roos-comparison and the total-limit model of
lem-weil-pbc-ringed-strict-tower-homotopy-limit to both module categories. Their universal
units fix thetaA and thetaR. The inclusion is (0, gamma). The signed permutation
(b,a) to (a,-b) identifies these coordinates with those in
lem-cbc-exact-product-functor-strict-limit without changing diagonal comparisons.
4. Apply that exact-product comparison to inverse image and sections. Its projection
formulas give productF and productT. Apply each on both cone coordinates to give
kappaF and kappaT, then conjugate by theta to get a and zeta in the displayed directions.
These are comparisons of the entire limit cones, independent of the tower resolutions.
5. The strict transformation of lem-trf-point-system-transport-descent has components u_n
commuting with the ORIGINAL transitions. Thus (1-s') product(u) = product(u) (1-s).
The actual cone map is (product(u),product(u)), with no off-diagonal component.
Naturality of thetaR identifies its localization with Rlim(I), as transport_model states.
6. On every ambient complex, restriction followed by insertion and sheafification is
actual restriction in the site-reindexing coordinates, by the point-transport recipe.
The completed coefficient identity makes it R-linear, and naturality with respect to
differentials makes a chain map. Exactness localizes this natural transformation.
7. Compare both coordinates after every product projection. Each is the actual
restriction x_n to x_n restricted along h^r; the coefficient identifications and finite j
identify them with u_n. Hence applying sections to kappaF after sigma equals the inverse
kappaT comparison after H(u), on the entire cone, including its shifted coordinate.
8. Substitute the conjugation formulas of step 4 and the localized cone-map equation of
step 5. Naturality of sigma with thetaA cancels the consecutive inverse comparisons and
gives transport. Natural chain comparisons localize along quasi-isomorphisms, giving
naturality for every derived system morphism, without assuming evaluation is faithful. -/
theorem point_system_roos_transport (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r) :
    Nonempty (Data D l E hl r hr) := by
  obtain ⟨models, products, comparisons, hproducts, hcomparisons⟩ :=
    point_system_roos_comparison_assembly D l E hl r hr
  obtain ⟨hcone, hprojection⟩ :=
    point_system_roos_restriction_assembly D l E hl r hr models products comparisons
      hproducts hcomparisons
  refine ⟨⟨models, products, hproducts, comparisons, hcomparisons, ?_⟩⟩
  refine ⟨?_, ?_, ?_, ?_, hcone, hprojection⟩
  · intro C
    let τ₁ : PointSystemTransport.derivedSections D l E ⋙ scalarLimit.{t, u} l E ⟶
        (G D l E r).mapDerivedCategory ⋙ L D l E ⋙ (T D l E).mapDerivedCategory :=
      Functor.whiskerRight (PointSystemTransport.derivedTransport D l E hl r hr) _ ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryCompIso (G D l E r)
          (PointSystemTransport.sections D l E)).hom _ ≫
        Functor.whiskerLeft (G D l E r).mapDerivedCategory comparisons.zeta.hom
    let τ₂ : PointSystemTransport.derivedSections D l E ⋙ scalarLimit.{t, u} l E ⟶
        (G D l E r).mapDerivedCategory ⋙ L D l E ⋙ (T D l E).mapDerivedCategory :=
      comparisons.zeta.hom ≫ Functor.whiskerLeft (L D l E) comparisons.sigmaD ≫
        Functor.whiskerRight comparisons.a.hom (T D l E).mapDerivedCategory
    have he : τ₁ = τ₂ := by
      apply Localization.natTrans_ext DerivedCategory.Q
        (HomologicalComplex.quasiIso (coefficientSequenceModules l E (Spec (.of D.k))) (.up ℤ))
      intro M
      exact point_system_roos_transport_representative D l E hl r hr
        models products comparisons hcomparisons hcone M
    exact NatTrans.congr_app he C
  · intro M
    apply comparison_transport models.thetaR
      ((PointSystemTransport.chainTransport D l E hl r hr).app M)
      ((PointSystemTransport.sections D l E).mapDerivedCategoryFactors.app M)
      ((G D l E r ⋙ PointSystemTransport.sections D l E).mapDerivedCategoryFactors.app M)
    exact (PointSystemTransport.point_system_transport_descent D l E hl r hr).2.exists
      |>.choose_spec |>.1 M
  · intro M
    exact roosU_natural ((PointSystemTransport.chainTransport D l E hl r hr).app M)
  · intro M p
    exact roosF_map_χ ((PointSystemTransport.chainTransport D l E hl r hr).app M) p

end WeilConjectures.PointSystemRoos
