/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Paper.FiniteRingConstructibleSheafOrigin
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.Paper.ProEtaleLisseOrigin
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ConstructiblePartitionLocalClosedStratum
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequence
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleStalkConservative
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.DerivedCategories

/-!
# Constructible pro-etale coefficients are of etale origin

Source: Weil blueprint, smooth purity, `lem-sf-proetale-constructible-origin`;
Stacks Project, Tags 09AK and 09AL (blueprint: lem-sf-proetale-constructible-origin).

The scalar conversion below is induced by constant scalar sections and sheafification.
It retains the recorded intrinsic constructibility predicate and the recorded category
of finite coefficient modules. Discrete topology is fixed canonically on lifted coefficients.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]

/-- The recorded finite coefficient ring sheaf with discrete lifted coefficients.
Source: blueprint, finite coefficient convention
(blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable abbrev originCoefficientRing : Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1} :=
  @finiteCoefficientRingSheaf.{u} T (ULift.{u + 1, u} B) _ _ ⊥
    (discreteTopology_bot _)

/-- The recorded module category with the discrete coefficient topology fixed.
Source: blueprint, finite coefficient convention
(blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable abbrev OriginModules :=
  ringedSiteModules.{u + 1} (originCoefficientRing T B)

/-- The recorded derived category with the discrete coefficient topology fixed.
Source: blueprint, finite coefficient convention
(blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable abbrev OriginDerivedCategory :=
  @FiniteCoefficientDerivedCategory.{u} T (ULift.{u + 1, u} B) _ _ ⊥
    (discreteTopology_bot _)

/-- The canonical comparison from sheafification in rings to sheafification in
commutative rings followed by forgetting commutativity. It is adjoint to the
commutative-ring sheafification unit, so its data involve no choice.
Source: Stacks, sheafification of algebraic structures
(blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable def originConstantRingComparison :
    (constantSheaf (Scheme.ProEt.topology T) RingCat.{u + 1}).obj
      (RingCat.of (ULift.{u + 1, u} B)) ⟶
    (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (Scheme.proEtaleConstantRing T B) :=
  (sheafComposeNatTrans (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    (sheafificationAdjunction (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (sheafificationAdjunction (Scheme.ProEt.topology T) RingCat.{u + 1})).app
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} B)))

/-- The canonical constant-ring comparison is invertible.
Source: Stacks, sheafification of algebraic structures
(blueprint: lem-sf-proetale-constructible-origin).

Proof: sheafification of a ring presheaf is computed on its underlying set presheaf,
with addition and multiplication uniquely glued from local representatives. If the
presheaf is commutative, the glued multiplication is commutative: choose common local
representatives for two sections and use commutativity there, then separatedness.
Thus its ring sheafification has the commutative-ring sheafification universal property.
The displayed comparison is the unique map extending the same unit, and the two universal
properties give its inverse. Both composites extend the unit and hence are identities. -/
theorem isIso_originConstantRingComparison : IsIso (originConstantRingComparison T B) := by
  sorry

attribute [instance] isIso_originConstantRingComparison

/-- Constant scalars induce the canonical map from the constant ring sheaf to the
continuous-function coefficient sheaf. The second arrow is adjoint to the recorded
constant scalar map. Source: Stacks, constant sheaves and Tag 09AK
(blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable def originCoefficientMap :
    (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (Scheme.proEtaleConstantRing T B) ⟶ originCoefficientRing T B :=
  (asIso (originConstantRingComparison T B)).inv ≫
    ((sheafificationAdjunction (Scheme.ProEt.topology T) RingCat.{u + 1}).homEquiv _ _).symm
      (@finiteCoefficientScalarMap.{u} T (ULift.{u + 1, u} B) _ _ ⊥ (discreteTopology_bot _))

/-- Restrict scalars along the canonical coefficient map; the underlying additive sheaf
is unchanged. This is the identification used to read intrinsic constructibility.
Source: Stacks, Tag 09AK (blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable def originConstantModules :
    OriginModules T B ⥤ Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T B) :=
  SheafOfModules.restrictScalars.{u + 1} (originCoefficientMap T B)

/-- The recorded canonical inverse image on module sheaves.
Source: blueprint, site comparison (blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable abbrev originComparison :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) ⥤ OriginModules T B :=
  @finiteCoefficientComparison.{u} T (ULift.{u + 1, u} B) _ _ ⊥ (discreteTopology_bot _)

/-- The recorded canonical derived inverse image.
Source: blueprint, site comparison (blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable abbrev originDerivedComparison :
    Etale.DerivedCategoryModule (ULift.{u + 1, u} B) T ⥤ OriginDerivedCategory T B :=
  @finiteCoefficientDerivedComparison.{u} T (ULift.{u + 1, u} B) _ _ ⊥ (discreteTopology_bot _)

/-- Intrinsic bounded constructibility: every cohomology sheaf is intrinsically
constructible, and cohomology vanishes outside a finite interval.
Source: blueprint clause (ii), Stacks Tag 09AL
(blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable def intrinsicOriginBoundedConstructible :
    ObjectProperty (OriginDerivedCategory T B) :=
  fun K ↦
    (∀ q : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T B
      ((originConstantModules T B).obj
        ((_root_.DerivedCategory.homologyFunctor (OriginModules T B) q).obj K))) ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((_root_.DerivedCategory.homologyFunctor (OriginModules T B) q).obj K)

/-- The recorded etale-origin object class, with discrete lifted coefficients.
Source: blueprint, final clause (blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable abbrev etaleOriginBoundedConstructible : ObjectProperty (OriginDerivedCategory T B) :=
  @isBoundedConstructibleFiniteCoefficient.{u} T (ULift.{u + 1, u} B) _ _ ⊥
    (discreteTopology_bot _)

/-- Both equivalences are induced by the specified comparison, expressed by natural
isomorphisms after the full inclusions. The last equality compares object properties
on exactly the same ambient derived category.
Source: blueprint clauses (i), (ii), and the final sentence; Stacks Tags 09AK, 09AL
(blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable def ConstructibleOriginComparison : Prop :=
  (∃ e :
    ObjectProperty.FullSubcategory (Scheme.IsConstructibleEtaleModuleSheaf (T := T)
      (Λ := ULift.{u + 1, u} B)) ≌
    ObjectProperty.FullSubcategory (Scheme.IsConstructibleProEtaleModuleSheaf T B),
    Nonempty
      (ObjectProperty.ι (Scheme.IsConstructibleEtaleModuleSheaf (T := T)
          (Λ := ULift.{u + 1, u} B)) ⋙ originComparison T B ⋙ originConstantModules T B ≅
        e.functor ⋙ ObjectProperty.ι (Scheme.IsConstructibleProEtaleModuleSheaf T B))) ∧
  (∃ e :
    (Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1, u} B) T).FullSubcategory ≌
    (intrinsicOriginBoundedConstructible T B).FullSubcategory,
    Nonempty
      ((Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1, u} B) T).ι ⋙
        originDerivedComparison T B ≅ e.functor ⋙ (intrinsicOriginBoundedConstructible T B).ι)) ∧
  intrinsicOriginBoundedConstructible T B = etaleOriginBoundedConstructible T B

/-- Constructible finite-level pro-etale sheaves and bounded constructible complexes
are exactly those obtained from the etale site by the specified comparison inverse image.
The coefficient ring is the recorded quotient by the chosen uniformizer power, with
finiteness supplied by its positive-level theorem rather than an extra hypothesis.
Source: Weil blueprint, smooth purity, lemma of this name; Stacks Tags 09AK and 09AL;
Bhatt--Scholze, Sections 5.1, 5.2 and 6.2
(blueprint: lem-sf-proetale-constructible-origin).

Proof plan, following the node's nine steps:
1. Choose the finite constructible locally closed partition of a constructible etale
sheaf. Comparison commutes with restriction to every stratum by
lem-weil-pbc-comparison-pullback. Clause (a) of lem-sf-proetale-locally-constant-origin
makes each inverse image lisse with finite stalks. The same partition works pro-etale.
2. The comparison unit is invertible on all etale module sheaves by
prop-weil-pbc-site-comparison-finite-level. The adjunction then gives bijections on Hom
sets, so comparison is fully faithful. A pro-etale sheaf is classical, meaning in its
essential image, exactly when its counit is invertible: one direction takes its direct
image, and the other uses the triangle identity and invertible unit.
3. Classicality is Zariski-local. Direct image commutes with restriction to an open
because both evaluate the same pro-etale sheaf on each etale object over that open.
Comparison commutes with restriction by lem-weil-pbc-comparison-pullback, so the counit
restricts to the open's counit. Covering-family locality in clause (1) of
lem-cbc-proetale-stalk-conservative glues these local isomorphisms. Geometric stalks
of arbitrary pro-etale sheaves are not used for this detection.
4. Classical sheaves are closed under extensions. The short exact sequence gives a
triangle by lem-sf-derived-ses-triangle. Exact comparison is triangulated by
lem-sf-exact-functor-derived-triangulated. Full faithfulness on bounded below complexes
from thm-weil-pbc-site-comparison lifts the boundary between the two classical terms.
Complete the lifted boundary to a triangle and rotate; TR3 and
lem-sf-triangle-morphism-iso identify its image with the original triangle.
The long exact cohomology sequence, lem-sf-derived-homology-long-exact, shows the lifted
middle term is concentrated in degree zero. By lem-sf-derived-concentrated-single it is
a sheaf in degree zero. Taking degree-zero cohomology proves the extension classical.
5. Induct on the number of nonempty strata, simultaneously for all schemes.
For no strata the scheme is empty and take the zero sheaf. Near any point choose the
affine open of lem-sf-constructible-partition-local-closed-stratum, so its stratum is
closed and its open complement is quasi-compact. Restrict strata with their fibre-product
scheme structures. Induction makes the restriction to the complement classical; clause
(b) of lem-sf-proetale-locally-constant-origin makes the closed restriction classical.
The open-closed exact sequence of lem-sf-proetale-open-closed-sequence has classical end
terms by lem-cbc-proetale-extension-zero-comparison and the degree-zero part of
prop-weil-pbc-comparison-direct-image. Step 4 and then step 3 give classicality.
6. If the comparison image of an etale sheaf is intrinsically constructible, restrict
to its given finite partition. Clause (b) of the locally constant origin lemma and full
faithfulness from step 2 descend each lisse stratum to a lisse etale sheaf. Thus the
original etale sheaf is constructible. Steps 1, 2, 5, and this reflection give (i).
7. Exact comparison commutes with all cohomology functors. Hence the image of an etale
bounded constructible complex has intrinsically constructible cohomology in the same
finite degree interval. Full faithfulness on bounded below complexes gives full
faithfulness on this full subcategory, by thm-weil-pbc-site-comparison.
8. Induct on the finite cohomological amplitude of an intrinsic complex. The zero
complex descends to zero. With one nonzero degree, apply (i) to its cohomology sheaf
and lem-sf-derived-concentrated-single, then shift. Otherwise use the top-degree
truncation triangle of lem-sf-derived-truncation-triangle. Its outer terms descend by
induction, and full faithfulness on bounded below complexes lifts the boundary between
them. Complete it to a triangle on the etale side and identify the image with the given
triangle using TR3 and lem-sf-triangle-morphism-iso. Its long exact cohomology sequence
shows that the lifted middle complex is bounded constructible. This proves (ii).
9. By def-weil-pbc-proetale-modules, the etale-origin object property is the essential
image of etale bounded constructible complexes. Step 7 proves its inclusion in the
intrinsic property and step 8 the reverse. Equality follows by propositional and function
extensionality. All changes of coefficient presentation use the constant scalar maps:
originConstantRingComparison is invertible by its universal property, and the recorded
finiteCoefficientScalarMap is locally bijective. Associated module sheafification and
restriction of scalars therefore identify the module sheaves and their exact derived
functors canonically, including the natural isomorphisms in the two equivalence clauses. -/
theorem constructible_proEtale_origin
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u}) :
    @ConstructibleOriginComparison.{u} T (Padic.coefficientExtensionRing l E n) _
      (Padic.finite_coefficientExtensionRing l E n hn) := by
  sorry

end AlgebraicGeometry.ProEtale
