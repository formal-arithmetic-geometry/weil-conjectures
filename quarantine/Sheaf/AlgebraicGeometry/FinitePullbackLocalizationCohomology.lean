/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Finite derived pullback and normalized slice cohomology

Source: Stacks Project, sites.tex, Tag 03CE (lemma-localize-given-products);
homology.tex, Tag 010N (lemma-exact-functor); derived.tex, Tag 015F
(lemma-right-derived-exact-functor); the graph calculation in the expanded proof of
lem-pur-etale-iso-descent, steps 2--3
(blueprint: lem-pur-finite-pullback-localization-cohomology).

The structure below packages exactly the normalized comparisons in the statement.
Its graph equation uses the specified module adjunction unit at the composed object
and restriction along the graph. It therefore fixes the module comparison on sections.
The cohomology equation uses the canonical cycles/boundaries comparison, rather than
an unspecified isomorphism of cohomology objects.
-/

@[expose] public section

set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The conclusions of the finite localization comparison, retaining their normalizations.
The coefficient isomorphism fixes constant sections. The inverse of `moduleComparison`
is the graph coprojection: take the canonical module adjunction unit at the composed
object and then restrict along the graph, the unit of composition/base change on sites.
`derived_on_complexes` specifies its degreewise descent through localization.
`cohomology_formula` uses the exact-functor cycles/boundaries comparison; the final
field spells out its naturality for every derived arrow, including roofs.

Source: Stacks, Tags 03CE, 010N and 015F, and the graph calculation in the expanded
lem-pur-etale-iso-descent proof, steps 2--3
(blueprint: lem-pur-finite-pullback-localization-cohomology). -/
structure ProEtaleFiniteLocalizationComparison {X : Scheme.{u}} (U : X.ProEt)
    (A : Type u) [CommRing A] where
  [finite : Finite A]
  ringIso : proEtaleConstantRing U.left A ≅
    (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
      U.hom U.prop).obj (proEtaleConstantRing X A)
  constantSections : ∀ V : U.left.ProEt,
    (toSheafify (ProEt.topology U.left)
      ((Functor.const U.left.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1, u} A)))).app (op V) ≫ ringIso.hom.hom.app (op V) =
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).app
            (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V))
  [restrictionAdditive : (proEtaleObjectModuleRestriction U A ringIso).Additive]
  [restrictionLimits : PreservesFiniteLimits (proEtaleObjectModuleRestriction U A ringIso)]
  [restrictionColimits : PreservesFiniteColimits (proEtaleObjectModuleRestriction U A ringIso)]
  moduleComparison : sfIntrinsicPullback A U.hom ≅ proEtaleObjectModuleRestriction U A ringIso
  module_graph : ∀ (M : proEtaleRingModules X (proEtaleConstantRing X A))
      (V : U.left.ProEt)
      (x : M.val.obj (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V))),
    (moduleComparison.inv.app M).val.app (op V) x =
      ((sfIntrinsicPullback A U.hom).obj M).val.map
        (proEtaleObjectInverseImageIndexPoint U V).hom.op
        (((sfIntrinsicConstantModuleAdjunction U.hom A).unit.app M).val.app
          (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V)) x)
  derivedComparison : sfIntrinsicDerivedPullback A U.hom ≅
    (proEtaleObjectModuleRestriction U A ringIso).mapDerivedCategory
  derived_on_complexes : ∀ K : CochainComplex
      (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ,
    derivedComparison.hom.app (DerivedCategory.Q.obj K) ≫
        (proEtaleObjectModuleRestriction U A ringIso).mapDerivedCategoryFactors.hom.app K =
      (sfIntrinsicPullback A U.hom).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex moduleComparison.hom (.up ℤ)).app K)
  cohomologyComparison : ∀ r : ℤ,
    sfIntrinsicDerivedPullback A U.hom ⋙
        DerivedCategory.homologyFunctor
          (proEtaleRingModules U.left (proEtaleConstantRing U.left A)) r ≅
      DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X A)) r ⋙
        proEtaleObjectModuleRestriction U A ringIso
  cohomology_formula : ∀ r : ℤ,
    cohomologyComparison r =
      Functor.isoWhiskerRight derivedComparison
          (DerivedCategory.homologyFunctor
            (proEtaleRingModules U.left (proEtaleConstantRing U.left A)) r) ≪≫
        ((proEtaleObjectModuleRestriction U A ringIso).mapDerivedCategoryHomologyFunctorIso
          r).symm
  cohomology_naturality : ∀ (r : ℤ) (K L : proEtaleDerivedCategory X A) (ψ : K ⟶ L),
    (DerivedCategory.homologyFunctor
        (proEtaleRingModules U.left (proEtaleConstantRing U.left A)) r).map
          ((sfIntrinsicDerivedPullback A U.hom).map ψ) ≫
        (cohomologyComparison r).hom.app L =
      (cohomologyComparison r).hom.app K ≫
        (proEtaleObjectModuleRestriction U A ringIso).map
          ((DerivedCategory.homologyFunctor
            (proEtaleRingModules X (proEtaleConstantRing X A)) r).map ψ)

/-- Finite-level derived pullback is normalized slice restriction and commutes with
cohomology, naturally on all unbounded derived morphisms. The positive coefficient
level is written `n + 1`; thus every integer level at least one is included.
The source and target are the ordinary intrinsic constant-ring module categories.

Source: Stacks, sites.tex, Tag 03CE; homology.tex, Tag 010N; derived.tex, Tag 015F
(blueprint: lem-pur-finite-pullback-localization-cohomology).

Proof plan, following the node's six steps:
1. Apply lem-sfb-proetale-object-inverse-image-restriction and
   lem-weil-proetale-weakly-etale-localization to get the graph comparison and
   constant-section coefficient isomorphism. In fixed-scalar coordinates the unit
   of sfIntrinsicConstantModuleAdjunction is the same module coprojection. Restrict
   it along the graph to obtain module_graph. Exactness of restriction is
   lem-pur-site-restriction-module-adjunction-exact, transported through the site
   and coefficient equivalences; additivity is sectionwise.
2. Apply lem-weil-pbc-exact-functor-derived-factorization and
   lem-weil-pbc-exact-functor-derived-functor to both exact functors. The finite-level
   pullback of def-weil-derived-pullback-tensor-hom is sfIntrinsicDerivedPullback
   at this quotient ring, by def-weil-pbc-proetale-operations. Every complex computes
   it, since the module pullback takes quasi-isomorphisms to quasi-isomorphisms.
3. Apply lem-sfb-exact-derived-natural-iso to moduleComparison. Its localization
   normalization is derived_on_complexes. Naturality at a resolution shows the
   same comparison results from every representative, without a boundedness condition.
4. Apply lem-weil-pbc-exact-functor-complex-cohomology to the restriction functor.
   The canonical map identifies cycles and boundaries and commutes with the
   projection from cycles onto cohomology. This is the sheaf quotient, not evaluation
   of a complex followed by cohomology of its section groups.
5. Descend that normalized comparison by lem-weil-pbc-localization-universal-property.
   Both complex functors invert quasi-isomorphisms; the descended comparison is
   the inverse of mapDerivedCategoryHomologyFunctorIso, normalized by the canonical
   factorization of def-weil-derived-cohomology-sheaves.
6. Compose with cohomology of derivedComparison to get cohomology_formula.
   Naturality gives cohomology_naturality. For a roof, use naturality at its two
   arrows and invert the quasi-isomorphism; hence the equation holds for every
   derived morphism, with no chain-map-representability assumption. -/
theorem finite_pullback_localization_cohomology
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) (X : Scheme.{u}) (U : X.ProEt)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : U.left, Invertible (l : U.left.residueField x)] :
    Nonempty (ProEtaleFiniteLocalizationComparison U
      (Padic.coefficientExtensionRing l E (n + 1))) := by
  sorry

end AlgebraicGeometry.Scheme
