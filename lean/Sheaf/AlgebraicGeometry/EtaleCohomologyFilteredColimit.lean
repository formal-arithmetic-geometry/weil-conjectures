/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Filtered colimits of etale cohomology

Source: Stacks Project, Tags 03Q5, 0739 and 03FD; blueprint `sec-curve-estimates/sk-prop-h2`
(blueprint: lem-weil-pbc-cohomology-filtered-colimit).

The image cocone has legs induced by the original coprojections. Its colimit property
expresses that the canonical comparison map is an isomorphism, rather than merely asserting
an unspecified isomorphism between the two cohomology objects.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- On a quasi-compact quasi-separated scheme, etale cohomology of abelian sheaves commutes
with filtered colimits, with no torsion hypothesis. Source: Stacks Tags 03Q5 and 0739
(blueprint: lem-weil-pbc-cohomology-filtered-colimit).

Proof:
1. In the Grothendieck abelian category of etale abelian sheaves, use functorial injective
   embeddings (lem-weil-pbc-grothendieck-functorial-injective-embedding). The canonical
   comparison is induced by the cohomology maps of the coprojections.
2. Take the qcqs etale objects and their finite coverings. The identity of the base is an
   etale object. Qcqs permanence makes all covering fibre products qcqs
   (lem-weil-pbc-qcqs-morphism-permanence), and affine refinements give cofinal finite covers
   (lem-weil-pbc-etale-qcqs-cofinal-finite-coverings).
3. Sections commute with filtered colimits on these objects
   (lem-weil-pbc-etale-qcqs-sections-filtered-colimit). Identify this with degree-zero derived
   cohomology (lem-weil-pbc-left-exact-injective-resolution-degree-zero).
4. Embed the diagram functorially into injectives and take its cokernel diagram. Exactness
   of filtered colimits gives a short exact colimit sequence
   (lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact).
5. The Cech complexes of the colimit of injectives are filtered colimits of their Cech
   complexes: each term is a finite product on qcqs fibre products. Injective Cech acyclicity
   and exactness of filtered colimits imply Cech vanishing, hence higher cohomology vanishing
   (lem-weil-pbc-injective-sheaf-cech-acyclic, lem-weil-pbc-cech-vanishing-criterion).
6. Induct on the degree using the two long exact sequences. Naturality of their connecting
   maps makes the comparison diagram commute (lem-weil-pbc-horseshoe-delta-functor).
   The induction hypothesis and the five lemma give the next degree
   (lem-weil-pbc-five-lemma).
7. Evaluate at the terminal object and identify the derived functors with K-injective
   derived global sections, naturally in the sheaf
   (lem-sp-derived-functor-single-identification). This identifies the comparison with the
   cocone below. No step uses torsion. -/
theorem etaleCohomology_isColimit_of_isFiltered (Y : Scheme.{u}) [CompactSpace Y]
    [QuasiSeparatedSpace Y] {I : Type u} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone F}
    (hc : IsColimit c) (q : ℕ) :
    Nonempty (IsColimit
      ((DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} Y (q : ℤ)).mapCocone c)) :=
  sorry

/-- The same canonical comparison is an isomorphism for etale sheaves of modules over a
fixed constant commutative ring. Source: Stacks Tags 03FD, 03CO and 03Q5
(blueprint: lem-weil-pbc-cohomology-filtered-colimit).

Proof (step 8 of the node): the forgetful functor to abelian sheaves is exact and commutes
with colimits (lem-weil-pbc-module-sheaves-colimits-forgetful). Apply steps 1--7 above to the
underlying abelian diagram. Module injectives are acyclic for underlying abelian cohomology
(lem-weil-pbc-injective-module-abelian-acyclic), so module injective resolutions compute the
same cohomology, naturally, by lemma-weil-pbc-leray-acyclicity. The comparison is linear
because its legs are the linear cohomology maps of the coprojections. Thus the abelian
comparison identifies with the module comparison and is an isomorphism. -/
theorem etaleModuleCohomology_isColimit_of_isFiltered (Y : Scheme.{u}) [CompactSpace Y]
    [QuasiSeparatedSpace Y] (Λ : Type (u + 1)) [CommRing Λ]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {c : Cocone F}
    (hc : IsColimit c) (q : ℕ) :
    Nonempty (IsColimit
      ((DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        Etale.cohomology (ModuleCat.{u + 1} Λ) Y (q : ℤ)).mapCocone c)) :=
  sorry

end AlgebraicGeometry.Scheme
