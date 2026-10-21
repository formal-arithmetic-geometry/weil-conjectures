## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence` states all
clauses of lem-sf-open-extension-scalar-restriction-coherence for the existing intrinsic
constant-ring module sheaves. All seven theorem proofs are `sorry`. Its six helper
definitions contain real constructions; none selects an arbitrary comparison.

Source read: sites-modules.tex, Tag 03DI, `lemma-extension-by-zero`, and Tag 03CY,
`lemma-sheafification-presheaf-modules`; the former constructs the sheafified direct
sum over maps to the open, and the latter supplies unique factorization. The exact
termwise derived API and the localization natural-transformation API were read in
Mathlib `DerivedCategory/ExactFunctor.lean` and `Localization/Predicate.lean`.

Hypothesis and clause correspondence:

- Finite commutative rings A, B, C are the explicitly declared `Type u` variables
  with `CommRing` and `Finite` instances. The maps are `(φ : A →+* B)` and
  `(ψ : B →+* C)`, and χ is exactly `ψ.comp φ`.
- Schemes U and Z are arbitrary `Scheme.{u}`; `(j : U ⟶ Z) [IsOpenImmersion j]`
  is the whole geometric hypothesis. The categories are the recorded
  `proEtaleRingModules T (proEtaleConstantRing T R)`, with site objects in `u+1`,
  morphisms in `u`, and module values in `u+1`. The derived objects use the same
  recorded `proEtaleDerivedCategory`. No equality between the two site universes
  is assumed.
- Scalar restriction is the existing `proEtaleCoefficientRestrictScalars T φ`,
  definitionally the recorded Mathlib ring-sheaf scalar restriction along the
  induced constant-ring map. Its exactness instances are already published.
- ρ is the existing `sfCoefficientRestrictionComp T φ ψ`. Its definition uses
  `pbcRestrictComp`, uniquely sectionwise identity. Its derived incarnation is
  exactly the existing `sfDerivedCoefficientRestrictionComp`, i.e. termwise
  localization with the canonical exact-functor composition comparisons.
- J_R is the dependency's `sfIntrinsicExtensionByZero j R`, with the exactness
  instances in `ProEtaleIntrinsicExtensionByZeroExact`. At the cochain level it
  is `mapHomologicalComplex (.up ℤ)`, and at the derived level `mapDerivedCategory`.
- Existence and naturality of e are furnished by the already published natural
  isomorphism `sfOpenRestriction j φ`, with exactly the source and target in the
  node. The module does not introduce a second sheaf comparison.
- Presheaf-identity normalization and uniqueness are
  `sfOpenRestriction_normalized_unique`. Its predicate
  `SfOpenRestrictionNormalized` says η_A ≫ j^*(e) ≫ q = r_φ(η_B), where η is
  the existing open-extension adjunction unit and q is
  `sfOpenRestrictionCoefficientSquare`. This is an explicit equation of maps,
  not a condition saying merely that e equals a chosen isomorphism. The unit is
  the sheafification map on every generator M(V→U); its equation is exactly
  e∘η_P = r_φ(η_P) on the defining presheaf. On objects not factoring through U,
  P has value zero, so there is a unique map. Thus testing the open generators
  is equivalent to testing the entire extension presheaf. The recorded
  adjunction's docstring and Stacks 03DI identify its unit with precisely these
  generators. q is the literal identity fixed-scalar restriction square
  transported by the same section-normalized realization equivalences used
  in the definition of J and e.
- The sheaf cocycle is `sfOpenRestriction_coefficient_comp`. Lean's `≫` reads
  from left to right, so its left side is J_A(ρ_U) ≫ e_χ and its right side is
  e_φ ≫ r_φ(e_ψ) ≫ ρ_Z. Both specified ρ components are present in their
  respective required positions.
- For every complex, the same equation is
  `sfOpenRestriction_cochain_comp`, with `NatIso.mapHomologicalComplex` of
  the very same e and ρ. Naturality of e supplies the differential compatibility
  in that construction. The index is all of ℤ, with no degree restriction.
- `sfOpenRestrictionDerived` is exactly
  `Functor.mapDerivedCategorySquareIso (sfOpenRestriction j φ)`: it localizes
  the normalized termwise comparison and includes the canonical endpoint
  factorization isomorphisms. Thus it has the specified endpoints on every
  object of the unbounded derived category. `sfOpenRestriction_derived_comp`
  gives the displayed cocycle there, with no representative or boundedness
  condition on K.
- The identity coefficient laws at the three levels are respectively
  `sfOpenRestriction_coefficient_id`, `sfOpenRestriction_cochain_id` and
  `sfOpenRestriction_derived_id`. They compare e_id followed by the canonical
  identification at Z with J of the canonical identification at U. The
  identifications are real definitions: `sfOpenFixedRestrictionId` is
  ModuleCat's sectionwise identity; `sfOpenCoefficientRestrictionId` transports
  that identity through the canonical realization square and counit; and
  `sfOpenDerivedCoefficientRestrictionId` is its termwise localization.
- There is no quasi-compactness, coefficient flatness, boundedness,
  constructibility, separatedness or finite-type assumption anywhere.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Sites.Proetale: `AlgebraicGeometry.Scheme.ProEt`
  and `ProEt.topology`, the recorded small pro-etale site.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings:
  `SheafOfModules.restrictScalars`, reached through the recorded intrinsic
  coefficient functor; it retains the underlying abelian presheaf.
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor:
  `CategoryTheory.Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`,
  its CommShift and triangulated instances, the exact-functor factorization leaf.
- Mathlib.AlgebraicGeometry.OpenImmersion: `AlgebraicGeometry.IsOpenImmersion`.
- Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero:
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero` and
  `sfIntrinsicModuleEquivalence` (canonical realization, fixed extension,
  canonical realization).
- Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact:
  `sfIntrinsicExtensionByZero_exact` and its additive, finite-limit and
  finite-colimit instances.
- Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction:
  `sfIntrinsicOpenRestriction` and `sfIntrinsicExtensionByZeroAdjunction`.
  Its already landed node, lem-weil-extension-by-zero-adjunction, was added
  to stmt_deps under the rule allowing added landed statement dependencies.
- Existing canonical map interfaces in Sheaf.Paper.SfCompactSupportRestrictionOfScalars:
  `sfFixedRestriction`, `sfRealizationRestriction`,
  `sfInverseRealizationRestriction`, `sfOpenRestriction`,
  `sfCoefficientRestrictionComp`, `sfDerivedCoefficientRestrictionComp`.
  These are reused literally. They do not yet state this node's normalization
  and all three coherence laws. The parent compact-support theorem has extra
  geometric hypotheses and a different composite comparison.
- Proof-only imports are the recorded
  `PresheafOfModules.sheafification` module,
  Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
  (`SheafOfModules.sheafRingCoefficientOrdinaryAdjunction`), and
  Mathlib.CategoryTheory.Localization.Predicate (`liftNatIso`, `natTrans_ext`,
  the natural-transformation localization leaf). Their full source interfaces
  were read. Other statement dependencies are public imports directly or
  transitively through the published interfaces above.

Import-cycle advisory: the parent module owns the canonical maps used here.
It must not acquire a reverse proof import of this module, which would close
an import cycle. No live module was edited. This delivery's own imports are
acyclic and the server compile checks their closure.

Edge cases checked mathematically before writing: U empty (zero extension),
j an identity, zero coefficient rings, identity coefficient maps, and the
nonflat map ℤ/4→ℤ/2. In all cases the presheaf-identity argument and canonical
ρ keep their meaning. An arbitrary non-quasi-compact open is allowed: no
quasi-compactness enters the site extension/sheafification argument. Complexes
with infinitely many nonzero degrees in both directions are included literally
by `CochainComplex ... ℤ` and the unbounded derived categories. No statement
fault or mathematical dispute was found.

Searches actually run:

- msearch.py leanfinder, query “Sheafified extension by zero commutes with
  restriction of scalars coherently for composition on unbounded derived
  categories”: eight hits, including `sheafificationCompForgetCompToPresheaf`,
  `sheafComposeIso_hom_fac`, and `sheafificationCompPullback`; these are generic
  sheafification/pullback ingredients, not this normalized three-level cocycle.
- msearch.py loogle, query `SheafOfModules.restrictScalars`: four hits, the
  restriction functor, its additivity, and its object/map formulas. Used the
  existing functor; none states the requested coherence.
- msearch.py grep, query `extensionByZero|lowerShriek|restrictScalarsComp`,
  Mathlib/CategoryTheory: no hits.
- rg in lean/WeilConjectures and lean/Sheaf for open scalar comparisons,
  `sfOpenRestriction`, scalar associators, and the proposed declaration names:
  found the shared canonical interfaces above and fixed scalar restriction
  APIs; no declaration has the full statement. Searching the item id in
  lean/WeilConjectures returned no hit. The proposed new declaration names
  also had no hit in the source library, Sheaf or dag/lean_names_upstream.json.

## Second reading by NM

This is a second pass by the same dispatched worker, not an independent-worker
review. The dispatcher explicitly forbids starting other agents and assigns
independent reading to the maintainer. I reopened the node and checked its
clauses against the final module: finite coefficient maps and arbitrary open
immersion; exact unchanged scalar restriction; canonical ρ; natural sheaf e;
its normalization/uniqueness; the sheaf, cochain and derived cocycles with both
ρ components; and the identity law at each level. The cocycle orientation
matches because Lean's `≫` reverses the written functional-composition order.
The normalization uses the actual canonical open unit, with an explicit
restriction/coefficient square, so the presheaf-identity clause is retained.
The derived comparison is a concrete localization of the same e. No hypothesis
or conclusion was corrected, and no dependency module or new DAG node is needed.

The helper definitions are data-bearing constructions, the universes are
explicit, and every postponed theorem has its source and natural-language proof
in its docstring and is listed in this item's lean.declarations. The only node
field changes are lean and the added landed adjunction dependency. Independent
mathematical review remains with the maintainer as specified in the brief.

Validation: the final full module passed scompile.py in both sandbox and module
coordinates with no errors or warnings (57.4 s and 25.8 s). The prescribed
`deliver2.py NM lem-sf-open-extension-scalar-restriction-coherence --no-push`
then printed `OK (dry run): commit d8e940b2925 passes the preflight and compiles;
nothing pushed`. All source lines are at most 100 characters. No live source
was edited, no direct Git command was run, and no global build was requested.
