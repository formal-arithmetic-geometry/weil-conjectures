## Worker report

The item is stated by `AlgebraicGeometry.RingedSpace.connective_hypercohomology_sheaf`
in `Sheaf.Topology.ConnectiveHypercohomologySheaf`. Its sole proof is `sorry`.
The original mathematical statement, proof, and proof dependencies are unchanged.
Its statement dependencies gain the new presheaf definition and the already landed
`def-pc-open-module-derived-sections`, whose declaration occurs explicitly in the conclusion.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Arbitrary ringed space: `(X : RingedSpace.{u})`; no locally ringed, scheme,
  quasi-compactness, separation, or finiteness hypothesis is imposed.
- Opens and open covers: `Opens X` and `Opens.grothendieckTopology X`.
  The opens and coefficient/module values use the common universe `u`.
  `HasDerivedCategory.{w}` and `HasDerivedCategory.{wAb}` explicitly allow independent
  localization morphism universes for modules and abelian groups. The intermediate
  presheaf derived category is internal and uses `HasDerivedCategory.standard`.
- The unbounded category of module sheaves is
  `DerivedCategory (SheafOfModules.{u} (moduleRings X))`. The underlying module category
  is exactly the dependency's `ringedSiteModules`, transparently `SheafOfModules`;
  `moduleRings X` is the existing structure sheaf viewed in `RingCat`.
- An object E with no negative cohomology sheaves is rendered by the binder
  `E : DerivedCategory ...` and `∀ i : ℤ, i < 0 → IsZero
  ((DerivedCategory.homologyFunctor _ i).obj E)`. There is no upper bound on E.
- H^i(V,E) is the explicitly recorded `openModuleDerivedSections X V`, followed by
  `DerivedCategory.homologyFunctor AddCommGrpCat.{u} i`. The first conjunct quantifies
  over every E satisfying the hypothesis, every open V, and every integer i < 0,
  and asserts that this abelian group object is zero.
- The degree-zero hypercohomology presheaf is
  `(ringedSpaceHypercohomologyPresheaf X 0).obj E`. Its genuine definition derives
  the underlying abelian presheaf functor using the recorded arbitrary-resolution
  universal right-derived functor, then takes cohomology in abelian presheaves.
  Evaluation on a presheaf category is exact. On a K-injective representative I,
  its values and restrictions are therefore precisely H^0(Γ(V,I)) and those induced
  by section restriction, rather than cohomology in the sheaf category.
- The right-hand presheaf is `(moduleAbelianPresheaf X).obj
  ((DerivedCategory.homologyFunctor _ 0).obj E)`, exactly the abelian presheaf of
  sections of the zeroth cohomology sheaf.
- The second conjunct supplies a family `e E hE` of isomorphisms in the abelian
  presheaf category. Naturality of each presheaf isomorphism includes every
  inclusion W ⊆ V, with the actual derived-evaluation and sheaf-section restrictions.
- The first condition on the family is the full naturality square in E for every
  derived morphism `f : E ⟶ E'` between objects satisfying the negative vanishing.
- The next condition asserts `Presheaf.IsSheaf ...` for the hypercohomology
  presheaf and `IsZero` for its value at `op ⊥`. Thus the sheaf assertion explicitly
  includes the empty open, even when X itself is empty.
- Canonicity is specified by the final condition: for every module M and every
  derived map `f : M[0] ⟶ E`, precomposing the comparison with
  `hypercohomologyPresheafSingleUnit X M` and the map on hypercohomology gives
  the underlying presheaf map of H^0(f), with the canonical M ≅ H^0(M[0]) inserted.
  This is the cycle identification of the node, with its normalization fixed.
  In particular the comparison is not merely an unspecified isomorphism. Taking
  M = H^0(E) and the standard connective truncation map M[0] → E determines it;
  the statement does not ask for any extra map, model, or hypothesis as input.

Dependency declarations read and used:

- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`: `AlgebraicGeometry.RingedSpace`
  (imported from Basic), `PresheafedSpace.Hom`, `LocallyRingedSpace.Hom`.
  The item uses the general ringed-space component, as the dependency record permits.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the site here is the existing
  opens topology, not a new choice of coverings. The record imports the ordinary
  Mathlib sheaf/cohomology interfaces. There is no unusable dependency to repair.
- `def-weil-size-convention` is a metatheoretic convention; explicit `u`, `w`, and
  `wAb` render it. It has no object-level declaration, as its recorded note explains.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`, and `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  the helper uses that exact transparent abbreviation in its signature.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` and
  `rightDerivedFunctorOfQuasiIsoResolutionsUnit`. Both are used directly, rather
  than substituting a stronger resolution assumption.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`. The actual resolution objects and quasi-isomorphisms
  come from `CochainComplex.kInjectiveResolutionFunctor`, `toKInjectiveResolution`,
  and `monoQuasiIso_toKInjectiveResolution_app` in the existing
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`, including in the
  real unit construction. `FullyFaithful` supplies
  `singleFunctorCompHomologyFunctorIso` for the canonicity equation.
- `WeilConjectures.Topology.OpenModuleDerivedSections`:
  `AlgebraicGeometry.RingedSpace.openModuleDerivedSections`. Its full signature and
  K-injective computation docstring were read; it is reused for negative vanishing.
- Proof imports include `WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives`
  (`moduleSheaves_abelian_enoughInjectives`), Mathlib TStructure (`DerivedCategory.Plus`),
  DerivabilityStructureInjectives (`DerivedCategory.Plus.exists_injective_nonempty_iso`),
  DerivedCategory.KInjective (`CochainComplex.IsKInjective.Qh_map_bijective`), and
  `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses` (the recorded
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`).

Edge cases checked before writing and again against the final signature:

- E = 0 gives zero groups and the zero sheaf, with its canonical unit normalization.
- A module in degree zero has its own section sheaf in degree zero; its potentially
  nonzero positive hypercohomology is neither excluded nor asserted to vanish.
- A connective complex with arbitrarily high nonzero cohomology is included.
- Every negative integer, including -1, occurs in the first conjunct; degree zero
  has its own conclusion. No nonnegative-to-integer cast loses negative degrees.
- V = ∅ and X = ∅ are included. The explicit empty-open conclusion follows from
  the empty-cover axiom and the presheaf isomorphism.
- All opens, including non-quasi-compact opens of non-quasi-compact ringed spaces,
  and arbitrary derived maps between connective objects are included.
- Different module/abelian-group localization sizes remain independent. No equality
  is imposed between them or with the common coefficient universe.

Searches:

- `msearch.py ... leanfinder`: “For a connective complex of sheaves of modules,
  derived sections have zero negative cohomology and degree zero is sections of the
  zeroth cohomology sheaf” — eight hits; ordinary `Sheaf.H`,
  `Sheaf.cohomologyPresheaf(Functor)`, and complex-vanishing support, no exact theorem.
- `msearch.py ... loogle`: `DerivedCategory.homologyFunctor, SheafOfModules` — zero hits.
- `msearch.py ... grep`: `hypercohomology|cohomologyPresheaf` — ten Mathlib hits,
  ordinary natural-number-indexed cohomology of sheaves, not the unbounded presheaf here.
- `msearch.py ... leansearch`: “hypercohomology presheaf of an unbounded derived
  module sheaf on a ringed space” — eight hits; ordinary sheaf cohomology presheaves
  and module-presheaf interfaces, no exact definition.
- Direct `rg` in Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` found the existing
  open derived sections, the cohomology-presheaf evaluation comparison, and
  `AlgebraicGeometry.schemeDerivedSectionPresheaf`. The latter requires a scheme
  morphism and cannot represent the arbitrary ringed-space presheaf. All the new
  declaration names and the item id had no upstream hits.
- DAG grep found `def-pc-derived-section-presheaf`, whose statement explicitly has
  schemes, and `lem-pc-cohomology-presheaf-derived-sections-evaluation`, which assumes
  an already given presheaf rather than constructing one. Neither is duplicated.
  `tools/blueprint_refs.py search 'hypercohomology presheaf'` and
  `... search 'derived section presheaf'` each returned zero blueprint nodes.
  The new node retains the search outputs, including the three required kinds.

Source read: `literature/stacks-project/cohomology.tex`, proof of Tag 0D66 (1),
and Tag 0D5V and its proof for termwise sections on arbitrary opens. The tag table
was checked: 0D60 is actually an RΓ/Rlim lemma, so the new module cites 0D5V
rather than repeating that inexact citation from the older open-sections docstring.
No statement dispute or mathematical correction is needed.

Validation: both delivered modules compiled separately in dependency order through
`scompile.py`. The server returned clean results (7.9 s and 2.9 s) after the local
wrapper's disk-space fallback. All parameters and universes are explicit and
`autoImplicit` is disabled. The main theorem is the only postponed theorem.
No definition contains `sorry`, arbitrary comparison data, or a choice from an
existence assertion not fixing the object by a universal property.

## New nodes

`def-trf-ringed-space-hypercohomology-presheaf` in the item's chapter defines the
missing functor E ↦ (V ↦ H^n(RΓ(V,E))) for arbitrary ringed spaces, together with
its canonical unit on module sheaves in degree zero. Its module is
`Sheaf.Topology.RingedSpaceHypercohomologyPresheaf`; every declaration is listed
in its Lean record. The definition applies the recorded universal derived functor
to the existing underlying presheaf functor, with actual functorial K-injective
resolutions, then applies the Mathlib homology functor. The unit is the actual
universal unit transported by the existing quotient/single/homology comparisons.
Sources are Tags 0D5V and 0D66, and the derived-functor unit of 070K. The searches
above establish why the ordinary sheaf-cohomology functor and the scheme-only
presheaf do not provide this notion. No new proof obligation is introduced.

## Second reading by NX

A separate pass by this worker reread the node alongside both final modules;
the maintainer performs the independent review specified by the dispatch brief.
The rereading checked all binders, the universal quantification over connective
objects and every negative integer, presheaf (rather than objectwise) isomorphisms,
naturality in derived morphisms, restrictions, and the empty-open value. It also
checked the direction of every arrow in the unit-normalization equation: both
sides start at the underlying presheaf of M and end at that of H^0(E).
The unit definition first identifies ordinary single-complex cohomology, then
applies the homotopy-category derived unit transported to complexes; it does not
choose an arbitrary natural isomorphism. The missing ringed-space presheaf was
supplied as a new definition node, rather than restricting the statement to schemes.
The initially named proposition-valued helper was removed after the compiler's
linter warning; its fully proved resolution term is inlined in the two definition
bodies. No mismatch between the node and final statement was found.
