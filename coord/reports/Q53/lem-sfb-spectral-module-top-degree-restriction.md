## Worker report

The module Sheaf.Topology.SpectralModuleTopDegreeRestriction states
`AlgebraicGeometry.RingedSpace.surjective_openModuleCohomologyRestriction_of_spectralSpace`.
Its sole theorem has `sorry`; there are no new definitions and no proved statements.
The statement is unchanged. Added the already landed definition node
`def-sc-open-module-cohomology` to stmt_deps because it owns the canonical restriction map.
No dependency repair or statement correction is needed.

Clause-by-clause correspondence:

- The space T with its sheaf of commutative rings O is bundled as
  `(X : RingedSpace.{u})`. Mathlib's RingedSpace is `SheafedSpace CommRingCat`,
  with no locality assumption on its rings. `[SpectralSpace X]` is precisely the
  spectral-space assumption; it does not assert that X is a scheme or Noetherian.
- The arbitrary O-module F is `(F : ringedSiteModules.{u} (moduleRings X))`.
  The recorded abbreviation unfolds to Mathlib's SheafOfModules, and moduleRings
  forgets commutative rings to rings without changing the sheaf or its modules.
  There is no quasi-coherence, coherence, or finite generation assumption.
- The nonnegative integer d is `(d : ℕ)`. The bound is
  `(hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))`, with bottom representing
  dimension minus infinity. This uses the recorded Mathlib definition verbatim.
- Every quasi-compact open is covered by `(W : Opens X)` and
  `(hW : IsCompact (W : Set X))`; compact here means quasi-compact, with no
  Hausdorff requirement. There is no assumption that W is nonempty.
- The conclusion is Function.Surjective of the component at F of
  `openModuleCohomologyRestriction X d (homOfLE (le_top : W ≤ ⊤))`.
  Its source is `(openModuleCohomology X d ⊤).obj F` and target is
  `(openModuleCohomology X d W).obj F`. These are the right derived functors
  of sections over the whole space and W, in all O-modules. The map is
  NatTrans.rightDerived of actual section restriction, hence is exactly the
  restriction on section complexes of injective resolutions. Restriction of
  injective module resolutions to opens identifies the target with the
  cohomology of the ordinary restrictions F|W and O|W. No abelian-sheaf Ext
  group is substituted for module cohomology.

Dependency declarations read and used:

- Mathlib.Topology.Spectral.Basic: SpectralSpace (T0, compact, quasi-sober,
  quasi-separated, and a basis of compact opens).
- Mathlib.Topology.KrullDimension: topologicalKrullDim, defined as
  Order.krullDim of nonempty irreducible closed subsets.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules,
  the transparent general-site specialization of SheafOfModules.
- WeilConjectures.Topology.RingedSpaceModuleCohomology:
  AlgebraicGeometry.RingedSpace.moduleCohomology, the module-valued right
  derived global sections functor, and its resolution comparison.
- WeilConjectures.Topology.OpenModuleCohomology:
  AlgebraicGeometry.RingedSpace.openModuleSections, openModuleCohomology,
  and openModuleCohomologyRestriction. These give the specified additive
  cohomology groups on opens and their canonical maps. This is the existing
  project convention for cohomology on opens, including the top open; it
  agrees with moduleCohomology after forgetting scalars.

Every already recorded proof-dependency module is imported privately, including
Mathlib.Algebra.Homology.HomotopyCategory.KInjective for the mathlib_match
CochainComplex.isKInjective_of_injective. The unrecorded comparison node
lem-sfb-ringed-sections-forget-abelian has no module to import. All five steps
of the accepted proof are reproduced in the theorem docstring with node ids:
degree-zero clopen gluing; restriction-natural module/abelian comparison;
punctured-neighborhood dimension drop and vanishing; filtered-colimit zero
detection; and Mayer–Vietoris lifting of (xi,0).

Edge cases checked before writing:

- X empty: its dimension is bottom, so the bound is allowed for every d,
  and both section-derived groups vanish.
- W empty: its target is zero in every degree and surjectivity holds.
- W = top: the inclusion is the identity, so the derived map is the identity.
- d = 0 and X nonempty: spectral dimension zero makes X profinite. A compact
  open W is clopen and sections extend by zero; no restriction on O is needed.
- dim X strictly below d: cohomology on W vanishes in degree d, so the upper
  bound rather than equality causes no strengthening beyond the source.
- F zero and the zero ring sheaf are allowed; the result still holds.
- No Noetherian, Hausdorff, scheme, or coherence class is introduced. One common
  size universe is used for the small open site and coefficients, as in the
  recorded cohomology interface; larger sheaves/spaces can be placed in a
  common universe without changing the assertion.

Sources opened: literature/stacks-project/cohomology.tex,
proposition-cohomological-dimension-spectral (0A3G), statement and proof of (2),
and lemma-modules-abelian (01F1), statement and common-resolution proof of (1).
The proof confirms both the compact-open restriction map and the module convention.

Searches for an existing statement:

- msearch.py leanfinder: "For a spectral ringed space of Krull dimension at most d
  the degree d cohomology of every module sheaf restricts surjectively to a quasi
  compact open". Eight hits, concerning basic opens, degree-zero scheme sections,
  affine Zariski covers, and pointsPi; no top-degree spectral module theorem.
- msearch.py leansearch: "Top degree cohomology of module sheaves on a spectral
  ringed space restricts surjectively to quasi compact open subsets". Eight hits
  on basic opens, scheme module restriction and restriction to top; no match.
- msearch.py loogle: `"cohomology", "surjective"`. Only
  CochainComplex.HomComplex.CohomologyClass.mk_surjective, which concerns
  representatives of Hom-complex classes, not this theorem.
- msearch.py grep: `cohomolog.*surject|surject.*cohomolog|cohomologicalDimension`.
  Two hits in injective/projective Ext, neither the result.
- rg in lean/WeilConjectures and lean/Sheaf for moduleCohomology/restriction
  combinations found OpenModuleCohomology and ModuleMayerVietoris, which supply
  the canonical objects. The existing scheme-only top-degree restriction
  modules do not state the theorem for arbitrary spectral ringed spaces.
- rg in both source roots for `spectral.*[Ss]urject|surject.*spectral` and
  the item id found only unrelated spectral closed-restriction results; no
  matching item declaration. The exact proposed theorem name is absent from
  dag/lean_names_upstream.json and both source trees.

No STATEMENT-DISPUTED issue was found.

## Second reading by Q53

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
