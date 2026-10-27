## Worker report

The delivery states lem-trf-geometric-standard-differential-comparison in
`Sheaf.CategoryTheory.Sites.GeometricStandardDifferentialComparison`, namespace
`CategoryTheory.GeometricStandardDifferentials`. The node changes only in `lean` and the addition of two landed definition
nodes to `stmt_deps`, as requested in the return. There are no new nodes, dependency repairs, statement corrections,
or disputed statements. Nothing is proved: all eight named theorem bodies are
`sorry`, with their source and natural-language proof in the docstring.

The primary declaration is `geometric_standard_differential_comparison`.
The companion declarations state construction existence, ring-square maps,
naturality, the availability of identity and composite lifts, and their
coherence equations. `derivedComparison` is a real definition applying the
existing localization functor to the actual complex isomorphism.

### Hypotheses and clauses

- Sites C and D: the explicitly bound independent object and morphism universes
  `uC, vC, uD, vD`, with `Category` and `EssentiallySmall.{w}` instances and
  arbitrary Grothendieck topologies J and K. This is precisely smallness in the
  common sheaf-value universe w, without equating site universes.
- The geometric morphism: `f : GeometricMorphism (Sheaf K (Type w))
  (Sheaf J (Type w))`. Its inverse is `f.inverse`; the recorded structure includes
  its direct image, adjunction, and preservation of finite limits.
- R and E: `R : Sheaf J CommRingCat.{w}` and `E : Sheaf J (Type w)`.
  `AlgebraConstruction.free R` is left adjoint to the specified underlying-set
  functor on `Under R`, the category of commutative R-algebra sheaves.
  `polynomial`, `coefficient`, `variableMap`, and `evaluate` are its actual
  object, structure map, adjunction unit, and adjunct evaluation map.
- The requested sheafification of sectionwise R(U)[E(U)] is retained by
  `PolynomialPresentation`: its presheaf has section isomorphisms to
  `CommRingCat.of (MvPolynomial (E.obj.obj U) (R.obj.obj U))`; `restriction`
  specifies polynomial evaluation on restricted coefficients and variable labels.
  `sheafification` identifies its actual `presheafToSheaf` with `polynomial`;
  the two normalization fields identify coefficients and variables. The theorem
  `construction_exists` supplies these presentations for every R and E, as well
  as the standard differential construction. No extra existence assumption is
  required of the sites.
- F(R[E]) ≅ (FR)[FE]: `FreeComparison.iso R E` is an isomorphism in commutative
  ring sheaves; `coefficient` makes it an FR-algebra isomorphism, and
  `variable_map` fixes the inverse image of the variable map. `evaluation`
  states compatibility with every evaluation, including the counit;
  `variable_map` is compatibility with the free-algebra unit. `naturality`
  includes simultaneous maps of coefficients and generator sheaves.
- The induced ring and module inverse images are not arbitrary: `InverseLift`
  has a ring functor with its underlying natural isomorphism and, for each ring,
  the recorded `AlgebraicInverseImageOfUniverses`. `ring_underlying` identifies
  the ring comparisons, so every ring and module graph-transport axiom of that
  dependency applies. Its `additive` field is part of the asserted construction,
  not an additional assumption on a geometric morphism.
- A → B: the explicit commutative-ring-sheaf morphism `φ : A ⟶ B`, with no
  flatness, nonzero-ring, or other extra condition.
- P0=A[B], P(n+1)=A[Pn] with all specified operators: `standard_spec` uses the
  recorded `Comonad.IsStandardSimplicialResolution` of the exact free/forgetful
  adjunction. It specifies powers of that comonad and every counit face and
  comultiplication degeneracy. `resolution` evaluates those endofunctors at
  `Under.mk φ`; `prior`, `labels`, and `coordinates` expose the prescribed
  recursive terms. `augment` is the iterated evaluation augmentation.
- FP ≅ P': `StandardComparison.algebra` is an actual natural isomorphism of
  simplicial ring sheaves. `base` and `augmentation` preserve the algebra
  structures and augmented maps. `generator` fixes its recursive generator
  maps. Being a natural isomorphism on the entire simplex category includes
  every face and every degeneracy, not merely a family of term isomorphisms.
- Sheaf differentials and their universal derivation:
  `SheafDifferentials.omega`, `.derivation`, and `.d` are the existing actual
  sheafifications of sectionwise differentials. `TermDifferentialIso` is a
  module isomorphism, with the target restricted along the algebra-term
  comparison. `omega_derivation` fixes the transported universal derivation.
- Ω(P/A) tensor_P B: `differentialTerm` uses the existing
  `changeOfRingsOfUniverses` on the augmentation and `omega (base φ n)`.
  This is the sheafified tensor with coefficient factor first, B tensor_P Ω;
  symmetry gives the displayed Ω tensor_P B convention. `tensorSection`
  applies the actual module-sheafification unit to the sectionwise pure tensor;
  `tensorD` specializes to b tensor dp. `DifferentialConstruction.term` identifies
  every term with this exact construction; `operator` fixes every simplex map
  on differential tensors.
- The compatible simplicial FB-module isomorphism is
  `StandardComparison.simplicial`, a natural isomorphism of simplicial module
  sheaves. Its `pairing` field quantifies over every test sheaf T and morphisms
  b, x, z expressing the actual tensor pairing, then fixes the transported
  pairing on every section of FT. It applies to arbitrary differential-module
  sections x, not only to individual dp. In particular x=dp fixes universal
  differential tensors, and b=1 fixes the coefficient tensor map ω↦1 tensor ω.
  This avoids assuming that F is computed sectionwise.
- s(M)^(-n)=M_n with alternating differential and positive terms zero:
  `AlternatingConstruction.term`, `.differential`, and `.positive_zero` specify
  exactly those terms and differential. Term identifications are explicit
  isomorphisms of modules; they do not assert an unspecified derived equivalence.
- The actual complex isomorphism is `StandardComparison.complex`; its
  `complex_degree` identifies its negative-degree components with the stated
  simplicial comparison. The derived isomorphism is `derivedComparison`, defined
  as `localization.mapIso e.complex`, using the existing `DerivedCategory.Q`
  and `HasDerivedCategory.standard`, with no additional derived-category
  universe assumption and no independently chosen derived arrow.
- Naturality for arbitrary commutative ring squares:
  `constructionSquare_exists` supplies `ConstructionSquare` for any
  a:A→A', b:B→B' with a≫φ'=φ≫b. Its `ResolutionSquare` fixes the actual recursive
  polynomial map; `tensor_generator` fixes the differential-tensor map, and
  `complex_degree` fixes its actual complex map. `comparison_naturality`
  states equality of the two orders for algebra terms, module terms and every
  integer complex degree, after forgetting along the faithful underlying
  functors. These are equivalent to the corresponding simplicial and complex
  equations, also with changing target scalars. Localization preserves them.
- Identity coherence: `identityLift_exists` supplies the literal identity
  ring lift and underlying comparison; `comparison_identity` states that every
  normalized free, algebra-resolution, differential-tensor and complex
  comparison is the identity under these identifications.
- Composition coherence: `compositeLift_exists` supplies the exact composite
  ring lift and successive underlying comparisons. `comparison_composition`
  identifies direct and successive free, algebra, module and complex arrows.
  The HEq equations retain independently presented coefficient objects while
  the supplied ring-functor equality identifies them; they do not replace
  naturality or invertibility by a bare existence assertion.
- Presheaf topoi: J, K (and L in composition) are arbitrary, so bottom topology,
  where only maximal sieves cover, is included without another hypothesis.

### Dependency declarations read and used

- def-trf-comonad-standard-resolution:
  `Sheaf.CategoryTheory.ComonadStandardResolution`,
  `CategoryTheory.Comonad.resolutionPower` and
  `CategoryTheory.Comonad.IsStandardSimplicialResolution`; the owning definition
  node is now explicitly listed in stmt_deps.
- def-sfb-sheaf-differentials:
  `Sheaf.CategoryTheory.Sites.InverseImageDifferentials`,
  `CategoryTheory.SheafDifferentials.ring`, `.sets`, `.moduleSets`, `.omega`,
  `.derivation`, and `.d`; the owning definition node is now explicitly listed
  in stmt_deps. Underlying ring-map morphisms use `(setsFunctor J).map` or
  `(setsFunctor K).map`, rather than the theorem-owned `.setsMap` abbreviation.

- def-trf-geometric-morphism:
  `Sheaf.CategoryTheory.Sites.GeometricMorphism`,
  `CategoryTheory.GeometricMorphism` and `.comp` (publicly through
  InverseImageDifferentials).
- def-weil-pbc-sheafification:
  `Mathlib.CategoryTheory.Sites.Sheafification`,
  `CategoryTheory.presheafToSheaf`, `.toSheafify`, and `.sheafificationAdjunction`.
  Ring sheafification at independent site universes uses Mathlib's
  `hasSheafifyEssentiallySmallSite`, with its explicit universe arguments.
- def-weil-pbc-kahler-differentials:
  `Mathlib.RingTheory.Kaehler.Basic`, `KaehlerDifferential`,
  `KaehlerDifferential.D`, `KaehlerDifferential.linearMapEquivDerivation`;
  these are used through the recorded `SheafDifferentials.omega` and derivation.
- def-weil-sheaf-of-modules-category:
  `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, the existing Mathlib `SheafOfModules`.
- def-weil-abstract-derived-category:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `HasDerivedCategory.standard`, and `DerivedCategory.Q`.
- def-weil-pbc-mv-polynomial-ring:
  `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`,
  `MvPolynomial`, `MvPolynomial.eval₂Hom`, and the coefficient/variable maps.
  The polynomial universal property and extensionality give the stated proof.
- def-pur-sheaf-tensor-product:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, with the
  existing `SheafOfModules.changeOfRingsOfUniverses` and
  `.changeOfRingsPresheafOfUniverses` publicly imported through it.
- def-weil-pbc-algebraic-inverse-image:
  `Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses`,
  `SheafOfModules.AlgebraicInverseImageOfUniverses`, including every ring and
  module graph equation and its underlying-module natural isomorphism.

All available proof dependencies are imported: the recorded adjunction lift,
standard simplicial homotopy theorem, simplicial operator reconstruction,
geometric inverse-image exactness, sheafified differential cokernel,
inverse-image differential comparison, normalized inverse-image tensor
comparison, and sheaf tensor bilinear universal property. The actual comonad
operator specification is reused from
`Sheaf.CategoryTheory.ComonadStandardResolution`; no copy of those identities
is introduced.

### Edge cases

Checked the empty generator sheaf (only coefficients, giving R), zero coefficient
and target rings (no nontriviality binder), arbitrary/infinite generator sheaves,
identity ring maps, changing base and target rings in the same square, degree 0,
degree -1 (two alternating faces), all positive degrees (zero), identity geometric
morphisms, composites, and bottom topologies. No field, characteristic, point,
flatness, topological-space, or equal-site-universe hypothesis occurs.
Underlying sets are lifted by the same `uliftFunctor.{w,w}` as the recorded
algebraic inverse-image dependency, not by a different universe convention.

### Searches

- msearch.py leanfinder: "geometric inverse image compares standard simplicial
  free commutative sheaf algebra resolutions and differential complexes".
  Eight hits were Dold-Kan formulas and Rep.standardComplex.compForgetAugmentedIso;
  none states the sheaf polynomial/differential comparison.
- msearch.py loogle: "CategoryTheory.Sheaf, MvPolynomial". Zero hits.
- msearch.py leansearch: "geometric inverse image free sheaf polynomial algebra
  standard simplicial resolution differential tensor complex". Eight hits on
  free module sheaves and module pullback; none on this algebra resolution.
- msearch.py grep: "standardResolution|cotangentComplex|polynomialSheaf" in
  CategoryTheory. Zero hits in Mathlib.
- rg of the same concepts and standard/free-algebra variants in the live
  `lean/WeilConjectures` and `lean/Sheaf` trees; rg of the exact blueprint id in
  WeilConjectures; rg of names in dag/lean_names_upstream.json. No declaration
  already states this node. Existing ring cotangent coherence is about rings;
  SheafPolynomialCotangentComparison is a naive two-term presentation theorem;
  StandardSheafCotangentFlatModel and SheafCotangentComparison are over
  topological spaces. None provides the arbitrary-topos statement with the
  required full simplicial, differential, square and composition normalization.
- Read the existing small-site polynomial sheaf construction in
  Sheaf.CategoryTheory.SheafPolynomialCotangentComparison. The delivery does
  not construct another competing polynomial sheaf: it uses the free adjunction
  and identifies that canonical object with sectionwise polynomial sheafification
  in PolynomialPresentation, at the required independent site universes.
- Source read: literature/stacks-project/cotangent.tex, section on sheaves of
  rings, the paragraph before 08SR through the proof of 08SV and its application
  to the chaotic topology in 08SW. These give exactly the free-adjunction,
  standard-resolution, differential-tensor and geometric-inverse-image route.

### Validation

Each compiler invocation used the prescribed scompile.py against the live build;
no source checkout was modified and no global build was run. Early compiler
repairs made the Monad.Adjunction public import explicit, avoided Lean keywords
as field names, supplied independent universe arguments on scalar extension,
and supplied Mathlib's ring-sheafification transport instance. Final validation
and delivery results are recorded below after the prescribed dry run.

## Second reading by Q62

This dispatcher assignment explicitly forbids starting another agent. This is a
second clause-by-clause self-reading, not a claim of an independent worker review;
the maintainer supplies the independent delivery review.

Reopened the node and the full module. Matched its small-site/geometric-morphism
hypotheses to the binders, its R[E] to PolynomialPresentation plus the exact free
adjunction, P0 and higher terms to the actual specified comonad powers, all faces
and degeneracies to standard_spec and the simplicial natural isomorphisms,
augmentations to the augmentation equations, differentials to the imported
sheafification, tensor maps to the universally tested pairing normalization,
negative degrees and signs to AlternatingConstruction, positive terms to IsZero,
and the derived comparison to Q.mapIso of the actual chain isomorphism.
Rechecked the square theorem for changing coefficients, rather than only maps
over one fixed ring. Rechecked the identity and composition equations for every
comparison layer and the inclusion of bottom topologies.

This reading added identityLift_exists and compositeLift_exists: their coherence
conditions are supplied by asserted canonical presentations, not left as possibly
uninhabited conditions. It also retained arbitrary differential-module x in the
pairing field, so the coefficient tensor map is included in addition to dp tensors.
No missing node clause or source-based statement correction was found. All data
in definitions are explicit adjunction operations, existing tensor/sheafification
operations, or recorded isomorphisms; no definition extracts a choice from a sorry.

Final validation: scompile.py passed both the sandbox and named-library module
checks, with no errors or unexpected warnings (22.5 s and 21.8 s). The prescribed
deliver2.py --no-push printed `OK (dry run)` for ced2f05eae4: server preflight and
per-file compilation passed. No global build or direct Git operation was run.


## Repair of return on bf443b066338

H2/H4: added the already landed definition nodes
`def-trf-comonad-standard-resolution` and `def-sfb-sheaf-differentials` to
`stmt_deps`, using the explicit permission for landed-node additions in
brief-stage2 §5 and the return's correction. Read each current node, its lean
record, and the full recorded definitions and docstrings. The comonad node owns
`resolutionPower` and `IsStandardSimplicialResolution`; the sheaf-differential
node owns `ring`, `sets`, `moduleSets`, `omega`, `derivation`, and `d`.
These definitions are reused through their existing public imports.

Replaced all thirteen occurrences of `SheafDifferentials.setsMap` by the map
of the existing `setsFunctor` at the appropriate site. Source-site maps use J
in squareLabels, ResolutionSquare, the source coordinates in inverseLabels,
and the source ring-square map in comparison_naturality. Transported ring maps
use K in inverseLabels, StandardComparison, StandardComparison.algebraArrow,
and the target ring-square map in comparison_naturality. The existing
setsFunctor is exactly the same `sheafCompose` functor as setsMap's body.
No private copy or replacement definition was introduced.

The primary theorem signature is textually unchanged, verified against
lean.statement. The node's mathematical statement, proof and proof dependencies
are unchanged. Comparing the retained sandbox node to current main before the
repair found only the original lean record, so no intervening main-node change
was overwritten. The delivery wrapper refreshes main and constructs the repair
commit on the current server base.

Second reading of the repair: reopened the return, both owning definition nodes,
the existing setsFunctor and setsMap definitions, and each changed Lean use.
Checked that all thirteen maps retain their original source/target objects,
including the two different sites in inverseLabels and comparison_naturality.
The return accepted all mathematical clauses; their normalizations and
coherence equations are preserved. This is a self-reading under the dispatcher's
no-subagents rule, with independent review left to the maintainer.

Repair validation: scompile.py passed the sandbox and named-library module
checks with exit code 0 and no errors or warnings. The wrapper reported
999.5 s for the sandbox check (including server waiting) and 52.4 s for the
named-library check.

The repair dry run `deliver2.py --no-push` passed: commit
fc7a1387516 passed server preflight and per-file compilation.
