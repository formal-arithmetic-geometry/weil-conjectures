## Worker report

The module `Sheaf.Topology.SheafCotangentComparison` states
`TopCat.SheafCotangent.exists_comparison`. Its conclusion `Nonempty (Comparison C)`
collects the specified standard sheaf complexes and every comparison and coherence
clause. `C : Algebra.CotangentResolution.Coherence` is the already recorded ring
construction, not a new polynomial resolution or a hypothesis on the rings.
The section instance
`[∀ B : CommRingCat.{u}, HasDerivedCategory.{u+1} (ModuleCat.{u} B)]`
fixes the same localization-size choices as the ring dependency; it imposes no
condition on a ring. Sheaf module categories use `HasDerivedCategory.standard`.
There is one postponed theorem, `exists_comparison`, and its docstring contains
all nine proof steps of the node. Definitions contain actual data; no definition
chooses data from that theorem.

Hypothesis and clause correspondence:

- A topological space is `T : TopCat.{u}`, with arbitrary common size universe `u`.
  A homomorphism of sheaves of commutative rings is
  `f : Arrow (T.Sheaf CommRingCat.{u})`; its domain is A and codomain is B.
  No reducedness, nonzero, finiteness, separation or characteristic assumption is used.
- The module category is the dependency's `ringedSiteModules`, transparently
  `SheafOfModules`. `sheafComplex` is the actual termwise
  `PresheafOfModules.sheafification` of `SectionModel.complex`, retaining the B-action.
  `SectionModel.coordinate` identifies every section complex with the recorded
  `standardComplex C (sectionArrow f V)`, and `restriction` fixes every restriction
  as the recorded standard square map, in every integer degree.
- The standard sheaf polynomial resolution is `StandardSheafModel.algebra`.
  `freeAlgebraPresheaf A E` is the real presheaf `V ↦ A(V)[E(V)]`, with
  restrictions acting on coefficients and variable labels. `freeSheafAlgebra A E`
  is its sheafification; `freeSheafSection` is its canonical local polynomial map.
  The helper uses only the underlying sets of E, although E is supplied as a ring
  sheaf, as needed for B and the successive P_n. `initialFreeIso` states
  P_0 ≅ A[B]; `freeTermIso n` states P_(n+1) ≅ A[P_n].
  `initialFree_coeff` and `freeTerm_coeff` fix the coefficient maps.
  `initialFree_generator` identifies the degree-zero local generator [b] with
  the canonical generator of A[B]. `freeTerm_generator` identifies the local
  section [p] in the sheafified sectionwise next term with the generator
  [image(p)] of the actual free sheaf algebra on P_n. Thus `algebraIso`
  supplies a substantive comparison between the sheafified sectionwise iterates
  and the iterates in sheaves. It is no longer the entire term specification.
  `base_formula`, `augmentation_formula`, `face_formula` and
  `degeneracy_formula` give the coefficient, evaluation and unit maps in these
  normalized coordinates. Since every section of P_n is locally in the image
  of its sectionwise polynomial presheaf, these equations also fix the sheaf
  operators, including on generators labelled by arbitrary local P_n sections.
- Sheaf differentials are the existing `SheafDifferentials.omega` and
  `SheafDifferentials.derivation`, the actual sheafifications of sectionwise
  Kaehler differentials. `differentialSheaf` uses the existing
  `SheafOfModules.changeOfRings` (sectionwise tensor, then module sheafification).
  `StandardSheafModel.differentials`, `differentialIso` and `operator` are the
  simplicial module Omega(P/A) tensor_P B, normalized on b tensor dx.
  `complexIso` identifies its alternating-face complex with `sheafComplex`.
  `generator` fixes this isomorphism on every local standard differential tensor.
  `negativeComplex` is the dependency's alternating-face construction extended
  to nonpositive cohomological degrees; its positive terms are zero.
- For each open V the chain map is `SheafModel.sectionMap V`.
  `section_formula` identifies it with `sectionElement`, the actual module
  sheafification unit in standard coordinates. `section_restriction` is exactly
  restriction compatibility. Thus these maps sheafify to the displayed complex,
  rather than merely inducing an abstract isomorphism on cohomology.
- A continuous map is `v : T' ⟶ T`. `RingSquare v f g` is a square of sheaf rings
  in adjoint form, with maps A -> v_*A' and B -> v_*B'. `MapModel.section_formula`
  fixes the cotangent map by the corresponding recorded section-ring squares,
  and `scalar` states its actual semilinearity. `Comparison.maps` and `map_unique`
  supply the unique normalized maps for every such square. `map_id` and
  `map_comp` give identity and composition, hence naturality in maps of ring
  sheaves, including commuting diagrams between inverse-image squares.
- The inverse-image case is `Comparison.inverse`, with no hypotheses on the
  continuous map or rings. `inverseImageArrow v f` is the actual ordinary
  topological inverse image of the arrow of ring sheaves, and
  `inverseImageSquare v f` is its canonical adjunction unit square. These objects
  and maps are defined in full, rather than replaced by arbitrary presentations.
- `InverseModel.complex` is the inverse-image module complex. `underlying`
  identifies it with the *actual* topological inverse image of the underlying
  additive complex. Its `scalar` formula specifies the transported action on
  the inverse-image unit; locally these sections and scalars generate the
  inverse images. `comparison` is a module-complex isomorphism to L(B'/A'),
  and `normalization` fixes its underlying arrow to the adjoint of the canonical
  section map. `derived` is an isomorphism in the derived category of module
  sheaves, with `derived_normalization` fixing it as the image of `comparison`.
- `Comparison.inverse_comp` gives composition compatibility with the canonical
  inverse-image associator `inverseComposition`, defined by uniqueness of the
  left adjoint to the same composite pushforward. Together with the normalized
  module comparisons this states composition coherence of the requested
  identifications, rather than equality of unrelated chosen isomorphisms.
- A point is `t : T`, and `stalkArrow f t` is the actual arrow of stalk rings.
  `StalkModel.underlying` identifies its module complex with the actual additive
  stalk complex. `scalar` is the ordinary germ scalar formula.
  `comparison` is a stalk-module complex isomorphism to the recorded standard
  complex over the stalk rings. `germ_formula` fixes it by the actual section-to-
  germ square; `derived` and `derived_normalization` give its image in D(B_t).
  `StalkRingMap.germ_formula` fixes the ring maps in naturality.
  `Comparison.stalk_naturality` is naturality for every ring-sheaf square over
  a continuous map, on all germs of all sections, in every integer degree.
  This includes maps over the identity and restrictions to open subspaces.
- In the ring localization clause `f : Arrow CommRingCat`, S and W are arbitrary
  submonoids; `h : S ≤ W.comap f.hom.hom` is precisely f(S) contained in W.
  `localizationArrow` is the actual `IsLocalization.map` between `Localization S`
  and `Localization W`. `localizationSquare` uses their canonical structure maps.
  `baseChangeMap` is the tensor-adjoint of `standardComplexMap`, so it is exactly
  the canonical ordinary tensor comparison, with the symmetric order B' tensor L.
  `Comparison.localization` gives its `LocalizationModel`: the derived
  isomorphism, the equation identifying its hom with Q of this canonical chain
  map, and `QuasiIso` of that chain map itself. Thus the main comparison is in
  D(W^-1 B), and the assertion about the canonical quasi-isomorphism is retained.
- `successive_tensor` is the explicit equation on c tensor (b tensor x) identifying
  the two successive maps with the direct map on (c * r(b)) tensor x.
  This specifies compatibility with the actual tensor associativity comparison;
  in particular it applies to successive simultaneous localizations.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `HasDerivedCategory.standard`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, its universal
  derivation and universal linear-map equivalence; these are used through the
  existing standard differential module and sheaf-differential constructions.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Algebra.CotangentResolution.Coherence`, `standardTerm`, `standardBase`,
  `standardAugmentation`, `standardFace`, `standardDegeneracy`,
  `standardSquareMap`, `negativeComplex`, `complexGenerator`, `cotangentComplex`.
  Their full signatures and generator normalizations were read.
- Existing helpers in proof dependencies used in the statement:
  `Sheaf.RingTheory.CotangentTransitivityTriangle`: `standardComplex`,
  `standardComplexMap`, `tensorComplexAdj`;
  `Sheaf.CategoryTheory.Sites.InverseImageDifferentials`:
  `CategoryTheory.SheafDifferentials.ring`, `omega`, `derivation`;
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`:
  `SheafOfModules.changeOfRings`, `changeOfRingsPresheaf`.
- All recorded proof-dependency modules are imported, with private imports for
  those used only in the proof plan. No proof import is omitted for a cycle.

Edge cases checked before and during writing: the empty space has no stalk
obligation; its empty-open sections and the zero ring are allowed. All section
and restriction conditions include the empty open. There is no nontrivial-ring
or nonempty-space assumption. Positive cohomological degrees are the actual
zero terms of the recorded negative alternating complex. Degree zero uses the
actual evaluation faces and the standard augmentation. Infinite polynomial
variable sets are retained. S and W may be the unit submonoids, giving identity
localizations, or may contain zero, giving the zero localizations. Successive
and identity inverse images and localizations are included. All integer degrees
occur, and all variables/universes are explicitly bound (`autoImplicit false`).

Searches (2026-10-22):

- `msearch.py ... leanfinder "Cotangent complex sheaves rings stalk inverse image localization"`:
  eight hits, on naive cotangent modules/localization and module stalks;
  no full sheaf cotangent complex or this comparison statement.
- `msearch.py ... loogle "Algebra.Cotangent, SheafOfModules"`:
  zero hits, unknown identifier `Algebra.Cotangent`.
- `msearch.py ... leansearch "sheaf cotangent complex inverse image stalk localization"`:
  eight hits on tilde stalks and structure-sheaf localizations; none match.
- `msearch.py ... grep "CotangentResolution|SheafCotangent|cotangent.*[Ss]heaf"`:
  zero Mathlib hits. A broader cotangentComplex search found the naive
  extension cotangent map, not the standard full cotangent complex here.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for cotangent construction names
  found the recorded ring construction and related ring statements; no
  duplicate of the assigned sheaf statement. Searching the exact blueprint id
  found only a proof-plan citation in `PolynomialCotangentIdentification.lean`.
- Read Stacks `cotangent.tex`, the definitions and proofs at the seven cited
  labels, including the sectionwise sheafification remark and the localization
  proof. All sources are present locally; no external source was needed.

No statement correction, dependency replacement, new node or disputed statement.
The auxiliary structures are coordinate presentations of the objects and maps
in this node, all owned by its module and listed in `lean.declarations`.

## Second reading by Q31

Reopened the node and module and reread each clause against the correspondence
above. The rereading checked that section comparisons are chain maps; sheaf
polynomial operators are prescribed, not arbitrary; the sheaf differentials and
tensors are the existing sheafifications; scalar actions survive both inverse
image and stalks; the displayed identifications include derived module-category
isomorphisms; localization is the tensor-adjoint of the canonical square map;
and both composition assertions identify actual maps. The inverse-image
clause uses the canonical ring inverse images and adjunction-unit square
directly and imposes no topological/ring hypotheses. The germ
naturality clause covers open restrictions as well as maps on one space.

Compiler checks found that evaluation must be exposed as forget followed by
presheaf evaluation to synthesize additivity, and that underlying additive
carriers need their module actions supplied explicitly in scalar equations.
Both were corrected without changing the mathematical assertion. The canonical
inverse-image unit square uses the symmetric form of unit naturality. Line widths
were checked. This is the worker's rereading; no second agent was started,
as required by the dispatcher's brief. Independent delivery review is performed
by the maintainer.

## Repair of H3 (returned head 4b9173e067c0)

The required initial dry run of the saved packet passed at f30f37a303a, but a
self-check against the return confirmed that this was only a mechanical pass:
the mathematical H3 defect remained. The saved report's assertion that the
sectionwise iterates alone specified the standard sheaf resolution was removed.
The three construction helpers and six fields described above are the concrete
repair. They belong to the standard-resolution construction already introduced
by this node (Stacks 08SR), not a separate theorem or a chosen arbitrary map.
No additional postponed theorem or definition with unknown data was introduced.
The node's mathematical statement and its dependencies are unchanged; only its
Lean record changes. The delivery wrapper rebases the packet on current main;
comparison of the sandbox and current node confirmed equality outside `lean`.

Read Stacks `cotangent.tex` at the standard-resolution definition (08SR) and
at the inverse-image and sheafification comparisons (08SV, 08SW). The source
explicitly iterates the free algebra on sheaves, before making the sectionwise
comparison. The new fields make precisely this distinction in the statement.
The degree-zero comparison includes both C(a) and X(b); each successor includes
C(a) and X(p), with p mapped through `polynomialSection`. The latter sections
locally generate all labels in P_n, including when the global sectionwise map
is not surjective. The existing face and degeneracy formulas are retained and
now transport the actual evaluation/unit operators under these comparisons.
Thus step 2 of the proof docstring requires the free-algebra preservation
argument from step 1; it does not follow from a tautological choice of P_n.

Additional repair searches (2026-10-22):

- `msearch.py leanfinder "free sheaf of commutative algebras sheafification of
  polynomial rings"`: eight hits, on free module sheaves and tilde module
  sheaves, with no free commutative algebra sheaf construction.
- `msearch.py leansearch "free sheaf commutative algebra on underlying sheaf
  of sets polynomial sheafification"`: eight hits on free module sheaves,
  free Yoneda and set sheafification; no matching algebra construction.
- `msearch.py loogle "MvPolynomial.eval₂Hom, MvPolynomial.C"`: twelve hits;
  the existing `eval₂Hom` is used for restriction on coefficients and labels.
- `msearch.py grep
  "freeSheafAlgebra|polynomialPresheaf|free.*[Ss]heaf.*[Aa]lgebra"`: zero hits.
- `rg` for `freeSheafAlgebra|freeTermIso` in the topological project sources
  and Mathlib sheaf/algebra directories: no declaration. The broader free-sheaf
  searches in the library and DAG gave free module sheaves, not this construction.

Second reading of the repair: empty opens and the empty space require no
nonempty set of labels; zero coefficient rings are allowed by `MvPolynomial`
and sheafification. The successor generator equation includes every p, with
no nonzero, finiteness or injectivity assumption on a sheafification unit.
The inverse-image, stalk and localization clauses checked sound in the return
were reread and preserved. The advisory concerning plain construction defs in
proof-dependency modules requires no replacement: these exact existing
constructions remain imported and used, as recorded above. No node statement
correction or new dependency interface is involved.

Compilation-cost repair: the full-file profiler reached `Comparison` with no
elaboration errors; generation of automatic structure size specifications and
constructor injectivity lemmas contributed unnecessary work. The final file
uses Mathlib's `genSizeOfSpec false` and `genInjectivity false` options to omit
these unused generated lemmas. No mathematical field is removed, no file is
split, and the per-file compile limit remains 60 seconds. Profiling and the
temporary heartbeat diagnostic are removed from the delivered source.

Validation: `scompile.py Q31 lem-trf-affine-cotangent-comparison
lean/Sheaf/Topology/SheafCotangentComparison.lean` passed cleanly for the complete
module in both wrapper checks: sandbox 51.6 seconds, final library name 41.5
seconds. The source has exactly one named theorem with `sorry`; the new
construction definitions have real data and their functor laws are checked.
The signature matches `lean.statement` verbatim and every line is at most 100
characters. The final required dry run and push use `deliver2.py`.
