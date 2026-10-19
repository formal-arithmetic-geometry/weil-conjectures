## Worker report

The module `Sheaf.CategoryTheory.BoundedFilteredPageFunctorNormalized` states
`CategoryTheory.boundedFilteredComplex_pageFunctor_normalized`, with its entire
proof `sorry`. It defines no objects and proves no theorem. The statement is an
explicit strengthening of the recorded `boundedFilteredComplex_pageCore`:
all its comparison, exact-couple, convergence and stabilization clauses remain,
for the very same functor, with the quotient comparisons chosen globally so the
successor normalization refers to those same comparisons.

Hypothesis and clause correspondence:

- The abelian category is `(C : Type u) [Category.{v} C] [Abelian C]`, with
  independent object and morphism universes explicitly bound.
- Integer-indexed complexes with finite decreasing subcomplex filtrations form
  `ObjectProperty.FullSubcategory (fun W : FilteredObject (CochainComplex C ℤ) ↦
  W.filtration.IsFinite)`. A subobject of a cochain complex is a subcomplex.
- The supplied family is `φ U p r hr`, with precisely the source and target
  quotient complexes in the node. `hr : 1 ≤ r` covers every positive integer page.
- `hφ` is exactly the source quotient projection equation, using
  `Subobject.ofLE` for the filtration inclusion. No further hypothesis is added.
- The existential `S` is a functor from that full subcategory to
  `CohomologicalSpectralSequence C 1`.
- `e₁` and `eI` are the first-page and image comparisons of the page core.
  Its first conjunct on these witnesses is the page-one image inclusion equation.
  Its filtered-map conjunct supplies the step, two quotient and graded maps,
  all four projection equations, and both comparison naturality equations.
- The global containment witnesses `hBZ` and isomorphisms `eZ` identify each
  actual page object with `cokernel (Subobject.ofLE _ _ (hBZ U p q r hr))`,
  exactly the specified `Q_r = Z_r/B_r`. These are conclusion witnesses, not
  assumptions. The original representative clause uses these very same `eZ`.
- Successor representatives are cycles: the first new conjunct supplies `hZ`
  and an epic map `f : Z_(r+1) → (S(U).page r).cycles (p,q)` with
  `f ≫ iCycles = ofLE hZ ≫ π_r ≫ eZ.inv`.
  This is the categorical interpretation of the node's element language.
- For every candidate isomorphism `e : H(S(U)_r) ≅ S(U)_(r+1)`, the
  universal normalization square is equivalent to
  `e = (S.obj U).iso r (r+1) (p,q) rfl hr`. Thus the actual successor satisfies
  the square, and every normalized candidate equals it. The square is
  `f ≫ homologyπ ≫ e.hom ≫ eZ_(r+1).hom = π_(r+1)` for every containment
  proof and every cycle lift with the stated inclusion equation. This is
  `FilteredComplexHomologyNormalized`'s defining equation transported through
  the explicitly chosen page identifications, rather than a new predicate.
- The next conjunct is exactly the node's filtered-map successor equation,
  in Lean's left-to-right composition convention: `iso_U.hom ≫ S(t)_(r+1)`
  equals `H(S(t)_r) ≫ iso_V.hom`. Both sides use the functor's actual maps.
- Every remaining clause of the page core is retained explicitly: the short
  exact sequence and both quotient-projection equations for `d₁`; the maps
  `z,g` and image-comparison representative equation; `G` with the image
  formula, finiteness and separatedness; the type-zero couple `X`, `L`,
  alpha-colimits `A`, `aH`, `eD`, `eC`; the alpha-colimit cocone, alpha,
  initial-gamma and derived-differential equations; `X.ConvergesTo L A`;
  the infinite-page comparison; eventual cycle/boundary stabilization,
  zero outgoing/incoming differentials, and stationary page isomorphisms.
- There is no cochain-degree boundedness, support/quadrant, projectivity,
  concrete-category, direct-sum or extra-universe hypothesis.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`.
- `WeilConjectures.CategoryTheory.Abelian.Filtration`:
  `CategoryTheory.DecreasingFiltration`, read via `scompile.py --source` because
  this published module is missing from the older local source checkout.
  `Sheaf.CategoryTheory.Filtration` supplies its `step`, `antitone_step`,
  `gradedPiece` compatibility accessors and the filtered-map category; the
  published upstream compatibility interface supplies `IsFinite`.
- `Sheaf.Algebra.Homology.FilteredComplexSubquotients`:
  `DecreasingFiltration.complexQuotient`, `complexQuotientπ`,
  `complexCycleRepresentatives`, `complexCycles`, `complexBoundaries`.
- `Mathlib.Algebra.Homology.SpectralSequence.Basic`:
  `CategoryTheory.SpectralSequence`, `CohomologicalSpectralSequence`,
  `SpectralSequence.iso`, `SpectralSequence.Hom.comm`.
- `Sheaf.CategoryTheory.BoundedFilteredComplexPageCore`:
  `CategoryTheory.boundedFilteredComplex_pageCore`; its entire signature is
  retained, with its previously local quotient comparisons moved to global
  witnesses to bind normalization to the representative image equation.
- `Sheaf.CategoryTheory.FilteredComplexNormalizedHomology`:
  `CategoryTheory.filteredComplex_normalized_homology` and its defining
  predicate `FilteredComplexHomologyNormalized`. The normalization and
  uniqueness are written out for the identified actual page differential.

All stated proof dependencies are imported. Proof-only imports are non-public.
The proof docstring follows all ten proof steps of the DAG node, naming their
supporting nodes. Source read: `literature/stacks-project/homology.tex`,
section-filtered-complex, lemma-spectral-sequence-filtered-complex and
lemma-spectral-sequence-filtered-complex-functorial (Tags 012K, 012M, 012O).
These formulas work degree by degree in an arbitrary abelian category.

Edge cases checked before writing: the zero complex and zero pages; trivial,
shifted and negative-index finite filtration tails; r=1 including its page-two
successor; negative p,q and total degree; complexes unbounded in both cochain
directions. Every normalization is a morphism equation, so no element carrier
or projective generator is assumed. Finite filtration is not replaced by a
first-quadrant or bounded-complex condition. Containment-proof choices do not
change subobject inclusion maps by proof irrelevance. Isomorphism candidates
are universally quantified, so the assertion includes uniqueness rather than
merely existence of some comparison.

Searches performed through the prescribed wrapper:

- LeanFinder: "finite filtered cochain complex spectral sequence functor with
  normalized successor homology isomorphisms". Eight hits, including
  `CochainComplex.ConnectData.homologyIsoPos`, `homologyIsoNeg`, mapping-cone
  homology and truncation results; none states this filtered-page functor.
- Loogle: "CategoryTheory.SpectralSequence, HomologicalComplex.homology".
  Seven hits, the abstract `SpectralSequence.iso`, `mk`, homology natural
  isomorphism components and `Hom` compatibility. Source inspection confirms
  none constructs a finite filtered-complex functor with normalized successors.
- Mathlib grep: "filtered.*spectral|normalized.*homology|page.*functor" in
  `Algebra/Homology`. Three hits, abstract `SpectralSequence.pageFunctor` and
  `pageHomologyNatIso`; no matching construction.
- LeanSearch: "spectral sequence of a finite filtered cochain complex with
  normalized successor maps". Eight hits, Moore complex and cochain-complex
  constructor results; none matches.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for filtered
  spectral-sequence/normalized-homology language found the existing page core,
  normalized homology, canonical functor and canonical descent interfaces.
  The canonical functor implementation chooses normalized successors, but its
  signature does not assert their normalization or the page-core comparisons;
  it therefore does not state this node. `FilteredCanonicalPageDescent` assumes
  normalized presentations; it does not construct the requested witnesses.
- The exact item id has no upstream source match. The proposed declaration
  name has no match in `dag/lean_names_upstream.json`, Mathlib, upstream, or
  project sources.

No new node, dependency repair, statement correction or statement dispute is
needed. Only the item's `lean` field changes.

## Second reading by Q107

Author self-check, not an independent review: reopened the node, page-core
signature, normalized predicate and delivered signature. Checked that the
first-page/image, d1, representative, exact-couple, convergence and stabilization
clauses all concern the single existential S. Hoisted the local quotient-page
isomorphisms into the same existential family used in the normalization square;
this prevents an unrelated identification from satisfying the normalization.
Checked the universal candidate-isomorphism equivalence gives both normalization
of `S.iso` and uniqueness, and that the separate cycle-cover clause makes the
representative rule nonvacuous. Checked the successor naturality equation is
oriented according to Lean composition and uses `S.map`, with no supplied
arbitrary successor family. All variables and universes are explicit. The only
postponed proof is the main named theorem, with the full ten-step proof docstring.
The maintainer supplies the independent review described in the worker brief.
