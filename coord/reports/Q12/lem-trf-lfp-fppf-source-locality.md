## Worker report

The module states `AlgebraicGeometry.locallyOfFinitePresentation_iff_of_fppf_source_family`,
with a sorry proof. It renders the current, independently reviewed eight-step node without
changing its statement, proof, dependencies or review fields. Q52's 2026-10-19 PASS is a
stage-1 split review; it supplies no Lean record and does not supersede this stage-2 work.
No definition or helper node is needed.

Clause-by-clause correspondence:

- Schemes and the morphism `f : X → S`: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- An arbitrary indexed source family: `{I : Type v} (U : I → Scheme.{u})`
  and `(h : ∀ i : I, U i ⟶ X)`. The explicit universe `v` is independent of `u`;
  there is no smallness, finiteness, nonemptiness or coproduct assumption on `I`.
- Every source map is flat: `[∀ i : I, Flat (h i)]`.
- Every source map is locally of finite presentation:
  `[∀ i : I, LocallyOfFinitePresentation (h i)]`.
- Joint surjectivity means every point has a preimage in some member:
  `hjoint : ∀ x : X, ∃ (i : I) (y : U i), h i y = x`.
  Individual maps need not be surjective.
- The exact two directions are
  `LocallyOfFinitePresentation f ↔ ∀ i : I, LocallyOfFinitePresentation (h i ≫ f)`.
  Lean's composition `h i ≫ f` is the node's `f ∘ h_i`.
- No quasi-compactness, separatedness or Noetherian hypothesis is introduced.
  There are no further instance binders or implicit mathematical hypotheses.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`. Read the structure signatures and docstrings:
  schemes are locally affine locally ringed spaces; morphisms are their morphisms.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`. Read its full affine-pair signature and
  `Flat.iff_flat_stalkMap`, which identifies it with the node's stalkwise definition.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  in `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`. Read the full affine-pair
  signature and `HasRingHomProperty.iff_exists_appLE` in `Morphisms.RingHomProperties`:
  this is the recorded pointwise affine-neighbourhood notion.

The non-public proof imports supply the affine-open basis and affine quasi-compactness
(`AffineScheme`), flat-lfp openness (`Morphisms.UniversallyOpen`), affine quasi-separatedness
(`Morphisms.QuasiSeparated`), scheme coproducts and finite affine coproduct spectra (`Limits`),
and `Module.FaithfullyFlat.of_comap_surjective` (`RingTheory.Flat.FaithfullyFlat.Algebra`).
Composition and the affine flatness/finite-presentation criteria are already in the public
imports. The algebra node `lem-trf-finite-presentation-fppf-source-algebra` currently has no
Lean record; its step remains in the complete proof docstring. No unstated proof dependency
is introduced as an additional hypothesis.

Source and edge cases:

Read Stacks descent.tex, Tag 036N (lemma-locally-finite-presentation-fppf-local-source),
Tag 036H (lemma-properties-morphisms-local-source), and Tag 02KK's statement. The theorem
is exactly their source-cover locality assertion, using the finite affine reduction in the
node. Its docstring reproduces all eight reviewed steps and names the supporting nodes.
For empty `I`, joint surjectivity forces `X` empty and the right side is vacuous, agreeing
with local finite presentation of an empty source. Empty members in a nonempty family are
allowed. For a singleton identity cover the equivalence reduces to the same property on
`f`. No nonempty target, no nonzero affine ring and no global compactness is required.
The explicit `universe u v` and complete binders introduce no auto-bound variables.
No statement dispute or correction was found.

Searches for an existing statement:

- `msearch.py ... leanfinder "Being locally of finite presentation is fppf local on the
  source: descent along a jointly surjective family of flat locally finitely presented
  morphisms"`: eight hits, including the class, composition, base-change stability and
  `instDescendsAlongSchemeMinMorphismPropertySurjectiveFlatLocallyOfFinitePresentationOfQuasiCompactOfIsZariskiLocalAtTarget`.
  Read `Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent`: those descent instances
  concern target base change and do not state this source-family equivalence.
- `msearch.py ... loogle "AlgebraicGeometry.LocallyOfFinitePresentation"`: twelve hits;
  class, composition, open immersion and base change, no source-family theorem.
- `msearch.py ... grep "LocallyOfFinitePresentation.*(source|fppf)|locallyOfFinitePresentation.*(source|fppf)"
  AlgebraicGeometry`: zero hits.
- `rg` over upstream `WeilConjectures` and side `lean/Sheaf` for source locality,
  finite-presentation source/fppf/family/cover names, and the item's blueprint id:
  upstream `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
  contains `LocallyOfFinitePresentation.of_comp_of_flat_of_surjective`, whose full
  statement and docstring were read. It is the single-surjective-map implication
  of Tag 02KL, not the arbitrary-family iff in this node, so it is not an exact
  existing binding. The side `locallyOfFinitePresentation_of_fpqc_cover` was also
  read in full: its conclusion concerns pullbacks under target coverings, not
  precomposition by source coverings. `LocallyOfFiniteTypeOfFlatLfpSource` is a
  different, finite-type property. The blueprint-id hit in `NodalFamilyEtaleSourceLocality`
  is only a proof-docstring citation. No exact family theorem was found.
- Exact proposed name `locallyOfFinitePresentation_iff_of_fppf_source_family`:
  no matches in Mathlib, upstream or side Lean.

Validation: compilation and delivery preflight are run through the prescribed wrappers.

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
