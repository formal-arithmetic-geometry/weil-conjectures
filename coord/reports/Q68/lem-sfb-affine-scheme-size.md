# Q68: lem-sfb-affine-scheme-size

## Worker report

The module `Sheaf.AlgebraicGeometry.AffineSchemeCardinalSize` states
`AlgebraicGeometry.Scheme.cardinalSize_of_isAffine`. Its only proof is `by sorry`.
There are no definitions, helper theorems, new nodes, dependency repairs or statement
corrections. The item's JSON changes only in `lean`; its accepted stage-1 split is preserved.

Clause-by-clause correspondence:

- “Let Y be an affine scheme” is `(Y : Scheme.{u}) [IsAffine Y]`. Mathlib's `IsAffine`
  says its canonical map to the spectrum of its global sections is an isomorphism;
  `Scheme.isoSpec` realizes the equivalent definition in def-pc-scheme.
- “A = Gamma(Y, O_Y) is its ring of global sections” is rendered directly by `Γ(Y, ⊤)`.
  This is the actual structure-sheaf value on the whole space, not an arbitrary ring
  isomorphic to it. `↥Γ(Y, ⊤)` is its underlying type and `Cardinal.mk` is its cardinality.
  No independent A or equality hypothesis is needed for this abbreviation in the node.
- The complete three-part size `s(Z)` is the existing `Scheme.cardinalSize` from
  def-sfb-scheme-cardinal-size. I opened its implementation: it is exactly
  `max Cardinal.aleph0 (max (Cardinal.mk X.affineOpens)
  (⨆ U : X.affineOpens, Cardinal.mk ↥Γ(X, U.1)))`.
  Thus it counts actual affine open subsets and all their section rings.
- The conclusion `s(Y) = max{aleph_0, |A|}` is
  `Y.cardinalSize = max Cardinal.aleph0 (Cardinal.mk ↥Γ(Y, ⊤))`.
  This is equality, with the same size and the same ring as in the node.
- “The zero ring and empty affine scheme are allowed” needs no further binder:
  there is no `Nontrivial`, `Nonempty`, reducedness, characteristic, field,
  Noetherian or separation hypothesis. The explicitly bound universe `u` is arbitrary;
  all cardinalities and the scheme-size definition live in `Cardinal.{u}`.

Statement dependencies read and used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`; the affineness predicate
  is `AlgebraicGeometry.IsAffine` in `Mathlib.AlgebraicGeometry.AffineScheme`.
- def-weil-affine-spectrum: `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`
  in `Mathlib.AlgebraicGeometry.Scheme`. Their full definitions were read. The theorem
  uses the actual global sections directly; the source's identification with Spec A
  belongs to the proof, rather than an extra hypothesis in the statement.
- def-sfb-scheme-cardinal-size: `AlgebraicGeometry.Scheme.cardinalSize` in
  `Sheaf.AlgebraicGeometry.SchemeCardinalSize`, publicly imported and used verbatim.
  Its module was opened in the live read clone. No private size notion is introduced.

The proof-only imports retain the accepted six-step DAG plan. The recorded matches are:
`IsAffineOpen.fromSpec`, `isOpenImmersion_fromSpec`, `range_fromSpec`, `primeIdealOf`,
`fromSpec_primeIdealOf`, `IsAffineOpen.isLocalization_basicOpen` in AffineScheme;
`PrimeSpectrum.isTopologicalBasis_basic_opens`, `localization_away_isOpenEmbedding`,
`localization_away_comap_range`, `mem_basicOpen` in Spectrum.Prime.Topology;
`Scheme.compactSpace_of_isAffine` in AffineScheme and `quasiSeparatedSpace_of_isAffine`
in Morphisms.QuasiSeparated; `CompactSpace` in Topology.Defs.Filter;
`Cardinal.mk_list_le_max` in SetTheory.Cardinal.Arithmetic;
`Localization.Away` in GroupTheory.MonoidLocalization.Away;
`Scheme.evaluation_eq_zero_iff_notMem_basicOpen` in AlgebraicGeometry.ResidueField;
`LocallyRingedSpace.Hom` and its ringed-space structure in
Geometry.RingedSpace.LocallyRingedSpace; and `Opens.grothendieckTopology` in
CategoryTheory.Sites.Spaces. All module paths here start with `Mathlib.` unless
stated otherwise. The size definition is also a proof dependency and is public.

Source and edge cases checked before writing:

I read `literature/stacks-project/sets.tex`, section-categories-schemes (the definition
preceding Tag 000I), and the whole lemma-bound-affine and proof (Tag 000P).
The statement agrees with the node, including equality rather than just an upper bound.
For the empty affine scheme (spectrum of the zero ring), the only open is empty and its
section ring is a singleton: both sides are aleph_0. For a finite field, both sides are
again aleph_0. For an uncountable field the top section ring contributes its full
cardinality even though there are only two open subsets. Countably infinite rings such
as Z give aleph_0. Nilpotents and zero localization elements do not require cancellation:
all sections are counted, and the proof's fraction parametrization need only be surjective.
Empty finite lists, covers and products are included in the proof docstring.
No node fault or statement dispute was found.

Searches run with the required `msearch.py Q68 lem-sfb-affine-scheme-size` wrapper:

- LeanFinder: “The cardinal size of an affine scheme counting affine open subsets and
  their rings of sections is max aleph0 cardinality of its global sections”. Eight hits:
  `isAffine_affineScheme`, `AffineScheme`, `IsAffine`, `isAffineOpen_top`, affine basis
  covers and related results; none is the size equality.
- Loogle: `"affineOpens", "Cardinal"`. Zero hits.
- Mathlib grep, subdirectory AlgebraicGeometry:
  `(cardinal|mk_le|small).*(affineOpens|IsAffineOpen)|(affineOpens|IsAffineOpen).*(cardinal|mk_le|small)`.
  Zero hits.
- LeanSearch: “The size of an affine scheme counting affine open subsets and all their
  rings of sections is the maximum of aleph zero and the cardinality of its global sections”.
  Eight hits, including `AffineScheme`, `Scheme.affineOpens`, `IsAffineOpen.isoSpec`
  and generated structural `SizeOf` theorems. Those `SizeOf` theorems do not express
  Stacks cardinal size.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  `cardinalSize|cardinal.*affine|affine.*cardinal|lem-sfb-affine-scheme-size`:
  found the existing size definition, the consumer QuasiCompactLocallyFiniteTypeSchemeSize,
  and unrelated affine geometry; no existing theorem states this equality.
- `grep -rn 'lem-sfb-affine-scheme-size' lean/WeilConjectures`: no hits.

Validation: `scompile.py Q68 lem-sfb-affine-scheme-size` on the delivered module
succeeded both as sandbox module and under its library name (8.2 s and 6.3 s), with
no errors or warnings. Module mode, exposed public section, explicit `universe u` and
`set_option autoImplicit false` are used; every line is at most 100 characters.

The inherited BLOCKED ending concerned a stage-1 unchanged-item rejection after Q59's
split. The current stage-2 queue explicitly lists this item, and the live node has no
Lean record. This delivery supplies its first Lean statement, rather than reopening Q59's
reviewed split. No released repair note for the item was found.

## Second reading by Q68

This is a separate second pass by the same dispatched worker; the dispatch explicitly
forbids starting other agents. The maintainer's independent review remains required.
I reopened the completed module alongside the item's statement and its size dependency.
The only mathematical binder is the affine scheme Y. `Γ(Y, ⊤)` is exactly the node's A,
not its point set or a chosen presentation. The left side calls the landed three-part
cardinal-size definition; the right side uses max, aleph_0 and the cardinal of that actual
ring. The equality therefore renders every clause, without extra assumptions or a
restriction to nonempty spectra. The definition's index is all affine open subsets,
not a selected affine cover. The universe matches the recorded size definition and
no auto-bound universe or variable is present. The six proof-plan paragraphs reproduce
the accepted steps, including finite lists with affine union, common exponents in the
localization product, sheaf uniqueness and empty-cover cases. No mismatch was found,
and no mathematical change was needed in this second pass.
