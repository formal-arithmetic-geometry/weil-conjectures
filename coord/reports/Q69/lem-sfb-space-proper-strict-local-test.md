## Worker report

Stage-2 statement of `lem-sfb-space-proper-strict-local-test` in
`Sheaf.AlgebraicGeometry.SpaceProperStrictLocalTest`, main declaration
`AlgebraicGeometry.AlgebraicSpace.proper_iff_strictLocalization`.
No theorem is proved: the sole theorem has `sorry`. The helper
`strictLocalizationSpaceMap` has real data: the Yoneda image of the recorded canonical
strict-henselization structural morphism, bundled in the existing full subcategory.
It makes no arbitrary choice of map or algebraic space.

The inherited BLOCKED ending concerned stage-1 re-splitting of an unchanged accepted
item. The current `coord/brief-stage2.md` section 0 expressly distinguishes that from
this stage-2 handoff. The current queue assigns this node to stage 2, it has no Lean
record, its Q82 split passed, and no item repair note is present. I preserved the
statement, proof, proof dependencies and accepted split; only `lean` and the permitted
addition of three already landed definition dependencies change.

Hypothesis and clause correspondence:

- The scheme T is `{T : Scheme.{u}}`; its algebraic-space source is
  `(X : AlgebraicSpace T)`. This retains algebraic spaces, with no representability,
  Noetherian, flatness, separatedness or dimension assumption.
- The map f to T is `(f : X ⟶ schemeSpace (Over.mk (𝟙 T)))`.
  The target is the actual sheaf represented by T over T, not an extra target space.
- Finite presentation is exactly `hqc : MapIsQuasiCompact f.hom.hom`,
  `hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom)` and
  `hlfp : MapIsLocallyOfFinitePresentation f`. Quasi-separatedness means
  quasi-compact diagonal; the last predicate is the node's compatible etale-chart
  test of the recorded scheme property `LocallyOfFinitePresentation`.
- Every geometric point is quantified as
  `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (barT : Spec (.of Ω) ⟶ T)`.
  This uses the existing size convention, with field and scheme universe both u;
  it does not quantify over an unrelated smaller universe or restrict characteristic.
- The strict localization is precisely `Scheme.strictHenselizationScheme barT`.
  In `strictLocalizationSpaceMap barT` the scheme object is
  `Over.mk (Scheme.strictHenselizationStructuralMap barT)`. Thus its structural map
  is the recorded canonical map, whose common-limit-leg characterization is
  `Scheme.exists_strictHenselizationStructuralMap`.
- `enlargedFibreProductFst (strictLocalizationSpaceMap barT) f` is the projection
  from T_(barT) ×_T X to T_(barT), the same base change as X ×_T T_(barT) with
  factors exchanged. The existing definition bundles the actual sheaf pullback
  using `fibreProduct_isAlgebraicSpace`; it supplies no new assumption.
- Both occurrences of properness are the same recorded predicate `MapIsProper`:
  separated, finite type, universally closed. The conclusion is `↔`, retaining
  both implications.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (affine-local ring-map test).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, scheme-test `IsRepresentableWith`, `IsEtale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsLocallyOfFinitePresentation`, `MapIsProper` and all its three constituents.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact`, whose definition
  tests compactness on point spaces of pullbacks to affine schemes. This existing
  definition also implements quasi-separatedness via the diagonal. Its owning
  landed node `def-sfb-proper-curve-moduli` is added to `stmt_deps`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the inline geometric-point
  encoding agrees with `Scheme.SpecToEquivOfField` in
  `Mathlib.AlgebraicGeometry.ResidueField`.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`:
  `Scheme.strictHenselizationRing`, `Scheme.strictHenselizationScheme`, and
  `Scheme.strictHenselization_properties`; these are the recorded small-neighbourhood
  colimit/limit construction, not the distinct strictLocalization API.
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap` and its named characterization theorem.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, read with its full universal property.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `schemeSheaf_isAlgebraicSpace`, `enlargedFibreProduct`, `enlargedFibreProductFst`.
  Its already landed definition owners `def-trf-scheme-algebraic-space`
  (`schemeSpace`) and `def-sfb-space-sheaf-fibre-product`
  (`enlargedFibreProduct`, `enlargedFibreProductFst`) are added to `stmt_deps`.
  The enlarged-site theorem is not used as a statement dependency.

The module imports the recorded modules of stated proof dependencies: affine etale
essential smallness, algebraic closures, directed reindexing, final-functor limit
transport, affine morphisms; fppf topology and scheme etaleness are already publicly
available from the statement imports. The algebraic-space eventual-properness,
flat/proper/fp-locality and proper-base-change proof nodes have no recorded module
at this handoff, so no invented import is used. Their names and the entire six-step
accepted proof remain in the theorem docstring.

Sources opened: spaces-limits.tex, `lemma-eventually-proper` (08K1);
etale-cohomology.tex, `lemma-describe-etale-local-ring` (04HX), including its affine
pointed-neighbourhood colimit proof; spaces-descent.tex,
`lemma-descending-property-proper` (0422). The node is correctly an extracted
corollary, not a verbatim claim about the statement of 08K1.

Edge cases checked: empty T gives a vacuous geometric-point quantifier and properness
of the unique empty source; the source may be empty. No nonemptiness of fibres or
connectedness is assumed. No choice of an initial neighbourhood is an extra theorem
hypothesis. An algebraically closed field base reduces to the expected properness
test. Positive characteristic and transcendental algebraically closed test fields
remain included. General non-affine, non-Noetherian and non-quasi-compact T are
allowed; compactness is only the relative hypothesis on f. The forward implication
does not need finite presentation, but retaining it in the equivalence matches the
node. No statement dispute or source-based correction was necessary.

Searches actually run (msearch log is in this sandbox):

- `msearch.py ... leanfinder "A finitely presented morphism from an algebraic space
  to a scheme is proper if and only if all strict localizations are proper"`:
  eight scheme-only properness/local finite presentation hits, no algebraic-space
  strict-local properness test.
- `msearch.py ... loogle "AlgebraicGeometry.IsProper, HenselianLocalRing"`: zero hits.
- `msearch.py ... grep
  "(proper|Proper).*(strictHensel|strict.hensel)|(strictHensel|strict.hensel).*(proper|Proper)"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Properness of a finitely presented algebraic space over
  a scheme is detected by strict henselizations at all geometric points"`: eight
  scheme properness / finite-presentation hits, no exact statement.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id and strict-henselization/properness combinations found no existing
  declaration. Broader searches found the consumer `ConnectedProperFibresProper`,
  whose docstring cites this node but whose theorem assumes flatness and connected
  proper fibres; it is not the strict-local test. Searches for scheme-as-space and
  fibre-product definitions found the existing `EnlargedEtaleRingedSite` declarations,
  which are reused. No new notion or dependency repair is required.

Validation: scompile.py compiled the sandbox and library forms separately, each
within two seconds, with no diagnostics. Only the theorem's expected sorry remains.

## Second reading by Q69

This is a second pass by the dispatched worker; no separate agent was started,
following the dispatcher's explicit instruction. The maintainer supplies the independent
review. I reopened the node and module and checked the scheme target, algebraic-space
source, all three finite-presentation hypotheses, all geometric points, canonical
structural map, base-changed projection and both properness clauses against the
source and recorded dependencies. The factor order in the existing fibre-product
API puts the strict localization first so its first projection is the desired map;
this is just the canonical exchange of factors. The three already landed owning definition nodes
are added as explicit dependencies. No hypothesis is added or omitted. The helper
is definitionally the Yoneda image, and the main theorem is the only sorry. There are
no new nodes, dependency-module repairs or statement corrections.

## Repair of returned head d19ab032c036

H2: replaced `lem-trf-space-enlarged-etale-ringed-site-model` in `stmt_deps`
with the existing definition nodes `def-trf-scheme-algebraic-space` and
`def-sfb-space-sheaf-fibre-product`. Their live Lean records point to precisely
`schemeSpace`, `enlargedFibreProduct` and `enlargedFibreProductFst` in the same
imported module. I read both definition nodes and the declarations with their
docstrings: `schemeSpace` retains the Yoneda sheaf, the product retains the
underlying sheaf pullback, and its first projection is the actual pullback
projection. No conclusion of the enlarged-site theorem is required by this
statement. Retained `def-sfb-proper-curve-moduli`, which owns
`MapIsQuasiCompact`. The Lean module, statement, proof and proof dependencies
are unchanged. Comparison with the current shared node confirms that the only
node changes are `lean` and the three added definition dependencies.

The initial saved-packet dry run passed (commit `60ca0024f77`), but it still
contained the returned H2 metadata; that pass was not treated as repairing H2.
The final repaired packet is compiled and dry-run again before delivery.
