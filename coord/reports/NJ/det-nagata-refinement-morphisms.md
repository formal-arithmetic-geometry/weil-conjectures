## Worker report

The module `Sheaf.Compactification.DenseRefinementMorphisms` states
`AlgebraicGeometry.denseCompactification_refinement_morphisms`, with its entire proof
`sorry`. It adds no definition and states no other DAG node. The item's JSON changes only
in `lean`. The source read was the current main-20261015 blueprint's
`sec-nagata-compactification/sk-prop-nagata-sketch-comp-category/`
`det-nagata-refinement-morphisms.md` and its `.proof.md`, together with the node's five
expanded proof steps. No statement correction, new node, dependency module, or dispute is
needed. There is no repair note for this item.

Hypotheses and objects, individually:

- `{X S : Scheme.{u}} {f : X ⟶ S}` are precisely the two schemes and the morphism being
  compactified. The universe `u` is explicitly declared, and every variable is bound.
- `(c' c : Compactification.QuasiCompactObjects f)` supplies the two compactifications
  and both explicit quasi-compactness hypotheses. This recorded abbreviation is the full
  subcategory of `Compactification f` on `QuasiCompact c.i`; its `.obj` is the existing
  compactification, not a replacement notion. For each object, `.obj.Z` is the ambient
  scheme, `.obj.i` is the open immersion and `.obj.g` is the proper structure map.
  `Compactification.comm` says `f = i ≫ g`, and its property fields give properness and
  the open immersion. The full-subcategory `.property` is exactly `QuasiCompact i`.
  Mathlib's `quasiCompact_iff_forall_isAffineOpen` identifies this with the node's
  compact inverse images of affine opens. No finite-type hypothesis on `f` is added.
- `(hc' : IsSchemeTheoreticallyDominant c'.obj.i)` is scheme-theoretic density of the
  source compactification only. The dependency records this exact Mathlib class.
  Its `ker_eq_bot` is equivalent, for a quasi-compact open immersion, to injectivity
  of the structure-sheaf map; `Scheme.Hom.app_injective` supplies injectivity on opens.
  There is no density assumption on the target compactification.
- `(h : c'.obj.Z ⟶ c.obj.Z)` is the arbitrary ambient scheme map in the node.
- `(hS : h ≫ c.obj.g = c'.obj.g)` says it is an S-morphism, namely `p ∘ h = p'`.
- `(hj : c'.obj.i ≫ h = c.obj.i)` is `h ∘ j' = j`.

Conclusions, individually:

1. `IsProper h` is exactly properness of this ambient scheme map.
2. `Compactification.boundaryRefinementProperty f
   (ObjectProperty.homMk (X := c') (Y := c) ⟨h, hj, hS⟩)` uses the dependency's
   recorded definition. Here `⟨h, hj, hS⟩` constructs the existing upstream
   `Compactification.Refinement` with only the two given triangle equalities;
   `ObjectProperty.homMk` regards it as a map between the quasi-compact objects.
   This construction assumes no inverse-image condition. Unfolding the recorded
   property gives exactly
   `h ⁻¹ᵁ c.obj.i.opensRange = c'.obj.i.opensRange` in `c'.obj.Z.Opens`.
   These are open subschemes, with the restrictions of the same structure sheaf,
   rather than independently chosen closed structures or mere equality of images.
   Together with `hS` and `hj`, it is precisely the three-condition boundary refinement
   of `det-nagata-definition-refinement`. No duplicate predicate is introduced.
3. `∀ (h' : c'.obj.Z ⟶ c.obj.Z), h' ≫ c.obj.g = c'.obj.g →
   c'.obj.i ≫ h' = c.obj.i → h' = h` states uniqueness among ALL S-morphisms with
   the required restriction. In particular it does not require a competitor to
   already be proper, boundary preserving, or bundled as a refinement. Existence
   is the given `h`, `hS`, and `hj`, so this universal clause is exactly uniqueness.

Dependency declarations read and used:

- `WeilConjectures.Compactification.Defs`, `AlgebraicGeometry.Compactification`:
  read the complete structure and docstring. Its open immersion alone is not
  quasi-compact, so the recorded `QuasiCompactObjects` wrapper is necessary and
  supplies exactly the node's two explicit extra hypotheses.
- `Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`,
  `AlgebraicGeometry.IsSchemeTheoreticallyDominant`, `ker_eq_bot`, and
  `Scheme.Hom.app_injective`: density uses this recorded dependency directly.
- `Sheaf.Compactification.BoundaryRefinement`,
  `AlgebraicGeometry.Compactification.QuasiCompactObjects` and
  `AlgebraicGeometry.Compactification.boundaryRefinementProperty`: the complete
  module and all six declarations' docstrings/signatures were read. The definition
  of `BoundaryCompactification` packages this exact morphism property; the theorem
  states its property on the supplied map rather than merely existence of some map.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`:
  the class extends separated, universally closed, locally finite type; universal
  closedness gives quasi-compactness, hence the node's finite-type formulation.
- The public imports contain the modules of all four statement dependencies.
  Private proof imports additionally retain `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`,
  `Sheaf.AlgebraicGeometry.BaseChangeConventions`, and
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated`.
  The proof dependencies' recorded declarations were inspected: `IsProper.of_comp`,
  the proper `pullback.snd` instance, `IsClosedImmersion.of_comp`,
  `IsOpenImmersion`, `IsClosedImmersion`, the base-change module's pullback
  conventions, and `ext_of_isSchemeTheoreticallyDominant_of_isSeparated`.
  The theorem docstring records the five DAG proof steps and names their dependencies.

Edge cases checked against the signature and source argument:

- The empty scheme is allowed for `X` and all other schemes; density forces an empty
  source ambient scheme when `X` is empty, since the ambient structure sheaf injects
  into zero. Properness, empty inverse-image equality, and uniqueness then hold.
- Identity maps and identical compactifications are included. Whenever the trivial
  compactification is available its open immersion is the identity, hence quasi-compact
  and dense; no nontrivial-boundary or nonidentity assumption is present.
- Nonreduced schemes are allowed: the density hypothesis is scheme-theoretic, and the
  uniqueness lemma requires no reducedness. Replacing it by topological density would
  lose precisely this strength; the signature does not do so.
- No quasi-compactness of `X` or `S` as spaces, Noetherianity, connectedness,
  nonemptiness, characteristic, or density of `c` is imposed. Quasi-compactness applies
  to the two open immersions exactly as the node requests.
- The uniqueness clause handles arbitrary ambient competitors; it does not assume
  the conclusion for them. The refinement constructor appearing in clause 2 also
  contains only the supplied triangle hypotheses, so that clause is not circular.

Searches actually run (all Mathlib-service searches through `msearch.py`):

- LeanFinder: `A map from a scheme-theoretically dense compactification to another
  compactification commuting with the open immersions and proper structure maps is
  proper, preserves the inverse image open, and is unique`. Eight hits included
  valuative-criterion uniqueness, `IsOpenImmersion.lift`/`lift_uniq`, and immersion
  coborder lifts; none stated the whole three-clause result.
- Loogle: `AlgebraicGeometry.Compactification.Refinement, AlgebraicGeometry.IsProper`.
  Zero hits with unknown-identifier diagnostic for the upstream compactification
  name; this invalid query is not evidence of absence.
- Loogle (valid follow-up):
  `AlgebraicGeometry.IsSchemeTheoreticallyDominant, AlgebraicGeometry.IsProper`.
  Zero hits, with no diagnostic. No exact whole-item match.
- Mathlib grep: `Compactification|scheme.theoretically dense` in `AlgebraicGeometry`.
  Zero hits for that query. Direct reads of the dependency files supply the existing
  properness, density, and open-subscheme interfaces.
- LeanSearch: `Morphisms out of a dense compactification are proper, preserve the
  distinguished open, and are unique`. Eight hits included `IsProper.instMorphismRestrict`,
  `Scheme.Hom.isProperMap`, `IsProper.mk`, and one-point compactification statements;
  none is the node's complete statement.
- `rg` of `WeilConjectures/Compactification` by `Refinement`, `IsProper`,
  `IsSchemeTheoreticallyDominant`, `opensRange`, and `QuasiCompact` found the upstream
  pieces: `Refinement.isProper`, `Refinement.ext_of_isSchemeTheoreticallyDominant`, and
  `Refinement.isPullback_of_isSchemeTheoreticallyDominant`. Their full source files,
  signatures and docstrings were read. They are separate results, the last stated as
  a cartesian square, not a declaration stating this complete result with the recorded
  boundary-refinement interface. They were therefore not attached as an exact match.
- Exact item-id search in `WeilConjectures/` returned no declaration. Searches in
  `dag/lean_names_upstream.json` by the item id and proposed declaration name returned
  no match; the broader refinement search lists other dense-refinement constructions.
- `rg` in project `lean/Sheaf` by boundary-refinement identifiers found the dependency
  `BoundaryRefinement.lean` only; it defines the property and categories, not this result.
  The proposed full declaration name was absent from Mathlib, upstream, and the project.

Validation: `scompile.py NJ det-nagata-refinement-morphisms` compiled the delivered
file successfully as a sandbox module and at its library path, with no warnings or
errors. An intermediate application supplied the implicit objects of a
`MorphismProperty` positionally; Lean rejected it, and the final signature supplies
objects to `ObjectProperty.homMk` explicitly and applies the property only to the map.
Only the expected named theorem `sorry` remains. The mandatory `deliver2.py --no-push`
preflight follows; the independent second reader will write the second-reading section.

## Second reading by NJ

I independently reread the current node, its source place, and
`Sheaf.Compactification.DenseRefinementMorphisms.lean`. The node introduces the
following data and assumptions, in order:

1. Schemes `X` and `S` (the file fixes their common universe `u`) and a morphism
   `f : X ⟶ S`.
2. A source compactification `c'` and target compactification `c`, rendered by
   `c' c : Compactification.QuasiCompactObjects f`. Their `.obj` fields are the
   recorded `Compactification f` objects, and the full-subcategory property gives
   quasi-compactness of both open immersions.
3. Scheme-theoretic density of the source open, rendered by
   `hc' : IsSchemeTheoreticallyDominant c'.obj.i`.
4. An ambient map `h : c'.obj.Z ⟶ c.obj.Z`, with the two hypotheses
   `hS : h ≫ c.obj.g = c'.obj.g` and
   `hj : c'.obj.i ≫ h = c.obj.i`.

The three conclusions are rendered exactly as follows. First,
`IsProper h` is the properness assertion. Second,
`Compactification.boundaryRefinementProperty f
(ObjectProperty.homMk (X := c') (Y := c) ⟨h, hj, hS⟩)` is the recorded
third refinement condition, namely equality of the inverse-image open
subschemes; `ObjectProperty.homMk` supplies the two triangle equalities already
assumed. Third, the universal clause quantifies every ambient
`h' : c'.obj.Z ⟶ c.obj.Z`, assumes precisely its `S`-map equality and its
restriction equality, and concludes `h' = h`. The quantifier order and all
three conjunction clauses match the node signature verbatim.

The dependency interfaces were checked directly. `Compactification` supplies
proper `g`, open immersion `i`, and the factorization of `f`; `QuasiCompactObjects`
adds exactly the quasi-compact open-immersion hypotheses needed by the recorded
refinement definition. `IsSchemeTheoreticallyDominant` is the Mathlib
scheme-theoretic density predicate. `boundaryRefinementProperty` has the
correct source/target order: for the map `c' → c` it states
`h ⁻¹ᵁ c.obj.i.opensRange = c'.obj.i.opensRange`. No private duplicate notion or
extra finite-type, Noetherian, separated, connected, characteristic, or
nonemptiness assumption occurs.

The source blueprint prose omits an explicit quasi-compact sentence, while the
current node (and the prior accepted split correction) includes it. This is
required by `det-nagata-definition-refinement` and by the source proof's
injective-structure-sheaf characterization of scheme-theoretic density; the
current node therefore has the needed hypotheses and no further statement
mismatch was found. The Lean file adds no hypotheses beyond that corrected node
statement. Its only postponed item is the named theorem proof (`sorry`), with
source and blueprint proof steps in the docstring.

Edge cases were checked: empty schemes and empty opens are admitted; identity
maps and identical compactifications satisfy the signature; nonreduced schemes
are covered because density is scheme-theoretic; no assumption of density of
`c` is present; arbitrary competitors occur in the uniqueness quantifier; and
`u` is the sole universe parameter, so no case is excluded by an independent
index or universe. The zero/empty inverse-image case is represented by equality
in `Scheme.Opens`, including its restricted structure sheaf.

I reran the existing-declaration searches. `msearch.py` LeanFinder for a dense
compactification refinement returned only general immersion and partial-map
results; Loogle for
`AlgebraicGeometry.IsSchemeTheoreticallyDominant AlgebraicGeometry.IsProper`
returned density lemmas but no complete theorem. `rg` over Mathlib,
`WeilConjectures/`, and project `lean/Sheaf` found only the separate
`Compactification.Refinement` properness/pullback results and the project's
`boundaryRefinementProperty`; no declaration states this three-clause result.
The exact item id and proposed theorem name were absent from upstream names.
Thus the module is correctly new, and no dependency module or new definition
node is needed.

The required `scompile.py` check passed for the module in both sandbox and
library paths, with only the expected theorem `sorry` and no errors or other
warnings. No source, dependency, or node repair was necessary in this second
reading.
