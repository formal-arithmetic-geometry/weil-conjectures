## Worker report

The module `Sheaf.AlgebraicGeometry.UniversalThickeningOpenPieces` states
`AlgebraicGeometry.universalFirstOrderThickening_open_pieces`, with one `sorry` proof.
It defines no new notion. The node is unchanged except for its `lean` record.

Source checked: https://stacks.math.columbia.edu/tag/04F3, general remarks preceding
its affine case. The local `literature/stacks-project/more-morphisms.tex` is absent on
this machine, so the original Stacks page was opened. The restriction and open-base
claims require only the assumed universal property, not formal unramifiedness of `h`.
The theorem docstring carries all eight steps of the node's proof and their inputs.

Hypotheses and clauses, in their order:

- The schemes `Z`, `X` and morphism `h : Z ⟶ X` are the outer binders.
  Every scheme, including the arbitrary test schemes in the dependency definition,
  is in the same explicitly bound universe `u`; no affine hypothesis is imposed.
- (0) Arbitrary schemes `T`, `T'`, immersion `iT`, and first order hypothesis are
  `∀ {T T' : Scheme.{u}} (iT : T ⟶ T'), IsFirstOrderThickening iT → ...`.
  The arbitrary target open is `∀ W' : T'.Opens`. The source open is exactly
  `iT ⁻¹ᵁ W'`, built into the type of Mathlib's `iT ∣_ W'`.
- (0) `IsFirstOrderThickening (iT ∣_ W')` includes the closed immersion and the
  square-zero defining ideal. For each affine open `Q` in `W'`, the equality
  `(iT ∣_ W').ker.ideal Q = iT.ker.ideal
  ⟨W'.ι ''ᵁ Q, Q.2.image_of_isOpenImmersion W'.ι⟩` identifies that ideal with
  the restriction of `iT.ker`. Affine-open ideal data determines the entire
  quasi-coherent ideal sheaf; the rings here are definitionally identified by
  Mathlib's construction of open restrictions (cf. `ker_morphismRestrict_ideal`).
- (0) The base structure morphism `b : T' ⟶ X` contributes no extra predicate:
  the recorded definition defines a thickening over a base by composing the
  structure morphism with the immersion. Thus the asserted first order thickening
  is over every such base with structure morphism `W'.ι ≫ b`, and source structure
  `(iT ∣_ W') ≫ W'.ι ≫ b`. `morphismRestrict_ι` identifies this with
  `(iT ⁻¹ᵁ W').ι ≫ iT ≫ b`. No additional over-base compatibility must be proved
  beyond the restriction construction; the module docstring makes this explicit.
- (0) `∀ W : T.Opens, ∃! W' : T'.Opens, iT ⁻¹ᵁ W' = W` expresses existence and
  uniqueness of the open above every source open. In particular, for a given `W'`
  its preimage determines it uniquely, as in the node. This is also the open
  correspondence used to specify `V'` in (1).
- (1) `Z'`, `i : Z ⟶ Z'`, `h' : Z' ⟶ X`, and
  `IsUniversalFirstOrderThickening h i h'` are the thickening data and hypothesis.
  `V : Z.Opens`, `U : X.Opens`, and `V ≤ h ⁻¹ᵁ U` are precisely the opens and
  image containment `h(V) ⊆ U`.
- (1) The conclusion supplies `V' : Z'.Opens` with `i ⁻¹ᵁ V' = V` and
  `V' ≤ h' ⁻¹ᵁ U`. The preceding clause (0), applied to the first order part of
  the universal hypothesis, makes this open unique. Thus existentially supplying
  it imposes exactly the same open as the node's phrase "the open subscheme".
- (1) `iV : V.toScheme ⟶ V'.toScheme`, `hV : V.toScheme ⟶ U.toScheme`,
  and `hV' : V'.toScheme ⟶ U.toScheme` are the restricted maps. The three
  equalities `iV ≫ V'.ι = V.ι ≫ i`, `hV ≫ U.ι = V.ι ≫ h`, and
  `hV' ≫ U.ι = V'.ι ≫ h'` specify these maps precisely as the restrictions;
  open inclusions are monomorphisms, so this leaves no arbitrary map choice.
  `IsUniversalFirstOrderThickening hV iV hV'` is exactly universality over `U`,
  and includes first order, the compatibility `iV ≫ hV' = hV`, and the unique
  extension property for every first order test thickening over `U`.
- (2) `U : X.Opens`, `hU : Z ⟶ U.toScheme`, and `hU ≫ U.ι = h` express the
  containment `h(Z) ⊆ U` together with its stipulated factorization. Conversely,
  that image containment gives the unique factorization by the open immersion
  property. Quantifying over the factorization with its equation is therefore
  equivalent to the node's hypothesis and does not strengthen it.
- (2) The supplied `Z'`, `i`, `hU'`, and universal-thickening hypothesis over `U`
  give `IsUniversalFirstOrderThickening h i (hU' ≫ U.ι)`. The same scheme and
  immersion are used, and only the base structure map is composed with inclusion.

Dependency declarations used, with signatures and docstrings read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, and `Scheme.Opens`.
- `Sheaf.AlgebraicGeometry.Thickening`: `AlgebraicGeometry.IsFirstOrderThickening`
  (closed immersion and `i.ker ^ 2 = ⊥`).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  used through the canonical open inclusion and its affine-image API.
- `Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening`:
  `AlgebraicGeometry.IsUniversalFirstOrderThickening`, including its full arbitrary-
  scheme unique-lift quantification. Its recorded uniqueness theorem was also read.
- Existing Mathlib constructions: `Scheme.Opens.toScheme`, `Scheme.Opens.ι`,
  `morphismRestrict`, and `Scheme.Hom.ker`. All are transitively imported by the
  single dependency import, which is used directly by the final universal predicates.

Edge cases checked before writing:

- `W' = ⊥`, or `V = ⊥`: the restricted scheme is empty; the corresponding open
  above an empty source is uniquely empty since a first order thickening is
  surjective on points. No nonempty binder rules out this case.
- `U = ⊥`: image containment forces the relevant source, and then its thickening,
  to be empty. All supplied morphisms still have the required types.
- Empty `Z`, `T`, or ambient schemes are allowed. A square-zero closed immersion
  into a thickening has the same underlying points, so there is no counterexample
  from a nonempty thickening of an empty scheme.
- Whole opens recover the original thickening and base; identity thickenings have
  zero ideal and restrict correctly. No strictness condition is put on the opens.
- Nonaffine schemes, arbitrary characteristics, and nonreduced schemes remain
  covered. The affine-open quantifier describes the ideal sheaf, not the schemes.

Searches made (recorded by `msearch.py` in `searches.jsonl`):

- LeanFinder: "Universal first order thickenings restrict to open subschemes and
  do not depend on an open base containing the image". Eight hits on open covers,
  scheme restrictions, and their underlying carriers; no universal-thickening claim.
- Loogle: `"Thickening"`. Twelve hits, all metric/uniform-space thickenings;
  none is a scheme universal first order thickening.
- Mathlib grep: `thickening|universalFirstOrder` in `AlgebraicGeometry`. Only
  the formally-unramified docstring at line 189 mentions infinitesimal thickenings.
- LeanSearch: "universal first order thickening of schemes restriction to open
  subschemes". Unavailable (Internal Server Error); no mathematical verdict taken
  from this unavailable service.
- `rg` on the source project and `lean/Sheaf` for universal-thickening names:
  no source match; the latter gives the two dependency definitions and the
  distinct ring-existence and flat-unramified results, not this node's statement.
- `grep -rn` of the item's id in the source project: no match.
- Exact new declaration and module name searched in `dag/lean_names_upstream.json`,
  Mathlib, the source project, and `lean/Sheaf`: no collision.
- Mathlib source reads found `ker_morphismRestrict_ideal` and
  `ker_ideal_of_isPullback_of_isOpenImmersion`, which supply the ideal-data encoding
  of the restriction clause but do not state the universal property.

Server compilation: `scompile.py C1 lem-weil-pbc-universal-thickening-open-pieces`
with the module path succeeded in 1.7 seconds, with no errors or warnings.
No statement correction, new node, unusable dependency, or disputed statement was found.

## Second reading by C1

I independently read the item node, its four statement dependencies and their
recorded Lean declarations, the delivered Lean signature and docstring, and the
source context. The local Stacks checkout is absent. I read the official pages
[04F3](https://stacks.math.columbia.edu/tag/04F3),
[04F2](https://stacks.math.columbia.edu/tag/04F2), and
[04EX](https://stacks.math.columbia.edu/tag/04EX), and fetched the original
`more-morphisms.tex` into the item's scratchpad. The source places read are
`definition-thickening` (lines 35–66), `section-universal-thickening`
(lines 1002–1022), and the general remarks in the proof of
`lemma-universal-thickening` (lines 1039–1062). There are no ambient finiteness,
Noetherian, separatedness, characteristic, or affine assumptions. Although the
existence lemma assumes formal unramifiedness, these general remarks assume a
universal thickening already exists and use only its universal property. The
node correctly states that general conditional result.

Objects, hypotheses, and conclusions, in node order, matched to the final Lean:

1. Schemes `Z`, `X` and morphism `h : Z ⟶ X`: the outer binders
   `{Z X : Scheme.{u}} (h : Z ⟶ X)`. Exact.
2. Clause (0), schemes `T`, `T'`, closed immersion `iT`, first order condition,
   and structure map `b : T' ⟶ X`: the first conjunct now starts
   `∀ {T T' : Scheme.{u}} (iT : T ⟶ T') (_b : T' ⟶ X),
   IsFirstOrderThickening iT → ...`. The dependency definition is literally
   `IsClosedImmersion iT ∧ iT.ker ^ 2 = ⊥`. The source structure map is the
   composite `iT ≫ _b`, as permitted by dependency clause (4). Exact after repair.
   The original signature omitted `b` entirely and thus asserted clause (0)
   even for `T'` without a map to the fixed `X`. I restored this given object;
   it is not an added property or instance. For example, a nonempty scheme
   has no map to empty `X`, so this binder is a real restriction to the
   over-`X` tests of the node, not a hypothesis automatically available for
   every scheme. Its underscore avoids an unused-variable warning because
   the intrinsic ideal and open correspondence do not depend on its value.
3. Clause (0), arbitrary open `W'`, inverse image `W`, restricted immersion,
   square-zero ideal, and ideal restriction: `∀ W' : T'.Opens`,
   `IsFirstOrderThickening (iT ∣_ W')`, and the equality of kernel ideals for
   `∀ Q : W'.toScheme.affineOpens`. By the signature of `morphismRestrict`, its
   source is exactly `(iT ⁻¹ᵁ W').toScheme`. The ambient affine open is the
   image under `W'.ι`, with its affine proof from that open immersion. Exact.
   I read `Scheme.Hom.ker` in `IdealSheaf/Basic.lean:689–693` and
   `Scheme.ker_morphismRestrict_ideal` at lines 816–822: the equality here is
   precisely that existing restriction equality. Kernels are well behaved
   because a closed immersion is quasi-compact; no extra quasi-compactness
   hypothesis is needed. The square-zero ideal data determines the ideal
   sheaf on an affine basis. Over-base compatibility is supplied by
   `morphismRestrict_ι` (`Restrict.lean:581–584`): the structure map is
   `W'.ι ≫ _b`, and its source composite is the restriction of `iT ≫ _b`.
4. Clause (0), unique corresponding target open: `∀ W : T.Opens,
   ∃! W' : T'.Opens, iT ⁻¹ᵁ W' = W`. This records the homeomorphism's open
   correspondence, including the node's uniqueness for the chosen preimage.
   A first order closed immersion is a homeomorphism on points, so existence
   here is part of the same correspondence, and also supplies the open in (1).
5. Clause (1), `Z'`, `i`, `h'`, and universality over `X`: the second conjunct's
   three binders and `IsUniversalFirstOrderThickening h i h'`. I read its full
   definition and uniqueness theorem in `UniversalFirstOrderThickening.lean`.
   It includes first order, `i ≫ h' = h`, and unique lifts for arbitrary
   first order test schemes, with both equations. Exact; no affine-only test.
6. Clause (1), source and base opens with `h(V) ⊆ U`: `∀ (V : Z.Opens)
   (U : X.Opens), V ≤ h ⁻¹ᵁ U → ...`. Exact containment and quantifier order.
7. Clause (1), corresponding `V'`, image containment, and restricted maps:
   `∃ V', i ⁻¹ᵁ V' = V ∧ V' ≤ h' ⁻¹ᵁ U ∧ ...`, followed by `iV`, `hV`,
   and `hV'` with their three inclusion equations. The open correspondence
   in (0), applied using `b = h'`, determines this `V'` uniquely. The
   equations identify the maps as restrictions, because the open inclusions
   are monomorphisms. Existentially choosing these maps neither changes them
   nor strengthens the conclusion. Exact.
8. Clause (1), universal first order thickening of `V` over `U` for `h|V`:
   `IsUniversalFirstOrderThickening hV iV hV'`. This includes the closed
   immersion, square-zero ideal, compatibility, and every unique test lift
   over `U`, in the dependency's general-scheme sense. Exact.
9. Clause (2), open `U` containing the image of `h`, its factorization `hU`,
   and inclusion `j`: `∀ (U : X.Opens) (hU : Z ⟶ U.toScheme),
   hU ≫ U.ι = h → ...`. I checked Mathlib's open-immersion lifting API:
   containment gives precisely this unique factorization, and conversely
   the displayed equation implies containment. This encodes the node's
   stipulated factorization without an extra assumption.
10. Clause (2), universal thickening over `U` and conclusion over `X`:
    binders `i`, `hU'`, assumption `IsUniversalFirstOrderThickening hU i hU'`,
    and conclusion `IsUniversalFirstOrderThickening h i (hU' ≫ U.ι)`.
    The scheme and immersion are unchanged and the base map is composed
    with the inclusion, as in the node. Exact.

Dependency check: `Scheme` in Mathlib is a locally ringed space locally
isomorphic to spectra of commutative rings, not a scheme over a field.
`IsOpenImmersion` (`OpenImmersion.lean:38–39`) is the underlying locally
ringed space open-immersion predicate. `Thickening.lean` and
`UniversalFirstOrderThickening.lean` give the exact predicates above and contain
no hollow data definitions. Their import provides the canonical `Opens`,
`toScheme`, `ι`, restriction and ideal-sheaf constructions. No dependency is
unusable; no new definition node or dependency module is needed. The item has
no `statement_change`, and I did not change its mathematical statement.

Edge cases: empty `Z`, `T`, `T'`, or `X` are allowed. In clause (0), empty
`X` now correctly permits only tests admitting the given structure map.
Empty opens and `U = ⊥` are covered: image containment or factorization then
forces the corresponding source empty, and a first order thickening has the
same points. Whole opens recover the original maps. The identity immersion
has zero ideal, so zero ideals and the order-zero example are allowed. There
is no index set or order parameter in this theorem. Arbitrary characteristics
and nonreduced/nonaffine schemes remain allowed. The explicitly bound `u`
is arbitrary and shared with the recorded universal predicate; test schemes
have the same universe as its objects, never an independently smaller test
universe. No variable or universe is left auto-implicit.

Independent searches, with wording different from the worker's:

- LeanFinder via `msearch.py`: “A square zero closed immersion restricts on
  open subsets and a terminal infinitesimal extension is preserved when the
  base is replaced by an open neighborhood”. Eight hits, including immersion
  restrictions and `IsOpenImmersion.lift`; none states this universal property.
- Loogle via `msearch.py`: `"ker", "morphismRestrict"`. One exact restriction
  ideal lemma, `Scheme.ker_morphismRestrict_ideal`, read as above; it is only
  one component of clause (0), not the three-clause theorem.
- LeanSearch via `msearch.py`: “Restriction of square-zero closed immersions
  to opens preserves the universal extension property over an open neighborhood
  of the image”. Internal Server Error: unavailable, not evidence of absence.
- `rg` for `thicken|infinitesimal|square.?zero` in Mathlib algebraic geometry,
  the source project's `WeilConjectures`, and project algebraic geometry;
  narrowed search for `universal.*thicken|thicken.*universal` throughout
  `lean/Sheaf` and those sources. Mathlib has restriction tools and a formal
  unramifiedness docstring, not this theorem. The source's universal
  homeomorphism result concerns surjective closed immersions, not universal
  first order lifts. The project's ring-existence, scheme-existence,
  thickening-integrality and flat-unramified statements have different
  hypotheses/conclusions; I opened their declarations. No duplicate.
- Exact item id, declaration and module-name searches in `WeilConjectures`
  and `dag/lean_names_upstream.json`: no match or collision.

The one mismatch repaired is the missing clause-(0) structure-map binder.
The rest of the signature and the eight-step proof docstring are unchanged:
restriction and open correspondence; image containment and restricted maps;
existence and uniqueness of lifts into `V'`; base enlargement and existence
and uniqueness of lifts over `X`. Its source and blueprint labels are present,
there is one named theorem with `sorry`, no new definition, no proof supplied,
no private notation or local instance, and all Lean lines fit 100 characters.
I updated `lean.statement` verbatim from the final signature. Server compilation
of the delivery module succeeded in 2.6 seconds, exit 0, with no warnings.
