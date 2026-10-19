## Worker report

`Sheaf.Compactification.NagataSketchClosure` states
`AlgebraicGeometry.nagata_sketch_closure`, with its sole proof `by sorry`.
It contains two independently quantified assertions, matching the two paragraphs
of the current node. No definition, theorem proof, or other DAG node is added.

Source read: main-20261015, sec-nagata-compactification,
sk-lem-nagata-sketch-closure/_section.md (order 4), and Stacks morphisms.tex:
lemma-quasi-compact-scheme-theoretic-image (01R8),
lemma-quasi-compact-immersion (01RG),
lemma-characterize-scheme-theoretically-dense (01RE), and
lemma-equality-of-morphisms (01RH). The synchronized node is already split and
reviewed in stage 1, but has no `lean` field. Its old unit record describes the
older master snapshot; the delivered statement follows the current node and
main-20261015 source, without changing either.

Hypotheses and conclusions, clause by clause:

* A morphism of schemes is `{U T : Scheme.{u}} (i : U ⟶ T)`.
  Quasi-compactness, immersion, and quasi-separated target are
  `[QuasiCompact i] [IsImmersion i] [QuasiSeparatedSpace T]`.
* The canonical scheme-theoretic image is `i.image`, defined in Mathlib as
  the closed subscheme of `i.ker`. Its inclusion is `i.imageι` and the
  canonical factor is `i.toImage`. The canonical composite is `i` by the
  existing `Scheme.Hom.toImage_imageι`; no new image construction is made.
* The image is closed: `IsClosedImmersion i.imageι`.
* The factor from U is open: `IsOpenImmersion i.toImage`.
* U is schematically dense in its image:
  `∀ V : i.image.Opens, Function.Injective (i.toImage.app V)`.
  For every open V, this is precisely injectivity of
  O_image(V) → O_U(i.toImage⁻¹(V)); these are the components of the sheaf
  morphism O_image → i.toImage_* O_U. Stacks 01RE identifies this with
  schematic density.
* The smallest-closed-subscheme convention is rendered by quantifying over
  every `Z`, closed inclusion `k : Z ⟶ T`, and factor `f : U ⟶ Z` with
  `f ≫ k = i`. There is a unique `l : i.image ⟶ Z` with
  `i.toImage ≫ l = f ∧ l ≫ k = i.imageι`. A map between these closed
  subschemes over T is automatically a closed immersion, so this is exactly
  the usual smallest-closed-factor property.
* The independent uniqueness assertion quantifies fresh schemes U, T, S, Y.
  The open subscheme is represented by `(j : U ⟶ T) [IsOpenImmersion j]`.
  Its density assumption is `hj : ∀ V : T.Opens, Function.Injective (j.app V)`.
  In particular, no quasi-compactness of j or quasi-separatedness of this T
  is imposed. Merely imposing Mathlib's `IsSchemeTheoreticallyDominant j`
  would not render the node's density convention for an arbitrary open.
* The separated target is `(s : Y ⟶ S) [IsSeparated s]`.
  For `{a b : T ⟶ Y}`, the common-base condition is `a ≫ s = b ≫ s`:
  both maps have the same structure morphism T → S. This is equivalent to
  specifying that structure morphism and saying both are S-maps.
* Agreement on U is `j ≫ a = j ≫ b`; the conclusion is `a = b`.

All seven statement-dependency nodes were read, including their source
signatures/docstrings. The following recorded interfaces are used:

* def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
* def-weil-closed-immersion: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  `AlgebraicGeometry.IsClosedImmersion`; its immersion notion is the existing
  `AlgebraicGeometry.IsImmersion` from Mathlib.AlgebraicGeometry.Morphisms.Immersion.
* def-weil-open-immersion: Mathlib.AlgebraicGeometry.OpenImmersion,
  `AlgebraicGeometry.IsOpenImmersion`.
* def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  using its recorded `QuasiCompact` notion from Morphisms.QuasiCompact (line 43).
  No local-finite-type assumption is added.
* def-weil-quasi-separated-morphism is a Mathlib leaf, so has no `lean` record.
  Its mathlib_match is `AlgebraicGeometry.QuasiSeparated` in
  Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated (line 50).
  The scheme form is `QuasiSeparatedSpace T`, equivalent to quasi-separatedness
  of the terminal structure map by `quasiSeparatedSpace_iff_quasiSeparated`
  (lines 133–135).
* def-weil-proper-morphism: Mathlib.AlgebraicGeometry.Morphisms.Proper,
  using the recorded `AlgebraicGeometry.IsSeparated` notion (defined in
  Morphisms.Separated, lines 42–46). No properness assumption is introduced.
* def-weil-scheme-over-base is a Mathlib leaf, with mathlib_match
  `AlgebraicGeometry.Scheme.Over` in Mathlib.AlgebraicGeometry.Over.
  The statement uses explicit structure maps and the commuting equality,
  as in `Scheme.Hom.isOver_iff` (line 49).

Canonical image declarations were read in Mathlib/AlgebraicGeometry/
IdealSheaf/Subscheme.lean: `Hom.image` (662), `Hom.imageι` (665),
`Hom.toImage` (710), `Hom.toImage_imageι` (715), and
`Hom.toImage_app_injective` (754). The open-factor instance was read at
Morphisms/Immersion.lean:259. The recorded proof modules are imported privately:
WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
(`IsClosedImmersion.eq_lift`, the comparison and its uniqueness) and
WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
(`ext_of_isSchemeTheoreticallyDominant_of_isSeparated`, lines 347–367).
The theorem docstring carries the node's three proof steps and names each
of its four proof-dependency nodes. No dependency record requires repair.

Edge cases checked before finalizing:

* Empty U: its schematic image is empty; density of the empty open in that
  image is vacuous. In uniqueness, the empty open can satisfy sheaf
  injectivity only when the target scheme T is empty.
* Identity immersion and closed immersion: the canonical image factor is
  an isomorphism, hence open and schematically dense.
* A nonreduced T is allowed: no `IsReduced` hypothesis is added. For
  Spec(k[x,e]/(e²,xe)), the open D(x) is topologically dense but restriction
  kills e; it correctly fails the sheaf-injectivity density hypothesis.
* Arbitrary non-quasi-compact open: density is stated on every open, not
  just through vanishing of the quasi-coherent image ideal. The example
  preceding Stacks lemma-characterize-scheme-theoretically-dense warns
  that these two conditions differ in general.
* No nonempty, finite-type, Noetherian, or characteristic assumption is
  introduced; every variable and the shared scheme universe u is explicit.

Searches actually run with msearch.py (Q31, this item):

* leanfinder: "A quasi-compact immersion is an open immersion into its
  scheme-theoretic image; two morphisms to a separated scheme agreeing on a
  schematically dense open are equal". Eight hits: the Mathlib open-factor
  instance, quasi-compact/dominant image-factor instances,
  `Hom.toImage_app_injective`, and the reduced-source equality lemmas.
  These supply individual clauses; none states the complete conjunction.
* loogle: "AlgebraicGeometry.IsImmersion.instIsOpenImmersionToImageOfQuasiCompact".
  One hit, that exact Mathlib instance, matching the open-factor clause only.
* leansearch: "Schematically dense open immersion into a scheme implies two
  morphisms into a separated scheme agreeing on the open are equal".
  Eight hits including `ext_of_isDominant_of_isSeparated'` (requires
  `IsReduced X`) and `isClosedImmersion_equalizer_ι_left`; no whole-item match.
* grep: "toImage_app_injective|ext_of_isSchemeTheoreticallyDominant|IsOpenImmersion f.toImage",
  subdirectory AlgebraicGeometry. Three hits: Immersion.lean:259 and
  Subscheme.lean:754,765. These are partial matches only.
* Direct rg searches in WeilConjectures and lean/Sheaf for scheme-theoretic
  image/dominance found upstream compactification APIs and downstream uses.
  Searching both trees and dag/lean_names_upstream.json for
  `nagata_sketch_closure|sk-lem-nagata-sketch-closure` returned no hit.
  The upstream schematic-dominance rigidity declaration exists, but gives
  only the independent uniqueness assertion and does not state the closure
  clauses; its exact interface is used as a proof dependency.

No new nodes, statement correction, disputed statement, or dependency module.
The retained theorem compiles cleanly via scompile.py (both the sandbox probe
and its actual module name); no warning was emitted.

## Second reading by Q31

I independently opened the split node, its source section, and
`lean/Sheaf/Compactification/NagataSketchClosure.lean`. The node's objects and
clauses match the theorem as follows.

* The first assertion introduces schemes `U T : Scheme.{u}` and a morphism
  `i : U ⟶ T`, with `[QuasiCompact i]`, `[IsImmersion i]`, and
  `[QuasiSeparatedSpace T]`. The Lean binders have exactly these hypotheses;
  there is no local-finite-type, Noetherian, reducedness, finiteness, or
  characteristic hypothesis.
* The canonical image is Mathlib's `i.image`, with closed inclusion
  `i.imageι` and factor `i.toImage`. The first conjunct
  `IsClosedImmersion i.imageι` renders that the image is a closed subscheme.
  The second, `IsOpenImmersion i.toImage`, renders the open factor.
* The third conjunct quantifies every `V : i.image.Opens` and requires
  `Function.Injective (i.toImage.app V)`. This is exactly injectivity of every
  section map of `O_image → (i.toImage)_* O_U`, the node's convention for
  scheme-theoretic density.
* The final first-assertion clause quantifies every scheme `Z`, closed
  immersion `k : Z ⟶ T`, and factor `f : U ⟶ Z` satisfying `f ≫ k = i`; it
  gives a unique `l : i.image ⟶ Z` with both
  `i.toImage ≫ l = f` and `l ≫ k = i.imageι`. This is the stated smallest
  closed-subscheme factor convention. The map is not an extra hypothesis:
  with both ambient maps closed immersions, the existing closed-immersion
  comparison theorem supplies the intended closed comparison.
* The independent assertion introduces fresh `U T S Y : Scheme.{u}`, an open
  immersion `j : U ⟶ T`, and `hj : ∀ V : T.Opens, Function.Injective (j.app V)`.
  It introduces `s : Y ⟶ S` with `[IsSeparated s]`, maps `{a b : T ⟶ Y}`,
  and hypotheses `a ≫ s = b ≫ s` and `j ≫ a = j ≫ b`; the conclusion is
  `a = b`. There is deliberately no quasi-compactness assumption on `j`.

The dependency declarations were re-read: `Scheme`, `IsClosedImmersion`,
`IsOpenImmersion`, `QuasiCompact`, `QuasiSeparatedSpace`, `IsSeparated`, and
`Scheme.Over`/`Hom.IsOver` are the recorded Mathlib notions. The finite-type,
proper, and over-base records remain stage-1 statement dependencies and add no
hypotheses to this theorem. The imported closed-immersion comparison and
separated-target rigidity modules are used as proof dependencies; no recorded
dependency interface is unusable, so no dependency module was added.

Edge cases checked again: empty `U` (the density statement is vacuous for its
empty image), identity and closed immersions (the image factor is an
isomorphism), arbitrary non-quasi-compact open `j` in the second assertion,
and nonreduced targets (where topological density need not imply the stated
section injectivity). The shared universe is explicit and no nonempty index,
zero-object, or characteristic assumption is present.

For the one-definition rule I reran searches in Mathlib, the upstream
`WeilConjectures` tree, and `lean/Sheaf`, plus LeanFinder/Loogle/LeanSearch
queries for the complete closure-and-rigidity statement. Only the individual
Mathlib image, open-factor, section-injectivity, and reduced-source equality
lemmas were found; no declaration states this item. The theorem therefore is
new and does not duplicate an existing notion. No mismatch was found and no
file or node change was required. `scompile.py` compiled the module cleanly
with no warnings other than the permitted `sorry`-proof condition.

The independent source check covered Stacks morphisms.tex lines 825-887
(smallest image and quasi-compact kernel ideal), 1100-1119 (injectivity
characterization of schematic density), 1139 onward (open factor), and
1212-1228 (relative separated-target equality). These impose no additional
standing Noetherian, base-field, or reducedness assumption. The current
blueprint section has exactly the node's two assertions. No statement
correction or new node is needed.

Fresh search details: LeanFinder's query began "The schematic image of a
quasi compact immersion is closed" and included the open dense factor and
separated-target rigidity clauses; its eight hits were individual image and
immersion lemmas. Loogle on `AlgebraicGeometry.Scheme.Hom.toImage_app_injective`
returned its affine-open section lemma only. LeanSearch's query began "The
canonical scheme theoretic closure of an immersion" and included relative
map equality; it returned equalizer and closed-immersion lemmas only. Direct
`rg` for `nagata_sketch_closure|Schematic closure|sketch closure` found no
declaration in upstream or the project; alternative scheme-image searches
found the existing canonical construction and comparison interfaces already
used here. The saved search log records the tool results.

Mechanical verification: the node's `lean.statement` is verbatim the file's
signature; every Lean line has at most 100 characters. The required
`deliver2.py --no-push` returned OK at `e625b8fb37`: preflight passed and the
module compiled, with nothing pushed. Only the second-reading report was
added; the reviewed Lean statement and node are unchanged.
