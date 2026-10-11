## Worker report

No new module: both independent clauses already exist in Mathlib. The node's lean record lists
AlgebraicGeometry.IsProper.isStableUnderBaseChange (Mathlib.AlgebraicGeometry.Morphisms.Proper,
line 72) and AlgebraicGeometry.smooth_isStableUnderBaseChange
(Mathlib.AlgebraicGeometry.Morphisms.Smooth, line 117). Its primary signature is copied verbatim
from Proper.lean. Both full signatures and their source bodies were read, together with the
MorphismProperty.IsStableUnderBaseChange definition and pullback_snd specialization in
Mathlib.CategoryTheory.MorphismProperty.Limits.

Hypothesis and clause correspondence:

- Arbitrary schemes X, S, S' are Scheme.{u}; arbitrary f : X ⟶ S and g : S' ⟶ S have
  no finiteness, field, characteristic, smoothness or properness assumptions on g.
- X' is CategoryTheory.Limits.pullback f g, and f' is pullback.snd f g, precisely the
  chosen fibre product and second projection. Scheme pullbacks exist without hypotheses.
- Clause (1) is IsProper f → IsProper (pullback.snd f g), obtained from the first existing
  stability instance by MorphismProperty.pullback_snd (P := @IsProper) f g.
  IsProper is the dependency's recorded notion: separated, universally closed, locally of
  finite type. UniversallyClosed supplies quasi-compactness, hence finite type as required.
- Clause (2) independently is Smooth f → Smooth (pullback.snd f g), obtained from the second
  existing stability instance by MorphismProperty.pullback_snd (P := @Smooth) f g.
  In particular no properness hypothesis is imposed in this clause.
  def-sbc-smooth-morphisms now explicitly records Mathlib Smooth; its note identifies it
  with locally of finite presentation and formally smooth by Stacks 02H6. Thus the old
  stage-1 mathlib_candidate caveat no longer requires a duplicate statement or definition.

Dependency declarations read and reused:

- def-pc-scheme: AlgebraicGeometry.Scheme and Scheme.Hom, Mathlib.AlgebraicGeometry.Scheme.
- def-pc-fibre-product: Limits.pullback, pullback.fst, pullback.snd, pullback.lift and
  pullback.hom_ext in Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback.
- def-pc-base-change: Sheaf.AlgebraicGeometry.BaseChangeConventions was read in full.
  Its record explicitly directs scheme base-change users to Limits.pullback f T.hom and
  pullback.snd; its main declaration Scheme.Modules.moduleBaseChange concerns modules,
  which do not occur here. No private copy or module specialization is needed.
- def-weil-proper-morphism: AlgebraicGeometry.IsProper, Mathlib.AlgebraicGeometry.Morphisms.Proper.
- def-sbc-smooth-morphisms: AlgebraicGeometry.Smooth, Mathlib.AlgebraicGeometry.Morphisms.Smooth.

Edge cases: empty schemes and empty pullbacks are allowed, including disjoint images of f
and g; identity base changes and identity f are allowed. No nonemptiness, Noetherian,
finite-dimensional, field, characteristic, or relative-dimension condition is introduced.
The statements are universe-polymorphic for schemes, matching the dependency convention.
Stability on arbitrary cartesian squares is equivalent to the chosen-pullback statement,
since these properties respect isomorphisms; no extra conclusion is being asserted.

Searches (actual queries logged in searches.jsonl):

- msearch.py leansearch: "proper and smooth scheme morphisms are stable under arbitrary base change";
  service unavailable (Internal Server Error).
- msearch.py leanfinder: "proper and smooth scheme morphisms are stable under base change";
  found IsProper.isStableUnderBaseChange and the deprecated alias
  isSmooth_isStableUnderBaseChange. Read Smooth.lean to select the current name.
- msearch.py loogle: "AlgebraicGeometry.IsProper, AlgebraicGeometry.Smooth"; zero hits.
- msearch.py grep: "isStableUnderBaseChange|class Smooth|class IsProper" and
  "instance.*pullback.snd|smooth_isStableUnderBaseChange|isStableUnderBaseChange" under
  AlgebraicGeometry/Morphisms; found stability infrastructure. Direct reads of Proper.lean
  and Smooth.lean confirmed the two exact instances and class definitions.
- rg in WeilConjectures and lean/Sheaf for proper/smooth baseChange, base_change and
  lem-pc-proper-base-change: no combined statement; source has narrower relative-dimension
  statements, unnecessary because the Mathlib instances already give both clauses.
- dag/lean_names_upstream.json searched for related names; no additional declaration needed.

The source literature is absent locally. Read the primary sources online:
[proper base change, Tag 01W4](https://stacks.math.columbia.edu/tag/01W4),
[smooth base change, Tag 01VB](https://stacks.math.columbia.edu/tag/01VB), and
[the smoothness equivalence, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6).
They confirm the two clauses and the dependency's use of Smooth.

No statement correction, new nodes, dependency modules, or disputed statements.
Server signature check uses scratchpad/Check.lean, excluded from delivery; it checks both
existing instances and their second-projection specializations without adding a declaration.

## Second reading by H1

Independently read the item and all five statement dependency nodes, the complete
BaseChangeConventions module, Scheme/Scheme.Hom, the chosen pullback and its projections,
IsProper, Smooth, both existing stability instances, and IsStableUnderBaseChange.of_isPullback
and pullback_snd. No semantic mismatch found; the existing records are retained unchanged.

Object/hypothesis/conclusion checklist, in the node's order:

- Schemes X, S, S': `{X S S' : Scheme.{u}}`, with arbitrary universe u. Scheme is a locally
  ringed space locally isomorphic to an affine spectrum; Scheme.Hom is a locally ringed
  space morphism. This is def-pc-scheme, not a variety or a scheme over a field. PASS.
- Arbitrary morphisms f:X→S and g:S'→S: `(f : X ⟶ S) (g : S' ⟶ S)` in the specialization
  of each stability instance. Neither morphism has any ambient extra instance. PASS.
- X'=X×_S S': `pullback f g`; `HasPullback f g` is supplied for all scheme morphisms by
  Mathlib.AlgebraicGeometry.Pullbacks, not an additional mathematical hypothesis. The
  definitions pullback.lift and its projection equations give exactly the dependency's
  universal property. PASS.
- f':X'→S', base change of f along g: `pullback.snd f g`. This agrees with the scheme-base-
  change convention in def-pc-base-change and its module header (the main declaration
  moduleBaseChange is a different, unused clause about modules). PASS.
- Clause (1) hypothesis: `IsProper f`, the recorded def-weil-proper-morphism notion.
  Its LocallyOfFiniteType field plus QuasiCompact from UniversallyClosed is precisely
  finite type, so no finite-type requirement is lost. PASS.
- Clause (1) conclusion: `IsProper (pullback.snd f g)`, from
  `IsProper.isStableUnderBaseChange` and `MorphismProperty.pullback_snd`. PASS.
- Clause (2) hypothesis: independently `Smooth f`, not Smooth AND IsProper. Opened
  def-sbc-smooth-morphisms: its landed record is Mathlib Smooth, explicitly identified
  with locally finite presentation plus formally smooth by Stacks 02H6. Read Smooth's
  affine-chart field, not just the name. PASS.
- Clause (2) conclusion: `Smooth (pullback.snd f g)`, from
  `smooth_isStableUnderBaseChange` and the same projection specialization. PASS.
- Quantifier order: schemes, f and g, then the respective hypothesis. The two independently
  universally quantified clauses are equivalent to the node's two clauses for each f,g.
  Stability on all cartesian squares introduces no stronger assertion: the pullback's
  universal property identifies every such square with the chosen pullback, and both
  properties respect isomorphisms. PASS.

Source check: local Stacks .tex files are absent. Read raw upstream morphisms.tex and
more-morphisms.tex from https://raw.githubusercontent.com/stacks/stacks-project/master/,
including lemma-base-change-proper (01W4), lemma-base-change-smooth (01VB),
lemma-base-change-finite-presentation (01TS), lemma-base-change-formally-smooth (02H2),
and lemma-smooth-formally-smooth (02H6). Also opened the tag pages
https://stacks.math.columbia.edu/tag/01W4, https://stacks.math.columbia.edu/tag/01VB,
https://stacks.math.columbia.edu/tag/02H6 and https://stacks.math.columbia.edu/tag/02H0.
These results concern arbitrary scheme morphisms; there is no surrounding Noetherian,
base-field or characteristic hypothesis. The six proof steps of the node agree with
separated/finite-type stability, universal closedness, their properness conjunction,
locally finite presentation stability, lifting via the fibre-product universal property,
and the smoothness conjunction. No correction record is needed.

Edge cases: empty schemes and empty fibre products are admitted; f or g may be identities.
There is no nonempty/inhabited condition, no characteristic restriction, and no dimension
or n parameter (so dimension-zero cases are included). Empty index sets and additive zero
objects do not occur in this statement. Universe u is arbitrary; a common universe is the
scheme-category convention of the dependencies, not a fixed small universe. No field,
Noetherian, quasi-compact-base or relative-dimension assumption is introduced.

Independent searches (in searches.jsonl):

- LeanFinder: "second projection from a fibre product preserves properness and smoothness
  of schemes" found IsProper.instSndScheme and related projection instances. Read the
  proper snd instance in Proper.lean; it uses exactly [IsProper f].
- Loogle: "MorphismProperty.IsStableUnderBaseChange AlgebraicGeometry.Smooth" returned
  zero hits / unknown identifier in that service; no absence claim follows from this.
- LeanSearch: "the pullback projection of a smooth scheme morphism is smooth" was
  unavailable (Internal Server Error); no absence claim follows from this.
- Grep: "IsProper.*pullback.snd|IsStableUnderBaseChange @Smooth|IsStableUnderBaseChange
  @IsProper" in Mathlib, and direct source reads, confirm the two exact existing instances.
- Independently rg-searched WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  proper/smooth with base-change or pullback, this blueprint id, and the stability name.
  Read the source Picard.Scheme theorem
  smoothOfRelativeDimension_and_isProper_and_geometricallyIntegral_pullback_snd: it only
  concerns field extensions and relative dimension one with geometric integrality, so
  it does not replace the two unrestricted Mathlib clauses. Cohomological smooth-base-
  change results found by the broad search concern different statements.

No new definition nodes or dependency modules are present or needed. No delivered Lean
module means no new definitions, hollow data, sorry proofs, import/docstring conventions
or unbound variables to repair. The primary lean.statement is verbatim the instance
signature in Proper.lean; the second declaration is listed separately with its module
identified in lean.note. No duplicate combined theorem was introduced.

Validation: reran scompile.py on scratchpad/Check.lean (not delivered). Both existing
instances and both fully quantified second-projection specializations compile cleanly
on the server, with autoImplicit disabled, no errors and no warnings. Changes in this
second reading: appended this independent checklist and validation; no statement,
definition, dependency or Lean-record changes.
