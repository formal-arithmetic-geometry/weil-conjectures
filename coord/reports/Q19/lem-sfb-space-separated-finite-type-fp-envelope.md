## Worker report

Item: `lem-sfb-space-separated-finite-type-fp-envelope`, stage 2, group Q19.

The module `Sheaf.AlgebraicGeometry.SpaceSeparatedFiniteTypeFPEnvelope` states
`AlgebraicGeometry.AlgebraicSpace.exists_separated_finitePresentation_closed_envelope`.
Its only theorem has proof `by sorry`. There are no new definitions, axioms, helper
statements, dependency repairs, or statement corrections.

Source read: `literature/stacks-project/spaces-limits.tex`, lines 2874–2908,
Tag 0873, proposition-separated-closed-in-finite-presentation, including its proof.
The accepted DAG split is preserved verbatim. The source's accidental reference to
X as a closed subscheme of Y instead of Z is already corrected in that split.

The inherited BLOCKED ending concerned Q34's already accepted stage-1 split. It
is not a stage-2 obstruction: `coord/brief-stage2.md` §0 explicitly distinguishes
this handoff. The live node is split, has a passing stage-1 review, has no `lean`
record, and is in `coord/queue.tsv` at stage 2. The subsequent independent return is addressed below.
This resumed worker reviewed the saved Lean module, node record and report against the
current live sources; the accepted stage-1 split remains unchanged.

Hypothesis-by-hypothesis and clause-by-clause translation:

- Ambient schemes and spaces: `X Y : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))`.
  The already defined `AlgebraicSpace` is the full subcategory of fppf sheaves
  with representable diagonal and an etale surjective scheme atlas. Its arrows
  `f : X ⟶ Y` are natural transformations of those sheaves. This keeps general
  algebraic spaces; it does not restrict X, Y, or Z to schemes.
- Absolute base and sizes: `universe u` is explicit, and `Spec (.of (ULift.{u} ℤ))`
  is the spectrum of the integers in the scheme universe u. The lift only moves
  the integer ring to that universe. Schemes, chart rings, and sheaf values use
  the existing foundation's universe. No independent smaller test universe and
  no equality of previously independent universes is introduced.
- Y quasi-compact: `hYqc` is the existence of `U : Over (Spec (.of (ULift.{u} ℤ)))`
  and `a : yoneda.obj U ⟶ Y.obj.obj` such that `CompactSpace U.left ∧ IsEtale a ∧
  IsSurjective a`. This is exactly the stated quasi-compact scheme atlas criterion.
- Y quasi-separated: `hYqs` is `IsQuasiCompactPresheafMap
  (prod.lift (𝟙 Y.obj.obj) (𝟙 Y.obj.obj))`. The displayed map is the absolute
  diagonal Y to Y times Y; over Spec Z this is the absolute sheaf product.
  The existing quasi-compactness predicate quantifies over every affine scheme
  test and supplies a quasi-compact scheme atlas of its pullback.
- f separated: `hsep : MapIsSeparated f`. Its definition is
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
  (pullback.diagonal f.hom.hom)`, precisely the relative closed diagonal test.
- f finite type: `hqc : IsQuasiCompactPresheafMap f.hom.hom` and
  `hlft : MapIsLocally (@LocallyOfFiniteType) f`. These are exactly quasi-compactness
  by affine tests and local finite type on all compatible etale scheme charts.
  No finite-presentation hypothesis on f, Noetherian hypothesis, or representability
  of f has been inserted. We use the atlas predicate directly, rather than silently
  changing the node to the point-space formulation of `MapIsFiniteType`.
- Envelope: `∃ (Z : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) (i : X ⟶ Z)
  (g : Z ⟶ Y)` supplies precisely the three requested objects.
- i closed immersion: `IsRepresentableWith
  (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom`. Every scheme test has an actual
  representing scheme and a closed-immersion projection; this is the existing
  representability predicate applied to the recorded Mathlib closed-immersion notion.
- g separated: `MapIsSeparated g`, the same closed relative diagonal test as for f.
- g finite presentation: `IsQuasiCompactPresheafMap g.hom.hom ∧
  IsQuasiCompactPresheafMap (pullback.diagonal g.hom.hom) ∧
  MapIsLocallyOfFinitePresentation g`. These are, in order, quasi-compactness,
  quasi-separatedness, and chartwise local finite presentation.
- Factorization: `i ≫ g = f` is equality of morphisms of algebraic spaces over
  Spec Z, hence equality of the corresponding natural transformations.

Dependency declarations and imports:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`
  (def-pc-scheme; their complete definitions/docstrings were read).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, `IsSurjective`; the actual
  representability, atlas, and category definitions were read in full.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, a closed embedding with surjective stalk maps.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, the affine-local ring-map condition.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, the analogous finite-presentation
  condition. Both Mathlib class signatures and docstrings were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`; full signatures and docstrings were read. The
  statement uses the existing presheaf fibre products and their canonical diagonals.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`:
  `AlgebraicGeometry.AlgebraicSpace.IsQuasiCompactPresheafMap` supplies exactly the
  atlas-based affine-test notion. Its owning landed definition node
  `def-sfb-space-quasi-compact-presheaf-map` is added to `stmt_deps`, as allowed by
  brief-stage2 §5 for already landed statement dependencies. No theorem from the
  trace-formula argument is assumed here; this is the existing foundational predicate.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocally`, `MapIsSeparated`, and
  `MapIsLocallyOfFinitePresentation`. Their definitions and docstrings were read.
  Their owning landed definition `def-sfb-space-morphism-properties` is likewise
  added to `stmt_deps`. The predicates reuse precisely the recorded scheme notions.
- `Mathlib.AlgebraicGeometry.Limits` supplies the size-polymorphic absolute scheme
  base; `specULiftZIsTerminal` was read to check that it is Spec Z.
- The size-convention node is metatheoretic and has no declaration to import.
- Plain proof imports cover the already stated Mathlib leaves:
  `Mathlib.AlgebraicGeometry.Sites.MorphismProperty` and
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` for etale covering composition;
  `Mathlib.AlgebraicGeometry.AffineScheme` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` for affine qcqs schemes.
  Their recorded instance signatures/docstrings were read.
- The other proof dependencies have neither `lean` records nor Mathlib matches at
  this handoff: lem-sfb-space-quasicompact-affine-tests,
  lem-sfb-space-closed-subspace-proper, lem-sfb-space-qcqs-source-products,
  lem-sfb-space-finite-type-fp-envelope, lem-sfb-space-fp-qcqs-source,
  lem-sfb-space-closed-subspace-fp-approximation,
  lem-sfb-space-separated-fp-composition, and
  lem-sfb-space-fixed-base-eventually-separated. Their module imports cannot yet be
  supplied; their steps remain in the theorem's proof docstring and the unchanged DAG.

Edge cases checked before writing:

- Empty Y forces empty X; the empty space and its empty atlas are permitted, and
  Z may be empty. Neither the atlas nor a space is required to be inhabited.
- Empty X and nonempty qcqs Y are permitted, again with an empty envelope available.
- The identity of a qcqs space satisfies the hypotheses and can use Z = Y.
- A non-finitely-presented closed immersion into qcqs Y still has finite type and
  is included; no finite generation of its defining ideal is imposed on i or f.
- No separatedness of Y is assumed: quasi-separatedness is its only diagonal
  hypothesis. No quasi-compactness or quasi-separatedness of X is added as a binder.
- Algebraic spaces not representable by schemes remain included. All field
  characteristics and universe levels u remain included.

Searches (all via the prescribed wrapper or read-only rg):

1. `msearch.py ... leanfinder` with query
   "A separated finite type morphism of algebraic spaces over a quasi compact quasi
   separated base factors as a closed immersion into a separated finitely presented
   algebraic space" returned eight scheme-only morphism-property hits (including
   IsSeparated, IsClosedImmersion.of_comp, and IsImmersion factorization). None is
   the space theorem.
2. `msearch.py ... loogle` with query
   `AlgebraicGeometry.AlgebraicSpace, AlgebraicGeometry.IsSeparated,
   AlgebraicGeometry.LocallyOfFinitePresentation` returned zero hits, with
   "unknown identifier 'AlgebraicGeometry.AlgebraicSpace'" because that is a project
   declaration. A second valid query
   `AlgebraicGeometry.IsSeparated, AlgebraicGeometry.LocallyOfFinitePresentation`
   returned zero hits.
3. `msearch.py ... grep 'separated.*(envelope|finite.presentation)|closed.*finite.presentation'
   AlgebraicGeometry` returned zero hits.
4. Read-only `rg` for the item id in `lean/WeilConjectures` returned no match.
   Read-only `rg` for `envelope`, `closed_in_finite_presentation`, and separated
   finite presentation in project/upstream sources found scheme-only results in
   `WeilConjectures/AlgebraicGeometry/SeparatedEnvelope.lean` and
   `WeilConjectures/Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean`, and the
   scheme-only Chow factorization module. Their signatures were read: they take
   `X Y : Scheme`, so cannot state this general algebraic-space result.
5. Read-only `rg` of `lean/Sheaf/AlgebraicGeometry` for quasi-compactness,
   separatedness, finite type and finite presentation found the already landed
   predicates listed above. No existing space envelope theorem was found.
6. The `dag/nodes` records for all original statement dependencies and all proof
   dependencies were read, including their `lean` and `mathlib_match` fields.

No STATEMENT-DISPUTED flag or source-based statement correction is needed.

Validation: the prescribed `scompile.py Q19
lem-sfb-space-separated-finite-type-fp-envelope <module>` completed successfully
in both module contexts: sandbox (5.2 s) and library module (9.6 s). No errors or
unexpected warnings. Auto-bound implicits are disabled with `set_option autoImplicit false`.

## Second reading by Q19

The dispatcher explicitly prohibits starting other agents; this is a separate
second pass by the delivering worker, not a claim of independent authorship.
The maintainer's independent delivery review remains required.

Reopened the source, node and completed module. Checked each binder against the
node: absolute Spec Z; arbitrary algebraic spaces X and Y; Y has a quasi-compact
scheme atlas and quasi-compact absolute diagonal; f is separated, affine-test
quasi-compact, and locally finite type on compatible etale charts. Checked every
conclusion: actual Z, i, g; representable scheme-test closed immersion i; separated
g; affine-test quasi-compact g and quasi-compact relative diagonal; local finite
presentation on charts; and exactly the factorization identity i followed by g = f.
The absolute diagonal uses `prod.lift` and the relative diagonal uses
`pullback.diagonal`; both refer to the existing sheaf/presheaf limits, not to
arbitrary maps. The atlas-based predicate is used for all quasi-compactness clauses,
so no unrecorded equivalence to point-space compactness is needed. Universes match
those of the existing algebraic-space foundations, with the sole explicit u.

No hypothesis or conclusion mismatch was found. The two added statement dependencies
are already landed predicate owners, not new notions or changes to the accepted
split. The module contains only the requested theorem, its natural-language four-step
proof, and `sorry`; no temporary `#check` command or proof experiment remains.

Resumption validation (2026-10-23): the current stage-2 queue still lists this item,
and the live node still has no Lean record. The prescribed deliver2.py --no-push
passed preflight and per-file compilation (dry-run commit 71a1276cc00). Repeated
LeanFinder, Loogle and Mathlib grep searches found no existing algebraic-space
envelope theorem; the available upstream envelopes quantify over schemes.

## Returned-delivery repair

The return on immutable head `9eb6cf49a3b4` raised one issue, H2/§5:
`lem-trf-space-qc-separated-etale-local` owns a theorem, whereas this statement
uses only the independent definition `IsQuasiCompactPresheafMap` in that module.
The suggested definition-node repair has since been landed by Q97 as
`def-sfb-space-quasi-compact-presheaf-map`. Read its complete node and Lean record:
it records `existing: true` on
`Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`, declaration
`AlgebraicGeometry.AlgebraicSpace.IsQuasiCompactPresheafMap`.
Replaced the theorem node in the item's `stmt_deps` with this landed definition
owner. No new node or dependency module is necessary, by the one-definition rule.
The module remains byte-identical to the returned delivery. Compared the saved
node with current live main without Git: only `stmt_deps` and `lean` differ;
the live item has no Lean record, and all accepted statement/proof fields agree.

Reopened the actual definition at lines 33–44: for every `Z : Over S`,
`IsAffine Z.left`, and `h : yoneda.obj Z ⟶ F`, it requires actual `U,p,q`,
the compatibility `q ≫ g = yoneda.map p ≫ h`, `CompactSpace U.left`, and
etaleness and surjectivity of the canonical `pullback.lift`. These are exactly
all clauses of the landed definition node. The definition does not invoke
`quasiCompact_separated_etaleLocal` or its proof. Its source is the atlas
condition in Stacks 03E3 (`spaces-properties.tex`, definition-quasi-compact),
and the affine-test morphism convention of 03HE/03KG. Empty schemes and empty
pullbacks are allowed; identity morphisms admit their affine test as atlas;
no representability of the original algebraic-space morphism is imposed.

Rechecked the item against Stacks 0873 and the retained Lean: `hYqc` supplies the
quasi-compact scheme atlas of Y; `hYqs` tests the absolute diagonal; `hsep`,
`hqc`, and `hlft` give precisely separated finite type f. The existential Z,i,g
has a scheme-test closed immersion i, separated g, quasi-compact g and relative
diagonal, chartwise local finite presentation, and `i ≫ g = f`. Changing the
predicate's owning node changes none of these hypotheses or conclusions.

Repair searches actually run: LeanSearch query "A morphism of presheaves on
schemes is quasi compact if every affine scheme base change admits an etale
surjective atlas by a quasi compact scheme" returned eight scheme-only hits;
Loogle `AlgebraicGeometry.QuasiCompact` returned twelve scheme-only hits;
Mathlib grep `IsQuasiCompactPresheafMap|QuasiCompact` in AlgebraicGeometry
returned scheme quasi-compactness uses. Read-only searches of the DAG and
`lean/WeilConjectures`/`lean/Sheaf` found the landed definition owner and the
single defining declaration in `SpaceQCSeparatedEtaleLocal.lean`. No definition
is copied or redefined. The interrupted Loogle call completed before the pause,
as confirmed by its successful entry in `searches.jsonl`.

The pre-repair saved-packet dry run passed at `2445f41b729`; it was not pushed.
This repair is substantive DAG ownership repair, not an unchanged re-push.

Repair validation: prescribed `scompile.py` succeeded in sandbox (5.2 s) and
library (9.6 s) contexts with no errors or unexpected warnings. The self-check
confirmed that only `lean` and `stmt_deps` differ from current live main, the
only two added dependencies are landed definition owners, and `lean.statement`
is verbatim the unchanged module signature. Explicit universes and
`autoImplicit false` remain present; the sole postponed theorem uses `sorry`.
