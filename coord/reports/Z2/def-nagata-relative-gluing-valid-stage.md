## Worker report

The module Sheaf.AlgebraicGeometry.NagataRelativeGluingValidStage defines the actual finite
relation lists of the fixed raw datum, their equality-choice inputs, the selected common
stage, and the canonical transport to that stage. No gluing axioms at that stage are assumed.
Every definition has full data; none selects data from a sorry theorem.

Hypotheses and clauses:

- The directed nonempty index, inverse diagram, affine transitions, limit cone and original
  qcqs base stage are the explicit section variables I, D, c, hc, i₀ and their instances.
  The scheme and finite-presentation morphism are X and f, with locally finite presentation,
  quasi-compactness and quasi-separatedness instances, matching the raw datum signature.
  The qcqs limit-base instances are retained from that signature.
- The fixed raw datum is R : NagataRelativeGluingDatum D c hc i₀ f. Its fixed presentation,
  overlap indices, base boundPair and boundOrder are used directly.
- nagataRelativeRawChart/Left/Right are the canonical pullbacks over R.raw.stage, with
  no unconstrained scheme choices. P : NagataRelativeRawInclusions contains the canonical
  inclusion maps with their first-projection equations. Over typing supplies the second
  projection equation, so these maps are uniquely determined. Its four fields do not
  assert any gluing axiom.
- nagataRelativeMapRelations enumerates both inverse composites on every overlap piece;
  both forward and backward piece-agreement equations; forward/reversed-backward agreement;
  identity maps on diagonal pieces; and all triple cocycle equations on canonical common
  domains. Its List entries are computed from R and P, never supplied arbitrarily.
  Intersections are pullbacks in Over of the raw base, which canonically are scheme
  intersections over the named chart. The triple common domain first pulls back the
  forward image against the next left inclusion, then against the direct left inclusion.
- nagataRelativeOpenRelations enumerates diagonal coverage, opposite-orientation domain
  agreement, and the two-step versus direct domain equality on every first piece. The
  finite unions are iSup over R.base.base.overlapIndex. Finite instances are R's, and
  Fintype.ofFinite supplies enumerations only within definition bodies.
- NagataRelativeOpenEqualityChoice supplies qcqs source, compact opens and their actual
  limit-preimage equality. nagataRelativeOpenEqualityStage calls nagataQCOpenEqualityStage
  on exactly that entry. Its classical selection is the proved upstream existence theorem.
- NagataRelativeMapEqualityChoice retains the finite-presentation and qcqs structures needed
  by NagataMorphismEqualityStageData. Its choice field is that existing record on exactly
  the computed phi and psi, with e.phi.w and e.psi.w proving they are over the base.
  nagataRelativeMapEqualityStage calls nagataMorphismEqualityStage on that choice.
- NagataRelativeGluingValidStageData gives one choice for each Fin length index in the two
  computed lists; no arbitrary list or omitted condition is possible.
- nagataRelativeGluingEqualityStages inserts R.raw.stage into the union of the images of
  all open and map equality-stage choices. nagataRelativeGluingValidStage applies
  directedFiniteUpperBound i₀ R.base.boundPair R.base.boundOrder to exactly this set.
- nagataRelativeRawStage_le_validStage is the sole named theorem with sorry. Its docstring
  gives the full proof: membership of the inserted raw stage, then
  le_directedFiniteUpperBound with R.base.boundPair_le. This proof is used only to type
  transport, not to supply selected schemes, morphisms or equality-stage choices.
- nagataRelativeGluingAtStage constructs every field of NagataRelativeGluingTransport by
  Over.pullback on the raw objects and arrows, and inverse images under pullback.fst for
  opens. nagataRelativeGluingValidDatum applies it at the computed stage. The functor maps
  any parallel equation to an equation with the same transported source and target;
  this is canonical base change and retains the earlier R and P parameters.

Dependencies read and used:

- Sheaf.AlgebraicGeometry.NagataRelativeGluingDatumDescent:
  AlgebraicGeometry.NagataRelativeGluingDatum and the whole chain of raw records;
  all charts, opens and forwardRaw/backwardRaw maps are these recorded declarations.
- Sheaf.AlgebraicGeometry.NagataMorphismEqualityStage:
  AlgebraicGeometry.NagataMorphismEqualityStageData and nagataMorphismEqualityStage.
- Sheaf.AlgebraicGeometry.NagataQCOpenEqualityStage (publicly imported by the previous one):
  AlgebraicGeometry.nagataQCOpenEqualityStage.
- Sheaf.Order.DirectedFiniteUpperBound (publicly imported by the dependency chain):
  directedFiniteUpperBound and le_directedFiniteUpperBound.
- Sheaf.RingTheory.FilteredColimitFiniteData:
  CommRingCat.exists_finite_data_stage is imported as the recorded justification for
  finite coefficient witness choices; no data is chosen from this unproved theorem.
- Upstream WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit:
  baseChangeDiagram and baseChangeCone, as used by the raw datum and equality constructions.
- Mathlib Over.pullback and pullback.fst/snd provide canonical transport and common domains.
  Mathlib Scheme.GlueData was read in full: it is gluing of already-valid data, not this
  definition of the stage and raw transported pieces, and is not duplicated here.

Edge cases: all finite chart and overlap indices can be empty; empty lists contribute
no equality stages while insertion still retains the raw stage. Empty overlaps give bottom
unions; diagonal bottom=top is required only on an empty chart, as expected. Coincident
charts, repeated stages and repeated equations are allowed (Finset removes duplicate stages).
The preorder is not strengthened to a partial order; homOfLE and pullbacks use canonical
comparison maps. All schemes and the directed index are in universe u, as required. No
ring characteristic, nonempty chart index, or extra separatedness hypothesis is imposed.

Searches for an existing notion:

- msearch.py leanfinder: "finite upper bound stage for inverse and cocycle equalities of
  descended scheme gluing data": eight hits, principally Scheme.GlueData and Cover.gluedCover;
  none selects the stage of a raw finite relative gluing datum.
- msearch.py loogle: "AlgebraicGeometry.Scheme.GlueData,
  AlgebraicGeometry.nagataMorphismEqualityStage": zero hits; the project name is absent
  from the service index. The actual local declaration was read directly.
- msearch.py grep: "nagata.*[Gg]luing|[Cc]ocycle", AlgebraicGeometry: twelve hits, all
  existing gluing/cocycle theorems, none this finite stage construction.
- rg of WeilConjectures and lean/Sheaf for nagataRelativeGluing, NagataRelativeGluing and
  the item id: only the landed raw-datum module, no existing stage definition.
- rg over dag/nodes for the item id: the item, the two actual citers, and a textual
  statement-change mention in def-nagata-qc-open-equality-stage (not a dependency citer).

Validation: lcompile.py compiled the complete module with no errors or warnings in 4.7 s.
The server compile and maintainer preflight are checked by the required dry run.

## Statement corrected

The old statement says: "For the raw datum, form the finite list of required equalities of
 overlap opens, inverse identities, and triple-overlap cocycles. Attach to each the
 selected equality stage from the preceding constructions and define
 lambda_rel(X/S) to be their common upper bound together with lambda_raw(X/S). Let
 R_X,lambda_rel be the raw datum transported to this stage. Canonical comparison maps
 identify the source and target of each later-stage equality. Transporting its witness
 preserves the equation, so the finite upper-bound list is well typed."
The verbatim original TeX is retained in statement_change.old_statement.

The list, its domains and its parallel-map comparisons were not specified. In particular,
separately descended basic pieces need not agree at the raw stage, and triple composition
is defined on an intersection domain, not the whole first piece. The correction spells out
these lists, including the piecewise, diagonal and reverse-orientation equations needed to
glue them. It follows the same blueprint order 360 and its neighbouring eventual-axioms
and finite-presentation gluing nodes; compare Stacks Tag 01ZM's affine descent/gluing proof.
No easier existence theorem replaces the constructed stage, and no gluing axiom is assumed.
The item's five stmt_deps, empty proof and empty proof_deps are unchanged.

Every dependency citer was read:

- lemma-nagata-relative-gluing-axioms-eventually: holds true. It proves the simultaneous
  equations of these computed lists at their common upper bound, giving the named axioms.
- def-nagata-finite-presentation-descent: holds true. It glues exactly the transported
  charts and pieces after the subsequent axioms lemma; the fixed base-change comparisons
  remain those of the retained raw datum.

No dependency module and no extra definition node is needed: the explicit lists and choice
records are portions of this node's own finite-stage construction.

## Second reading by Z2

I read the corrected node first, the original statement in its statement_change,
Stacks `limits.tex`, Lemma `lemma-descend-finite-presentation` (Tag 01ZM), especially
parts (2) and (3) and the final gluing paragraph of part (1), and both actual citers.
The blueprint file is unavailable on this machine; the original node and the neighbouring
nodes supply its construction. The correction specifies the previously unnamed finite
list and its common domains; it does not replace the construction by an existence theorem.
Stacks explicitly requires equality of the two-step and direct overlap domains and the
cocycle at a sufficiently late stage. Descending basic pieces separately also requires
piecewise agreement before the transition maps can glue. The diagonal and inverse
conditions recover the ordinary scheme gluing datum. All listed equations hold in the
original datum, because its overlap maps identify the same basic opens of X.

Independent object/hypothesis/clause checklist (every verdict is pass):

- Nonempty directed inverse system, affine transitions, limit and qcqs initial base:
  the section's `I`, `Preorder`, `Nonempty`, `IsDirected`, `D`, `c`, `hc`, `i₀`,
  `IsAffineHom`, `CompactSpace` and `QuasiSeparatedSpace`. The system only needs the
  tail above i₀: affine transitions make every stage in that tail qcqs. This is the
  fixed-base form of the Stacks hypotheses, not an omitted finiteness requirement.
- Finite-presentation scheme X over the limit: `X`, `f`, `LocallyOfFinitePresentation f`,
  `QuasiCompact f`, `QuasiSeparated f`. The qcqs limit instances are derivable from
  its affine projection to the initial qcqs stage and are the same instances needed
  by the landed raw record. No Noetherian, separated or characteristic assumption
  is introduced.
- Fixed earlier choices: `R : NagataRelativeGluingDatum D c hc i₀ f`, with
  `R.base.base`, `R.raw.stage`, `R.base.boundPair`, `R.base.boundPair_le` and
  `R.base.boundOrder`. I read all nine portions of that record, not only its name.
  They retain the relative presentation, canonical chart comparisons, open descents,
  overlap identifications, forward/backward descents and their transport equations.
- Raw schemes: `nagataRelativeRawChart`, `nagataRelativeRawLeft` and
  `nagataRelativeRawRight` are the corresponding canonical pullbacks. The chart is
  the canonical expression to which `R.raw.rawChart_eq` equates the retained chart.
  The overlaps use precisely `R.schemes.leftMap` and `rightMap`.
- Canonical inclusions: `P : NagataRelativeRawInclusions ... R` has `left_fst` and
  `right_fst`. The other projection is fixed by each morphism's `Over` typing.
  Together these equations characterize the reassociation map uniquely by the
  pullback universal property. No arbitrary overlap map or gluing axiom is added.
- Forward and backward maps to charts: `nagataRelativeForwardToChart` is the raw
  forward map followed by `P.right`; `nagataRelativeBackwardToChart` is the raw
  backward map followed by `P.left`. These are exactly g and h in the corrected node.
- Finite open list: `nagataRelativeOpenRelations` computes the unions W and V by
  `iSup`, then diagonal coverage, W(j,k)=V(k,j), and on every first piece the
  equality of the inverse images of W(k,z) under g and W(j,z) under a. Thus the
  domain equation is on the overlap scheme, where both inverse images are typed.
- Finite map list: `nagataRelativeMapRelations` computes both inverse composites
  versus the identity on each piece; forward agreement on left-piece pullbacks;
  backward agreement on right-piece pullbacks; forward versus reversed backward
  agreement; the diagonal identity; and the triple equation. In the final block,
  first `pullback (g j k l) (a k z m)` makes the two-step composite meaningful.
  Its map into chart j is then pulled back against `a j z n`; both displayed maps
  from this common source have target chart z. Quantifiers range over every chart
  triple and all three piece indices. No first-piece-wide composite is assumed.
- Equality inputs and selections: `NagataRelativeOpenEqualityChoice` retains qcqs
  source, compactness of both actual opens, and their actual limit-preimage equality;
  `nagataRelativeOpenEqualityStage` calls the landed `nagataQCOpenEqualityStage`.
  `NagataRelativeMapEqualityChoice` retains the source/target finite-presentation
  instances and exactly `NagataMorphismEqualityStageData` on the computed pair,
  with `e.phi.w` and `e.psi.w` supplying the base equations. The existing data
  record includes limit equality, affine covers, generators and actual coefficient
  equality witnesses. `nagataRelativeMapEqualityStage` calls the existing selector.
  I read these dependency signatures and bodies, including the proved theorem used
  by the open selector, and the finite-data theorem's signature. No data is chosen
  from a theorem proved with sorry.
- Every equation is included: `NagataRelativeGluingValidStageData.opens` and `.maps`
  are indexed by `Fin` of the lengths of the computed lists, not supplied lists.
  Their geometric properties are consequences of the canonical raw constructions;
  their coefficient choices are the choices stipulated by the node, not extra
  finite-stage gluing assumptions.
- Selected upper bound: `nagataRelativeGluingEqualityStages` inserts the raw stage
  into exactly the union of the two images of selected equality stages.
  `nagataRelativeGluingValidStage` folds the existing `directedFiniteUpperBound`
  with the raw datum's original base point, binary bounds and auxiliary order.
- Transported datum: `nagataRelativeGluingAtStage` supplies all nine fields of
  `NagataRelativeGluingTransport` by `Over.pullback.obj`, `.map` and inverse image
  of opens under `pullback.fst`. `nagataRelativeGluingValidDatum` uses the selected
  common stage. Sources and targets of each transported parallel equation are
  transported by the same functor; preservation of equations is functoriality.
  The transport record is an output carrier, not unconstrained input choice data.
- Typing proof: `nagataRelativeRawStage_le_validStage` is the only new theorem,
  with sorry and a source-tagged complete proof plan (insert membership followed
  by `le_directedFiniteUpperBound`). It only supplies a comparison index map;
  it never supplies scheme or morphism data. The eventual gluing axioms remain
  the next node's theorem. Every declaration has the item tag and source docstring.

Edge cases: the directed index is nonempty, as in the source. The chart and piece
indices may be empty. With no charts both relation lists are empty and the raw
stage still belongs to the bound set. With an empty piece family its union is
bottom; diagonal coverage can hold after transport when the chart is empty, and
is not imposed at the raw stage. Triple and pair map lists then have no entries.
Empty schemes, repeated charts/stages, non-antisymmetric preorders and every
characteristic are admitted. The original finite algebra presentations allow zero
generators and relations; this construction adds no restriction on them. I, all
schemes, chart indices and overlap indices use the same arbitrary universe u;
there is no lower-universe test object or extra independent index universe.

Independent searches used different concept queries from the first writer:

- LeanFinder: "simultaneous eventual equality of finite diagram gluing transition
  morphisms in inverse limits of schemes". Eight hits included
  `ExistsHomHomCompEqCompAux.exists_eq`, cover gluing and pullback gluing maps.
  They are existence/equality results or gluing of valid data, not this selected
  upper bound for the fixed raw finite lists.
- Loogle: `AlgebraicGeometry.Scheme.GlueData`. Twelve hits. I opened Mathlib's
  scheme gluing record and its `CategoryTheory.GlueData` parent: they already
  require the diagonal and cocycle axioms and give a glued scheme, not the raw
  relation list, equality choices or stage selector needed here.
- msearch grep: `gluing.*stage|stage.*gluing|equal.*transition`, zero hits.
  Independent rg in Mathlib/AlgebraicGeometry, WeilConjectures and lean/Sheaf for
  `gluing.*stage|stage.*gluing|validstage|equalitystages` found the raw-datum module
  and upstream finite-presentation descent discussion. I opened upstream's
  `Scheme.exists_isPullback_of_finitePresentation`: it proves existence by
  induction gluing two charts, not this fixed simultaneous finite-list selector.
  Thus the module is not a duplicate of that declaration or Scheme.GlueData.

There are no new definition nodes or dependency modules in this delivery. The two
actual citers are exactly those in statement_change: the eventual-axioms lemma
uses the common stage to establish all of these relations, so holds:true; the
finite-presentation descent definition glues the transported pieces after that
lemma, so holds:true. Neither citer requires a different stage or an earlier
finite-stage identity. The later finite-presentation and separated-stage nodes
retain the same model and comparison; their statements do not alter this list.

No mathematical mismatch was found; the Lean module and node correction were
left unchanged. The second reading adds this independent clause-by-clause audit.
The node's `lean.statement` is verbatim `def nagataRelativeGluingValidStage : I`
from the file's section-based signature. All section variables and universes are
bound; there are no signature lets, hidden show terms, local notation or private
copies. The dependent records have at most eleven fields and both automatic
record-generation options are disabled.

Validation: independent lcompile.py run passed in 4.6 seconds without warnings.
Local `lcompile.py --all` also compiled the single delivery module with its .olean
in 4.5 seconds, within the unchanged 60-second limit. The required deliver2.py
--no-push passed the server compile and maintainer preflight (OK); nothing was
pushed, following the launcher's instruction to stop at READY.
