## Worker report

This is stage 2, after NB's stage-1 split was reviewed and merged on 2026-10-18 at
02:03 UTC. That merge did not add a `lean` record. The earlier worker's stale-assignment
diagnosis confused a completed split with a completed Lean statement. The current
delivery adds the module `Sheaf.AlgebraicGeometry.EtaleSheafAlgebraicSpaceRealization`
and changes only the item's `lean` record. No shared source or tool was edited, and
no direct git command, global build or agent delegation was used.

The principal statement is
`AlgebraicGeometry.AlgebraicSpace.etaleSheaf_algebraicSpace_realization`.
The definitions give actual Hom presheaves, their postcomposition maps, the canonical
adjunction counit comparison, the base-change functor of points, and the identity
restriction isomorphism. The three postponed propositions are
`realizationPresheaves_isSheaf`, `realizationBaseChange_isEtaleSpace`, and the main
theorem. They are the sheafhood, base-change and realization assertions of this node;
all are listed in `lean.declarations`, with sources and complete proof docstrings.
The main docstring carries all twelve steps of the reviewed split.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Arbitrary base scheme X | `(X : Scheme.{u})`, with explicit `universe u` and `autoImplicit false` |
| Small étale site | `X.Etale`, `Scheme.Etale.forget X`, `X.smallEtaleTopology` |
| Small pro-étale site | `X.ProEt`, `Scheme.ProEt.forget X`, `Scheme.ProEt.topology X` |
| Published comparison ν_X | The actual functors and counit of `Scheme.proEtaleSiteComparison X` |
| Algebraic space over X | The recorded `AlgebraicSpace X`, not a new presentation-based substitute |
| Étale over X means every representable étale chart has étale composite | `IsEtaleOver E := ∀ (T : Over X) (a : yoneda.obj T ⟶ E.obj.obj), IsEtale a → Etale T.hom` |
| All morphisms over X between such spaces | `EtaleSpaces X` is the full subcategory defined by that predicate |
| h_E^et(V) = Hom_X(V,E) | `(Scheme.Etale.forget X).op ⋙ E.obj.obj.obj` in `etaleRealizationFunctor` |
| h_E^proet(U) = Hom_X(U,E) | The same fppf functor of points restricted by `ProEt.forget`, then `uliftFunctor` |
| Equivalence for the displayed functor | `(etaleRealizationFunctor X).IsEquivalence`, including full faithfulness and essential surjectivity |
| Canonical natural comparison is an isomorphism | `IsIso (etaleProEtaleRealizationComparison X)`; the named map is built from the counit, associator and unitor, so its adjoint is the identity |
| Every weakly étale U → X | The unrestricted `∀ (U : Scheme.{u}) (f : U ⟶ X) (hf : WeaklyEtale f)` |
| E_U = E ×_X U | `realizationBaseChangeSheaf f E` is actual precomposition with `Over.map f`; on T → U its value is Hom_X(T,E), the fibre-product universal-property formula |
| E_U algebraic and étale over U | `realizationBaseChange_isEtaleSpace`, used only for the proof fields in `realizationBaseChange`; no data is selected from an existence theorem |
| Restriction to U_proet | `proEtaleRealizationRestrictionFunctor f hf`, the existing continuous localization functor `MorphismProperty.Over.map ⊤ hf` |
| Restricted Hom identification | `proEtaleRealizationRestriction f hf E` is `Iso.refl`, since the displayed functors of points coincide definitionally |
| Restricted comparison with ν_U^* h_EU^et | `restrictedRealizationComparison f hf E` is the comparison over U followed by that fibre-product identification; the last conjunct asserts it is an isomorphism |

The explicit sizes preserve the allowed cases. Algebraic spaces in the recorded
interface have `Type u` section sets, and the equivalence concerns *all* sheaves in
`Type u`, without any finite, constructible, separated, quasi-compact or locally
constant hypothesis. The published site adjunction acts on `Type (u + 1)`. Its input
is therefore the canonical lift of the same Hom sheaf. This is witnessed by the
data definition `largeEtaleRealizationLiftIso`, whose value is `Iso.refl`. No equality
between distinct site/coefficient universes is assumed. The universe `u` is arbitrary,
so it may be chosen after the ambient enlargement in the node's size convention.
For size bookkeeping in a fixed universe one can take a small affine étale generating
basis and all its sections; its coproduct is an allowed scheme. The construction does
not require a coproduct indexed by the entire large type of all schemes in the site.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Etale` and `Morphisms.Etale`:
  `Scheme.smallEtaleTopology`, `Scheme.Etale`, `Scheme.Etale.forget`, and `Etale`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale` and `Morphisms.WeaklyEtale`:
  `Scheme.ProEt`, `Scheme.ProEt.topology`, `Scheme.ProEt.forget`, and `WeaklyEtale`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, whose left adjoint is the actual Kan extension
  followed by sheafification. Its inclusion and continuous localization interfaces
  come from `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`, and
  `IsAlgebraicSpace`, including the existing representable diagonal/atlas conditions.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections and universal property (used in the source interpretation of the
  base-change sheaf). `Over.map` and its continuous sheaf pushforward implement that
  universal-property formula without a new arbitrary comparison arrow.
- `def-weil-size-convention` is the recorded metatheoretic convention, not a Lean
  data object; the universe binders and canonical lift implement it here.

All stated project proof dependencies are imported by their recorded module,
including the source-cover descent, relation quotient, fibre-product, final-open
subsheaf, fpqc-cover and weakly-étale stability inputs. Dependencies without Lean
statements are named in the proof docstring and remain stage-3 prerequisites.

Edge cases checked: empty X and empty U; the initial sheaf/empty algebraic space;
the final sheaf/X; arbitrary constant sets, including infinite ones; non-separated
étale spaces; identity and composite weakly étale restrictions; empty charts and
empty covering families. There is no nonemptiness or finiteness binder. The
restriction identification is the identity on sections even for identity maps,
so it does not replace an identity case by an arbitrary lift or choice.

Searches were run through the prescribed wrapper and recorded in `searches.jsonl`:

- LeanFinder: `equivalence between sheaves on the small etale site and etale
  algebraic spaces; proetale inverse image represented by the same algebraic space`.
  Eight hits, on site forgetful functors and transport of sheaves; none is this theorem.
- Loogle: `AlgebraicGeometry.Scheme.Etale, CategoryTheory.Functor.IsEquivalence`.
  Two hits state equivalence with the affine étale site, not algebraic-space realization.
- Mathlib grep: `AlgebraicSpace|etale.*space|space.*etale` in `AlgebraicGeometry`.
  Three files, concerning scheme morphisms and the affine étale site, no matching theorem.
- LeanSearch: `sheaves on the small etale site equivalence etale algebraic spaces`.
  Eight hits, including generic sheaf equivalences and scheme étale definitions,
  no algebraic-space realization.
- Direct source grep for the exact node id in `WeilConjectures` returned no hit.
  Direct source/project/Mathlib searches for the new names returned no pre-existing
  declaration. The shared project's algebraic-space definition was read in full.
  The existing `IsChartwiseEtale` describes maps between two spaces over a fixed
  base; the item's `IsEtaleOver` directly spells out its own stated chartwise
  condition over the scheme, without choosing a terminal algebraic-space model.

I read [Stacks 0GF6](https://stacks.math.columbia.edu/tag/0GF6), including the
set-theoretic footnote, and Bhatt--Scholze's
[paper](https://arxiv.org/pdf/1309.1198), Lemmas 5.1.1 and 5.4.1.
The latter does not assert algebraic-space realization by itself: the node's
atlas coequalizer and Yoneda argument supply that passage. There is no statement
correction or `STATEMENT-DISPUTED` claim.

## Second reading by NP

The dispatcher forbids starting another agent; this section records a separate
second pass by this worker, not a claim that another worker independently reviewed
the file. The maintainer's independent review remains necessary.

I reopened the node and module and checked each row above. In particular, the
full subcategory uses all scheme charts, not just a chosen atlas; the functor
acts on actual Hom sets; its equivalence is not replaced by existence of some
unrelated equivalent category; the natural comparison is the specific counit;
and the base-change sheaf is the actual pullback functor of points. The proof
fields used to bundle these data are the only uses of the two supporting `sorry`
theorems. I added the explicit canonical universe-lift identity to make the
relation between the small and large étale Hom functors inspectable in Lean.
All universes and variables are bound, and there are no `let` binders, file-local
notations, private copies, extra geometric assumptions or hidden data sorries.

## Repair validation (2026-10-18)

The returned immutable head `3e44a1ef65f5` failed while importing
`Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint` from the module
`Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover`: the compiled dependency
was reported as non-module. The retained packet supplies both current published
module sources as preliminary overlay inputs. This forces the prescribed compiler
to rebuild that import chain before checking the realization module. Both preliminary
sources and their node records are byte-for-byte identical to the current shared
repository; they introduce no mathematical or declaration change and are omitted
from the resulting delivery commit as unchanged files. No compiler script or shared
source was edited.

As instructed for this retry, I first read the retained report and ran
`deliver2.py NP lem-a1-etale-sheaf-algebraic-space-realization --no-push` on the
saved packet, without restarting its construction. All three modules compiled
separately through the authorized wrapper, and server preflight returned
`OK (dry run): commit 54c6309ea0 passes the preflight and compiles; nothing pushed`.
This supersedes the earlier failed-cache diagnosis. The concrete repair is retaining
the two dependency-first overlay inputs, not rebasing and re-pushing an unchanged
single-file compilation packet.

I compared every packet node with the current shared node: only the item's `lean`
record differs. I reread the item's statement, its saved module, the recorded
algebraic-space definition and comparison adjunction. The full subcategory predicate,
actual Hom functors, canonical counit, explicit base-change functor of points, and
identity restriction retain the clause correspondence and edge cases in the worker
report. Every postponed proof is a named theorem with its source and proof docstring;
all data definitions are explicit. No Lean statement or definition needed alteration
for this import-artifact repair.

## Dependency modules

`lem-sbc-flat-composite-fibre-dimension-at-point`, module
`Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint`: its previously cached
compiled interface was unusable from a `module` importer. The saved source is the
current published module, stating pointwise fibre-dimension additivity for a flat
first morphism with both morphisms locally of finite type. It is supplied unchanged
as a preliminary compilation input; its node record is unchanged.

`lem-trf-etale-descent-through-source-cover`, module
`Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover`: its import of that compiled
interface caused the returned error. Rebuilding it after the preceding module
preserves exactly the theorem that a morphism is étale when its composite with a
surjective étale source cover is étale, without extra hypotheses. Its source and node
record are unchanged preliminary inputs. Neither dependency is a new declaration or
a node-record repair in the final commit.

## Returned-head retry validation (2026-10-18)

This retry addresses the same non-module import diagnostic on immutable head
`1ed2f1bee697`. Following the dispatcher's saved-packet instruction, I read this
report and ran the prescribed dry run before making any change. It passed:
`OK (dry run): commit a1427f5ab3 passes the preflight and compiles; nothing pushed`.
The wrapper separately compiled the retained flat-composite fibre-dimension source,
the source-cover descent source, and the realization source in dependency order.
The reported import failure did not recur. Both dependency sources remain unchanged
preliminary compilation inputs, rather than new mathematical interfaces.

I retained the saved Lean work as instructed after a successful dry run. For the
required self-check I reopened the item, all statement-dependency node records,
the algebraic-space and site-comparison definitions, the two preliminary modules,
and the Mathlib scheme, etale-site, pro-etale-site, etale, weakly-etale and pullback
interfaces. The saved node differs from the current shared node only in `lean`;
both preliminary nodes and sources are identical to their current shared versions.
The recorded main signature matches the file verbatim, all lines meet the width
limit, and all three postponed proofs are named theorems. The clause correspondence
and empty/identity/universe cases described above still apply. This retry changes
only this validation report and does not restart or replace the retained statement.

## Immutable-head c119aed8a125 retry (2026-10-18)

I first inspected the retained report and ran the prescribed dry run on the saved
packet, before editing it. The returned non-module import diagnostic did not recur:
`OK (dry run): commit 389978f3dd passes the preflight and compiles; nothing pushed`.
The wrapper checked all three supplied files separately in dependency order,
including both dependency overlays and the realization module. Per the dispatcher's
instruction for a passing saved packet, I retain these Lean sources.

The self-check reopened the main node and module, every statement-dependency node
record, the algebraic-space and comparison-adjunction sources, both preliminary
dependency sources, and the Mathlib scheme, site, morphism and pullback interfaces.
The displayed Hom functors, full subcategory, canonical counit, explicit base change,
and identity restriction still give the clause correspondence in the worker report.
The empty-base, empty-space, identity-restriction and universe-lift cases remain
included. The recorded signature matches the file verbatim, every delivered line
meets the width limit, and the JSON layout is unchanged. Only the item's `lean`
record differs from the current shared node; both preliminary dependency nodes
and sources remain byte-for-byte identical to their shared versions. No mathematical
statement, definition, shared source, or launcher tool was changed in this retry.

## Immutable-head 675714e5fc54 return and self-check (2026-10-18)

I first ran the saved packet unchanged, as the repair brief requires. The dry run
passed: `OK (dry run): commit dc2c707c16 passes the preflight and compiles; nothing
pushed`. All three input modules were checked separately by the prescribed wrapper.
The staged delivery contains exactly the realization module, its node record, and
this report. The two unchanged dependency modules are compilation inputs only.

The return's sole diagnostic is an `--apply-fixes` path error for
`EtaleDescentThroughSourceCover.lean`. That module already exists on the base, and
is byte-for-byte unchanged in this packet, as is
`FlatCompositeFibreDimensionAtPoint.lean`. Neither belongs in a reviewer's directory
of NEW modules under `lean/Sheaf/`. No fix to either published dependency is requested
by this delivery. Omit these unchanged compilation inputs from `--apply-fixes`;
use the prescribed basename form for an actual correction to a delivered module.
The saved packet itself passes delivery preflight without reviewer fixes.

Per the instruction for a passing saved packet, I retain the Lean sources. I reopened
the item statement and module, every statement-dependency record, the algebraic-space
and comparison-adjunction declarations, both compilation inputs, and the relevant
Mathlib interfaces. The clause correspondence above still holds, including empty
objects, arbitrary section sets, identity restrictions, and the canonical universe
lift. The recorded signature matches verbatim, every variable and universe is bound,
and no line exceeds 100 characters. Only the item's `lean` field differs from the
current shared node; both dependency records are unchanged. This report explicitly
resolves the returned path diagnostic without introducing a new dependency module
or altering any mathematical statement.
