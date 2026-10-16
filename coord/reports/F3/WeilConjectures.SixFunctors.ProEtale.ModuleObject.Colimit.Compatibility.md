## What changed

Retired the disputed all-unbounded coefficient-change instance
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper`
and its anonymous all-unbounded Omega shriek example. The existing justification used an ambient
exceptional right adjoint that the library does not provide. No counterexample to this exact
condensed instance is claimed, and its former assertion is not reported as proved.

Added the distinctly named bounded-below component theorem
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE`.
Its proof combines the existing unit/copower mate criterion, exact faithful restriction,
a scalar-basis decomposition, and the fully proved bounded-below copower-continuity theorem.
The latter uses the existing continuity theorem for the exact internal condensed categories;
no equivalence with ordinary ring-sheaf modules is assumed.

Adapted `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` by extracting each constructible
input's lower bound and applying the new component theorem. Its entire statement, visibility,
and all comparison definitions remain unchanged. No target or target definition changes.
The module is unclaimed at the downstream audit. The change record lists all 50 downstream
modules and their holders. The copy of CoefficientPushCopowerCriterion is unchanged and is
present only to compile the newly landed dependency locally.

Validation: each new proof and the item module compile with `lcompile.py`. The adapted
consumer compiles in 31.6 seconds. Compiling the original consumer against the changed
item fails at its two ambient `IsIso (derivedPushHom ... f)` requests (original lines 106
and 111); the adaptation replaces exactly these requests with the private bounded-input
restriction lemma and reuses it for f and f'. That private lemma also keeps conversion of
the full-subcategory comparison explicit, without repeatedly unfolding the large functors.

Repair of reviewer X-514ed, H10 (returned head 514ede3d3): refactored only the added
bounded-comparison implementation in the item module. A new private wrapper of the abstract copower helper supplies the indexing families explicitly
to `Sigma.desc`, eliminating the `show` wrappers on both unit maps in the concrete application.
The original helper's signature and proof are unchanged. Derived restriction-reflection is proved once for an exact reflecting functor in a private
helper in this same file. The chosen adjunction and pullback definitions are locally irreducible;
the mate proof unfolds `derivedPushHom` explicitly. The final application elaborates its four
hypotheses separately. No file or proof obligation was moved to another module, the 60-second
limit was not changed, and all retained signatures and the bounded theorem statement are
unchanged. No new imports or nodes were needed for this repair. The two new modules and the
adapted consumer are unchanged from the returned delivery. Single-file validation of the repaired
item with the signature-preserving wrapper completed without warnings in 40.2 seconds. The
repository declaration-table check against the returned sandbox reports no changed retained
signature, no public addition or removal, and no new `sorry` in this retry. The final complete delivery
passed `lcompile.py --all`: scalar-basis 39.1 seconds, bounded copowers 21.4, the unchanged
criterion 1.1, the repaired item 46.6, and the adapted consumer 58.6. Each file passed the
unchanged 60-second limit without warnings; the transcript is in
`scratchpad/repair-H10-all-final.log`. The prior second reading below records
the returned version, not an independent reading of this performance repair.

The current second reader found an additional consumer timeout and made `derivedPushHom`
locally irreducible there. This prevents expansion of the ambient mate during the
full-subcategory component transfer; the consumer compiled in 9.5 seconds afterward.
All statements, definitions, imports, and proof arguments are unchanged by this adjustment.

## Proved and sorry left

Original direct holes: 1. Original holes proved with their old signatures: 0. The disputed
ambient instance is retired as unused by the repaired target route, not counted as proved.
The item module has 0 direct `sorry` after this repair. H10 changes no hole count: 0 closed and
0 added relative to the returned sandbox; the retained scalar-basis module still has its 1 hole.

Fully proved new declarations:

- `AlgebraicGeometry.ProEtale.CondensedRing.condensedSubfield_bounded_copower_comparison`
  (`lem-weil-pbc-condensed-subfield-bounded-copowers`): no new holes. Its private finite-sum,
  filtered-colimit, and homology comparison helpers are also fully proved.
- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE`
  (`lem-weil-pbc-condensed-qbar-bounded-push`), from the named scalar-basis input and existing
  continuity. The private derived restriction-reflection and central-unit/copower arguments
  contain no holes.
- The adapted `constructibleToQbar_baseChange_compatibility` proof has no direct hole.

Exactly 1 added direct hole remains:
`AlgebraicGeometry.ProEtale.CondensedRing.condensedQbar_derived_scalar_basis`
(`lem-weil-pbc-condensed-qbar-derived-scalar-basis`). It is in its own module and has a complete
proof in words. What still needs Lean: construct the finite-support continuous-coordinate
coproduct decomposition for an algebraic E-basis of Omega; transport it along p_Z^*; identify
the tensor decomposition with the extension adjunction unit; descend this exact decomposition
and scalar multiplication to the derived categories; transpose scalar compatibility along
pullback/direct image. The source finite-basis proof supplies the finite analogue, but does
not itself supply the infinite copower statement. No direct-image preservation of infinite
coproducts is required in this scalar lemma. No data definition chooses an arbitrary witness
from this unproved existence theorem: the consumer destructs it only within a proof.

This is a decomposition of the needed bounded comparison together with retirement of an
unneeded stronger API, not a proof of the original all-unbounded assertion. Direct hole
arithmetic is one retired and one added; no positive net hole reduction is claimed.

## No longer needed

The target route no longer needs the disputed all-unbounded instance
`isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper`, its anonymous Omega shriek
example, or an ambient proper exceptional right adjoint. All finite-extension results and the
finite-extension shriek example are retained.

The parent still uses `lem-weil-pbc-proper-base-change`, discharged by Mathlib pullback
stability; that dependency is retained. Its coefficient comparison now uses the explicit
bounded-push node. No blueprint unit, realized statement, or proof step is removed, and no
whole existing module becomes unreachable in this delivery.

The ordinary ring-sheaf bounded-coproduct module
`Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts` and a bridge from that model are not
needed: `Sheaf.Paper.CondensedQcqsPushforwardContinuity` already states continuity in the exact
internal condensed-module categories. None of these unused bridge obligations is imported
or added as a node. No original import is removed from the item module; the two new proof
imports and the derived-coproduct helper import are non-public. TStructure is public because
the new component statement uses its lower-bound predicate.

## Where the brief, the DAG or earlier work was wrong

The original hole had no primary DAG attachment of its own. Its actual parent is the
condensed Qbar base-change compatibility node, whose statement asks only for bounded
constructible inputs. The old module documentation and parent proof claimed an ambient
proper exceptional right adjoint. The supplied source constructs such an adjoint only on
bounded constructible categories with extra geometric hypotheses. The previous dispute
comment correctly identified this gap; the analogous ordinary-sheaf counterexample is not
silently treated as a counterexample for the exact internal condensed model.

The repaired route keeps the parent's complete statement and the blueprint unit route.
The new bounded theorem has a distinct name so that retirement of the ambient assertion
cannot be confused with proving it or silently replacing its signature.

## Forced adaptations

`Sheaf.Paper.CondensedQbarBaseChangeCompatibility` was unclaimed at the audit. Its original
lines 106 and 111 fail to synthesize the retired ambient `IsIso (derivedPushHom ... f)` and
`IsIso (derivedPushHom ... f')` instances against the changed dependency. The changed lines are the proof import at 11, the private restriction lemma starting at 60,
and the two componentwise uses starting at 121. These adaptations compile (31.6 seconds). The private lemma extracts
the bound from `K.property.1.1` and transfers the new component through
`ObjectProperty.isIso_hom_iff`; the rest of the Cartesian-square proof is unchanged.

## New nodes

`lem-weil-pbc-condensed-qbar-derived-scalar-basis`: the one remaining scalar-basis obligation,
independent of geometric continuity. Its statement quantifies over a chosen copower of each
individual input, avoiding inference of an entire family of coproduct structures.

`lem-weil-pbc-condensed-subfield-bounded-copowers`: fully proved from condensed qcqs filtered
continuity using finite subcoproducts and homology. Arbitrary and empty indexing types are
included, and all summands have the stated common lower bound.

`lem-weil-pbc-condensed-qbar-bounded-push`: the complete mate/reflection combination at a
bounded-below input. The existing parent node's proof and dependencies are updated accordingly.

Change record: `coord/changes/condensed-qbar-bounded-push.md`.

## Earlier second reading (a previous round; superseded)

1. **Interfaces: PASS.** Independently diffed all existing delivered modules against the
   read-only repository and compared declaration tables with `stage3_delivery.diff_module`.
   Every retained signature and visibility is unchanged. The only removed named declaration
   is the explicitly recorded disputed all-unbounded instance; its anonymous Omega shriek
   example is also explicitly retired. Neither is counted as proved. The two retained public
   imports in the item still supply its coefficient statements; the added TStructure public
   import supplies the new lower-bound predicate. All added proof dependencies are plain
   imports. No target or data definition changes. The copied copower criterion is identical
   to the repository and therefore contributes no delivery diff.

2. **Proofs and axioms: PASS with the declared scalar obligation open.** Independently
   compiled every sandbox module in dependency order using `lcompile.py --all`: no errors or
   warnings (38.5, 22.4, 1.3, 53.0, and 59.1 seconds). Read the finite-subcoproduct universal
   property, truncation transport, homology comparison cancellation, exact-restriction
   reflection, and central-scalar mate calculation. The sole direct `sorry` is the public
   named scalar-basis theorem with its docstring and node. There are no prohibited axioms,
   unsafe declarations, or holed definitions. Scratch `#print axioms` checks show that
   `condensedSubfield_bounded_copower_comparison` uses only `propext`, `Classical.choice`, and
   `Quot.sound`. The scalar-basis theorem, new bounded push theorem, and constructible
   consumer additionally use `sorryAx`, as expected from their open dependencies. Independently
   compiling the original consumer against the changed sandbox reproduces precisely the
   two missing ambient `IsIso` instances at original lines 106 and 111 (11.1 seconds).

3. **Split statement: PASS.** Read the finite-subextension coefficient construction and
   its sectionwise colimit proof. For a chosen E-basis of Omega, the compositum of E with
   a section's finite field is finite-dimensional over E. The union of the basis supports
   of a finite spanning set bounds all coordinates; coordinate restrictions are continuous
   by finite-dimensional linear algebra over Q_ell. Conversely a finite sum of continuous
   E-valued coordinates lies in the finite compositum generated by its basis vectors.
   These mutually inverse maps commute with restrictions and module actions. Tensoring,
   inverse image, and exact derived descent give the stated unit map; the global scalar
   actions commute with pushforward by adjunction. This argument includes zero inputs,
   empty schemes, and identity morphisms. The existential data is destructed only in a
   proof, never used to define an arbitrary object. The obligation is strictly algebraic
   and assumes no pushforward continuity; it does not restate the original item. Independent
   msearch queries used different terms: leanfinder searched restriction of scalars,
   regular algebraic-closure modules, Hamel bases, and finite-subextension continuous
   functions (eight field-theory hits, no match); loogle searched preservation of the
   finite-subcoproduct diagram (no match); grep found finite-dimensional continuity API.
   Repository searches found only finite-free basis arguments and the existing stronger
   all-diagrams preservation helper. Neither closes this scalar construction in a few
   minutes. No further hole was added.

4. **Route and pruning: PASS.** The copower proof uses the already proved continuity
   theorem in the exact internal condensed module categories, not an ordinary ring-sheaf
   model. The finite-subcoproduct helper needs preservation of only this bounded diagram;
   the existing upstream helper requires preservation of every diagram of that shape.
   The empty indexing case is covered because its finite-subset category is nonempty and
   filtered, and additive functors preserve its finite zero coproduct. All old parent
   `proof_deps` are retained and used, with the new bounded node added; there is no omitted
   old dependency to list as pruned. Checked `dag/units/sk-thm-properbasechange.json`:
   none of its realized statement or step nodes is bypassed or changed. No whole module
   is pruned. The recorded retirement is an interface repair and decomposition, not a
   positive net hole reduction.

5. **DAG agreement: PASS.** Checked all four delivered nodes against the proof terms.
   Each `proof_deps` equals the union of the proof steps' `uses`; every cited node exists.
   The three new nodes have the required source, origin, searches, creation, blueprint,
   chapter, unit, and Lean records; their Lean statement text occurs verbatim in the
   corresponding module. The parent statement and statement dependencies are unchanged.

**Second-reader change:** corrected the adapted consumer's stale seven-step proof docstring,
which still cited the ordinary-sheaf coproduct node. It now describes its actual three-step
proof via the new condensed bounded comparison, full-subcategory transfer, and the existing
exchange-equality theorem. No proof term, signature, definition, import, or DAG route was
changed by this second reading. Original holes proved unchanged: 0 of 1; one disputed hole
retired and one strictly separate scalar-basis hole added; no positive net reduction claimed.

## Second reading by F3

1. **Interfaces: PASS.** Diffed every delivered existing module against the shared repository.
   Independently compared raw signature slices, byte for byte, for all retained named
   declarations: no changes. The only named removal is the explicitly recorded disputed
   all-unbounded instance; its anonymous Omega shriek example is also recorded as retired.
   The constructible consumer and all target statements and definitions are unchanged.
   The copied copower criterion is byte-identical to the repository. The change record
   declares the new bounded component API, removed API, and consumer adaptation.

2. **Proofs and axioms: PASS after the consumer elaboration repair.** Read the finite-sum
   colimit argument, good-truncation transport, homology comparison cancellation, exact
   restriction reflection, and central-unit mate calculation. The first independent
   complete compile passed the repaired item in 52.5 seconds but timed out on the consumer.
   Keeping `derivedPushHom` locally irreducible there made that file compile in 9.5 seconds.
   The final `lcompile.py --all` passed without warnings: scalar basis 39.7 seconds,
   bounded copowers 21.9, unchanged criterion 1.3, item 50.1, and consumer 42.4.
   Transcript: `scratchpad/second-reading-final-all.log`. Scratch `#print axioms` checks
   passed in 1.9 seconds: bounded copowers uses only `propext`, `Classical.choice`, and
   `Quot.sound`; the scalar theorem, bounded push theorem, and consumer additionally use
   `sorryAx` from their declared open inputs. Transcript:
   `scratchpad/second-reading-final-axioms.log`. There is exactly one direct hole, the
   named public scalar-basis theorem; no holed definitions or prohibited declarations
   occur. The chosen scalar data is destructed inside a proof and defines no arbitrary object.

3. **Split statement: PASS.** The scalar-basis obligation is true for this specific
   finite-subextension-valued coefficient ring. For a section valued in F, the finite
   compositum EF has a finite E-spanning set; the union of those vectors' basis supports
   bounds every coordinate of the section. Coordinate maps on EF are continuous. Conversely,
   a finite sum of continuous E-valued coordinates lies in the finite extension generated
   by the finitely many basis vectors. These maps commute with restrictions and scalar
   actions. Tensoring and exact derived descent identify the stated unit map; the same
   global scalars commute with direct image by adjunction. Zero inputs, empty schemes,
   and identity maps cause no exception. The statement asserts no pushforward continuity
   and is strictly part of the needed argument. Fresh leanfinder searches for derived
   internal-module basis decompositions returned ordinary algebraic basis and base-change
   results only. Loogle and grep found the exact-functor and finite-subcoproduct APIs,
   with no complete replacement. A malformed initial Loogle query was rerun correctly.
   Repository searches also found the split-unit faithfulness proof, which supplies only
   a retraction, not this coproduct decomposition. The remaining construction cannot be
   closed in a few minutes from these results. Its source, word proof, and node are present.

4. **Route and pruning: PASS.** The proof uses continuity in the exact internal condensed
   module categories, then the existing copower mate criterion. The finite-subcoproduct
   helper requires preservation of one bounded diagram; the upstream shape-wide theorem
   assumes preservation of every such diagram and therefore does not replace it. Empty
   copowers are covered by the nonempty filtered finite-subset category. Every old parent
   proof dependency remains used; no omitted dependency or whole module needs pruning.
   Checked `dag/units/sk-thm-properbasechange.json`: its realized statement and steps are
   preserved. The disputed instance is retired, never counted as a proof.

5. **DAG agreement: PASS.** Read all four delivered nodes. Each `proof_deps` is the union
   of its steps' `uses`, and every cited node exists. The three new nodes carry the required
   source, searches, origin, creation, blueprint, chapter, unit, and Lean records. Their
   statements match the Lean signatures; the existing parent's normalized signature and
   natural statement are unchanged. The current repair adds no node or proof dependency.

**Changes by this reader:** one local irreducibility attribute and its explanatory comment
in the adapted consumer, plus this review and the corresponding change-record update.
Independently compiling the original consumer against the changed dependency reproduced
exactly the missing ambient instances at original lines 106 and 111 (13.0 seconds).
Original holes proved with unchanged signatures: 0 of 1. One disputed hole is retired and
one scalar-basis hole is added; no positive net reduction or whole-module pruning is claimed.
