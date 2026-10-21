# Worker report: lemma-nagata-scheme-image-of-closed-immersion

## Files written

- `dag/nodes/sec-nagata-compactification/lemma-nagata-scheme-image-of-closed-immersion.json`: existing statement, now a Mathlib leaf. The exact isomorphism is `AlgebraicGeometry.IsClosedImmersion.instIsIsoSchemeToImage`; compatibility is `AlgebraicGeometry.Scheme.Hom.toImage_imageι`.
- `citations.json`: empty list, because a Mathlib leaf has no proof steps.
- `report.md`: this report. No new nodes; one Mathlib leaf (the item).

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint id, instance name, closed-immersion image factors, and the geometric formulation found no project declaration stating this item exactly. The matching declaration belongs to Mathlib, so this is a Mathlib leaf rather than an ATTACH delivery.

## Wanted literature

None.

## Corrections and observations

The imported proof had `elementary: null`, no uses, and a stale proof dependency `lemma-nagata-scheme-image-ideal-qc`. Its Mathlib match was not recorded despite naming the exact Mathlib instance. The item is already available directly in Mathlib: no split into additional lemmas is appropriate. Its statement is unchanged. I replaced the proof by an empty list and removed proof dependencies, as required for a Mathlib leaf. I retained imported metadata and its earlier logged text-search record, appending only the six searches actually run through msearch.py.

Statement dependencies now cite the existing closed-immersion definition, the canonical factor definition, and the scheme-theoretic image definition. The separate scheme-theoretic-closure definition is unused here and was removed. The source image definition has a `blueprint_update`; the current meaning is the closed subscheme cut out by the largest quasi-coherent ideal contained in the sheaf kernel, exactly Mathlib's `f.ker.subscheme`. I read and used that corrected current meaning, not the historical statement saying largest closed subscheme.

## Blueprint and duplicate search

I read the chapter and unit records and the current main-20261015 unit statement, item statement and proof. The unit uses the closed-immersion image identification when restricting an immersion to an open where it is closed. An exact Mathlib leaf implements this input without replacing the unit route. `tools/blueprint_refs.py search 'scheme-theoretic image'` searched all imported blueprint nodes, returning 23; the existing item itself is the only match for this precise isomorphism. I also searched the whole DAG for the instance name and the geometric formulation, and read the existing image/factor/interface definitions. The ancestor command returns the item itself. No new nodes were created, and `blueprint.same_as` is empty.

## Mathlib search evidence

All six appended `mathlib_searches` entries reproduce queries actually run with the required search command and appear in `searches.jsonl`. LeanFinder, Loogle and LeanSearch each return the exact instance. The first grep locates compatibility at `Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean:715`; a later directory grep locates the instance type at `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean:156`, with its instance declaration starting at line 155. A single-file grep returned line numbers misparsed as filenames; I recorded that output honestly and used the directory grep to confirm the file and line. Every search service was available. There was no absence conclusion requiring a second phrasing.

## Review by Q94

I read the current blueprint item and its complete proof under `literature/blueprint/main-20261015/blueprint/sec-nagata-compactification/sk-lem-nagata-sketch-closure/`, together with Mathlib `ClosedImmersion.lean:130–174` and `IdealSheaf/Subscheme.lean:660–718`. The instance quantifies over arbitrary schemes and a morphism with only `[IsClosedImmersion f]`, and concludes `IsIso f.toImage`. Thus it matches every hypothesis of the item without a reducedness, Noetherian, quasi-separatedness or finite-type assumption. Its anonymous generated name is confirmed by both semantic services and Loogle, and its actual source proof contains no sorry.

For the second clause, I checked the equality itself: `f.toImage ≫ f.imageι = f` at Subscheme.lean:715–718. Taking the isomorphism with hom `f.toImage` therefore gives an isomorphism over the original target, not merely an abstract isomorphism of schemes. The source and factor definitions at lines 662, 665 and 710–712 agree literally with the existing DAG definitions under their current blueprint updates. I opened the statements of `def-weil-closed-immersion`, `def-nagata-scheme-image-factor`, `def-nagata-scheme-theoretic-image`, `def-nagata-scheme-theoretic-closure` and `lemma-nagata-scheme-image-ideal-qc` before deciding the dependencies. There are no cited proof steps, so C1 and C4 create no missing statement or quote obligations; the declarations for both clauses are instead named with files and lines in `mathlib_match.how`.

For small cases, the empty closed subscheme is its own image (on an affine target its ideal is the whole ring); the identity closed immersion has zero ideal and is its own image; and a nonreduced closed subscheme Spec(A/I) has image Spec(A/I), preserving its nilpotents. No reducedness shortcut is used. These cases also confirm the direction of the canonical factor. The two-clause match avoids creating a new node restating the item, and avoids hiding an argument in a long step. No statement dispute was found. No new statement-only nodes need separate source checks, and there are no same-tag duplicate pairs to explain. This direct-delivery self-review is the review authorized by the brief; no second worker or agent was started.

## Return repair: current cited definition

The returned delivery was head `6e2273dbc56`; the return identifies a changed statement of `def-nagata-scheme-theoretic-image`, not a failed mathematical argument. I compared the retained delivered item with the current repository item: the target statement and maintainer-owned metadata agree; the sandbox owns the Mathlib-leaf conversion, its statement dependencies, search evidence, provenance and split report. I rebuilt the sandbox item from the current repository node and overlaid those permitted fields. The delivery tool fetches and packages on current `origin/sheaf-dag`; no manual git operation was run.

I re-opened every current statement dependency. `def-weil-closed-immersion` still defines a closed embedding with surjective structure-sheaf map, equivalently the affine quotient condition; Mathlib `IsClosedImmersion` has precisely that property (ClosedImmersion.lean:45). `def-nagata-scheme-image-factor` still explicitly says the factor is `Scheme.Hom.toImage g` and names `Scheme.Hom.toImage_imageι`. Its current blueprint update says the same canonical factorization. The dependency specifically returned, `def-nagata-scheme-theoretic-image`, is now a reviewed Mathlib leaf (Q92, 2026-10-21), with its statement equal to its main-20261015 update. Its relevant sentences are:

> Its *kernel ideal* $\ker(g)\subseteq\mathcal O_Y$ is the largest quasi-coherent ideal contained in the kernel of $\mathcal O_Y\to g_*\mathcal O_T$ (this kernel itself when $g$ is quasi-compact). The *scheme-theoretic image* $\operatorname{SIm}(g)$ of $g$ is the closed subscheme of $Y$ defined by $\ker(g)$.

This is the definition required here. In Basic.lean:692, `Hom.ker` is `ofIdeals` applied to the affine section kernels. At :104, `ofIdeals` is the supremum of the quasi-coherent ideal data lying in those kernels; :125 characterizes which ideal data lie below it. At Subscheme.lean:662, `Hom.image` is exactly the closed subscheme `f.ker.subscheme`. These lines validate the changed citation directly, rather than asserting that the ordinary sheaf kernel is always quasi-coherent. I also read Stacks 01R6 (morphisms, `lemma-scheme-theoretic-image`), 01R7 (`definition-scheme-theoretic-image`) and 01R8 (`lemma-quasi-compact-scheme-theoretic-image`): they use the largest quasi-coherent subideal, give the smallest closed factorization, and require quasi-compactness for the ordinary-kernel identification. The historical master detailed form said “largest closed subscheme”; the current definition corrects that, and the leaf match uses only the corrected current notion.

Revalidation by Q94: the revised definition introduces no extra hypothesis into this item, because `Hom.ker`, `Hom.image`, `Hom.toImage` and `Hom.toImage_imageι` are defined for every scheme morphism. The isomorphism instance adds exactly the item's closed-immersion hypothesis. Hence the canonical isomorphism and its equality over $Y$ are still exactly the two clauses proved by the recorded Mathlib declarations. The empty source, identity and a nonreduced quotient $\operatorname{Spec}(A/I)$ remain valid edge cases with the current definition. The correction is now explicit in `mathlib_match.how` and `split_report.summary`; it is not an unchanged re-push. There are no proof steps, no long steps, no new nodes and no step citations, so the preserved empty `citations.json` is still complete. The prior search results were read and reused: neither the item statement nor the search question changed, so no search was repeated or invented.

## Delivery validation

The first dry run rejected a null `proof_origin`, even for this Mathlib leaf. I retained the blueprint proof provenance as an agent-origin source record; the leaf still has no proof steps or proof dependencies. This fixes the reported metadata failure without changing the statement or Mathlib match.

## Unfinished work

None in the mathematical audit. The required delivery tool supplies the server-side dry run and push verification. The first repair dry run failed while creating its server baseline with Errno 28 (no space left on device), not with a DAG or mathematical diagnostic; retrying after the citation revalidation.

## Repair validation blocker

Both sequential repair dry runs exited before validation could complete because the server could not construct its temporary DAG baseline. The first reported Errno 28 at `/tmp/sheaf-dag-base-8ek47n6j/dag/nodes/sec-smooth-purity/lem-sf-reduction-flat-model.json`; the repaired retry reported the same error at `/tmp/sheaf-dag-base-i7gmvffj/dag/nodes/sec-proper-base-change/lem-weil-pbc-model-of-residue-smooth.json`. Each printed `Could not verify the DAG baseline: [Errno 28] No space left on device`. Both processes have exited; no concurrent delivery process or push was launched. The citation repair above is retained for the next retry after server storage is available. The server temporary filesystem and launcher tools were not changed.

## Repair retry: validation restored (2026-10-21)

The previous storage failure is resolved for this retry: the required sequential dry run exited successfully with `OK (not pushed)` at `594755c2f5a`. The earlier blocker paragraph records the prior attempt only; it is no longer an outstanding blocker.

I compared the retained repaired item with the current shared-repository item again. Only the permitted split-owned fields differ (status, statement dependencies, proof and its provenance/dependencies, Mathlib evidence, blueprint.same_as and split_report); the statement and all maintainer-owned metadata are unchanged. I re-read the current statements of all three statement dependencies. In particular, the reviewed Q92 image definition still says largest quasi-coherent subideal, so the citation repair saved by the previous worker remains valid. I also re-read the Q93 image-ideal statement and the Q91 closure statement: neither changes the meaning of the image used here, and neither is a proof dependency of this leaf.

I re-read the complete closed-immersion instance at ClosedImmersion.lean:155–174, the image, inclusion and factor definitions at Subscheme.lean:662, :665 and :710, and the equality at :715–718. Basic.lean:104, :125 and :692 identify the revised image definition directly. Stacks 01R6–01R8 confirm that the ordinary-kernel description requires quasi-compactness; that extra description is not used by this leaf. A fresh project-source search for the item tag, exact instance name and isomorphism of toImage found no project declaration stating the item. The retained six logged search results were read, with no invented or repeated searches. There are still no new nodes, no proof steps, no long steps, and the empty citations list remains correct. The empty, identity and nonreduced quotient checks remain valid.

The report now records the resolved tool failure; a final dry run of this exact report and retained citation repair precedes the authorized push.


## Latest return repair: def-nagata-scheme-image-factor (2026-10-21)

This repair addresses the latest landing refusal verbatim: “cited node def-nagata-scheme-image-factor: statement changed since the reviewed delivery; rebase and revalidate the citation.” The earlier repair sections concern a different return about the image definition and are retained as history. I compared the retained returned-delivery node with the current repository item: its statement and maintainer-owned metadata still agree. I reconstructed the item from the current repository record and overlaid only the retained split-owned fields. The delivery command packages this work on current server main; no manual git command was run. The initial dry run of the retained version passed at `275ebb633b3`; this repair additionally changes `mathlib_match.how`, `split_report.summary` and this report, rather than pushing unchanged content.

I read the whole current Q90 factor definition, including its repaired statement and Mathlib match. It now explicitly introduces a scheme morphism $g:T\to Y$, the image defined by the largest quasi-coherent ideal inside the sheaf kernel, and the closed inclusion $g_{\mathrm{im}}$. Its operative sentences are:

> to be `AlgebraicGeometry.Scheme.Hom.toImage g`. It satisfies $g_{\mathrm{im}}\circ g^{\mathrm{im}}=g$, namely `AlgebraicGeometry.Scheme.Hom.toImage_imageι g`.

This is exactly the factor used in the item's first clause. Subscheme.lean:710–712 defines `Hom.toImage` with source $T$ and target `g.image`; :662 defines that image as `g.ker.subscheme`; :665 defines its inclusion; and :715–718 proves `g.toImage ≫ g.imageι = g`. Basic.lean:104–105 defines `ofIdeals` by the supremum of quasi-coherent ideal data contained in the section ideals, :125–126 gives `le_ofIdeals_iff`, and :692–693 defines `Hom.ker` by those section kernels. Hence the newly explicit convention in the changed dependency identifies precisely these objects and maps, for arbitrary $g$. No extra quasi-compactness hypothesis or raw-kernel substitution enters the match.

I also re-read the current Q92 `def-nagata-scheme-theoretic-image` statement and the `def-weil-closed-immersion` statement, which are the other two statement dependencies. Q92 uses the same largest quasi-coherent subideal. The closed-immersion definition matches Mathlib's closed embedding and surjective stalk maps (ClosedImmersion.lean:43–46). The complete Mathlib instance at :155–174 assumes exactly `[IsClosedImmersion f]` and proves `IsIso f.toImage`. Taking $f=i$ gives clause one; the equality at Subscheme.lean:715 gives clause two with exactly the changed factor definition's inclusion. Thus both clauses still match directly; there is no reason to change the target statement or dependency list.

I reopened the main-20261015 item statement and complete proof and its unit statement, and read Stacks 01R6 (`lemma-scheme-theoretic-image`), 01R7 (`definition-scheme-theoretic-image`) and 01R8 (`lemma-quasi-compact-scheme-theoretic-image`) in morphisms.tex:803–865. These confirm the largest-subideal convention and that quasi-compactness is needed only to replace it with the ordinary kernel. The project-source search for the item id, generated instance name, and `IsIso` of `toImage` found no project declaration stating this item. I read the six actual records in `searches.jsonl` and reused them: the statement and search question are unchanged. No searches were invented or repeated.

Review by Q94 for this latest repair: B1–B9 still hold with no new nodes and a self-contained unchanged item. The source lines and both matching declarations are recorded in `mathlib_match`. C1–C4 create no proof-citation obligations because this is a Mathlib leaf with no steps; `citations.json` remains `[]`. There are no duplicate nodes, cycles introduced by a new dependency, off-route proof uses or long steps. D1–D5 are avoided by using the existing Mathlib leaf directly, without a restatement node. For E1–E7 I checked that the arbitrary-scheme quantifiers, closed-immersion hypothesis, image, factor direction and equality over $Y$ agree. The empty closed subscheme has unit ideal, the identity has zero ideal, and a nonreduced quotient $\operatorname{Spec}(A/I)$ retains its nilpotents as its image; all three still satisfy the repaired convention. No statement dispute or unfinished mathematical work remains. The next dry run validates these exact repaired files before the authorized push.
