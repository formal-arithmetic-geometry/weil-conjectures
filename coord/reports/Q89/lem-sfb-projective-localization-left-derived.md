# Q89 stage-1 report: lem-sfb-projective-localization-left-derived

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-projective-localization-left-derived.json`: split, statement unchanged; five steps, one new generic Mathlib leaf and the existing right-Kan uniqueness leaf.
- `dag/nodes/sec-six-functors-basics/lem-sfb-pointwise-right-kan-from-limits.json`: statement, Mathlib leaf. Constructs a right Kan extension from only the individual comma-diagram limits, with its specified counit. No projective-object assertion is moved to this node.
- `citations.json`: one verbatim supporting statement excerpt for every step/node citation.

## Attachments

None. Searched the live `lean/WeilConjectures/` by exact blueprint tag, item id, projective/localization and derived-functor terminology. No declaration states the item. The existing resolving-class theorem concerns triangulated homotopy categories, not these arbitrary categories. The upstream search gave no attachment either. No Lean file was written and no compiler, Lake or build tool was run.

## WANTED

None. Stacks `derived.tex`, `dga.tex` and the Mathlib sources used are available locally. The categorical generalization is explicitly agent-written; it is not attributed verbatim to Stacks.

## Audit of the imported item and blueprint

The imported statement is correct and is unchanged. The incoming proof was empty. Its reference to Stacks Tag 06XN is a comparison, not a direct application: 06XN is in the triangulated multiplicative-system setting, while this item permits arbitrary categories, arbitrary F and arrows q whose Q-images are invertible without requiring q in W. I read 06XN (`lemma-find-existence-computes`), 09LS (`lemma-derived-bc`) and 09KY (`lemma-hom-derived`), including the property-(P) computation in the proof of 09LS. The Hom bijection is precisely the stronger categorical hypothesis that makes the present elementary comma calculation possible. The item's localization universal property is more than the proof needs; essential surjectivity and (i),(ii) suffice, which is harmless.

Read the chapter and unit records and the latest blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3). This split supplies only the supporting categorical computation in the inherited effectivity prerequisite chain; it does not change that route or the unit/chapter. The item's inherited `blueprint.from.node` is null. `tools/blueprint_refs.py ancestor lem-sfb-projective-localization-left-derived` confirms that a new node's ancestor is None: the `created.item` chain ends at `Sheaf.SixFunctors.CtfStabilityDirectImages`, a Lean module name rather than a DAG id. I preserved that inherited result and its detailed place, with the item prepended to the new node's `via`. Blueprint-wide searches for `projective localization left derived`, `right Kan`, `pointwise`, `06XN`, `initial object`, `Kan extension` and `comma` found no blueprint statement identical to the item or the new generic lemma. Thus `same_as` remains [].

## Not duplicates

lem-sfb-pointwise-right-kan-from-limits vs lem-trf-small-pointwise-right-kan-adjunction: the existing node assumes all small limits in H and constructs an adjunction for every functor F; the new leaf requires only the comma-diagram limits for this F. H here is arbitrary and cannot be assumed complete. The existing node therefore does not apply.

lem-sfb-pointwise-right-kan-from-limits vs lem-pur-total-left-derived-localization: that node requires Q to be a localization and states existence of a universal pair; the new leaf applies to arbitrary Q and explicitly states the comma-limit object formula and the identity-indexed counit needed for computation. The former statement does not supply that formula.

lem-sfb-pointwise-right-kan-from-limits vs lem-sfb-right-kan-extension-unique-iso: the existing node compares two universal pairs already given; the new leaf constructs one from pointwise limits. I reuse the existing node for uniqueness.

No new Stacks-tag pair arises: the new node's actual source is Mathlib's generic theorem. Whole-DAG searches by the generic declaration names, right-Kan wording and comma/initial wording were read; infinity-category nodes concern a different categorical setting. `lem-trf-essential-pro-initial-evaluation` requires a cofiltered pro-object witness, not just the concrete limiting cones here, and is not used.

## Review by Q89

I checked B through E of delivery-errors.md against the actual files and sources, including the repeated historical checklist. There is exactly one new node, with an independently introduced C,D,H,Q,F, the comma category, cones, limiting condition, functors, natural transformations, universes and the universal bijection defined in its statement. It has empty proof and proof_deps and status mathlib. Its four current searches (LeanFinder, Loogle, LeanSearch and the directory grep) are copied from searches.jsonl as run; I read their returned declarations in Pointwise.lean:56-61,709-764 and Basic.lean:77-115. The earlier grep specifying a single file returned malformed file/line columns, so I ran a directory grep which gives the actual 709,733,749,758 lines. I did not treat that malformed output as evidence for a line number. The failed unqualified Loogle query is recorded as unavailable, and the corrected fully qualified search succeeded. Inherited item searches are retained. The entire item is not a one-line specialization of these results: its comma-limit construction and component-invertibility calculation are necessary and appear in its own steps.

Step 1 uses only the new node's definition of the comma category and the item's hypotheses. With u:Y→QX and q:P→X, a=(Qq)^{-1}u has the correct direction Y→QP; a comma arrow to (Z,b) lifts b a^{-1}:QP→QZ. Hypothesis (ii) has source P, exactly the source needed. This is a few-line direct definition check, so I marked it elementary rather than creating an initiality lemma.

Step 2 uses the comma diagram and limit definition in that node, not a theorem hidden in its proof. Initial arrows i_j satisfy f i_j=i_j' by uniqueness, so their images are a cone. A cone's component at j0 is its unique factor through it, since i_j0=1. This explicitly proves all comma-diagram limits without a completeness or small-index assumption on H. It is elementary and not a separate node.

Step 3 uses the new leaf's actual statement: existence of the functor, universal bijection and identity-indexed counit under exactly these individual limit hypotheses. The statement gives each assertion used. The new node's Mathlib match has one declaration per clause with the lines I read. Since it is a Mathlib leaf there is no off-route theorem to declare.

Step 4 uses that same identity-indexed counit formula, and redoes initiality for (P,1) using only (ii). I checked the two inverse identities: v_j0 t=1 by the limiting-cone factorization, and v_j t v_j0=T(i_j)v_j0=v_j by cone naturality, whence t v_j0=1 by limit uniqueness. All objects and domains agree. This proves the particular chosen pair's components are invertible without assuming full faithfulness of Q on all objects.

Step 5 uses the exact statement of existing `lem-sfb-right-kan-extension-unique-iso`, which I opened in full. Both pairs have its universal property for every G, so v:LF≅L0 satisfies epsilon=e0(vQ), in the correct orientation. Thus epsilon_P is invertible. The final equation is precisely epsilon's naturality and the inverses' naturality follows by multiplying that equation. The full subcategory contributes no extra arrows or assumptions. This ensures the claim is for EVERY universal pair, not only the constructed one. Each citation in citations.json is a verbatim substring of the statement being used; no proof-only construction is borrowed.

Small cases checked: C=D empty (unique empty functor and all assertions vacuous), terminal categories with P nonempty, Q=id (then (ii) holds for any chosen P and (i) says every object is isomorphic to P), a terminal localization of a category with an initial object (P that initial object, yielding the constant derived value F(P)), and P empty (then (i) forces C empty and essential surjectivity forces D empty). A noncomplete H causes no issue because every required limit is explicitly an evaluation at an initial comma object. No additive, abelian, triangulated, calculus-of-fractions or W-membership hypothesis was introduced. I checked that no step exceeds 2000 characters, the dependency union is exact, and there is no new backward reference or possible cycle. All elementary arguments remain steps; no new node is a clause of the item. Source names contain no forbidden SGA route.

## Unfinished work

None in the split. The required dry run and delivery follow this report; their outputs determine the final delivery status.
