# Q138 stage-1 delivery: lem-per-field-pullback-galois-action

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-field-pullback-galois-action.json`: statement node, now split into five proof steps; not a Mathlib leaf. Its statement and statement dependencies are unchanged.
- `citations.json`: twelve citations, one for every step/node pair, copied verbatim from the cited statements.
- `report.md`: this report.
- `searches.jsonl`: five searches actually run by the prescribed msearch command, including the second semantic phrasing. No previous sandbox split or searches existed to resume.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the complete project `lean/WeilConjectures/` for the exact blueprint tag and Galois/pullback/stalk terminology, and inspected the field-stalk modules. `AlgebraicGeometry.Scheme.etaleSheafEquivDiscreteModule` in `AlgebraicGeometry/Sites/GaloisModule.lean` compares the categories for one field; `AlgebraicGeometry.Scheme.sheafHAddEquivContinuousCohomology` in `AlgebraicGeometry/EtaleStalkContinuousCohomology.lean` compares the cohomology for one field. Neither states this extension-of-fields compatibility, nor all its clauses. The sections/invariants theorem in `FieldSectionsStalkInvariants.lean` concerns finite intermediate extensions in a fixed separable closure, with an algebraicity hypothesis on the ambient closure. It is not an attachment for arbitrary L/K and arbitrary algebraically closed Omega. No compiler or Lake command was run.

## WANTED

None. All sources used are present in the read clone.

## Findings and changes

The item was genuinely unsplit, with an empty proof, and there is no released repair note. No statement error was found. The existing statement correctly allows arbitrary field inclusions and a common algebraically closed field that need not be algebraic over either base field. The proof must therefore not specialize to an algebraic closure of K. It also must identify the actual global pullback, rather than merely give an unspecified isomorphism of invariant groups.

I read GOAL.md, the stage-1 brief, stages/1-dag.md, the worker contract, SETUP.md's three blueprint levels and tool-lemma rule, tools/README.md's field/search conventions, and delivery-errors.md B--E in full (including their repeated merged copy). The historical `coord/dag-sync.md` mentioned by the inherited brief is absent; the explicit current brief instead specifies the shared live repository and delivery overlay. I made no repository or launcher changes and did not run git there.

Read the chapter and unit DAG records and their current blueprint counterparts, and `latest/.../lem-per-artin-gabber-affine-curve.md` with its proof. The current snapshot named by COMMITS.txt is ef6f9619fdbffa59e88528fb56483d76c70258c8. This is a generic field-pullback compatibility used deep below the recorded Step 3 local-model comparison chain; it changes no chapter or unit route. The existing exact blueprint ancestry is retained. `blueprint_refs.py ancestor` confirmed the ancestor. Whole-blueprint searches for Galois, Galois action, restriction of Galois, field extension, pullback stalk, abelian sheaves, stalk-pullback and global-sections-point found no second blueprint statement of the full compatibility. The same-tag DAG search found existing general germ/action/invariant tools, which were reused.

The five new searches are recorded exactly, with the command log summaries in the item. LeanFinder returned inverse-limit Galois algebra equivalences and then Zariski stalk pullback maps. Loogle's combined sheafFiber/pullback query had no hits. The Mathlib grep returned scheme-fiber, relative-gluing and ideal-sheaf results. LeanSearch returned open restrictions, structure sheaves and equivalences of sites. These do not concern the same small etale abelian categories or give the action and unit compatibility. The older Q53 searches already present in the item were preserved as inherited evidence, not presented as fresh Q138 calls.

## Not duplicates

No new nodes were created. In particular the generic germ comparison, extension of an automorphism to Omega, and canonical global-section germ injectivity/image facts all exist. The field-extension compatibility itself remains the argument in the item's steps, rather than being moved to a new node.

## Review by Q138

I read Stacks `etale-cohomology.tex`, lemma-stalk-pullback (Tag 03Q1), its part (3) and direct colimit proof; section-galois-action-stalks (Tag 03QW), the precomposition action formula and the surjectivity of Aut(Omega/K) onto the absolute Galois group; lemma-equivalence-abelian-sheaves-point (Tag 04JQ), including the passage to abelian group objects; and lemma-global-sections-point (Tag 04JM), its formal proof and the canonical terminal-germ description in its direct proof. I checked the tags against `tags/tags`. I also read `fields.tex` lemma-galois-profinite (0BMJ) and theorem-inifinite-galois-theory (0BML) behind the existing restriction-image tool. There are no new nodes whose sources need a separate review.

Step 1 cites `lem-per-galois-restriction-image`, whose statement expressly gives a well-defined continuous restriction homomorphism for arbitrary K/L, and `def-exc-discrete-modules-category`, which defines morphisms as equivariant linear maps and continuity by open stabilizers. The stabilizer inverse-image calculation proves that restriction is a functor on the required discrete modules; no surjectivity of restriction is assumed or used. The stronger image description in that existing lemma is unused.

Step 2 cites `lem-weil-pbc-inverse-image-stalk-germ`. I checked that its statement gives an additive isomorphism, naturality in the sheaf, the formula on every base-changed pointed neighbourhood, and the terminal-section unit formula. Thus it supplies exactly the canonical map used later. `def-weil-pbc-geometric-stalks` supplies the colimit and its representatives. Bijectivity of the comparison then shows that pulled-back germs exhaust the source, without a separate claim of cofinality.

Step 3 cites `lem-exc-galois-automorphism-extension`, applied with base L and separable closure L^s. Its statement explicitly drops algebraicity of Omega, so the hypothesis of the item suffices. The same extension of tau is also a K-automorphism, restricting to r(tau) on K^s. `lem-exc-abelian-sheaves-gmodules-action` states the change-of-lift formula for every extending automorphism and arbitrary algebraically closed Omega, while `lem-exc-abelian-sheaves-gmodules` expressly says the abelian equivalence is compatible with that set-valued equivalence and the group operations. The comparison node from step 2 then gives the displayed equality on the pulled-back germs. The unchanged second coordinate p_L is justified by the automorphism fixing L. This directly proves equivariance; it does not appeal to an undocumented transport compatibility or to the proof of a cited node.

Step 4 is elementary assembly from steps 1--3 and the cited discrete-module category definition. I wrote out equivariance of the inverse and explained why naturality is the same square after restriction. These are immediate identities for equivariant additive bijections, not a hidden additional equivalence-of-categories theorem.

Step 5 cites `aux-etale-global-sections-injective` and `aux-etale-global-sections-image`. I read both statements: together they identify the canonical terminal-section germ map with the invariant subgroup, and allow an arbitrary containing algebraically closed Omega. This avoids the stronger algebraicity hypothesis of `lem-sc-etale-field-sections-invariants`. The supplied canonical equivalences have exactly the required lift-change action by step 3. The final clause of `lem-weil-pbc-inverse-image-stalk-germ` then identifies the germ of the pullback of a global section with the original germ. Hence the actual pullback is m maps to m, as claimed. All three statements are quoted in citations.json, not merely their tags or internal proofs.

The six off-unit statement tools are declared in split_report.tool_uses, with a reason for each. They are generic field-stalk or site-theoretic facts; no step of the perverse unit is replaced by another route. I checked that none of these tools, nor the restriction-image lemma, has a statement/proof dependency path back to the item. Statement dependencies were all retained: the algebraic-closure definition also defines the weaker property 'algebraically closed', so its use does not impose algebraicity.

Edge cases checked: for L=K with identical separable closures the germ formula is the identity; if G_L is trivial the result has target the underlying group M and global pullback is the inclusion of G_K-invariants; a purely inseparable field extension needs no separability assumption on L/K; for a transcendental L/K and a transcendental containing Omega the extension lemma still applies. For zero sheaves and for constant sheaves with trivial action the maps specialize to the expected identity. A non-surjective restriction homomorphism can enlarge the invariant subgroup, so the global map is only asserted to be the inclusion, exactly as in the item. No new statement, added hypothesis or weakened conclusion was introduced.

For delivery-errors B--E: there are no new statement-only obligations, duplicate nodes, fictitious searches, or Mathlib leaf claims. Every non-elementary input in each step is a cited statement and each quote is verbatim. The actual compatibility calculation stays in the item. Each proof step is below 2000 characters (526, 585, 1094, 543, 955); none hides a longer standard lemma. Only step 4 is marked elementary, with its inverse and naturality identities written out. No SGA source is used.

## Unfinished work

None within the requested one-level stage-1 split. Existing dependency nodes keep their current states and are not edited here. Required server dry-run and delivery results are recorded below when available.

## Server validation

The prescribed dry run `deliver.py Q138 lem-per-field-pullback-galois-action --no-push` exited successfully: `OK (not pushed) deliver/Q138/lem-per-field-pullback-galois-action at 2fa34ec49a6: preflight passed`. It ran the required server checks; no failure required repair. The direct-delivery brief authorizes the worker to push after this passing dry run.
