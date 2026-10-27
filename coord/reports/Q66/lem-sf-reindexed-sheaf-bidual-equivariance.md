# Stage-1 report: lem-sf-reindexed-sheaf-bidual-equivariance

## Files written

- `dag/nodes/sec-six-functors/lem-sf-reindexed-sheaf-bidual-equivariance.json`: statement, split; five elementary proof steps, no Mathlib match for the complete assertion.
- `citations.json`: one verified verbatim statement quotation for each step/node citation.
- `report.md`: this report. `searches.jsonl` is the unmodified log produced by the required search command.

New nodes: 0. New Mathlib leaves: 0. No Lean was written or compiled. Only the item sandbox was written.

## Attachments

None. Searched the project source by the blueprint tag, reindexing, bidual and evaluation concepts, and the double-dual declaration name. `AlgebraicGeometry.WeilSheaf.nonempty_iso_dual_dual`, `lean/WeilConjectures/WeilSheaf/VerdierDual.lean:229`, has a `sorry` at line 231 and assumes lisseness. `WeilSheaf.dualStr` and `dual` at Dual.lean:216 and :228 construct the specialized dual, without proving this arbitrary-ringed-site bidual equivariance. Other project evaluations concern the specialized Weil or adic categories and do not state every clause here. None qualifies as an attachment.

## WANTED

None. The proof is an agent-written calculation from definitions, using the available Stacks internal-Hom text and the upstream contragredient convention, rather than attributing the general assertion to a missing reference.

## Findings and changes

The statement is retained verbatim. It was not false or missing a hypothesis. The previously empty proof is replaced by the explicit slice change of indices, the evaluation map for arbitrary modules, the inverses of the contragredient structures, the equivariance formula, and the inverse fixed-pair equation. In particular the proof does not infer sheaf-Hom compatibility for an arbitrary inverse image and does not treat internal Hom on a slice as merely the dual of the module of sections on its terminal object.

Read the chapter record and the inherited unit `sk-prop-sf-rf-shriek-preservation`, as well as the current main-20261015 `lem-sf-hom-finite-projective` statement/proof. The helper's inherited unit concerns exceptional inverse image; this helper supplies the underived equivariance needed by its parent, without replacing a unit step. The computed blueprint ancestor is null because of the pre-existing parent provenance break. The existing detailed `blueprint.from` is retained, and the split report explains the recorded intended ancestor and the finite-projective biduality connection. Whole-blueprint searches for bidual, contragredient and reindexing found no equivalent statement. In particular `cor-coef-verdier-weil-equivariance` concerns bounded constructible derived objects on geometric schemes and does not give this arbitrary site/module assertion; the scheme-isomorphism resolution node likewise has narrower coefficients and does not state the fixed-pair equation.

All six new Mathlib queries in `searches.jsonl` were actually run through msearch.py and their hits read. They include LeanSearch, Loogle, LeanFinder with a second phrasing, and two source grep queries. `Module.Dual.eval_naturality` was read in Mathlib/LinearAlgebra/Dual/Defs.lean around line 177 and `Dual.eval` at line 80: these are for ordinary modules over one fixed commutative semiring. They do not supply the slice-site comparison or the semilinear coefficient identification. The second semantic search returns rigid dual-pair tensor-Hom statements, requiring dualizability; this assertion allows arbitrary modules. The other semantic hits concern free sheaves and section/unit maps. Thus the complete item is not a one-line specialization. Earlier imported search records were retained as provenance; the appended records are the exact new logged queries.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs to distinguish. Existing definition nodes are used directly. In particular no clause of the item was renamed as a new lemma, and the locally-free biduality sibling was not used to impose an unwarranted freeness assumption or introduce a cycle through the parent.

## Review by Q66

I read Stacks `literature/stacks-project/sites-modules.tex`, Tag 04TT (`section-internal-hom`, including the localized map definition, restriction and scalar rules, and evaluation), Tag 03EM (`lemma-internal-hom`), and Tag 0E8H (`lemma-internal-hom-restriction`). I also read the upstream dual construction at Dual.lean:205–235 and the blueprint finite-projective proof. The blueprint proves the underlying finite-free/retract assertion; it does not itself contain this semilinear argument, so the proof origin is explicitly agent-written. There are no new-node sources to audit.

Step 1 cites `def-pur-localized-ringed-site` for its precise slice objects, coverings and relocalization, and `def-pur-sheaf-hom` for the localized Hom formula. Both statements were opened and read. Applying tau and its chosen inverse gives inverse component formulas, and preservation of covering sieves is assumed in both directions. This is a direct reindexing of those definitions, not an uncited base-change theorem. The generic localization definition is the sole off-unit tool declared in `split_report.tool_uses`.

Step 2 cites `def-pur-sheaf-hom` and `def-weil-sheaf-of-modules-category`. Their statements give pointwise scalar operations and the componentwise linearity criterion for module-sheaf maps. The step verifies additivity/linearity in the functional and in the input, and writes the restriction identity. It then substitutes tau into the same formula, checking evaluation compatibility itself. No local freeness is needed to form evaluation.

Step 3 uses those same two statements for localized linear morphisms and module actions. I checked the scalar directions: the transported action is by t=s inverse, a inverse is t-semilinear, and b is s-semilinear before transport. Both inverse identities for b are written out. Substitution of D(M), b into that exact calculation defines c and its inverse, so their isomorphism properties are not asserted by a definition citation alone. Naturality of the given a and s verifies restriction compatibility.

Step 4 uses the slice-Hom statement to test all localized components, and `def-weil-endofunctor-fixed-pair-category` for the morphism equation. For x in TM(U), the intermediate scalar really lies in TR(V), so s_V has the correct input. The displayed cancellation s_V t_V=1 gives lambda_V(a_V(x restricted to V)); naturality of a gives the final evaluation at a_U x. This proves the equation for every functional on every further slice, not just global sections.

Step 5 cites only the fixed-pair definition. I checked the direction of the inverse equation by composing on the left with h and on the right with T(h); functoriality cancels T(delta h). The resulting equation is exactly h c = a T(h). The existing underlying inverse identities then give the categorical inverse identities without a further theorem.

I checked delivery-errors B–E against the files: every citation is to an existing unmerged node and uses its statement, every non-elementary prerequisite is already encapsulated in those definitions, and the remaining work is explicitly written component and inverse substitution. Elementary marking here is justified by those formulas; it is not used to suppress a sheaf-Hom preservation theorem or a local-to-global isomorphism argument. No step exceeds 2000 characters. There are no new statement-only nodes, new data definitions, new cycles, disguised item clauses, or unsupported Stacks tags.

For edge cases I checked the zero module and zero coefficient ring (all evaluations and inverses of the given structures are the unique maps), the identity reindexing/scalar identification (the formula becomes ordinary contragredient equivariance), a one-object trivial site with a nontrivial coefficient automorphism (the s and t cancellations retain the correct scalar direction), and an arbitrary non-reflexive module. The equivariance calculation remains valid in the last case; only the explicitly conditional final step uses invertibility of delta. No invariant cover, points, rank hypothesis, finite-generation assumption or extra pullbacks were introduced.

## Unfinished work

None for this one-level split. No new obligations were needed.
