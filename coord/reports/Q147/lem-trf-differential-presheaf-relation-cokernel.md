# Worker report: lem-trf-differential-presheaf-relation-cokernel

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-differential-presheaf-relation-cokernel.json`: statement, split into six steps; Mathlib search found ingredients but no declaration of the entire stated relation-map presentation and its sheafification.
- `citations.json`: verbatim statement extracts for all seven step/node citations.
- `report.md`: this report. The required search command produced `searches.jsonl`.

No new nodes and no new Mathlib leaves. The proof reuses four existing Mathlib leaves (free modules, ring differentials, sectionwise module-presheaf colimits, and module sheafification on a general site). The statement and its five statement dependencies are unchanged.

## Attachments

None. Searched the project Lean source by the item tag and by differential relations, differential construction, and sheafified cokernels. The existing scheme differential declarations in `WeilConjectures/AlgebraicGeometry/Modules/Differentials.lean` and the use of `DifferentialsConstruction` in `TangentSpace.lean` do not state the general presheaf-ring three-relation cokernel theorem. A partial ingredient is not an attachment.

## WANTED

None. All mathematical sources used are available locally.

## Findings and changes

The item was an unsplit statement-only child of `lem-trf-sheafified-module-differentials-cokernel`; the sandbox had no earlier node or report. There was no released repair note. The statement is faithful to Stacks 08TP. I retained its module-presheaf definition because its ring is only a presheaf; the existing definition `def-weil-presheaf-modules-sheafification` assumes a sheaf of rings, so citing that definition for a general presheaf ring would be a hypothesis error. The existing general-site theorem `lem-pc-sites-module-sheafification-interface` explicitly allows a presheaf ring and provides the exact scalar-extension adjunction needed here.

Rather than cite exactness on the open site of a scheme, I wrote the cokernel factorization directly from this adjunction. This is the explicit right-exactness argument behind the last sentence of 08TP. No additional exactness theorem or hidden sheaf-gluing assertion is needed. The final section formula follows from naturality of the actual sheafification unit.

The latest blueprint was read at `literature/blueprint/latest/blueprint/sec-trace-formula/`, including the chapter, unit `sk-i-curve-zero`, and `lem-trf-local-term-locality` statement/proof. This is supporting ring/sheaf input inherited through the parent chain; the contracting-correspondence route is unchanged. Whole-blueprint searches for differentials, sheafification and cokernels found no blueprint node stating this general relation-map presentation. Existing historical item searches remain in the node; five searches actually run by Q147 were appended. Both semantic phrasings and the Loogle/grep/LeanSearch hits were read. `DifferentialsConstruction.relativeDifferentials'` gives the differential presheaf; `SheafOfModules.presentationOfIsCokernelFree` requires the cokernel hypothesis rather than establishing this map's cokernel. These are not matches for the whole item.

## Not duplicates

No new nodes were created. The existing `def-weil-pbc-kahler-differentials` already states the ring quotient presentation and universal property; `lem-weil-pbc-presheaf-modules-colimits-sectionwise` states the general presheaf colimit result; `lem-pc-sites-module-sheafification-interface` states the required general-site module action and factorization. These are reused, not restated as children. The parent differential-sheafification theorem depends on this item and is not cited back.

## Review by Q147

I read Stacks `sites-modules.tex`, Tag 08TP (`lemma-differentials-sheafify`), its displayed relation map and sectionwise-cokernel proof, and Tag 03CY (`lemma-sheafification-presheaf-modules`) with its following adjunction formula. I also read `algebra.tex`, Tag 07BK (`definition-differentials`) and the construction immediately preceding it, and Tag 00RO (`lemma-universal-omega`) and proof. No new-node source needs review because there are no new nodes. Tags and labels were checked against `stacks-project/tags/tags`.

In step 1, the cited free-module statement says every element has a unique finite basis expansion. This gives additive semilinear restriction on sums. I explicitly checked all three restricted relations, including naturality of the base-ring map for the third relation; thus no naturality theorem is being assumed. This step is elementary.

In step 2, I read the whole ring-differentials statement: it gives the universal property for every module. The target module is P(V), restricted to B(U) along B(U) to B(V). The indicated map is an A(U)-derivation because the ring restrictions preserve operations and phi is natural. This checks the actual hypotheses needed to construct the restriction map. Uniqueness gives identity and composition, and evaluation on free generators gives naturality of p.

In step 3, that same ring-differentials node explicitly gives the quotient by precisely the three families at issue. The image of r_U equals their span by finite basis expansion. The cited presheaf-colimit statement explicitly permits a presheaf ring and gives the induced semilinear restrictions and colimit property. I apply it only to the finite category presenting the coequalizer of r and zero; it is small in the given value universe. Thus the quotient is the presheaf cokernel, not merely an objectwise list of modules.

In step 4, the interface node explicitly states both the B^# action on abelian sheafification and the unique factorization for B-module presheaf maps into B^#-module sheaves after restricting scalars. I checked the general-site and presheaf-ring hypotheses, not just the topological-space specialization in the similarly named `lem-pc-presheaf-module-sheafification-ring`. The full interface statement is quoted in the citation file for this step.

In step 5, the only external input is that same unique factorization. The argument starts with an arbitrary B^#-linear a killing r^#, pulls back to a presheaf map killing r, factors through the cokernel proved in step 3, and factors again through sheafification. The two uniqueness statements prove both the equation and uniqueness of the desired map. I made zero preservation explicit through factorization uniqueness; functoriality alone would not imply it for an arbitrary functor. This avoids importing any unquoted exactness lemma.

Step 6 uses functorial factorization from the interface to identify p^# eta_F with eta_P p, then evaluates on [b]. This is elementary evaluation, and proves the specified formula for every object and section.

For small cases, I checked A=B with the identity map: the base-ring relations include every basis generator, so P=0 and the sheafified cokernel is zero. For B=0 the free B-modules and P vanish. For a discrete one-object site the result reduces to the ring quotient presentation. Empty covering families cause no difficulty: sheafification may collapse values, but the adjunction proof remains valid and does not assume objectwise injectivity of its unit. No flatness, enough points, ring-sheaf hypothesis on B, or injectivity/surjectivity of phi is used.

Against delivery-errors B--E: all statements remain self-contained, no new proof-bearing unsplit node or duplicate is introduced, all cited statements were opened and their used clauses quoted, and no off-route theorem or cyclic ancestor is used. Every non-elementary step cites the actual general statement supplying its input; the elementary steps are the displayed finite-basis and evaluation calculations. No proof step exceeds 2000 characters. I corrected the potential zero-preservation shortcut before delivery. No source or statement dispute was found.

## Unfinished work

None in the authorized stage-1 scope. No Lean was written and no compiler, Lake, library build, local DAG checker or local preflight was run.
