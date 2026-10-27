# Stage-1 delivery: lem-pur-open-small-ringed-site-coherence

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-open-small-ringed-site-coherence.json: statement, split; preserved statement and seven statement dependencies, supplied six proof steps using existing nodes.
- citations.json: verbatim statements for every node cited in every step.
- searches.jsonl: searches actually performed through msearch.py; write_split.py is sandbox-only working material.

New nodes: 0. New Mathlib leaves: 0. No unit record changed: this item is not the unit's key node.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for small ringed/open site coherence, and inspected the existing localized-module implementation. No project declaration supplies both small-site identifications together with constant-coefficient normalization and all coherences. Scheme.Etale.overEquiv and overSheafEquiv already belong to lem-weil-pbc-etale-site-localization-open; localizedModule_adjunction_exact belongs to lem-pur-site-restriction-module-adjunction-exact. These component results are reused, not offered as full attachments.

## WANTED

None. The relevant sources are present as Stacks TeX. No SGA source is used.

## Corrections and scope

No statement dispute or change of hypotheses. The imported item was statement-only. Its source refers to retained old parent Steps 2--4; the assigned node contained no such proof to preserve. The present argument realizes the open-site normalization described in blueprint.from.place, along its existing parent chain to cor-pur-dualizing-object-purity. Read the current main-20261015 corollary and proof, and the fixed chapter and unit records. The purity/DNC route is untouched.

The main potential gap was treating equality on constant elements as equality of maps of constant sheaves. Step 5 instead precomposes with the entire constant-presheaf sheafification unit and uses its universal property; its displayed equality proves the required equality on all sections. Step 6 explicitly computes both scalar actions and naturality squares. Exactness is sheaf exactness, not sectionwise right exactness.

During source verification corrected the small-pro-etale definition's tag to 098K (proetale-definition-big-small-proetale); 098H is not that definition. Tags 03EH/04IY are the respective sites/ringed-sites relocalization lemmas. The ringed source omits a ring-map verification, which Steps 5--6 supply for the present constant coefficients.

## Mathlib and duplicate searches

Preserved inherited search records from the repository. Ran the exact initial semantic query again in this sandbox, plus an alternate semantic phrasing, Loogle SheafOfModules.overFunctor, the logged grep overFunctor|pushforwardContinuousSheafificationCompatibility, and LeanSearch for small-site constant-coefficient transitivity. All services returned hits. Read Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:59--89 and Mathlib/CategoryTheory/Sites/CoverLifting.lean:382--422. These give restriction, sectionwise compositor and sheafification normalization, but not the complete item. The alternate semantic results concern PresheafOfModules sheafification interfaces. Thus no full Mathlib match.

Searched the whole DAG by localization/relocalization, constant restriction, exact restriction, and relevant Stacks tags. Searched the imported blueprint with blueprint_refs.py search (ringed localiz; constant restriction; small site open; ringed-site coherence; relocalization constant). Reused the existing etale/pro-etale site-equivalence nodes, ring-presheaf localization leaf and exact module-adjunction theorem. No new node is justified. same_as remains empty: no imported blueprint node states this complete coherence assertion. Traversed statement and proof dependencies of the four substantive citations: none reaches this item, so reuse does not introduce a cycle.

## Tool use

lem-weil-proetale-weakly-etale-localization is a generic off-unit site-equivalence tool, declared in split_report.tool_uses. It gives precisely the weakly-etale localization identification used at an open subscheme; the smooth-purity unit contains no replacement for that general theorem. Other results are definitions, Mathlib leaves or already Lean-closed tools.

## Review by Q71

I read sites.tex section-localize (00XZ), definition-localize (00Y0), lemma-relocalize (03EH) and its explicit object formulas; sites-modules.tex section-localize (03DH), definition-localize-ringed-site (04IX), extension-by-zero/exactness context (03DJ) and lemma-relocalize (04IY). I also read proetale.tex definition-big-small-proetale (098K), more-morphisms.tex lemma-composition-weakly-etale (094T) and lemma-weakly-etale-permanence (0951), and morphisms.tex lemma-open-immersion-etale (02GP). Ring-valued sheafification normalization was checked against the cited node's full statement and the actual Mathlib CoverLifting unit equation. The assembled coherence proof is marked agent-origin because it combines these sources and fills the omitted verification.

Step 1 uses the size convention, the open-immersion-etale leaf and both site-localization theorem statements. The etale statement explicitly identifies the topology; the pro-etale statement explicitly includes open subschemes, arrow formulas and coverings. No finite-type, Noetherian, quasi-compactness or separatedness hypothesis is used. Work first in common bounded representatives and transport equivalences to the chosen skeleta; sectionwise identifications are understood through that transport.

Step 2 uses the definition of constant ring sheaf and the ring-presheaf sheafification-localization leaf. The latter states both an isomorphism of ring sheaves and its unit equality, so it provides more than an underlying-set comparison. Restricted constant presheaves have literally the same values and arrows. The source's coefficient universe condition holds by the common size convention.

Step 3 uses the localized ringed-site definition for values, arrows and scalar action, and the exact module-adjunction theorem for exactness. Its statement says exactness for module sheaves over a commutative ring sheaf, not merely abelian sheaves; A_T has that property. Changing a ring by an isomorphism and reindexing along inverse site equivalences have explicit inverse functors. Universal properties carry kernels and cokernels across these inverses. I did not assert that an epimorphism is surjective on every object's sections.

Step 4 uses the localized-site definition, which includes the relocalization identification. I checked objects, arrows and covering families directly; this is a routine unpacking, not a hidden additional lemma. Step 5 uses the previously established ring-unit equation and the universal-property definition of sheafification. Both candidate maps from A_W agree after its unit, as the displayed three-equality calculation shows; uniqueness gives their equality. Step 6 uses the module-restriction formula and the already proved cocycle: both actions on an arbitrary section are written out. The naturality square consists of the same component of f. Identity and associativity reduce to equal composites of identity component maps with those same scalar actions. These last three steps are elementary from the statements cited and preceding steps.

Checked delivery-errors B--E: all cited objects are introduced, each citation supplies the clause actually used, and citations.json copies its statement verbatim. No new statement-only nodes, duplicate clauses or inline hidden lemmas are introduced. The inherited statement contains ordinary TeX escapes, proof_deps is exactly the union of uses, and no non-elementary step exceeds 2000 characters (all six are under 800). I retained metadata and the original statement.

Edge cases checked: U=T gives identity restriction and coefficient comparison by unit uniqueness; W=U does the same; U or W empty gives the unique maps on the empty site's sheaves and satisfies the same unit calculation. A may be the zero ring, F the zero module, and T disconnected. The proof never assumes constants exhaust global sections, enough points, nonempty opens or nonzero coefficients. Finiteness of A is allowed but not needed for this argument. No new nodes require separate source or small-case reviews.

## Unfinished work

None in the requested stage-1 split. Formal Lean proof and compilation are outside this stage. Delivery is subject to the required server dry run and independent maintainer review.
