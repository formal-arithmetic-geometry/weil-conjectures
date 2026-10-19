# Worker report: lem-weil-verdier-preservation-strata

## Files written

- `dag/nodes/sec-six-functors/lem-weil-verdier-preservation-strata.json`: updated the imported item to the main-20261015 statement and split its proof into five cited steps; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim quotations for every node used in every proof step.
- `report.md`: this report.

## Attachments

None. `AlgebraicGeometry.Etale.torAmplitudeIn_verdierDual` in `WeilConjectures/SixFunctors/Etale/Derived/BoundaryDuality.lean:87` has the quantitative conclusion but its proof is `sorry`. `AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual` in `Dualizing.lean:105` also has a `sorry` proof and only states qualitative preservation. Neither is a finished declaration attachment.

## WANTED:

None.

## Corrections and blueprint comparison

The repository item had the superseded sentence asserting independence from Verdier biduality and boundary exchange. The current main-20261015 blueprint omits that sentence, so it was removed. The source, order, statement, and proof origin now point to `literature/blueprint/main-20261015/.../lem-weil-verdier-preservation-strata.md` and its `.proof.md`. No conclusion or hypothesis in the current blueprint statement was otherwise changed.

The proof is a direct split of the current proof. Step 1 makes the finite smooth stratification and local projective models explicit. Step 2 uses the supplied localization triangles for the finite cone induction. Step 3 applies the ambient stratum Hom identity and composition of right adjoints to identify the stratum dualizing object. Step 4 computes the smooth-stratum amplitude and applies the direct-image vanishing and Tor-amplitude bounds. Step 5 spells out the exact tensor/internal-Hom triangle argument that assembles the interval. Every cited fact is an existing DAG node; no clause of the item was moved into a new node.

## Not duplicates

No new nodes were created. The existing `lem-sf-etale-smooth-stratified-ctf` is a neighboring-unit stratification theorem, while this item proves preservation under Verdier duality; `lem-weil-bounded-finite-tor-perfect` is a ring-level projective-model theorem, while this item globalizes it over strata. The other cited nodes state generic operations or bounds and do not duplicate the item.

## Mathlib searches

The item-level searches were run with `/home/ubuntu/weil-launcher-nt/msearch.py` and are recorded in `searches.jsonl` and the item's `mathlib_searches`: LeanFinder and LeanSearch returned only generic derived-category/T-structure declarations; Loogle reported the project identifiers as unknown; grep found no `verdierDual`, `torAmplitudeIn`, or `constructibleFiniteTor` declaration in Mathlib. No Mathlib declaration states this item or a one-line specialization.

## Unfinished work

None. No Lean source, compiler, Lake, build, or live project file was written or run.

## Review by Q28

I read the current chapter and unit records, the main-20261015 item and proof files, the imported item, and all cited DAG statements. The source declaration in `BoundaryDuality.lean` has the same quantitative interval conclusion under explicit finite-ring, invertible-exponent, separated finite-type, compactification, and dimension hypotheses, but is `sorry`; I therefore left the item as a stage-1 split rather than attaching it.

Step 1 cites `lem-sf-etale-smooth-stratified-ctf` for the finite partition, smooth locally closed strata, dimensions, finite locally constant restrictions, and local finite-projective models. It cites `lem-weil-bounded-finite-tor-perfect` for replacing each bounded finite-Tor stalk complex by a projective model in `[a,b]`, and `def-weil-site-perfect-complex` for the covering definition of site-perfectness. I checked that the field and finite coefficient hypotheses match the stratification theorem and that the empty complex and zero-dimensional strata introduce no exceptional case.

Step 2 cites the same stratification statement's displayed triangles `Rs_{r!}P_r -> F_{r-1} -> F_r -> Rs_{r!}P_r[1]`, including `F_0=K` and `F_m=0`, so the finite cone induction is an actual cited construction. `def-weil-open-closed-recollement` supplies the meaning of the open--closed factorization used for `Rs_{r!}`; it is not being used to assert an unstated preservation theorem.

Step 3 cites `lem-weil-stratum-ambient-hom`, whose statement is the natural ambient isomorphism `RHom_X(Rs_!P,M) ≅ Rs_*RHom_S(P,Rs^!M)` for arbitrary complexes. It cites `def-weil-pbc-composite-adjunction` for composing the right adjoints and hence identifying the exceptional pullback of `omega_X` with the structure-morphism dualizing object on the stratum. This step uses no biduality or constructible-preservation assumption.

Step 4 cites `thm-asd-smooth-tensor` for the locally free rank-one shift `[2e_r]`, `lem-sf-hom-finite-projective` for the tensor--internal-Hom comparison, `lem-sf-etale-direct-image-vanishing` for `UDV(s_r,A;2e_r)`, and `thm-sf-direct-image-tor-amplitude` for the resulting interval `[-b-2e_r,-a]` and bounded constructibility. I checked that each locally closed immersion is separated and finite type, that `e_r <= dim X <= d`, and that the coefficient exponent is invertible. Thus the interval is contained in `[-b-2d,-a]`.

Step 5 cites `lem-kun-derived-tensor-triangulated` for tensor exactness on the localization triangles and `lem-sf-hom-triangulated` for the contravariant internal-Hom triangles. The long exact cohomology argument preserving a common vanishing interval is elementary once those distinguished triangles are cited, and finite induction gives the item. The specialization `K=A_X` is the defining evaluation of internal Hom into `omega_X`. I checked the edge cases `K=0`, one smooth stratum, `d=0`, and empty `X`; all reduce to the same statements with zero or the shifted rank-one dualizing object. All quotes in `citations.json` were checked verbatim against the cited node statements, and `proof_deps` is the union of the step uses.


## Second reading by Q28

Statement: checked against the main-20261015 statement and all three proof paragraphs at `sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/lem-weil-verdier-preservation-strata.{md,proof.md}`, the unit and chapter records, `def-weil-finite-field-fiber`, and the finite coefficient convention in `def-weil-finite-torsion-constructibility`. The quantitative interval and preservation conclusion agree. The delivered statement now spells out the inherited field/coefficient context, the domain of K, and the ordinary etale meanings instead of relying on a pro-etale constructibility definition. These are the source's global conventions, not additional mathematical hypotheses. The current blueprint's deletion of the old boundary-exchange sentence remains correct.

Step 1: checked `lem-sf-etale-smooth-stratified-ctf` in full and its source ingredients in `etale-cohomology.tex`, labels `lemma-connected-ctf-locally-constant` (09BI), `lemma-when-ctf` (03TT), `lemma-ses-associated-to-open` (095L), `varieties.tex`, `lemma-dense-smooth-open-variety-over-perfect-field` (0B8X), and `more-algebra.tex`, `lemma-perfect` (0658). Verdict: the existing node supplies the connected pure-dimensional strata AND an actual covering with projective models in [a,b]; a ring-stalk lemma alone would not supply that covering. Retained this reduction, removed redundant ring-level and pro-etale definition citations.

Step 2: checked the displayed triangles and the formula Rs_!=j_!i_* in `lem-sf-etale-smooth-stratified-ctf`, not its proof. Verdict: valid finite reduction; removed `def-weil-open-closed-recollement`, whose statement defines pro-etale data and neither proves etale existence nor defines this stratum factorization. The replacement cites the node that states both facts.

Step 3: checked `lem-weil-stratum-ambient-hom` for arbitrary P,M on ordinary etale derived categories; `thm-nagata-compactification` for compactifiability; `thm-amb-etale-exceptional-adjoint` for ambient adjoints; `lem-amb-unbounded-compact-support-comparisons` for composition on the WHOLE unbounded category; `def-weil-pbc-composite-adjunction` against `categories.tex`, `lemma-compose-counits` (0DV0); and `det-sp-unique-right-adjoint` for identification. Also read `more-etale.tex`, `lemma-shriek-composition` (0F7J). Verdict: repaired the missing compact-support composition input, then wrote all natural Hom bijections. No constructible-preservation assumption occurs.

Step 4: checked `thm-asd-smooth-tensor` for finite coefficients with invertible exponent, Noetherian base, compactifiability, and PURE relative dimension e_r; the restriction/calculus statement `lem-weil-pbc-ringed-internal-hom-exact-restriction` against `sites-cohomology.tex`, `lemma-internal-hom` (08J9), `lemma-restriction-RHom-to-U` (08JB), `lemma-RHom-triangulated` (08JC); the K-injective model in `def-pur-derived-internal-hom`; and the precise statements of `lemma-constructible-flc-serre`, `lem-kun-flat-bounded-tor-amplitude`, and `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. Verdict: replaced the single-projective-module, six-functor-datum-dependent citation `lem-sf-hom-finite-projective` by a direct bounded-complex calculation. Exactness of Hom from a finite projective is the summand-of-finite-powers calculation; the finite filtration proves the quasi-isomorphism claim. The degree formula -i-2e_r, local finite-projective terms, constructibility, and descent of the Tor bound are explicit. The all-sheaf first assertion of `lem-sf-etale-direct-image-vanishing` applies over the stated algebraically closed field; `thm-sf-direct-image-tor-amplitude` applies to s_r and yields [-b-2e_r,-a]. The inclusion e_r<=d gives precisely the source bound. No smooth-purity route was replaced and no SGA source is cited.

Step 5: checked `lem-sf-hom-triangulated` for the displayed CONTRAVARIANT triangle, `lem-kun-derived-tensor-triangulated` for tensor exactness, and `lem-sf-derived-homology-long-exact` for the exact segment with the middle cohomology term. Checked `thm-constructible-serre` against `etale-cohomology.tex`, `lemma-constructible-abelian` (03RZ), including kernels, cokernels and extensions for finite (hence Noetherian) A. Verdict: wrote descending induction from F_m=0, preserving the interval under extensions; cited constructible closure as well as vanishing. Internal Hom from A_X is calculated termwise in the cited K-injective definition.

New nodes: none; hence no B1-B7 defect, duplicate, item-clause restatement, or unsearched new Mathlib leaf remains. All additional dependencies already exist; only this item's node and report are delivered. A dependency traversal found no path from any newly cited tool to this item. `citations.json` has one complete verbatim statement per (step,node), regenerated from the statements read; proof_deps is exactly the union of step uses.

Edge cases: K=0 gives D_XK=0; empty X gives zero strata and F_0=F_m=0; a=b=0 and e=0 give an ordinary finite-projective dual in degree zero; a term in degree t on a smooth e-dimensional stratum dualizes into degree -t-2e, agreeing with the signs. n=1 gives field coefficients; n>1 does not require the cohomology modules to be projective or finite-projective-dimensional, only the supplied complex model. Every interval calculation is independent of n. The former assertion of stability under arbitrary cones would be false: the cone of A[0]->0 is A[1], outside [0,0]; the repaired proof uses the middle object of the displayed triangle with BOTH outer objects in the common interval.

Independent Mathlib check: ran a new LeanFinder query using “internal Hom into a dualizing object” and “finite tor dimension” rather than the original project identifiers. Hits concern generic t-structures and internal projectivity of light condensed modules, not the item. Ran a source grep `Verdier|dualizing|tor.?amplitude` at the real Mathlib root; the displayed hits are references/comments and unrelated categorical dualization. An earlier second-reader grep with subdirectory `Mathlib` accidentally addressed a nonexistent nested Mathlib/Mathlib directory: its recorded zero hits are NOT used as evidence; the corrected search and result remain in searches.jsonl, and the item's recorded grep now names the valid search. The original worker's searches are otherwise retained. No Mathlib declaration states this item.

Existing-source audit: read `BoundaryDuality.lean:87` in slopmaster2. `AlgebraicGeometry.Etale.torAmplitudeIn_verdierDual` remains `sorry`; no finished attachment was claimed. No Lean, compiler, Lake, live repository, or launcher file was changed.

Changes and reasons:
- Expanded inherited conventions in the statement/stmt_deps so the etale theorem has a defined coefficient, field, ctf domain, and ambient dualizing object.
- Removed redundant ring/stalk and pro-etale data citations from the etale reduction; retained the existing theorem supplying the actual cover and triangles.
- Added unbounded compact-support composition, compactification/adjoint existence, and categorical uniqueness, with the actual natural Hom argument.
- Replaced the inapplicable single-module Hom lemma by the local bounded-projective Hom calculation and explicit restriction/flatness/constructibility inputs.
- Replaced “cones preserve the interval” by the correct reverse extension induction, adding the missing constructible Serre closure and exact cohomology statements.
- Refreshed citation evidence and the valid Mathlib source-search record. The first worker's report and `## Review by Q28` above remain intact.

The existing off-unit nodes declared in split_report.tool_uses are generic tools or the prescribed geometric/smooth-purity inputs. In particular the unit's own statements do not give unbounded compact-support composition, ringed-site restriction, or Serre closure; these are used only for their stated interfaces. The maintainer may record approved uses in the maintainer-owned top-level tool_uses; I did not edit that field.

Step 3 hypothesis follow-up: read `lem-weil-pbc-finite-type-over-noetherian` (Morphisms 01T6), `lem-weil-pbc-noetherian-open-subscheme-noetherian`, `lem-weil-pbc-qc-open-immersion-finite-type`, and the affine quotient clause of `def-weil-closed-immersion`. Added these explicit citations and the quotient-algebra calculation to justify Noetherianity and finite type of the chosen closed/open strata; separatedness follows from the immersion diagonal. Verdict: the compact-support and smooth-theorem hypotheses are now accounted for in the step itself.

Metadata clarification: `source` and `blueprint_order` of an existing node are maintainer-owned. Restored the sandbox source metadata to its base value; the delivery tool preserves these fields. The current main-20261015 source used for the proof is recorded in proof_origin, each step source, and split_report, and the inherited blueprint_update remains the authoritative current-text notice. This corrects the original report's claim that the delivery itself updates the maintainer-owned source/order fields.

Step 5 qualitative follow-up: made the choice of a finite common dimension bound explicit as the maximum of the finitely many stratum dimensions (and 0). This proves preservation for every finite-Tor K as well as the stated quantitative implication, without an additional uncited finite-dimension theorem.

Step 1 empty-interval follow-up: retained arbitrary integers a,b in the quantitative statement rather than silently imposing a<=b. Checked `lem-kun-tensor-unit`; if a>b the Tor test with A_X forces K=0, so the conclusion holds. The stratification theorem is invoked only after this case, with a<=b as it requires. This completes the zero-object edge case including reversed endpoints.
