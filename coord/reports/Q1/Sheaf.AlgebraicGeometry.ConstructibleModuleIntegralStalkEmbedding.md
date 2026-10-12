## What changed

Completed the earlier sandbox reduction of
`AlgebraicGeometry.Etale.exists_integral_lowerStar_stalk_injective` without changing its
signature. Its two proof imports are
`Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`.

The proof extends a generic isomorphism by adjunction along g and the inverse unit, checks
that pulling back this extension recovers the isomorphism using the triangle identity,
and takes its adjoint along nu. Naturality of the existing module-valued stalk comparison
shows the stalk of the first extension is invertible. The stalk of the final map has an
invertible composite, hence is monic and therefore injective. This categorical and stalk
argument is entirely proved in Lean.

The new geometric-data theorem supplies only Y, nu, K, g, finite M, the invertible generic
unit, a generic isomorphism and lifts of geometric points. It supplies neither a map from
F nor any stalk injectivity assertion, so it is strictly the geometric portion of the
argument, rather than a restatement of the item. Added its DAG node, updated the original
node's proof fields, and expanded its proof docstring to explain transport from the
canonical generic inclusion used by the existing normal-constant theorem.

Read Stacks Tag 09Z6, label lemma-constructible-maps-into-constant, in the locally available
Stacks source, especially the normalization paragraph, the two adjunctions, and its stalk
square. The route remains the constructible/finite-pushforward route in unit sk-thm-p1;
this item is not itself one of that unit's fixed realized steps.

## Proved and sorry left

Proved the sole original sorry:
`AlgebraicGeometry.Etale.exists_integral_lowerStar_stalk_injective`
(node `lem-weil-pbc-constructible-module-integral-stalk-embedding`).

One new public theorem remains sorry:
`AlgebraicGeometry.Etale.exists_constructible_module_normalized_generic_data`
(node `lem-weil-pbc-constructible-module-normalized-generic-data`, module
`Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData`).
It has a source, a complete proof in its docstring, and four corresponding DAG proof
steps. Its remaining work is the finite-value constructibility pullback bridge, finite
separable trivialization, normalization, transport of the generic unit isomorphism, and
lifting each geometric point by IsAlgClosed.lift. The existing field-trivialization and
normalization declarations are the intended inputs for the next worker.

Both sandbox modules compiled together in import order with lcompile.py. The original
module has no sorry; the remaining geometric theorem is intentionally a named obligation.
No definitions, existing theorem signatures or target statements were changed.

Edge cases checked mathematically: an empty X has no x, so imposes no existence demand;
the zero sheaf allows the zero finite module; no nonzero-module hypothesis is required.
For a closed or generic x the same normalization construction applies. Normalization
need only be integral, and is not assumed finite or Noetherian. Lifts are chosen separately
for each algebraically closed Omega, as required by the quantifier order.

## No longer needed

No original import was removed. Both added proof imports are used.

The original route's specialized germ nodes are unnecessary for this proof, including its
new geometric input:

- `lem-weil-pbc-inverse-image-stalk-germ`
  (`Sheaf.Paper.InverseImageStalkGerm`);
- `lem-weil-pbc-counit-stalk-germ-restriction`
  (`WeilConjectures.SixFunctors.Finite.Stalk`);
- `lem-weil-pbc-inverse-image-module-adjunction`
  (`Sheaf.AlgebraicGeometry.EtaleInverseImageModuleAdjunction`).

The first two are replaced by the existing natural, module-valued
`upperStarCompSheafFiberIso`. The third is replaced by the already defined adjunction
with coefficient category ModuleCat. These are claims about this route only; other
users can still need these modules.

The finite separable trivialization, normalization, constant-sheaf pullback, inverse-image
composition, finite-value comparison and normal-constant generic nodes remain needed
inside the new geometric obligation. They have been moved to its proof dependencies,
not pruned. No other original dependencies are claimed globally unnecessary.

For completeness, the exact old-to-new direct `proof_deps` removal list is:

- `prop-constructible-pullback`: moved to the geometric obligation.
- `def-weil-pbc-etale-constructible-sheaf`: moved to that obligation's proof;
  retained in the existing statement dependencies.
- `lem-weil-pbc-constructible-field-finite-separable-constant`: moved to the obligation.
- `lem-weil-pbc-inverse-image-composition`: moved to the obligation.
- `lem-weil-pbc-finite-locally-constant-module-values`: moved to the obligation.
- `lem-weil-pbc-normalization-in-residue-field-extension`: moved to the obligation.
- `lem-weil-pbc-normal-constant-generic`: moved to the obligation.
- `lemma-constructible-pullback-constant`: moved to the obligation.
- `def-weil-geometric-point`: moved to the obligation's proof and retained in statement
  dependencies; the proved stalk argument uses the lifts it supplies.
- `def-weil-pbc-constant-sheaf`: retained in statement dependencies of both nodes;
  no separate constant-sheaf construction is needed in the categorical reduction.
- `def-weil-pbc-direct-image`: retained in statement dependencies of both nodes;
  adjunction is supplied by the retained inverse-image node.
- `lem-weil-pbc-inverse-image-module-adjunction`: superseded by the existing adjunction.
- `lem-weil-pbc-inverse-image-stalk-germ`: superseded by the existing stalk comparison.
- `lem-weil-pbc-counit-stalk-germ-restriction`: superseded by comparison naturality.

These are direct-edge removals, not claims that their statement imports or every use by
other modules can be removed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt already contained a compiling categorical proof but had no
node for its new theorem and no report. Those missing delivery records are now supplied.
The existing normal-constant theorem takes the canonical Spec of the generic stalk,
whereas normalization provides a general g with generic image and invertible residue
field map. The new obligation's proof explicitly explains the necessary source-isomorphism
transport instead of silently treating those morphisms as definitionally equal.

The blueprint ancestor helper returns None for this item because the historical
created.item chain contains module names. The new node records the same actual blueprint
ancestor as the existing Noetherian finite-pushforward node:
`lemma-weil-pbc-h1-constructible-representation`, step 4, through its 09Z7/09Z6 embedding
input. The unit's fixed realized statements and steps were not changed.

Mathlib search logs from the prior attempt were checked: LeanFinder returned integral
structure-sheaf injectivity results, not this module-sheaf construction; Loogle returned
Adjunction.homEquiv tools; grep returned general injectivity tools. A fresh LeanSearch
query for generic trivialization and normalization failed with Internal Server Error and
is recorded as unavailable. Source-library searches found no exact generic-data theorem.
A whole-blueprint search for normalization and constant returned no equivalent statement.

## New nodes

`lem-weil-pbc-constructible-module-normalized-generic-data` in
`dag/nodes/sec-proper-base-change/`: the geometric setup preceding the two adjunctions in
Stacks 09Z6, transferred to module sheaves as directed by its proof of (3). It has one
new module, one public named sorry, finite-valued constructibility hypotheses identical
to the item's, and no map or injectivity conclusion. Three kinds of actual Mathlib
search are recorded (including unavailable LeanSearch), along with the existing
geometric proof dependencies. No change record is needed because no existing definition
or statement changed.

## Second reading by Q1

1. **Unchanged interface: pass.** Diffed the existing module against the repository.
   The only Lean changes are the two plain proof imports and replacement of the original
   `sorry`; the existing theorem signature and docstring are byte for byte unchanged.
   No definition, target, or other existing declaration is changed, and no change record
   is needed. The new module has one new statement, recorded verbatim in its node.
2. **Proof and trust: pass with the recorded open obligation.** Compiled both modules
   in import order through `lcompile.py`: no errors or warnings. Inspected the entire
   adjunction construction, both naturality identities and `mono_of_mono_fac` step.
   A scratch-copy `#print axioms` for both declarations showed exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. There is exactly one direct `sorry`,
   the public named geometric-data theorem; no definitions or forbidden declarations
   occur in the delivery. The scratch copy was removed.
3. **Split-off statement: pass.** Read the full Stacks 09Z6 normalization paragraph
   and 09Z5 in the local Stacks source copy, and the actual field-trivialization,
   normalization, normal-constant and composition interfaces. The statement supplies
   geometric data only; the original map and stalk injectivity are genuinely proved
   separately. Its docstring explains every required clause, including transport from
   the canonical generic stalk inclusion and extension of each residue-field map.
   Checked the empty scheme, zero module (including the zero coefficient ring), a
   field base, and closed versus generic x. No finiteness or Noetherianity of Y is
   assumed. Fresh LeanFinder search for finite-etale trivialization found unrelated
   condensed/module results; Loogle on `IsAlgClosed.lift` confirmed the lifting input;
   Mathlib grep on normalization and this lift found general tools, not this theorem.
   Searched both library roots for generic units and residue-field normalization: the
   existing inputs do not already assert this combined data statement. The proved
   `isConstructibleEtaleModuleSheaf_iff` is an available shortcut for the first bridge.
   Closing all the geometric construction and source-isomorphism transport is beyond
   a few-minute repair, so the named obligation remains.
4. **Route and pruning: pass after report repair.** The categorical route follows
   09Z6 and uses the already proved module-valued stalk comparison, avoiding the two
   specialized germ statements and the additional module-adjunction bridge. Both
   added imports are proof-only and used; the original public imports supply the
   unchanged signature. Reviewed `dag/units/sk-thm-p1.json`: this item is not a fixed
   realized step, and the unit's route and realized fields remain untouched. Expanded
   `No longer needed` to enumerate every removed old direct proof dependency, including
   dependencies moved into the new geometric obligation and retained statement inputs.
5. **DAG agreement: pass.** Existing node changes are exactly `proof`, `proof_deps`,
   and `proof_origin`. Each new proof describes the Lean argument, and each dependency
   list equals the union of its proof steps' uses. The new node has the required source,
   statement inputs, proof steps, searches, creation record, blueprint ancestry, chapter,
   unit and verbatim Lean record. Added the second reader's independent search evidence.

Second reading changed only the report (complete dependency-removal accounting and this
review) and the new node's search evidence. The compiling Lean proofs were left intact.
