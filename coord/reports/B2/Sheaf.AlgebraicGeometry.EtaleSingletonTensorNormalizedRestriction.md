## What changed

Completed `AlgebraicGeometry.Scheme.singletonTensor_normalized_restriction` in
`Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizedRestriction`, with its signature
unchanged. Added the proof-only import `Sheaf.AlgebraicGeometry.EtaleTensorSections`.
The proof follows the existing node: evaluate both normalized pure tensors, apply
semilinearity and composition of restrictions, identify retained projections by
`Pi.lift_π`, and remove the inserted unit using `Fin.prod_univ_succAbove`.
Proved private helpers evaluate semilinearity and restriction composition. Each
restriction map used in the calculation is represented by `pinnedValue`: its
witness theorem `exists_equal` is fully proved and states equality to the original
map, so its data is completely determined. `seal_eq` proves that equality. This
prevents the kernel from unfolding the large normalized adjunction maps during
pointwise composition. It changes no public definition or signature. Local irreducibility avoids expensive tensor-pullback comparisons. The node's proof and proof origin
now describe this implementation; the dependencies and mathematical route stay
as before.

Validation after H10 repair: the corrected module compiled without warnings through
`lcompile.py` in 9.5 seconds against the published build. A separate sandbox
compilation wrote the corrected module's artifacts (29.0 seconds), then compiled
its unchanged direct importer
`Sheaf.AlgebraicGeometry.EtaleSingletonTensorCechNormalizedCoface` against those
artifacts in 6.3 seconds, without warnings. The importer copy is byte-identical
to the repository source and stays under scratchpad, outside the delivery.
The command-change flag is documented in
`coord/changes/normalized-restriction-proof-scopes.md`. No adapted module is needed.
The corrected delivery dry run printed OK: compile, axiom probe, and preflight
passed. Nothing was pushed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.singletonTensor_normalized_restriction`
(node `lem-sc-singleton-tensor-normalized-restriction`). No holes added or left in
this delivery. The private helpers `restriction_smul`, `exists_equal`, `seal_eq`, `comp_sealed`,
`comp_over_pinned_apply`, and `smul_pinned` are fully proved. The private definition
`pinnedValue` uses only the proved equality witness theorem.
This is a proof, not a decomposition into new statements. Existing dependencies
remain subject to their own proof status.

## No longer needed

None. No imports removed, no nodes or modules pruned. Both existing proof
dependencies are used: the normalization definition and restriction functoriality.
No Čech coface identification, tensor generation, or comparison injectivity is needed
by this node, as its existing statement and proof already specify.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox attempt used a broad `simp` and did not close the goal.
No mathematical defect was found in the statement or its DAG plan. Semilinearity
is currently an equality of additive maps intertwining multiplication, rather than
a pointwise equation; the private proved helper evaluates that equality. Direct
pointwise restriction composition triggered a kernel timeout even without the
product objects; using maps fixed by a proved equality avoids that reduction.
The proof is valid in degree zero, for either omission, and for zero modules or
empty schemes: the product calculation uses no nonemptiness or cancellation.
Searches found no complete replacement theorem. The Stacks sources 03DR
(equation the project server) and 03P2 were read online; local literature source files are
absent from this clone.

The first dry run required a change record for the local proof options and
attributes. After adding that record, the tool printed OK and deferred the missing
second-reader section as expected. The independent second reading below was
subsequently added. Reviewer H10 identified a downstream timeout from the two
local instance-attribute blocks. The repair deletes exactly those blocks and
updates the change record; the corrected module and unchanged importer now
compile without warnings.

## Earlier second reading (a previous round; superseded)

1. **Public interface: PASS.** Independently diffed the delivered Lean module
   against the repository version and compared the complete existing theorem
   signature byte for byte: identical. The public import and theorem docstring
   are unchanged. The sole new import, `EtaleTensorSections`, is proof-only.
   All new declarations are private, and every reducibility attribute
   is local to the existing section. The conservative command-change record
   explains these elaboration settings; no downstream adaptation is necessary.
2. **Proof and data: PASS.** The original independent reading compiled the file
   with `lcompile.py` (5.7 seconds, no warnings). After H10, repair validation
   recompiled the corrected module (9.5 seconds against the published build;
   29.0 seconds when emitting local artifacts) and its unchanged direct importer
   against those artifacts (6.3 seconds), all without warnings. The original
   independent reading compiled a scratch copy containing
   `#print axioms AlgebraicGeometry.Scheme.singletonTensor_normalized_restriction`:
   exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Scanned the delivered source: no remaining `sorry` or forbidden declaration.
   Read every helper: `restriction_smul` evaluates the multiplication-map
   equation; `comp_sealed` transports restriction composition; the over-U helper
   uses `h.w` in the correct direction. `exists_equal` is proved by the original
   value and reflexivity, and `seal_eq` fixes the chosen value to that original
   value. Thus `pinnedValue` contains neither an unproved witness nor arbitrary
   undetermined data. The final equality chain transports both normalization
   equations through these proved equalities.
3. **Split statements and edge cases: PASS.** No statements are split off and no
   holes are added. Checked the scalar argument at n = 0: the two choices of j
   insert one before or after the single original scalar, giving the same
   retained factor. The general argument uses finite-product decomposition,
   preservation of one, and projection composition; it requires no cancellation,
   nonzero coefficient, nonempty scheme, or affine hypothesis. Zero sections and
   empty schemes therefore introduce no missing case.
4. **Route, searches, imports, pruning: PASS.** Read the normalization predicates
   and restriction semilinearity/composition declarations. The proof uses hf and
   hf-prime directly, then `Pi.lift_π`, `map_prod`, and
   `Fin.prod_univ_succAbove`; it needs no coface theorem or comparison injectivity.
   Independently searched the library using insertNth/succAbove and restriction
   terminology, and queried LeanFinder for semilinear restriction of products
   along omitted projections and Loogle for the finite-product decomposition.
   No complete replacement was found; Loogle confirms the existing product lemma
   already used here. The two direct imports support respectively the public
   signature and the proof. Both old proof dependencies remain used, so the
   existing No longer needed list (none) is complete. Read
   `dag/units/sk-prop-h2.json`: no realized statement or step is bypassed or
   changed by this restriction calculation.
5. **DAG and report: PASS.** Independently diffed the node: only `proof` and
   `proof_origin` change. The proof description matches the evaluated
   normalization, scalar-product calculation, over-U restriction composition,
   and private equality transport actually written in Lean. `proof_deps` still
   names precisely normalization and restriction functoriality. No new node or
   statement-change record is required. The report accounts by declaration name
   for the one hole closed and zero holes added.

The original second reading changed only this report. This H10 repair then
removed the two instance-attribute blocks exactly as requested and updated these
validation notes; the mathematical proof and DAG remain unchanged. No downstream
adaptation is necessary. The delivered theorem is fully proved with the three
permitted axioms, not merely reduced to new holes.


## Second reading by B2

1. **Unchanged interface: PASS.** Read and diffed the delivered module against
   this repository. Independently compared the complete existing theorem signature
   byte for byte, including its letI, universes, all hypotheses and both evaluated
   sections: identical. Its docstring and public import are unchanged. The added
   EtaleTensorSections import is proof-only; all helpers are private. The two
   options are inside the noncomputable section and the three irreducibility
   attributes explicitly say local. The H10 instance-attribute blocks are absent.
   Read the proof-scope change record; no public object is altered.
2. **Proof, axioms and construction: PASS.** Compiled the actual delivered file
   through lcompile.py without errors or warnings (7.5 seconds). A freshly written
   scratch copy of this exact source, with #print axioms for
   AlgebraicGeometry.Scheme.singletonTensor_normalized_restriction, compiled
   successfully and reported exactly propext, Classical.choice and Quot.sound.
   The delivered source contains no sorry or forbidden declaration or option.
   Read every helper: restriction_smul evaluates the supplied multiplication-map
   equality; comp_sealed transports the proved restriction composition equation;
   comp_over_pinned_apply uses the over-U triangle and evaluates composition in
   the correct contravariant order. exists_equal is proved by the original value
   and reflexivity. Thus pinnedValue chooses a value determined by equality from
   a proved theorem, and seal_eq proves that equality. No arbitrary witness or
   unproved construction enters the calculation.
3. **Split statements and edge cases: PASS.** No new public statements or nodes,
   no split-off holes. The private statements are elementary equality transports
   and evaluations, not restatements of the item. In degree zero, j has the two
   possible values in Fin 2 and succAbove retains the unique original scalar;
   insertNth puts one in the other place. Fin.prod_univ_succAbove handles both.
   No step cancels a scalar or requires a nonzero module, a nonempty scheme, or
   affine objects, so zero scalars, zero sections and empty schemes are covered.
4. **Shortest route, imports and pruning: PASS.** Read both imported modules,
   the normalization predicate and the semilinearity/composition declarations.
   hf and hf-prime supply exactly the two evaluated pure-section equations.
   Pi.lift_π identifies retained projections; map_prod and
   Fin.prod_univ_succAbove identify the scalar products, and restriction
   composition identifies the coefficient. Independently searched the tensor
   modules with insertNth/succAbove and restriction terminology. A new Loogle
   query confirmed the finite-product lemma already used; a LeanFinder query
   about pullback products and inserted units returned no replacement geometric
   theorem. Both imports are needed for signature or proof. Both original
   proof_deps remain used; No longer needed = none is complete. Read
   dag/units/sk-prop-h2.json: its realized statement/step lists are empty, and
   this below-unit restriction argument changes no unit route.
5. **DAG agreement: PASS.** Parsed and compared the node files independently:
   only proof and proof_origin differ. The unchanged statement matches each
   hypothesis and the evaluated restriction conclusion of the Lean theorem.
   The two proof_deps identify exactly normalization and the functorial tensor
   restrictions used here; the implementation narrative correctly accounts for
   the private equality wrapper and scalar calculation. No new node fields or
   additional change records are needed. The report names one hole closed,
   singletonTensor_normalized_restriction, and zero added or remaining holes.

This second reading changed only report.md, adding this current independent
review. The Lean proof, node and scope change record required no repair.

Fresh downstream validation for this reading also passed: lcompile.py --all on
scratchpad/current-second-reading emitted this exact module's local artifacts
in 23.0 seconds, then compiled the byte-identical repository direct importer
EtaleSingletonTensorCechNormalizedCoface against them in 6.0 seconds. Neither
compilation produced a warning. These validation copies are outside delivery.
