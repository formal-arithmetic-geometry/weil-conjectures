## What changed

Replaced the original bijectivity hole by a canonical comparison proof. The statement and
existing docstring are unchanged. The proof cancels each surjective algebraic quotient
projection, identifies both completion maps on every evaluated limit projection, and expresses
the given comparison as the composite of two isomorphisms.

Added three modules. `FormalCompletionAffineSections` proves the source completion
identification for an arbitrary quasi-coherent module on any scheme. Its proved private
`quotient_sections_iso` helper reuses the actual proved `multiplication_range` and `product_qc`
declarations via a proof-only `import all`, along with the affine cokernel theorem. The inverse
limit is constructed by `adicCompletion_iso_of_stable_ranges` with c=0.
`FormalFunctionsAffinePushforwardSections` proves the formal-functions transport from
`globalSections_formal_functions`: it explicitly transports the quotient linear maps, the
completion, the diagram limit and both projection equations.
`FormalFunctionsAffineRestrictionDictionary` states the remaining finite-level geometric
identifications on the actual restricted scheme and morphism, with their quotient equation.
It asserts no completion or limit isomorphism and contains no candidate comparison kappa.

The item now imports these two proved section-comparison modules and the coherent-to-quasi-
coherent criterion as proof dependencies. No existing public import, definition, statement or
visibility changed. The only local heartbeat increase is on the new formal-functions transport;
its scalar identifications unfold two section functors and an affine chart, and it compiles
within the 60-second file limit.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.formalCompletion_pushforward_limit_app_bijective`
(node `lem-weil-pbc-formal-completion-pushforward-limit-app-bijective`).

Also proved the new declarations
`AlgebraicGeometry.formalCompletion_affine_sections`
(node `lem-weil-pbc-formal-completion-affine-sections`) and
`AlgebraicGeometry.formalFunctions_affine_pushforward_sections`
(node `lem-weil-pbc-formal-functions-affine-pushforward-sections`), and the private
`AlgebraicGeometry.quotient_sections_iso` helper. These contain no direct sorry.

Added exactly one hole:
`AlgebraicGeometry.formalFunctions_affine_restriction_dictionary`
(node `lem-weil-pbc-formal-functions-affine-restriction-dictionary`). It is the whole proof of
that named public theorem, with a source and full proof in words. No sorry remains in the item.
The delivery closes one upper hole and adds one strictly smaller finite-level transport hole;
this is a decomposition, with net hole change zero, not a fully sorry-free proof of the target.
Existing imported lemmas may themselves depend on sorry and are not claimed closed here.

All four delivered modules compile in dependency order. The dictionary was checked against the
actual restriction and affine-chart interfaces: its scheme, ideal, module and morphism are fixed
real constructions, not arbitrary existential objects. The empty affine open, zero module, zero
ideal and unit ideal give respectively zero or constant systems; no nonzero-ring hypothesis or
surjectivity of individual proper-pushforward quotient comparisons is assumed.

## No longer needed

Removed the item's direct proof-only imports
`Sheaf.AlgebraicGeometry.TheoremFormalFunctions` and
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`.
Both remain needed through the new proved section modules; neither corresponding node or
module is pruned from the transitive proof route. No landed module is claimed newly unreachable.

Removed the earlier sandbox's proposed injectivity and surjectivity modules and nodes. They were
unlanded proposals, not library dependencies, and are not counted as pruning. The independent second reading is recorded below.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt paired two new holes for injectivity and surjectivity. Each still hid almost
the entire affine formal-functions calculation, and its report called this a proof. Replaced that
split by a proof of the source quotient and inverse-limit computation, an explicit application
of the existing formal-functions theorem, and one remaining finite-level restriction dictionary.
The previous claims of second reading were removed.

The node's mathematical plan and the unit route are retained: affine quotient calculation,
degree-zero formal functions, and evaluation preserving limits. The new DAG proof steps match
the Lean and do not bypass any unit statement or realized unit step.

The literature files are not materialized in this read-only clone. Read the cited statements and
proofs directly at https://stacks.math.columbia.edu/tag/02OC and
https://stacks.math.columbia.edu/tag/088B, and the affine correspondence at Tags 01I8 and 01IC.
LeanSearch returned Internal Server Error on all three new queries, recorded as unavailable;
LeanFinder, Loogle, Mathlib grep, library rg and blueprint searches were run and recorded.
No exact existing declaration states the finite-level restriction dictionary. The proved private
restrictionQuotientIso, restrictionQuotientIso_pi and restrictionCompletionIso declarations in
TorsionControlledFormalRestriction are relevant reusable ingredients for its next worker.

## New nodes

`lem-weil-pbc-formal-completion-affine-sections` corresponds to the proved generic affine
quotient-completion identification in `Sheaf.AlgebraicGeometry.FormalCompletionAffineSections`.
It uses the existing affine ideal-product, quasi-coherent cokernel-image and stable-range nodes.

`lem-weil-pbc-formal-functions-affine-pushforward-sections` corresponds to the proved transport
in `Sheaf.AlgebraicGeometry.FormalFunctionsAffinePushforwardSections`. Its proof applies the
existing degree-zero formal-functions theorem and the new finite-level dictionary, then performs
the quotient and completion conjugations in Lean.

`lem-weil-pbc-formal-functions-affine-restriction-dictionary` is the sole new unfinished item,
in `Sheaf.AlgebraicGeometry.FormalFunctionsAffineRestrictionDictionary`. It identifies the original
section module and quotient diagram with the actual restricted proper morphism's inputs,
including the scalar actions and quotient projection equation, before taking inverse limits.
No change record is needed because no existing interface changed.

## Second reading by T1

1. Compared the delivered item with the repository using diff. Its sole existing public
   declaration, every binder, conclusion, visibility, and original docstring are byte-for-byte
   unchanged. All public imports of the item are retained; only proof imports and the proof
   body change. The other three modules are new. No definition or existing interface is changed.
2. Compiled all four modules in import order using lcompile.py: clean, respectively 9.8,
   3.6, 26.0 and 11.3 seconds. A scratch axiom probe reports only propext, Classical.choice,
   Quot.sound for formalCompletion_affine_sections; the dictionary, pushforward transport,
   and item additionally report sorryAx. There is exactly one direct sorry, the dictionary's
   entire named theorem. No delivered definition chooses data from this unfinished existence
   assertion: a and b are eliminated inside a theorem proof. Scanned all four files for the
   forbidden declarations and options; none occurs. The source quotient identifications and
   their projection equations are proved, rather than arbitrary isomorphisms assumed.
3. Read Stacks Tags 02OC (degree-zero assertion), 088B (first affine inverse-limit calculation),
   01I8 and 01IC, and the actual dictionary signature. Properness is preserved by the open
   base change and affine chart; coherence restricts locally. K and P are fixed restrictions,
   and the spectrum ideal is transported along ΓSpecIso, so the scalar convention matches
   globalSections_formal_functions. The quotient isomorphism points from restricted quotient
   sections to original pushforward sections and its equation has this same orientation.
   Empty U gives the zero section ring; F=0 gives zero modules; J=0 gives constant systems;
   J=1 gives zero quotients. None needs a nonzero ring or finite-level pushforward surjectivity.
   Searched independently with LeanFinder for open restriction section/quotient compatibility,
   Loogle for restrictFunctor (service under load), and rg in Mathlib, the upstream library,
   lean/Sheaf and dag/nodes. Read restrictAppIso and its scalar-action formulas, and the proved
   restrictionQuotientIso, restrictionQuotientIso_π and restrictionCompletionIso helpers in
   TorsionControlledFormalRestriction. They supply quotient transport but not the full scalar
   and ideal dictionary. No existing declaration closes the remaining theorem in a few lines.
   It is strictly finite-level and contains neither a completion nor a limit comparison;
   this delivery is a decomposition of one hole into one smaller hole, not net hole progress.
4. Read the proof from the item downward. hκ and the surjective algebraic mkQ determine
   each comparison; heS/heT and limit hom_ext determine the limit map. Its factorization as
   eS.inv followed by eT.hom proves bijectivity. The source theorem uses the actual proved
   affine range/cokernel results and c=0 stable ranges; the target transport actually applies
   globalSections_formal_functions and proves both transported projection equations. No
   shorter existing route was found. Checked each import against the signatures or proof.
   Both old proof dependencies remain transitively used, so no node is pruned. Read
   dag/units/sk-thm-p1.json realized: no unit statement or realized step is bypassed or changed.
5. Read all four node records against their Lean declarations. The item's proof_deps name
   the two comparisons and coherence criterion; the source comparison records range,
   cokernel and stable-range ingredients; the transport records the dictionary and formal
   functions. New nodes carry source, complete statements, creation/Lean/blueprint records
   and logged searches. Found and repaired the dictionary's second proof step: the cited
   ideal-product statement did not itself assert its affine ideal equality. Replaced that
   citation with the explicit ext_of_isAffine, ideal_comap_of_isOpenImmersion,
   ofIdealTop_ideal, isoSpec appTop, and comap_comp calculation and removed that step's
   erroneous dependency from proof_deps. The quotient step still records the proved
   restriction helpers. The mathematical statement and its Lean signature are unchanged.

Second-reading changes: repaired that DAG proof citation and its dependency union, removed
an obsolete report sentence about the missing second reading, and added this review. No Lean
proof required repair. No further holes were closed or added during this reading.
