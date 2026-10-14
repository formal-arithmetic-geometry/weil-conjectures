## What changed

Repaired `Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionUniqueAux`
without changing any existing signature or visibility. Its proof imports the new
`Sheaf.RingTheory.PrimeLocalizationEtaleAlgebraModel`.
The new statement isolates unpointed affine étale algebra descent. The main proof constructs
the residue-field pointing using `SpecToEquivOfField`, proves the point lies over p by
applying `Spec.map` to the compatibility identity, assembles the global triple, and obtains
`Epi i` from `IsLocalization.epi` with explicit submonoid and localization data.

The three private, proved pointing helpers follow the already proved helpers in
`Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationCompatibleMapExists`; importing that
whole theorem is unnecessary. No definition or public interface was changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_component_extension_unique_aux`
(node `new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux`).
There is no remaining sorry in the item's module. The private lemmas `pointing_spec_map`,
`exists_pointing`, and `pointing_over` are fully proved.

Added one named hole:
`AlgebraicGeometry.Scheme.primeLocalization_etale_algebra_model`
(node `new-lem-sbc-prime-localization-etale-algebra-model`). This is a decomposition,
not a complete descent proof: one hole closed and one added, net zero. Unlike the rejected
split, it contains no field K, no point of Spec B, no residue-field morphisms, and no
pointing compatibility. Those parts are now proved by the caller. The localization data
identifies the actual map i, rather than an arbitrary compatible ring map.

Both delivered modules compile with `lcompile.py --all` without warnings or errors.
The repaired Epi step explicitly identifies i with its induced algebra map before
applying `IsLocalization.epi M t.B`; the final witness uses this exact proof hi.
Edge checks for the new statement: if p is maximal or minimal, the same principal
localization system works; if R is already a field one may take C=B and i=id; the zero
ring B is allowed (its spectrum is empty and localization may invert zero). R cannot
itself be the zero ring when p : Spec R is given. No domain, injectivity, maximality,
separable closure, or surjectivity of i is assumed.

## No longer needed

Relative to the rejected sandbox proof, removed the proof imports
`Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionUniqueAuxEpi` and
`Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionUniqueAuxLocalization`.
The Epi wrapper node
`new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux-epi`
is not used by this proof: Mathlib `IsLocalization.epi` provides the final step directly.
The rejected new localization module and its node
`new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux-localization`
were removed from this sandbox delivery. They repackaged the entire pointed-model
obligation. No imports are removed relative to the current repository baseline, which
has only statement imports. The second reading also removed the redundant added
proof import `Mathlib.Algebra.Category.Ring.Instances` from the item and the
redundant public import `Mathlib.RingTheory.Localization.AtPrime.Basic` from the
new model module; both are already available through its Etale import. No claim is made that the Epi wrapper is globally unreachable.
The existing compatible-model and identity-model lemmas are also not needed by this
route: they supply no localization data. The new unpointed descent obligation retains
the source's affine descent route; the unit's realized steps are empty and unchanged.

## Where the brief, the DAG or earlier work was wrong

The returned compiler error applied `component_extension_epi` without its required
submonoid M and `IsLocalization M t.B` arguments. Mere structure and pointing
compatibility does not imply Epi. This repair supplies localization data for the actual
map i and uses Mathlib directly, so it cannot leave the returned partial application.

The old localization split was stronger than the entire target, with the same global
pointed-model construction left unproved. It was not a valid reduction. The replacement
splits strictly before constructing the pointing, and all remaining pointing and Epi
steps are real Lean proofs. The prior second-reading approval is obsolete; this repair
requires a fresh independent reading. No importer adaptations are necessary because
all existing signatures and visibility remain unchanged. The unchanged immediate
importer `Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionUnique`
compiled against the repaired sandbox module without errors or warnings; its temporary
copy was removed before the delivery dry-run.

The LeanSearch service returned Internal Server Error. Its unavailable search is recorded
without a mathematical verdict; LeanFinder, Loogle, and source searches were also run.

## New nodes

`new-lem-sbc-prime-localization-etale-algebra-model` states unpointed affine étale descent
with a canonical localization identification, in
`Sheaf.RingTheory.PrimeLocalizationEtaleAlgebraModel`. It is precisely the algebra-descent
part of the parent's source argument (Stacks Tags 01ZM, 07RP, 01Z6, 00CR and 00CP).
Its docstring records the complete construction in words and its search records identify
the available generic descent, affine-stage and localization ingredients. The parent's
proof and proof dependencies now record this reduction. No change record is needed.



## Second reading by M4

1. Compared both delivered modules with the repository. The only existing public
   declaration is `etaleResidueTriples_primeLocalization_component_extension_unique_aux`;
   its complete signature is byte-for-byte identical (checked by extracting the text
   from `theorem` through `:= by`). The original public imports and visibility remain.
   The added model import is proof-only. No definition or target statement changes.
   Verdict: pass.
2. Compiled both modules with `lcompile.py --all`, without errors or warnings. A temporary
   copy with `#print axioms` showed only `propext`, `Classical.choice`, and `Quot.sound`
   for all three private pointing helpers, and additionally `sorryAx` for the main theorem
   and the new model theorem. There is exactly one delivered sorry, in the named model
   theorem, and no axiom, unsafe/opaque declaration, foreign implementation, or hollow
   definition. The temporary copy was removed. The existential model is eliminated only
   inside a proof of an existential proposition; no definition chooses arbitrary data
   from its unproved existence statement. Verdict: pass as a decomposition, not a
   complete proof of descent.
3. Read the model theorem, its docstring, its node, the existing scheme-level
   `etale_finite_data_descent`, and Stacks Tags
   [01ZM](https://stacks.math.columbia.edu/tag/01ZM),
   [07RP](https://stacks.math.columbia.edu/tag/07RP), and
   [01Z6](https://stacks.math.columbia.edu/tag/01Z6). Affine source and target supply the
   quasi-compactness and quasi-separatedness needed to upgrade the given etale map to
   finite presentation. Principal stages are qcqs and have affine transition maps;
   base-changing a descended model preserves affine transition maps, allowing 01Z6.
   The base-change isomorphism identifies B with the localization at the image of
   R minus p, for precisely the algebra structure induced by i. The statement is true
   without injectivity of i or nontriviality of B: B=0 is obtained by C=0, while for
   R a field C=B and i=id suffice. Nonmaximal p and nilpotents in R introduce no extra
   hypotheses. The new statement omits all field-point data and is strictly the
   unpointed descent part, rather than a renamed pointed target. Additional LeanFinder
   search for finite-presentation algebra descent through filtered ring colimits found
   generic factorization and finite-presentability lemmas, not this model theorem;
   Loogle `IsLocalization, Algebra.Etale` returned zero hits. Source searches through
   Sheaf/RingTheory and upstream RingTheory found no noncircular direct replacement.
   Closing the descent theorem requires substantial assembly, beyond a few-minute
   repair. Verdict: pass; retain the one documented split.
4. Read the proof from the target down. The field-point equivalence constructs the
   pointing, application of Spec.map verifies its base point, and IsLocalization.epi
   proves epimorphy for the actual map i. No weaker compatible-map lemma can supply
   that last step. Imports added for the proof are private and needed; the new module's
   sole public import supplies its signature. The original node had no proof_deps, so
   no old dependency is omitted from No longer needed. The unit
   `sk-prop-input-spreading` has empty realized statement/step lists, unchanged; the
   route remains affine descent. Verdict: pass; no repository-baseline pruning.
5. Compared the original node with the delivered node: only proof, proof_deps and
   proof_origin change. These record the exact unpointed-model reduction followed by
   proved pointing and localization-epi steps. Checked the new node's complete
   signature, source, statement dependencies, proof plan, search records, provenance,
   chapter, unit, blueprint origin and Lean record against its new module.
   Verdict: pass.

Second reading changed no Lean proof or statement: no further fault was found.
Added this independent review and removed the temporary axiom-check copy.
