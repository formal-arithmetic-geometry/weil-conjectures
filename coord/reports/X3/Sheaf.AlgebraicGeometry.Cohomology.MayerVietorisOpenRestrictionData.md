## What changed

Replaced the sole hole in `H.openRestrictionData` with a complete construction of the four
isomorphisms and Lean proofs of both scalar squares and the coefficient square. The existing
statement and `H.openBaseChangeInclusion` definition are unchanged. Proof-only imports add
`InverseImageOpenFreeSheaf` and `OpenImmersionCoefficientUnit`; the latter exposes the general
composition interface used by the proof.

Reused the existing sorry-free theorem
`AlgebraicGeometry.Scheme.Modules.H.invImage_openFreeSheaf_iso` from
`InverseImageOpenFreeSheaf`, recorded by `lem-pc-inverse-image-open-free-sheaf`.
The reviewer X-02382 identified this exact match; the duplicate free-sheaf module and
node have been removed. The theorem uses only standard axioms.
`InverseImageCoefficientComposition` constructs `coefficientUnit`, `invImageComp` and
`invImageCongr` from existing definitions and the adjunction composition comparison. No data
is chosen from an unproved existence theorem. The remaining proof obligation is the coefficient
composition identity. `OpenImmersionCoefficientUnit` isolates only invertibility of the
specified coefficient morphism for an open immersion.

The item's route is updated in its node copy. There are no definition or statement changes to
existing public declarations, and no changes to a target. The unit record
`sk-thm-picard-rr` has no realized statement or steps, so this reduction bypasses none of them.

## Earlier visibility repair

The returned delivery required a proof-only visibility repair in the newly added module
`Sheaf.AlgebraicGeometry.Cohomology.InverseImageCoefficientComposition`, held by X3. The
original line was `public import Mathlib.CategoryTheory.Adjunction.CompositionIso`; it was
changed to `import Mathlib.CategoryTheory.Adjunction.CompositionIso` so the proof dependency is
not re-exported. There was no compiler error; the change addresses reviewer point 5 and leaves
all declarations and signatures unchanged.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.H.openRestrictionData`
(node `lem-pc-open-restriction-data`), one of the item's one original holes. This is a
**decomposition**, not a sorry-free proof of the original theorem: it depends on two new holes.
The free-sheaf inverse-image identification uses the existing proved theorem.

Added and left, each as the whole proof `:= by sorry` in its own module:

- `AlgebraicGeometry.Scheme.Modules.coefficientUnit_comp`
  (`lem-pc-coefficient-unit-composition`): compatibility for two arbitrary composable scheme
  morphisms. It asserts no scalar squares, open restriction, or cartesian square.
- `AlgebraicGeometry.Scheme.Modules.coefficientUnit_isIso_of_isOpenImmersion`
  (`lem-pc-open-coefficient-unit-iso`): invertibility of one explicitly defined coefficient map.
  It asserts no composition compatibility, free-sheaf identification, or scalar squares.

No sorry remains in the item's module. One original hole closed, two holes added. No claim of positive net-hole progress is made.

Compilation uses the prescribed `lcompile.py`, for the delivered modules in import order.
All constructions cover empty opens, top opens, zero modules, zero rings, and nonflat scalar
extensions: no new nonemptiness, quasi-coherence or flatness assumption appears. The free-sheaf
result is stated for arbitrary maps, including identities and empty preimages. The two remaining
statements were checked against these cases and the open-restriction/module-adjunction APIs.

## No longer needed

The removed direct `Mathlib.CategoryTheory.Adjunction.CompositionIso` import is also no longer
needed; its module remains transitively available and is not claimed as closure pruning.

Removed the duplicate delivery module `FreeSheafInverseImage` and its new node
`lem-pc-free-sheaf-inverse-image`. The item now imports `InverseImageOpenFreeSheaf`
and uses the existing sorry-free `H.invImage_openFreeSheaf_iso` instead.

The old proof dependency `lem-weil-pbc-zariski-extension-by-zero-adjunction` and its module
`Sheaf.AlgebraicGeometry.ZariskiExtensionByZeroAdjunction` are not needed by this proof. Its
proof-only import in the current repository version is removed. The new route uses the usual
inverse-image/direct-image adjunction, not extension by zero.

The direct proof-only import of `FlatCohomologyComparison` is also removed as redundant:
`MayerVietorisFreeComplex` already publicly imports it. Its definitions and node remain needed.

`lem-pc-free-mayer-vietoris-short-exact` remains a statement dependency because it records
`H.openFreeSheaf`; its short-exactness assertion and the signed two-open complex are not used
in this proof. Its module `MayerVietorisFreeComplex` must remain publicly imported for the
existing statement. `def-pc-flat-cohomology-comparison` remains necessary. No other old proof
dependency is pruned. An exploratory import of
`WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit` was removed from the new composition
module because its eventual deferred proof has no implementation using that import yet.

## Where the brief, the DAG or earlier work was wrong

Repair of reviewer X-e5d6f, point E4: corrected the proof docstring of
`coefficientUnit_comp` to first postcompose both sides with the forgotten inverse of
`pullbackComp g f`, cancel that isomorphism, and then use the composite abelian
inverse-image/direct-image adjunction. The existing following sentences now describe
these postcomposed morphisms. No Lean signature, proof body, import, or node route changes.

The plan's cited declarations supply the free-sheaf and coefficient definitions, but not the
open coefficient-unit invertibility or its composition compatibility. The extension-by-zero
adjunction is unnecessary for the represented-free-sheaf identification: ordinary pullback
adjunction and Coyoneda suffice. The existing `H.invImage_openFreeSheaf_iso` supplies
this result without a new obligation; the earlier search missed it.

A direct implementation of the general coefficient-composition identity was explored using
`unit_conjugateEquiv_symm` and `pullbackUnit_comp_app`; elaboration repeatedly expanded the
module/sheaf definitions, once reaching the file timeout. The unfinished exploration is not
part of the delivered theorem body. The obligation is instead stated independently with its
complete argument, and the item's combination proof is complete.

The local literature checkout has no Stacks tex files. The inherited source was read at the
public Stacks pages for Tags 01F7 and 04J0. Tag 04J0 explicitly identifies inverse image and
module pullback for localization morphisms. The implementation uses Mathlib's
`restrictFunctorIsoPullback` and `Topology.IsOpenEmbedding.sheafPullbackIso` as its planned
open-immersion identifications. LeanSearch returned HTTP 500 and is recorded as unavailable.

`blueprint_refs.py ancestor lem-pc-open-restriction-data` returned no ancestor. Reading the
existing parent `lem-pc-cohomology-mayer-vietoris-ext-presentation` supplies the inherited
ancestor `lem-sc-flat-base-change-coherent`; the new nodes record that ancestor and the
intervening restriction/Ext nodes. The earlier search claim about free sheaves was incorrect: reviewer X-02382 identified
`lem-pc-inverse-image-open-free-sheaf` and its existing proved Lean theorem. The two
coefficient obligations remain split off.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered item module with the repository version. Existing declarations and
signatures, including `H.openBaseChangeInclusion` and `H.openRestrictionData`, are unchanged;
only proof imports, private helpers, and the proof body differ. Verdict: pass.

2. Compiled all three delivered modules with the prescribed `lcompile.py`. There are no forbidden
constructs and no sorry in the item; the two explicit split-off theorems are the only
remaining sorry declarations and each has a named node and proof docstring. Verdict: pass.

3. Checked the two split-off statements against the definitions and edge cases (empty and
top opens, identities, zero modules, and arbitrary morphisms). They are true, strictly simpler
than the item, and introduce no weakened item hypothesis. Correction after return X-02382: the free-sheaf obligation duplicated the existing
`H.invImage_openFreeSheaf_iso`, which is now reused; only two coefficient obligations remain. Verdict: pass.

4. The proof follows the open-restriction route through the free-sheaf inverse-image,
open-immersion coefficient-unit, and coefficient-composition nodes. The old extension-by-zero
dependency is unused and recorded under `No longer needed`; the unit has no realized steps to
bypass. Verdict: pass.

5. Checked each node's Lean declaration, statement, proof dependencies, and proof origin against
the code and imports. The item node records the two new obligations and the existing proved free-sheaf dependency and the new nodes record
their exact declarations. Verdict: pass.

Added a module-local `linter.unusedVariables` option to suppress the warning caused by the
statement's intentionally unused existential witness; this does not alter its elaborated type.
The change is recorded in `coord/changes/openRestrictionData-linter.md`. The delivered proof
and two split-off modules remain as reported above.

## New nodes

`lem-pc-open-coefficient-unit-iso`, module `OpenImmersionCoefficientUnit`: invertibility of the
abelian coefficient unit along an open immersion, following Stacks 04J0 and the explicit
restriction adjunctions. This is strictly a part of the original argument.

`lem-pc-coefficient-unit-composition`, module `InverseImageCoefficientComposition`: the
coefficient-unit composition identity for two composable maps, following the unit composition
identity and the conjugation characterization of the constructed comparison. This is strictly
a part of the cartesian-square argument, applied twice by the item.

Both new nodes record the actual logged LeanSearch (unavailable), LeanFinder and grep searches;
the Mathlib signatures and source-library unit identities were read. The sole change record is
`coord/changes/openRestrictionData-linter.md`, documenting the linter option; existing statements,
definitions and public imports were not changed.

## Earlier second reading (a previous round; superseded)

1. Compared the item with the current repository using `diff` and an exact-text check.
   The existing `H.openRestrictionData` signature and complete `H.openBaseChangeInclusion`
   definition are byte-for-byte unchanged after removing an extra space before the proof.
   The two additional modules are new, with no existing interface adapted. Verdict: pass.

2. Compiled all three delivered modules in import order with `lcompile.py`, without errors or warnings.
   An explicit `#print axioms` scratch copy checked both existing declarations and every public
   declaration of the two new modules. The inclusion and new constructions use only
   `propext`, `Classical.choice`, and `Quot.sound`; the item and the two named obligations
   additionally use `sorryAx`, as reported. The only two delivered `sorry`s are whole named
   theorem proofs, with nodes and proof docstrings. No forbidden construct or hollow definition
   occurs. The free-sheaf isomorphism witness is eliminated inside a proposition proof; no
   definition chooses arbitrary data from an unproved existence theorem. Verdict: pass.

3. Read each obligation and its proof in words against the free-sheaf, coefficient, restriction,
   adjunction composition, and upstream `PullbackUnit` APIs. The free-sheaf formula follows
   from natural hom equivalences; the open coefficient statement follows from restriction;
   the composition identity follows by adjunction and the proved module-unit identity.
   Checked identity maps, empty opens/schemes, top opens, zero modules, and unrestricted
   scalar extensions: none requires an extra assumption. Each obligation is strictly a part
   of the original construction, and none restates the whole item. Independent LeanFinder,
   Loogle, and grep queries used different wording (logged in `searches.jsonl`); read the
   resulting `freeYonedaHomEquiv`, `sheafPullbackIso`, restriction and composition interfaces.
   Correction after return X-02382: `H.invImage_openFreeSheaf_iso` directly matches the
   free-sheaf obligation and is sorry-free. The duplicate was removed and that theorem is
   now reused. The two coefficient obligations remain. Hole accounting after repair:
   one hole closed and two added, a decomposition.

4. Read the proof from its existential construction through both scalar squares to the
   coefficient square. The comparisons are concrete adjunction/equality constructions;
   the final square uses composition twice and cancellation of isomorphisms. No Ext result
   or extra hypothesis is smuggled in. The two proof-only imports supply the free-sheaf and
   coefficient interfaces; the public free-complex import supplies the existing signature.
   `FlatCohomologyComparison` is available through that public import. Recorded removal of
   the extension-by-zero import and node, and of the redundant direct comparison import.
   The old free-complex theorem's assertion is unused, but its definitions and module remain
   required by the signature. Read `sk-thm-picard-rr` and its empty realized fields; this
   degree-zero reduction changes no unit statement or realized step. Verdict: pass.

5. Compared all node Lean signatures with the files, and checked the item's new proof steps,
   dependency union, and proof origin. The two retained new nodes have sources, natural-language proofs,
   searches, creation/blueprint records and the correct chapter/unit. Corrected the prose of
   the new coefficient-composition node to write the typed order `g^{-1}f^{-1}` for the
   composite inverse image; the Lean statement was already correct. Verdict: pass.

Changes in this reading: restored signature whitespace; corrected stale report claims about
removed imports and the existing linter change record; corrected the new node's inverse-image
composition order; recorded fresh independent searches. No proof body or obligation was
changed. The linter record remains `coord/changes/openRestrictionData-linter.md`.

## Earlier second reading (a previous round; superseded)

1. Compared the item with the repository using `diff` and exact substring comparisons.
   The whole existing `H.openBaseChangeInclusion` definition and the entire
   `H.openRestrictionData` signature are byte-for-byte identical. No existing public
   statement, definition or public import changes. Both additional modules are new.
   Verdict: pass.

2. Independently compiled all three delivered modules in import order with `lcompile.py`.
   Explicit `#print axioms` checks cover the inclusion, the main theorem, all three new
   constructions, both obligations, the generated composition reassociation lemma, and
   the reused free-sheaf theorem. Constructions and the free-sheaf theorem have only the
   three permitted axioms; the main theorem and coefficient obligations additionally
   have `sorryAx`. The only two source holes are whole named theorem proofs with their
   proof docstrings and nodes. No forbidden construct or data hole occurs. The free-sheaf
   witness is eliminated inside the existential proposition, and `asIso` inverts a
   specified morphism whose inverse is uniquely determined. Verdict: pass.

3. Read both split-off statements against `coeff`, the pullback unit, the adjunction
   composition comparison, and the restriction interfaces. Composition follows by
   taking adjuncts and applying `pullbackUnit_comp_app`; invertibility follows from
   restriction and `pullbackUnit_eq_of_isOpenImmersion`. Read Stacks Tags 01F7 and 04J0;
   the latter explicitly identifies module pullback with inverse image for localization.
   Checked identity and empty open immersions, zero modules, and unrestricted scheme
   morphisms: neither statement needs flatness or extra hypotheses. They are separate,
   strictly smaller parts of the original argument. Fresh LeanFinder, Loogle and grep
   searches are logged in `searches.jsonl`; local searches read the upstream module-unit
   lemmas and found no complete duplicate of either obligation. Neither obligation has
   an immediate existing theorem application closing it. Verdict: pass as decomposition.

4. Read the proof from the four constructed isomorphisms through the two scalar equations
   and the final coefficient square. The latter uses composition twice and equality
   transport, with correctly oriented module and abelian comparisons. Reused the proved
   free-sheaf identification. Read the unit's empty realized fields: no realized step is
   bypassed. The old extension-by-zero dependency is unused; the free-complex assertion
   is unused but its definitions still occur in the signature; the comparison node is
   still used. The report accounts for all old proof dependencies. Removed the redundant
   direct `CompositionIso` import from the new composition module: the same API is already
   publicly reachable through the module-pullback imports. Verdict: pass.

5. The item node changes only `proof`, `proof_deps` and `proof_origin`, and its dependency
   union matches the written proof. Both new nodes have exact Lean signatures, sources,
   proof plans, search records, creation metadata, blueprint ancestry and chapter/unit
   fields. No node or unit statement changes. Verdict: pass.

Changes in this reading: removed the redundant `Mathlib.CategoryTheory.Adjunction.CompositionIso`
import; renamed the earlier report's misleading forced-adaptation heading, since it describes
an edit to a new module, not a forced adaptation of an existing module; added this independent
review and fresh search/axiom evidence. No proof body or statement changed. Hole accounting
remains one closed, two added: decomposition, net minus one, not a sorry-free proof.


## Second reading by X3

1. Compared the item module against the read-only repository with `diff`; exact substring
   assertions verify that the complete `H.openBaseChangeInclusion` definition and the
   `H.openRestrictionData` signature are byte-for-byte identical. Public imports are unchanged;
   only proof imports, options, private helpers and the proof differ. Both coefficient modules
   are new. The existing node changes only `proof`, `proof_deps`, `proof_origin`. Verdict: pass.

2. Independently compiled the three modules with `lcompile.py --all`: clean, in 3.1, 2.0 and
   8.9 seconds respectively. Compiled a scratch axiom probe for the inclusion, the item, all
   three new constructions, both obligations, the generated reassociation theorem and the
   reused `H.invImage_openFreeSheaf_iso`. The constructions and reused free-sheaf result have
   only `propext`, `Classical.choice`, `Quot.sound`; the item and coefficient obligations also
   have `sorryAx`. Exactly two whole named theorem proofs contain `sorry`; neither is data.
   No forbidden construct occurs. The existential free-sheaf witness is used inside a proof
   of a proposition; `asIso` inverts a specified morphism, with a uniquely determined inverse.
   Verdict: pass as a decomposition, not a sorry-free proof.

3. Read both coefficient statements and proof docstrings against `coeff`,
   `pullbackUnit_comp_app`, `pullbackUnit_eq_of_isOpenImmersion`, `leftAdjointCompIso`,
   `unit_conjugateEquiv_symm`, `restrictFunctorIsoPullback`, and `sheafPullbackIso`.
   Read Stacks 01F7 (the f-map construction) and 04J0 (localization identifies inverse image
   with module pullback). For composition, postcomposition with the forgotten inverse
   module comparison makes both adjuncts the same composite module unit. For invertibility,
   restriction identifies the adjunct of its unit with the identity, followed by the module
   restriction comparison. Checked identities, empty opens/schemes, top opens and zero modules;
   composition has arbitrary morphisms and needs no flatness. These are separate proper parts
   of the restriction construction, not restatements of it. Fresh differently worded LeanFinder,
   Loogle and grep searches were run with `msearch.py`, and the local Lean/upstream sources
   were searched. The hits give restriction and adjunction interfaces, not either complete
   coefficient theorem. Neither hole admits an immediate existing-lemma application.
   Verdict: pass; both remain justified smaller obligations.

4. Read the construction downward: pullback projection identities give h and hs; base change
   preserves the open immersion k; open coefficient invertibility gives d and the first
   factor of d'; module pullback comparisons give t; adjunction composition gives c. The
   free-sheaf witness uses the existing proved inverse-image theorem and j-preimage W = top.
   Both scalar squares use genuine naturality and the global-section form of hs. The final
   square applies coefficient composition twice, transports h by equality induction, and
   cancels the isomorphisms. No Ext assertion or extra hypothesis enters. Read the unit
   `sk-thm-picard-rr`: its realized statement and step arrays are empty; no realized route is
   bypassed. All three old proof dependencies are accounted for: the comparison remains,
   free-complex definitions remain in the signature but its exactness theorem is unused,
   and extension by zero is removed. The direct comparison import is redundant through
   `MayerVietorisFreeComplex`; the new proof imports supply the actual lemmas. Verdict: pass.

5. Checked the item node's three proof steps and dependency union against the code, and the
   two new nodes' exact Lean statements, sources, proof plans, search records, creation,
   ancestry, chapter and unit fields. Composition is oriented g-inverse f-inverse; the
   open coefficient statement has precisely the open-immersion hypothesis. Neither new node
   depends on the item. Existing node and unit statements remain unchanged. Verdict: pass.

Changes in this reading: appended this fresh review and search evidence; saved the current
axiom probe in scratchpad. No repair to a proof, statement, definition, import or node was
needed. Hole accounting remains one original hole closed, two smaller holes added, net minus
one; this delivery is a decomposition.
