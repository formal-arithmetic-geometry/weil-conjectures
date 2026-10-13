## What changed

Repair of the returned landing at dd18cfc1b: restored all three original ordinary imports
identified by `tools/import_prune_check.py`: `Sheaf.AlgebraicGeometry.ChowRelativeAmple`,
`Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`, and
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism`. The import checker
reported that removing them loses access to `AlgebraicGeometry.Scheme.Modules.IsAmple`
for GenericRankLeadingDegree, TopDimensionalReductionIntersection, AbelianVariety.Projective,
Cohomology.Serre, Modules.Ample, and Modules.HilbertPolynomial. All original imports are
now retained. The proof and theorem signatures are unchanged by this repair; no downstream
module needs adaptation. The second reading below records the previous delivery and predates
this import repair.

Replaced the sorry in `AlgebraicGeometry.Scheme.Modules.exists_chow_finite_cohomology_witness`
with a complete Lean assembly of the Chow construction. The existing signature and all public
imports are unchanged. The module constructs the actual double pullback of the integral O(1),
takes its tensor power, and uses the actual two pushforward functors. No definition was added
and no object data was replaced by a sorry or chosen in a new definition.

Added two strictly separate intermediate theorems in new modules. The finiteness theorem
concerns the explicit twists of a specified projective model, without integrality or a
birationality condition; it proves coherence and finite cohomology only. The generic-stalk
theorem concerns every invertible module under a morphism isomorphic on a dense open, without
properness, projectivity, Noetherianity, or cohomology assumptions; it gives an additive
residue-field equivalence with scalar compatibility only. Neither restates the assigned theorem.

The original module proves the remaining combination in Lean: nonzero generic stalk,
closed support, both inclusions in the support equality, maximal-ideal annihilation,
transfer of the residue-field module structure without changing the additive group,
compatibility of scalar actions, and finrank one. It obtains Noetherianity of the base and
local Noetherianity of the source from Mathlib and uses the existing ChowModification.

Added ordinary proof imports of `ChowTwistFiniteCohomology`,
`BirationalLinePushforwardGenericStalk`, `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`,
and `Mathlib.Algebra.Module.TransferInstance`. A theorem-scoped unused-variable linter option
preserves the existing existential binder named `inst`, whose use is implicit in its body.

Read Stacks Tag 02O5, proposition-proper-pushforward-coherent, especially the construction
of L and pi_* L^n and the verification of property (a). The unit remains
`sk-thm-picard-coherence`; its projective/Chow route is retained. All three delivered modules
compile together with lcompile in import order, with no errors or warnings.

## Proved and sorry left

Closed the one assigned hole:
`AlgebraicGeometry.Scheme.Modules.exists_chow_finite_cohomology_witness`
(node `lem-pc-v3-chow-finite-cohomology-witness`). Its proof has no sorry.

Added exactly two holes, each in a separate module, with a source and complete proof in words:

- `AlgebraicGeometry.Scheme.Modules.exists_chow_twist_finite_cohomology`
  (`Sheaf.AlgebraicGeometry.ChowTwistFiniteCohomology`,
  node `lem-pc-q2-chow-twist-finite-cohomology`).
- `AlgebraicGeometry.Scheme.Modules.birational_line_pushforward_generic_stalk`
  (`Sheaf.AlgebraicGeometry.BirationalLinePushforwardGenericStalk`,
  node `lem-pc-q2-birational-line-pushforward-generic-stalk`).

This is a decomposition: one upper hole closed, two lower holes added, net minus one.
The resulting theorem still depends on those holes and existing unfinished projective/derived
results; no claim of a sorry-free proof is made.

Edge cases checked mathematically: the analytic lemma allows empty W or Y; zero-coordinate
projective space forces empty Y and all asserted modules are zero. Tensor exponent zero is
allowed and is the unit module. An integral W in the stalk theorem is nonempty; a dense open
contains its generic point. Extra components of Y outside the inverse image of that open do
not affect its generic pushforward stalk. With identity pi, the stalk comparison is exactly
the generic stalk of a line; with identity i, the closed scalar quotient is the generic
residue quotient. The residue field is nontrivial, which the Lean support proof uses explicitly.

## No longer needed

No original imports are removed in the repaired delivery. The three imports initially
removed were restored because the landing checker identified downstream uses of their
transitive declarations. They are retained for compatibility even though the outer proof
does not directly use their declarations. Globally pruned modules: none.

The attempted new imports of `RelativeSerreVanishing` and
`WeilConjectures.AlgebraicGeometry.Cohomology.Projective` were removed before delivery
because they would close a cycle. The outer DAG records the direct theorem dependencies
of the Lean proof; retaining compatibility imports does not add direct theorem dependencies.

The complete list of old direct `proof_deps` no longer used directly by the outer proof is:

- `lem-pc-chow-relative-ample`.
- `lem-pc-relative-kill-by-twisting`.
- `lem-pc-projective-coherent-finiteness`.
- `lem-pc-closed-immersion-coherent-cohomology`.
- `lem-pc-derived-direct-image-composition`.

These remain mathematical steps in the analytic intermediate's pending proof plan, so this
is a replacement of direct dependencies by a smaller interface, not global pruning.

## Where the brief, the DAG or earlier work was wrong

The previous delivery incorrectly treated the three unused ordinary imports as safe to
remove. The landing checker found downstream uses of `IsAmple` through those imports.
This repair follows the return's first permitted remedy, retaining every affected import,
without changing downstream files or any existing interface.

The old outer imports did not include the relative Serre vanishing or projective-finiteness
modules named in its node. Their statements are recorded in the analytic intermediate's source proof plan, but the
corresponding broad modules cannot currently be imported here without a cycle.

The existing `nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom` is formulated over a
field k. It cannot directly give the Gamma(T,top)-linear comparison for an arbitrary affine
Noetherian base. The analytic intermediate includes precisely this linearity/comparison glue,
which is explained in its docstring; it does not use the proper coherence theorem circularly.
The unbounded derived-composition isomorphism also needs the vanishing and cohomology passage
before it yields the finiteness conclusion. The source proof itself is not disputed.

The first dry run rejected a cycle through RelativeSerreVanishing, CoherentSerreVanishing,
AffineMorphismCohomologyEdge, Cohomology.DirectImage.AffineMorphism,
Cohomology.DirectImage.FiniteFreeComplex, and IntegralIdealProperCohomology back to this item.
The source Cohomology.Projective and Cohomology.Serre modules also reach this item, as checked
by import_direction.py. Consequently the analytic intermediate must use the independent
projective proof from the cited source, rather than relying on these current module imports
or the induction's general proper coherence theorem. Its source plan identifies the intended
projective results, and its docstring spells out the independent argument. Its pending sorry
needs no proof-only imports, so the cyclic imports were removed. No unrelated library module
was adapted to hide the cycle.

The blueprint-ancestor script returns None for the assigned node because its created.item is
a module name rather than a DAG id. The existing node's explicit blueprint.from identifies
`lem-pc-coherent-hi` as its ancestor, and the new nodes retain that ancestor and the intervening
Chow-witness/integral-ideal route. No existing non-proof fields were edited.

## New nodes

`lem-pc-q2-chow-twist-finite-cohomology` is the analytic construction for a specified projective
model, realized by `Sheaf.AlgebraicGeometry.ChowTwistFiniteCohomology`. Its proof follows the
common ample twist, local projective coherence, and Leray portions of Tag 02O5. It has no
support or generic-rank conclusion and assumes no birationality or integrality.

`lem-pc-q2-birational-line-pushforward-generic-stalk` is the local scalar-compatible stalk
comparison, realized by `Sheaf.AlgebraicGeometry.BirationalLinePushforwardGenericStalk`.
It follows the dense-isomorphism-open verification of property (a) and closed-pushforward
stalks. It has no finiteness or coherence conclusion. Each node records actual LeanSearch,
LeanFinder and Mathlib grep queries from searches.jsonl; LeanSearch returned HTTP 500 and is
recorded as unavailable, not as a successful no-match. Blueprint searches for Chow twist,
relatively ample, generic stalk, and invertible module found no duplicate of either statement.
There are no change records because no existing definition or statement was changed.


## Earlier second reading (a previous round; superseded)

1. **Unchanged interface: pass.** Diffed every delivered module against the read-only
   checkout. The existing theorem signature is byte for byte identical, its docstring and
   public imports are unchanged, and there are no new definitions. The two other modules
   are new. The existing node changes only `proof`, `proof_deps`, and `proof_origin`; no
   change record is needed.
2. **Lean proof and trust: pass as a decomposition.** Recompiled all three modules in
   import order using lcompile: no errors or warnings. Inspected every proof and searched
   for forbidden declarations: exactly the two reported named `:= by sorry` theorems remain.
   Scratch-copy `#print axioms` checks of all three declarations return only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The original hole is filled, but its
   theorem is not yet sorry-free. L and its powers and both pushforwards are concrete
   constructions; no definition chooses arbitrary data from an unproved existence theorem.
3. **Split statements: pass.** Independently checked both statements against the Chow
   construction in [Stacks Tag 02O5](https://stacks.math.columbia.edu/tag/02O5). The specified
   projective twist result removes the target's generic/support conclusions and needs no
   integrality or birationality. The stalk result is local and needs no finiteness,
   cohomology, properness, or projectivity. Empty Y, empty coordinates, identity morphisms,
   exponent zero, and extra components away from the dense open do not give counterexamples.
   For the stalk result, integral W is nonempty and its generic point belongs to every dense
   open; its local ring is a field and the closed immersion identifies residue fields.
   Both holes have source proofs in docstrings, nodes, and exact Lean signature records.
   New LeanFinder queries using "locally free rank one" and "Serre finiteness" and local
   searches for generic-stalk, invertible-stalk, and projective-finiteness interfaces found
   ingredients but no duplicate theorem. In particular `invertible_module_generic_stalk`
   does not supply the two pushforwards or the scalar-compatible residue-field comparison.
4. **Route and pruning: pass after report repair.** The outer proof first uses the existing
   proved Chow construction, twist invertibility, closed-stalk, coherent/finite-type and
   support results, then the two independent residual statements. Its support argument
   uses generic-point specialization and its module transfer preserves the additive group.
   No short existing declaration closes either residual statement in a few minutes.
   Checked `dag/units/sk-thm-picard-coherence.json`: its `realized` arrays are currently empty
   and this delivery leaves them unchanged; the projective/Chow route remains intact.
   All ordinary imports support the proof or its instances. The report now explicitly lists
   all five old direct DAG dependencies removed from the outer proof, in addition to all
   three removed imports. Global pruning remains none.
5. **DAG agreement: pass.** Checked the outer node's four proof steps against the code and
   the union of their `uses` against `proof_deps`. Checked both new nodes' required source,
   search, creation, blueprint, chapter, unit, status, and Lean records. Their plans describe
   the still-unproved mathematical subarguments; the report explicitly records the broad
   projective/Serre import cycles, rather than claiming those modules were imported or used
   in a completed proof.

Second reading changed only this report: completed the removed direct dependency list and
recorded the independent review and axiom evidence. No Lean proof or statement repair was
necessary. Counts remain one assigned hole closed, two split off, net minus one.


## Second reading by Q2

This is an independent reading of the repaired delivery, including the restored imports;
the earlier reading above is not used as evidence for the checks below.

1. **Interfaces: pass.** Diffed the original module and original node against the checkout.
   Independently compared the full existing theorem signature byte for byte: unchanged.
   The declaration docstring and all original imports remain. The only original node fields
   changed are `proof`, `proof_deps`, and `proof_origin`. The other two modules and nodes
   are new; no definition, existing public signature, or target statement changes.
2. **Proof and axioms: pass as a decomposition.** Compiled the three modules in import order
   through lcompile with no errors or warnings. Compiled separate scratch copies with
   `#print axioms` for each of the three declarations: exactly propext, Classical.choice,
   Quot.sound, and sorryAx. Checked the delivered text: only the two reported public named
   theorems contain sorry; no forbidden declarations or hollow definitions. The explicit
   Chow modification, double pullback, tensor power, and pushforwards are retained. The
   existential exponent is eliminated in a theorem proof; no new definition chooses an
   arbitrary witness from an unfinished existence theorem. The transported module structure
   uses the existing additive group and its compatibility is actually proved.
3. **Residual statements: pass.** Read [Stacks Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
   directly, especially its Chow construction and property (a). For the analytic statement,
   proper f and closed i give a Noetherian W; the closed embedding j and its compatibility
   give the two projective morphisms and their common twist. Relative vanishing and
   independent projective finiteness give the stated conclusion without integrality or
   birationality. For the stalk statement, density and integrality put eta in U, so the
   isomorphism on U transfers the line trivialization; closed pushforward and the residue
   field comparison give the displayed scalar identity without properness. Checked empty
   Y/W and empty projective coordinates for the analytic theorem, identity morphisms and
   extra components outside U for the stalk theorem, and the allowed tensor exponent zero.
   Neither statement repeats the whole item: one supplies only coherence/cohomology, the
   other only a local additive equivalence and scalar identity. Both have complete source
   arguments in docstrings, nodes, and verbatim Lean signatures (checked programmatically).
   Fresh LeanFinder searches for a line bundle pushforward near an isomorphism and for
   ample-twist Serre finiteness returned algebraic/localization ingredients, no duplicate.
   Searched current Sheaf and upstream sources with generic/pushforward and Chow/twist
   terms. Read invertible_stalk_linearEquiv and invertible_module_generic_stalk: the former
   supplies local trivialization but not restriction of pushforward or the closed-immersion
   residue comparison; the latter itself remains open and has no two-pushforward comparison.
   Neither residual statement can be closed by a short application of these declarations.
4. **Route and pruning: pass for the repaired version.** Traced the actual proof from
   ChowModification to the specified twist, invertibility, the stalk equivalence, closed
   support, maximal-ideal annihilation, and transferred finrank. The reverse support
   inclusion uses generic-point specialization correctly; residue-field nontriviality
   proves the generic stalk is nonzero. The common ample/projective route of the unit is
   kept. Read sk-thm-picard-coherence.json: its existing realized arrays are empty and
   unchanged. All added proof imports are ordinary, and the public imports of the new
   modules provide signature notions (including tensorPow and IsInvertible). The three
   restored original imports must stay for the downstream IsAmple uses identified by the
   return; this review does not repeat their invalid pruning. The five obsolete direct
   outer DAG dependencies are all named in No longer needed; they remain in the analytic
   plan. No global module is pruned. No new simplification was justified by the searches.
5. **Node agreement: pass.** Matched the original node's four steps to the Lean assembly:
   Chow plus analytic witness, invertible dense-open stalk, support equality, and residue
   module transfer. Checked each node's proof_deps equals the union of its step uses.
   Checked the new nodes' source, statement dependencies, search records, status, creation,
   blueprint ancestry, chapter/unit, and Lean records. The two residual proof plans describe
   the pending subarguments, not completed proofs. The report records the cyclic broad
   projective/Serre imports and the need for the independent source argument.

Second reading changed only this report: added this fresh review of the repaired imports,
independent signature/node checks, new searches, and current compile/axiom evidence. No Lean
or node repair was needed. One assigned hole is closed, two lower holes remain split off;
this is decomposition with net minus one, not a sorry-free proof or a pruning gain.
