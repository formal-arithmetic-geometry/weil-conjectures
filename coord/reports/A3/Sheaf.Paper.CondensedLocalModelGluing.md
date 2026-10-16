## What changed

Repair of the return at head `a5958f2ef`: removed the duplicate base-change module
and changed its sole consumer to use the existing library theorem directly.
No new holes or mathematical interface changes were introduced by this repair.
The rest of the retained delivery follows below. The retained second reading
predates this repair; the next reader must review the changed final set.

The original signature of
`AlgebraicGeometry.ProEtale.exists_finiteCoefficient_gluing_of_local_models`
is unchanged. Its proof now combines local finite-coefficient embeddings with
compatible-subobject gluing, then uses extension/restriction adjunction and
cover-detection to obtain the global scalar-extension isomorphism.

The gluing construction is explicit: `localSubobjectKernel` is the kernel of the
map to the product of pushed-forward local cokernels. Its inclusion, local
comparison maps, monicity, local factorization property, and the inverse criterion
are proved from the categorical API. The module action is lifted through this
inclusion; its unit and associativity laws and the linearity of local comparisons
are proved by cancellation. `LocalSubmoduleGluingData` is an ordinary structure
retaining these data and equations; it contains no postponed construction.

The original module also proves the scalar-adjoint compatibility and detection of
module isomorphisms on a cover. It reuses the existing proved private
`pullbackExtendScalarsIso` through `import all
Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars`. All new proof imports
in the original module are non-public. No existing definition or statement is
changed, and no consumer adaptations are required. The static preflight requests
a change record for the added proof-local commands; that record documents the
unchanged signature and downstream users. The unchanged direct consumer
`Sheaf.Paper.CondensedLfpCoefficientModel` compiled against the sandbox overlay.

## Proved and sorry left

Original hole closed (1 of 1):
`AlgebraicGeometry.ProEtale.exists_finiteCoefficient_gluing_of_local_models`
(node `lem-weil-pbc-condensed-local-model-gluing`).

New holes added (1), a strictly smaller arithmetic part of the argument:

- `AlgebraicGeometry.ProEtale.exists_finiteCoefficient_compatible_local_monomorphisms`
  in `Sheaf.Paper.CondensedFiniteLocalSubmodules`
  (node `lem-weil-pbc-condensed-finite-local-submodules`). This still needs the
  finite common-stage descent of the pairwise overlap comparisons and inverses,
  together with faithful-flat monicity of the scalar-adjoint embeddings. It makes
  no global object or effective-gluing assertion.

There are no other holes in the delivery. In particular, the new kernel API,
`localSubobjectQuotientMap_zero_of_compatible`,
`isIso_localSubobjectKernelComparison`,
`exists_subsheaf_of_compatible_local_monomorphisms`, and
`exists_module_of_compatible_local_monomorphisms` have complete Lean proofs.
This is a decomposition: one baseline hole closed and one lower hole added
(net zero), not an axiom-free completion of the original theorem.

All modules were compiled together through `lcompile.py --all`; the original
module also compiled separately. `#print axioms` for weakly-etale base change,
local quotient vanishing, and module gluing shows only `propext`,
`Classical.choice`, and `Quot.sound`. The original theorem additionally has
`sorryAx`, through the one reported arithmetic obligation. Empty covers are
admitted by every signature:
the kernel and cover-detection proofs introduce no nonempty-cover or positive-rank
assumption. The new finite-stage lemma explicitly permits F = E in that case.

## No longer needed

Repair pruning: all of the unlanded
`Sheaf.AlgebraicGeometry.ProEtaleKernelOverlapBaseChange` module, including its
copied pushforward-map formula, square isomorphism, continuity instances,
restriction comparison, mate calculation, and base-change API. Its only sandbox
consumer now imports the existing source-library base-change module instead.
The mathematical base-change node remains needed, attached to the existing
library theorem rather than a duplicated declaration.

Compared with the repository, the original module removes these six proof imports:
`Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`,
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`,
`Sheaf.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus`,
`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`,
`Sheaf.CategoryTheory.ModulePullbackTensorIso`, and
`Sheaf.CategoryTheory.SiteModuleSheafGluing`.
The general gluing files use the smaller coefficient-facing
functor and module-object imports directly; they expose no unnecessary
constructibility or coefficient-colimit imports. The unfinished
arithmetic statement needs only its three public signature imports; unused proof
imports of `Sheaf.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus` and
`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence` were removed from
that new file. Their nodes remain in its mathematical proof plan, since they are
still needed to finish the arithmetic argument.

The new route no longer needs these nodes or their modules for this item:

- `lem-pur-sheaf-hom-cover-gluing` /
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`.
  The global scalar-extension map is obtained by adjunction; invertibility is
  detected on the cover, so its maps and inverses need no separate Hom gluing.
- `lem-weil-pbc-ringed-topoi-module-pullback-tensor` /
  `Sheaf.CategoryTheory.ModulePullbackTensorIso`.
  The existing source-library pullback/scalar-extension isomorphism and a proved
  adjunction calculation provide the exact comparison needed here.
- `lem-weil-pbc-site-module-sheaf-gluing` /
  `Sheaf.CategoryTheory.SiteModuleSheafGluing`.
  The kernel constructs the underlying global subobject and its factorization
  property lifts the action directly.

Separate diagonal and triple-overlap cocycle equations are unnecessary for this
route: all local comparisons commute with monomorphisms into the same ambient
sheaf. The remaining finite-stage arithmetic uses pairwise comparisons and their
inverse identities. The finite coefficient fields, internal/sectionwise
comparison, qcqs calculus, covering, and weakly-etale localization remain relevant
through the statements or the smaller obligations; they are not claimed pruned.
The old direct dependencies
`def-weil-finite-subextension-directed-set`,
`def-weil-pbc-condensed-e-module-category`,
`def-weil-pbc-internal-abelian-sheaf-module-equivalence`, and
`lem-weil-pbc-proetale-qcqs-fp-section-calculus` move to the arithmetic node's
statement or proof plan. They are removed from this item's direct proof dependencies,
not pruned from the arithmetic argument or claimed removed from the target closure.
The five-target unit route is retained.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or weakened. The earlier DAG plan asked for general
module-sheaf gluing plus separate gluing of scalar-extension maps and inverses.
For local models embedded in one ambient module, this can be replaced by the
kernel construction and cancellation. This also avoids separately descending
triple-overlap equations.

The internal/sectionwise equivalence is proved in the library, but its statement
alone does not supply all localization/scalar-comparison coherence in one Lean
application. The delivered proof instead proves the exact scalar-adjoint formula
it uses. The returned delivery incorrectly retained a copy of the source-library
weakly-etale base-change proof. Return at head `a5958f2ef` identified its duplicate
`kernelOverlap_lowerStar_obj_obj_map` theorem. On current main, the legacy
functor modules re-export the canonical coefficient implementation. Therefore
`ProEtaleLocalQuotientVanishing` now imports
`WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale` directly and uses
`squareLowerStarIso` and `isIso_baseChangeMap_of_isPullback`. The copied
`Sheaf.AlgebraicGeometry.ProEtaleKernelOverlapBaseChange` module is removed from
the sandbox delivery in full, including the rejected duplicate lemma. This module
never landed and does not exist on current main, so there is no repository module
to withdraw through `deleted.txt`. The retained base-change node now attaches to
the existing source-library theorem. The square comparison is still matched to
the mate of `upperStarCompIso` by the proved conjugation calculation; naturality
and the mates unit equation prove the local quotient vanishing calculation.

## New nodes

`lem-weil-pbc-condensed-finite-local-submodules`:
`Sheaf.Paper.CondensedFiniteLocalSubmodules`; finite arithmetic overlap descent,
with the remaining arithmetic hole described above.

`def-weil-pbc-proetale-local-submodule-gluing-data`:
`Sheaf.AlgebraicGeometry.ProEtaleLocalSubmoduleGluingData`; real structure of a
global module, inclusion and compatible local module identifications.

`lem-weil-pbc-proetale-compatible-local-submodules`:
`Sheaf.AlgebraicGeometry.ProEtaleLocalSubmoduleGluing`; proved lifting of the
module action through the glued underlying abelian subobject.

`def-weil-pbc-proetale-local-subobject-kernel`:
`Sheaf.AlgebraicGeometry.ProEtaleLocalSubobjectKernel`; actual kernel construction
and proved inclusion, monicity, comparison, factorization and inverse-criterion API.

`lem-weil-pbc-proetale-local-quotient-vanishing`:
`Sheaf.AlgebraicGeometry.ProEtaleLocalQuotientVanishing`; proved local overlap
vanishing calculation, including the
compatibility of the relevant mates. Monicity is not needed for this equation.

`lem-weil-pbc-proetale-local-subobject-kernel-effective`:
`Sheaf.AlgebraicGeometry.ProEtaleLocalSubobjectKernelEffective`; proved deduction
of canonical comparison invertibility from vanishing and the kernel API.

`lem-weil-pbc-proetale-compatible-local-subsheaves`:
`Sheaf.AlgebraicGeometry.ProEtaleLocalSubsheafGluing`; proved assembly of the
constructed kernel, its local isomorphisms, and its factorization property.

`lem-weil-pbc-coefficient-site-weakly-etale-base-change`:
reuses the existing
`AlgebraicGeometry.ProEtale.isIso_baseChangeMap_of_isPullback` in
`WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale` directly. Its Lean
attachment and proof route now record that reuse. It adds no Lean module or
statement.

Change record: `coord/changes/A3-condensed-local-model-gluing-proof-scope.md`.
It documents the proof-local opens, private-helper section variables, and local
irreducibility attribute requested by the static preflight; no existing
mathematical interface is changed.

## Earlier second reading (a previous round; superseded)

1. **Interfaces — pass.** Compared every delivered path with the shared repository.
   Only the item module and its existing node replace repository files; the eight
   supporting modules and nodes are new. Extracted the original theorem signature
   and compared it byte for byte: identical. No existing definition or target
   statement changes. The change record documents only proof-local elaboration
   commands, with no forced adaptations.
2. **Proofs and constructions — pass as a decomposition.** Compiled all nine
   modules in dependency order through `lcompile.py --all`, then audited a scratch
   importer with `#print axioms` for the kernel definitions and API, base change,
   overlap vanishing, subsheaf gluing, module gluing, arithmetic theorem, and item
   theorem. The constructions and all proved gluing declarations use only
   `propext`, `Classical.choice`, and `Quot.sound`; only the arithmetic theorem and
   its caller additionally use `sorryAx`. The sole textual hole is the named
   arithmetic theorem reported above. No forbidden declarations or hollow
   definitions occur. The global underlying object is a categorical kernel;
   its action factor is unique by the monic inclusion and is obtained from a
   proved factorization theorem. No arbitrary data are chosen from an unproved
   existence theorem.
3. **Split statement — pass.** Read the arithmetic statement, its complete
   docstring argument, and its node against the upstream object-descent discussion.
   Checked the empty cover (choose F = E), zero local modules, and the identity
   singleton cover. Pairwise overlap comparisons and their inverse equations are
   the finite arithmetic obstruction; the statement asserts no global object or
   effective gluing. The separate kernel and action proofs supply those operations,
   so this is a strict reduction rather than a renamed original theorem. Repeated
   LeanFinder, Loogle, and grep searches with filtered-field descent and faithful
   flatness queries, and searched the project sources. Loogle found the general
   adjunction monicity instance assuming reflection of monomorphisms, but it does
   not provide the internal coefficient reflection or finite overlap descent.
   The other hits concern ordinary module/sheaf finite presentation and faithfully
   flat algebraic descent, not this exact interface. Closing the remaining hole
   requires the internal/sectionwise and coefficient-colimit coherence, beyond a
   few-minute repair.
4. **Route and pruning — pass.** Read the adjunction reduction downward through
   module-action lifting, the actual kernel, effectivity, quotient vanishing, and
   the coefficient-family adaptation of the existing weakly-etale base-change
   proof. The existing scalar/pullback comparison is reused by a proof-only
   `import all`; there is no duplicate comparison construction. Corrected the
   removed-import list against the actual repository diff and explicitly named
   all old direct dependency nodes that move to the arithmetic plan. The
   `sk-thm-properbasechange` unit's `realized` statement and three steps are
   untouched: this only changes an auxiliary descent argument below the unit.
5. **DAG — pass for this delivery.** Checked every attached Lean statement occurs
   verbatim in its delivered module, each proof-dependency set equals the union
   of its proof steps' uses, and every new node has the required creation, source,
   blueprint, unit, chapter, search, and Lean fields. The existing node's new
   plan follows the actual adjunction/kernel reduction. The eight supporting
   nodes describe their construction/proof APIs; only arithmetic retains an
   unproved plan. A further traversal found a pre-existing cycle among unrelated
   condensed-local-triviality/coefficient-realization nodes in the shared DAG;
   none of its edges is changed here. This is reported for the maintainer rather
   than repaired outside this delivery's scope.

Second-reading changes: made the proof-only `Adjunction.Unique` import non-public
in `ProEtaleKernelOverlapBaseChange`; gave its two copied continuity instances
explicit `kernelOverlap_` names so they do not duplicate the anonymous instance
names of the source weakly-etale module; corrected the change record's old open
command (the repository did not open `Opposite`); corrected the pruning report
against the repository and made the dependency transfer explicit. No mathematical
statement, definition construction, or proof argument was changed.

## Second reading by A3

1. **Interfaces — pass.** Compared the delivered item module with the shared repository and
checked the original theorem signature byte for byte. Existing declarations retain their
signatures; all supporting modules and nodes are newly delivered, and the change record only
covers proof-local commands and imports.

2. **Proofs and constructions — pass as a decomposition.** Compiled every delivered module
with `lcompile.py --all` and the item separately. The only remaining `sorry` is the named
finite-coefficient compatibility theorem in `Sheaf.Paper.CondensedFiniteLocalSubmodules`.
No forbidden declarations or hollow definitions occur. The global subobject is an actual
categorical kernel, and the module action is obtained by the proved factorization property.
The proved declarations use only the permitted axioms; the arithmetic theorem and its caller
retain `sorryAx` through the explicitly reported split.

3. **Split statement — pass.** The remaining arithmetic statement is strictly below the
original gluing target: it asserts only a common finite coefficient stage, monic local
adjoints, local invertibility, and pairwise overlap comparisons. It asserts no global object
or effective gluing. Empty covers, zero modules, and the identity singleton cover satisfy the
statement (with `F = E` where appropriate). Searches of the library and Mathlib found no
existing declaration supplying the finite overlap descent and coefficient reflection needed
to close it quickly.

4. **Route and pruning — pass.** The proof follows the retained unit route through finite
coefficient descent, compatible subobject gluing, action lifting, scalar adjunction, and
cover detection. The kernel construction replaces separate Hom and module-sheaf gluing while
preserving the unit-level route. Removed proof-only imports and the old direct dependency
nodes are listed above; the canonical weakly-etale base-change theorem is reused directly.

5. **DAG — pass.** Checked that attached statements occur verbatim in the delivered Lean
modules, that each `proof` and `proof_deps` follows the implemented route, and that the new
nodes carry the required source, blueprint, unit, Lean declaration, and split/proved status.
The item node records the decomposition and the retained unit route. No target statement was
changed.

**Changes made during this second reading:** added this required review section; no Lean proof,
definition, statement, import, or node was changed.
