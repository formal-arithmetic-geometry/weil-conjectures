## Worker report

### Maintenance resolution on 2026-10-24 (supersedes the blocker and packet-scope notes below)

Server commit `5edc0085370` prelanded the two definition nodes/modules and the
return-authorized downstream cover refactor. It was committed under the merge lock
as Bin Wu after per-file tools/lean_file.sh compilation (3.3 s, 6.5 s, 36.9 s),
import checks and changed-node DAG validation. The definition nodes and their
shared predicates now exist on the base. The cover node also cites both owners in
stmt_deps; no cyclic dependency was added. Its theorem signature and single sorry
are unchanged. Its unused proof import of this pending comparison statement was
deferred until that statement lands.

The cover node/module have been removed from this delivery sandbox after retaining
`.maint-NR-1792836891.bak` copies. The remaining packet is the unchanged comparison
module, its item node, and the two landed definition nodes/modules. All mathematical
statement checks below remain current; references below to four modules in the
packet and the ownerless-module refusal describe the earlier, superseded packet.
The normal deliver2.py dry run can now validate the item without a downstream node.
Do not restore the cover files or add a cover-theorem dependency to this item.

The server root disk was also full. Inactive old DAG cache entries were backed up
as .bak files and reclaimed; a 4096-byte truncated unrelated Rank.lean was backed
up, restored from HEAD and compiled successfully. No launcher, review or landing
tool was changed. Full maintenance details are in the maintenance REPORT.md and
server coord/reports/NR/closed-row-ownership-maintenance.md.


The item is stated in `Sheaf.AlgebraicGeometry.ClosedRestrictionTotalPullback`, main
`AlgebraicGeometry.closed_restriction_total_pullback`. Its three additional theorem
statements are `finiteClosedAugmentedRows_exists`, `closedRestrictionComparison_unique`,
and `closedTotalComparison_naturality`. All four proofs are `sorry`, with source and
stepwise natural-language proofs. The definition module has no `sorry` and selects no
data from an existence theorem. The original item statement is unchanged.

Repair of returned immutable head `19766f6117ab`, F1 and F2: the comparison
statement and its entire Lean module are byte-identical to the returned version.
The change is ownership and sharing of its constructions. Current main was read
without Git commands, and the live cover module was read with scompile.py --source;
it agrees with the read clone used for the refactoring. The original item on main
has no Lean record, so its current non-owned metadata was preserved while restoring
the repaired attachment and adding the two owning definition nodes.

F1: all thirteen shared helpers and instances were MOVED from
`FiniteClosedCoverResolution` to the new definition module
`FiniteClosedRowConstructions`. Their declaration names, signatures and executable
bodies are identical (checked textually for each declaration). Their only source
text alteration is the owning blueprint tag. The old copies are removed. Both the
item and the augmented-row definition cite `def-sfb-finite-closed-row-constructions`
in stmt_deps. The augmented-row module imports that construction module, never the
cover theorem. The item imports the augmented-row module. The cover theorem module
now imports the row module publicly and this item as a proof import. Thus a stage-3
proof can use the comparison theorem with no import inversion. No DAG edge to the
downstream cover theorem was inserted to disguise the problem.

F2: `FiniteClosedResolution` now EXTENDS `FiniteClosedAugmentedRows`, keeping only
its quasiIso, derivedIso and derivedIso_hom fields; all row fields are inherited.
It therefore supplies the ambient restriction fields already belonging to the
unit-normalized row notion as well. `finiteClosedPullbackRowFormula` is now a thin
alias of `FiniteClosedAugmentedRows.RowFormula`, ignoring the redundant nonempty
proof only when passing the existing all-subsets cs family. The cover's total clause
uses `TotalFormulaOn` with the identity functor on complexes. `TotalFormula` for
the comparison is a transparent specialization of that SAME predicate to Plus.ι.
The diagonal equation is defined once. No mathematical clause, covering condition,
exactness condition, or comparison normalization was removed or weakened.

The authorized downstream cover repair changes ONLY that node's lean record, with
an explanatory lean.note and declarations list excluding every relocated helper.
Its original statement, proof split, stmt_deps, proof_deps and all other metadata
are preserved. Its theorem still has the same signature and a sorry proof.

Hypotheses and objects, clause by clause:

- `X Z : Scheme.{u}`, `i : Z ⟶ X`, `[IsClosedImmersion i]` render the scheme and
  ambient closed subscheme. `m : ℕ`, `hm : 0 < m` render the nonempty ordered family.
- `W : Fin m → Over X`, `hclosed`, and `hfactor : ∀ a, Nonempty (W a ⟶ Over.mk i)`
  render the individual closed immersions and their factorization through Z. Indexing
  by Fin m instead of 1,...,m merely shifts the labels; signs depend on ordered position.
- `hqc` and `hqcW` explicitly assert quasi-compactness of each complementary open
  immersion, with the complementary-set equations. No hypothesis of covering occurs.
- `A : Sheaf (ProEt.topology X) CommRingCat.{u+1}` and
  `ProEtaleTensorComparison.Modules A` are the actual recorded ring/module sheaves.
  The site keeps object universe u+1 and morphism universe u; no universe equality
  or smallness restriction on test schemes is introduced.
- `finiteClosedIntersection W s` is the existing product in Over X, equivalently
  the scheme-theoretic iterated fibre product. `finiteClosedRestriction` is the
  actual inverse image followed by actual direct image, never a free endofunctor.
  `finiteClosedUnit` uses `ProEtaleClosedProjection.adjunction`, the recorded
  sectionwise unit-normalized adjunction, rather than an arbitrary adjunction.
- `FiniteClosedAugmentedRows` specifies rows WITHOUT the quasi-isomorphism fields of
  the existing `FiniteClosedResolution`. `restriction_unit` and `ambient_unit` fix
  the actual face maps after inverse-image composition: the pushed actual units
  have precisely these equations, and epimorphic units make the solutions unique.
  Noninclusions are assigned zero only as an indexing convenience.
- `terms` identifies each degree with existing `finiteClosedTerms`, the finite
  product/biproduct indexed by increasing tuples. `differential` uses the existing
  signed deletion formula `finiteClosedDifferential`. `support` sets the other
  columns to zero. The rows are actual cochain complexes, so d²=0 is part of their
  type. Their functoriality and the `additive` field give natural additive rows.
- The degree -1 term is kept as the augmented object `finiteClosedRestriction i A`.
  `augment_unit` is exactly the singleton-unit equation after eta_Z. `totalAugment`
  and `totalAugment_f` fix the chain augmentation by the (0,n) diagonal inclusion.
  The existence theorem states that these row data exist under the original
  geometric hypotheses, without covering or exactness; consumers do not have to
  assume an unavailable resolution.
- `g : Y ⟶ X` is arbitrary. `ProEtaleTensorComparison.inverseRing g A` is precisely
  g^-1 A. `finiteClosedPullbackFamily` uses chosen scheme fibre products; its
  intersections are the canonical presentations of the base-changed intersections.
- `c` and `hc` render the supplied comparison and unit equation for ambient Z.
  `cs : ∀ s, s.Nonempty → ... ≅ ...` and `hcs` render ONLY nonempty-subset comparisons
  and their equations. In particular no comparison is required at the empty subset.
  Functor composition is written in Lean order E_T followed by g*, matching g*E_T.

Conclusions, clause by clause:

- The first conjunction of the main theorem is the natural-transformation square
  for every nonempty s ⊆ t. Its second conjunction gives the corresponding square
  for r_Z,s, not just for singletons.
- `∃! σ : ... ≅ ...` gives the natural row chain isomorphism. `RowFormula` tests it
  on every finite-product projection, exactly the direct sum of cs. The next
  conjunct is its degree -1 augmentation square, using c at Z.
- `∃! τ : Plus.ι ⋙ ... ≅ Plus.ι ⋙ ...` gives the unique natural chain isomorphism
  on bounded-below complexes, with no row exactness assumption. `TotalFormula`
  gives its value after every actual `g*.map (ιTotal ...)`, with p+q=n and the
  corresponding component of σ. Thus this is the specified totalized map rather
  than an arbitrary map between isomorphic totals.
- `finiteClosedDouble` applies rows termwise then flips, so p is horizontal and
  the recorded ordinary total has differential d_D + (-1)^p d_K. All diagonal
  summands beyond the finite horizontal strip vanish. These constructors are
  reused unchanged from the existing module.
- The following equality of natural transformations is exactly
  τ g*alpha = alpha' c_Z, with termwise c_Z expressed by
  `NatTrans.mapHomologicalComplex c.hom`.
- The last clause is conditional on BOTH augmentations being quasi-isomorphisms.
  Its `e` is an isomorphism whose HOM IS REQUIRED TO EQUAL Q(g*alpha), not an
  arbitrary derived comparison. Its inverse is therefore exactly Q(g*alpha)^-1.
  The final equation is e.inv ≫ Q(c_Z) ≫ Q(alpha'), the displayed normalization
  in Lean's left-to-right composition order. This supplies an actual derived
  isomorphism, not merely isomorphisms of individual cohomology objects.
- Naturality in modules and complexes is intrinsic to the natural transformations
  and natural isomorphisms, not an objectwise Nonempty claim. The supplemental
  `closedRestrictionComparison_unique` states epi-cancellation uniqueness for any
  two unit-normalized comparisons. Applied after the canonical coefficient
  compositors, it identifies successive pullbacks with a separately supplied
  composite comparison, including the identity case.
- `closedTotalComparison_naturality` explicitly gives the total comparison square
  for every compatible morphism of bicomplex data, in arbitrary preadditive
  categories with the required diagonal coproduct preservation. Here b and e are
  the componentwise comparison isomorphisms, mu and nu the compatible data maps.
  Its totalized map is `mapTotalIso.inv` followed by `total.map`, characterized by
  exactly the diagonal formula in the main theorem. Applying its equation to
  arrows of a small parameter category gives diagram naturality; to automorphisms
  gives equivariance; and to composite pullback component comparisons, together
  with unit uniqueness and total functoriality, gives identity/composition/
  associativity coherence. Inversion and Q preserve these equalities. No existence
  of closed base change is asserted for arbitrary g without c and cs.

Dependency interfaces read and used:

- Mathlib `AlgebraicGeometry.Scheme`, `Scheme.Hom`; `Scheme.ProEt`, `ProEt.topology`;
  `IsClosedImmersion`, `IsOpenImmersion`, `QuasiCompact`; and `Limits.pullback` and
  its projections. Read the actual source definitions and their module docstrings.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, `proEtaleModuleInverseImage`,
  `proEtaleSheafInverseImage`, `proEtaleBaseChange` and the module-model transport.
- `Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection`,
  `ProEtaleClosedProjection.adjunction` and its uniquely normalized unit signature.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`, `proEtaleRingedDirectImage`,
  `proEtaleModuleCoefficients`, and `proEtale_ringed_open_closed` for epi units.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`, Q and its
  localization/inversion interface; the ordinary cochain complexes and Plus category.
- `WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap`, `mapTotalIso`,
  `map_ι_mapTotalXIso_inv`, and `mapTotalIso_inv_naturality`, read in full.
- Proof imports: `Sheaf.AlgebraicGeometry.ClosedImmersionProducts`,
  `closedImmersion_comp_products_and_finiteType_openImmersion`;
  `Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`,
  `GeometricMorphism.geometric_inverse_image_exact`; and Mathlib
  `Functor.preservesHomologyOfExact` and quasi-compact base change.
- Shared helpers are now OWNED by `def-sfb-finite-closed-row-constructions`,
  module `Sheaf.AlgebraicGeometry.FiniteClosedRowConstructions`:
  finiteClosedRestriction, finiteClosedRestriction_zero, finiteClosedUnit,
  finiteClosedIntersection, finiteClosedTerms, finiteClosedTermProjection,
  finiteClosedDifferential, finiteClosedAllTotal, finiteClosedDouble,
  finiteClosedTotal, finiteClosedInverseZero, finiteClosedPullbackComplex,
  finiteClosedPullbackFamily. Their actual bodies were relocated unchanged.
  Neither this definition module nor the augmented-row definition nor the item
  imports FiniteClosedCoverResolution. Only the downstream cover theorem imports
  the item and shares these definitions by importing the row definition.
- `lem-sfb-closed-restriction-signed-refinements` currently has no recorded Lean
  module. No nonexistent import is inserted: the row-existence theorem here
  states directly the construction already asserted in this item's statement,
  with the same signed-row proof. No refinement theorem is assumed.

Source and edge-case checks:

Read Stacks proetale.tex lemma-ses-associated-to-open (09AH), which assumes only
quasi-compactness of the complementary open and gives epimorphic actual closed
units. Read homology.tex lemma-double-complex-gives-resolution (0133) for the
ordinary total and augmentation conventions. Read the CURRENT blueprint direct
images statement and proof under literature/blueprint/latest: this technical
comparison is an agent deduction supporting paragraph (3), not the unit's own
statement. Its inherited ancestor is null, confirmed by blueprint_refs ancestor.

Checked m=1, negative horizontal degrees, p≥m, zero modules/complexes, empty X or Z,
empty or repeated closed members, empty nonempty-index intersections, i_a=i,
non-covering families, and g=id. Nonempty subsets may have an empty intersection
scheme: no Nonempty assertion on that scheme is present. Tuple projections use
Nonempty of the index FINSET only. Empty tuples never require a supplied comparison.
Neither reducedness, Noetherianity, constructibility, flat coefficients, finite
coefficients, nor a covering appears. The quasi-isomorphism equation is conditional,
so it imposes no false exactness claim on non-covering families.

Searches made through prescribed msearch.py and rg:

- LeanFinder: "Unit compatible closed restriction comparisons induce natural
  isomorphisms of finite total complexes under pullback": eight restriction and
  total-inclusion hits; none states this comparison from unit equations.
- Loogle: "HomologicalComplex₂.total.mapIso, HomologicalComplex₂.mapTotalIso":
  zero hits, the latter upstream identifier unknown to the service. Follow-up
  `"total", "mapIso"`: total.mapIso and its hom/inv equations, three hits;
  these require an existing bicomplex map and do not prove the closed-unit squares.
- Mathlib grep: closed.*restriction.*total|closed.*[Uu]nit.*[Cc]omparison in
  Algebra/Homology: zero hits. The more specific augmented-row grep also zero.
- rg over WeilConjectures and Sheaf for closed restrictions, signed refinements,
  the item id, finiteClosedTerms and FiniteClosedAugmentedRows: found the finite
  cover module's reusable helpers and exact resolution structure, no statement
  of the item and no row interface without exactness. No upstream item-id hit.
- LeanSearch on the missing row notion: eight unrelated measure/topology/finite
  morphism results, listed in the new node's mathlib_searches. blueprint_refs search
  "augmented row" and "finite closed": zero blueprint nodes. DAG search found the
  cover-resolution lemma, which already refers to this item as a proof input, not
  a separate definition of augmented rows without exactness.

Server verification: all FOUR delivered modules compiled separately in dependency
order through scompile.py under the unchanged 60-second limit, with no errors or
unexpected warnings. Final library checks: construction module 9.6 seconds, row
module 17.5 seconds, unchanged comparison module 22.8 seconds, repaired cover module
27.1 seconds. The cover compile validates the inherited fields, shared row predicate,
shared total predicate and the now-correct proof import of this item. Both definition
modules contain no sorry. The item retains four and the cover theorem retains one.
No local build, no global build, and no direct edits or Git commands in the shared
repository. No STATEMENT-DISPUTED finding and no statement correction.

## New nodes

`def-sfb-finite-closed-row-constructions` owns the thirteen constructions and instances
listed above in `Sheaf.AlgebraicGeometry.FiniteClosedRowConstructions`. Source: the
item's actual-unit signed-row construction and total convention, Stacks 09AH and 0133.
These exact helpers were found in the existing cover theorem module; this is their
relocation under a definition owner, not an alternative definition. The old copies
are removed by the same packet. The node is cited by both the item and the augmented
row definition; it cites the scheme, site, module, inverse image, normalized adjunction,
fibre product and ordinary-complex definition nodes. There is no theorem dependency
on the downstream cover theorem or on the item. The original three-kind searches are
supplemented by new LeanSearch, Loogle, and grep searches stored on this node.
LeanSearch returned generic sheaf pullback/pushforward adjunction and unit results;
Loogle returned generic total.mapIso; Mathlib grep found zero finiteClosed* hits.
Project grep found precisely the thirteen helpers being moved; blueprint_refs search
"finite closed row" found zero blueprint nodes.

`def-sfb-finite-closed-augmented-rows` owns `FiniteClosedAugmentedRows`, RowFormula,
TotalFormulaOn and TotalFormula in `Sheaf.AlgebraicGeometry.FiniteClosedAugmentedRows`.
Source: the item's displayed signed row and actual augmentation, 09AH for units and
0133 for the total convention. It imports and cites the new construction owner.
The original exact resolution is now an extension of this same structure, rather
than an independent copy of the row fields. RowFormula is the single projection
formula; TotalFormulaOn defines the single diagonal equation after any complex-valued
functor, and TotalFormula specializes it to bounded-below complexes. The cover theorem
uses the same predicates on its inherited parent data. These are explicit data fields
and predicates with no proof or chosen data from an existence theorem.

## Dependency modules

`lem-sfb-finite-closed-cover-resolution`: F1/F2 of the maintainer's immutable-head
return explicitly requests a lean-only repair of this DOWNSTREAM consumer under §1(B),
or reporting the delivery tool's refusal. Its old module could not import its own
comparison proof input because that input imported its helpers; and its resolution
structure and comparison formulas duplicated the row definitions. The supplied module
now imports the shared row definitions, inherits them through `extends`, reuses both
comparison predicates, and imports the comparison theorem as a proof dependency.
The theorem's statement and sorry proof are unchanged. Its lean.declarations now lists
only its nine remaining declarations, with lean.note documenting the relocation and
interface sharing. No stmt_deps or proof_deps is changed on this downstream node,
and the item does not cite it (doing so would create a DAG cycle). The current delivery
includes this node solely to carry the return-authorized module update and lean record.
The maintainer should attach the new definition owners to the cover node's stmt_deps
when integrating ownership, if required; that non-lean edit is deliberately not smuggled
into this §1(B) packet.

## Second reading by NR

Separate self-check of the original node, immutable returned comparison source, four
repaired modules and the current cover node/source; no other agent was started.
The previous head's clause-by-clause statement match is preserved: item Lean source
byte-identical; rows still mean actual E_T, signed differential and unit augmentation;
nonempty comparisons exclude no empty intersection scheme; Plus.ι restricts only
complexes as in the node; e.hom=Q(g*alpha) still fixes the derived inverse exactly.
No covering or exactness hypothesis was added to the comparison or row existence.

For F1, checked every relocated declaration body is identical to the old cover source,
that every helper has exactly one module and node owner in the packet, and that there
is no import of the cover theorem anywhere below it. The cover theorem now successfully
compiles after importing this item. Current-base node comparison confirms the cover
node changes only in lean and the item only in lean and two added definition stmt_deps.
For F2, checked no copied row fields remain in FiniteClosedResolution: only three
exactness/derived fields remain after extends. The projection equation occurs only in
RowFormula; the cover's old name delegates to that predicate. The diagonal equation
occurs only in TotalFormulaOn; both consumers specialize it. All four files passed
server compilation separately, including all inherited-field consumer uses. Existing
edge cases and all accepted normalization equations remain as described above.

## Delivery tool refusal for the return-authorized downstream repair

The completed F1/F2 packet was compiled successfully (all four files) and submitted
to the prescribed `deliver2.py NR lem-sfb-closed-restriction-total-pullback --no-push`.
The server preflight rejected it with one enforced reason:

> (c) lean/Sheaf/AlgebraicGeometry/FiniteClosedCoverResolution.lean: no node of the
> delivery has it as lean.file (every module is the module of the item, of a new
> definition node or of a dependency node)

Its preceding advisory gives the cause:

> dag/nodes/sec-six-functors-basics/lem-sfb-finite-closed-cover-resolution.json:
> the node lem-sfb-finite-closed-cover-resolution exists on the base and is not in
> the item's statement/proof prerequisite closure on the base or as delivered:
> a delivery changes only the item, new definition nodes and dependency nodes of
> the item

The packet DOES include that node and its lean.file exactly matches the repaired
module. The tool excludes the node before assigning module ownership because it is
a downstream consumer, not a prerequisite. F1/F2 explicitly authorizes this exact
lean-only consumer repair under §1(B), or reporting the merge tool's refusal. There
is no valid added dependency edge to make it a prerequisite: its proof_deps already
contains this item, so that would introduce a cycle. Dropping the consumer module
would leave duplicate helper declarations and the unresolved import inversion.
No tool was patched, no ownership was misrepresented, and no push was attempted.
The complete compiled repair remains in the sandbox for a maintainer-authorized
consumer-repair landing or a correction of the delivery tool's classification.

### Dispatcher retry on 2026-10-24

Retried the prescribed dry run against the retained F1/F2 repair without changing
its mathematical statements or ownership. The wrapper checked the four Lean files
on the server and again exited 1 at preflight, with the same enforced reason (c)
and the same downstream-node advisory quoted above. It additionally reported:
`delivery is based on 17495e4dd (sheaf-dag has moved on); checked against that base`.
The wrapper staged all four node records and all four Lean modules, including the
cover node whose lean.file names the rejected module. It printed `PREFLIGHT FAILED,
nothing pushed`. Thus the authorized repair remains blocked by delivery ownership
classification; another unchanged push cannot repair that classification. No launcher
file was modified and no push was attempted in this retry.

### Dispatcher retry 3 on 2026-10-24

Compared the retained packet with the current read clone: both definition nodes
remain new; the item differs only in lean and the two definition-owner stmt_deps;
the cover node differs only in lean. The item Lean source is byte-identical to the
returned baseline, and the repaired cover module imports the item in the permitted
proof direction. No Lean code needed another change or compilation after its prior
successful four-file server compile.

Retried `deliver2.py NR lem-sfb-closed-restriction-total-pullback --no-push`.
It staged every repaired module and node, then exited 1 with the same enforced
reason (c): FiniteClosedCoverResolution.lean has no eligible owning node. Its
advisory again excludes the included cover node because it is downstream rather
than in the prerequisite closure. This run reported base `7bb19ceb0` and
`PREFLIGHT FAILED, nothing pushed`. The return-authorized downstream repair is
therefore still refused by the tool; no push or tool modification was attempted.

### Dispatcher retry 4 on 2026-10-24

Rechecked the retained packet against the current read clone: both definition nodes
are still new, the item changes only lean and definition-owner stmt_deps, and the
cover node changes only lean. The item Lean source still matches the returned
baseline byte for byte. The four repaired modules retain their successful server
compile results; no Lean source changed in this retry.

The prescribed dry run was repeated and exited 1 with the same single enforced
reason (c): FiniteClosedCoverResolution.lean has no eligible owning node. All four
node files and all four Lean modules were staged, but the preflight advisory again
excluded the included cover node because it is outside the item's prerequisite
closure. This run printed `PREFLIGHT FAILED, nothing pushed` and did not report a
stale-base warning. The return-authorized downstream repair remains refused by
module ownership classification. No push or launcher modification was attempted.

### Dispatcher retry 5 on 2026-10-24

Compared the retained repair with the current read clone again: the two definition
nodes remain new; only lean and the definition-owner stmt_deps differ on the item;
only lean differs on the downstream cover node. The item Lean file remains
byte-identical to the returned baseline. No Lean source changed since the successful
four-module server compilation.

The prescribed dry run exited 1 again. All repaired node records and modules were
staged, but the downstream cover node was excluded from eligible ownership for
being outside the prerequisite closure. The single enforced reason remains (c):
FiniteClosedCoverResolution.lean has no eligible owning node. The wrapper printed
`PREFLIGHT FAILED, nothing pushed`. F1/F2 explicitly permits reporting this tool
refusal; making the cover node a prerequisite would create the prohibited DAG cycle.
No launcher file was changed and no push was attempted. The completed repair and
all refusal evidence remain here for maintainer integration or a tool correction.

### Further dispatcher retry on 2026-10-24

After the fifth refusal was returned, retried the prescribed dry run again.
It staged all four node records and all four modules and exited 1 with the same
single enforced reason (c), rejecting FiniteClosedCoverResolution.lean as having
no eligible owning node. The preceding advisory again excludes the supplied
cover node for being downstream. This run checked base `fb4db9b6e` and printed
`PREFLIGHT FAILED, nothing pushed`. Comparison with the refreshed read clone
still shows only lean changes on the cover node, lean and owner stmt_deps on
the item, and the two new definition nodes. The item source remains byte-identical
to the returned baseline. No Lean source changed, no launcher was modified,
and no push was attempted. Maintainer/tool intervention remains necessary to
accept the explicitly authorized downstream lean-only repair.

### Latest dispatcher retry on 2026-10-24

The prescribed dry run again staged all four modules and node records, then exited
1 with the identical enforced reason (c): FiniteClosedCoverResolution.lean is
ownerless because the supplied downstream cover node is excluded from eligible
ownership. It printed `PREFLIGHT FAILED, nothing pushed`; no stale-base warning
was present. Current-source comparison still confirms the item source matches the
returned baseline, both definition owners are new, and the cover node changes only
lean. No Lean code changed after the successful four-module compile. This is the
same unresolved tool refusal explicitly allowed to be reported by F1/F2, not an
unrepaired mathematical statement. No push or launcher modification was attempted.
### Latest full compile and delivery retry

Reran the prescribed scompile.py with all four modules in dependency order.
All four library compiles and the sandbox probes passed with no errors or
unexpected warnings. The reported library times were 9.6 s, 17.5 s, 22.8 s,
and 27.1 s for the constructions, rows, item and cover modules respectively.
The current-clone comparison still shows only lean and owner stmt_deps changes
on the item, only lean on the cover node, and the two new definition nodes.
The item source remains byte-identical to the returned baseline.

Reran the prescribed deliver2.py --no-push after this compile. It staged every
module and node, then exited 1 with the same single enforced ownership reason
(c), rejecting FiniteClosedCoverResolution.lean because it excludes the included
downstream cover node from eligible owners. It printed `PREFLIGHT FAILED,
nothing pushed`. The maintainer-return-authorized downstream repair is complete
and compiles, but its delivery is still refused by this tool classification.
No tool was changed and no push was attempted.
















### Most recent repeated dispatcher check

The prescribed dry run again staged all four modules and node records, then
exited 1 with the unchanged enforced ownership reason (c): the supplied cover
node is excluded as downstream, leaving its module without an eligible owner.
It checked base `8a2380ade` and printed `PREFLIGHT FAILED, nothing pushed`.
Current-clone comparison confirms only lean changes on the cover node, lean and
owner stmt_deps on the item, and both definition nodes new. The item source
matches the returned baseline. No Lean source changed after the successful
four-module server compile. No push or tool modification was attempted. The
explicitly authorized downstream repair remains refused by ownership classification,
as F1/F2 permits reporting.

## Maintenance prelanding resolves the delivery refusal

Current main now contains both definition nodes and their modules byte-identical
to this repair, and the cover module contains the requested extends refactor and
shared RowFormula/TotalFormulaOn predicates. Maintenance added both owner nodes
to the cover node's stmt_deps. Its lean.note explicitly says it prelands these
shared definitions before this returned comparison delivery and defers the proof
import until the theorem lands. The sole cover source difference is that deferred,
currently unused proof import. Maintenance also removed the downstream repair
from the sandbox delivery paths, retaining .maint-NR backups.

Removed the already-prelanded definition modules and records from delivery paths,
preserving copies under baseline. The remaining item module is unchanged from
the accepted returned source and imports the landed row definition. Its stmt_deps
cites both owning definition nodes. F1 and F2 are now satisfied using maintenance's
prelanding without another downstream edit. Earlier ownership refusals above are
historical and superseded by this prelanding.

## Final verification after prelanding

scompile.py compiled the comparison against the current server sources, including
both landed definition modules, successfully (2.8 s, 4.7 s, 19.1 s respectively).
The wrapper reported a local full-disk error, then its prescribed current-server
fallback completed with exit 0. The reduced delivery's dry run subsequently
passed preflight and compile: `OK (dry run): commit 5e673b80a1b passes the preflight
and compiles; nothing pushed`. Only the item node, its unchanged Lean statement
module and this report are included in the final packet.
