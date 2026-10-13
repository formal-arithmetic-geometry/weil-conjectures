## What changed

Repair of reviewer X-06699 at head 06699c37e, C3/C4: replaced both proof-plan
citations of the existence-only signed-dual equivalence. The representative
node now constructs the normalized evaluation map on the cocycle quotient,
proves its kernel and surjectivity using the actual module homology quotient,
and invokes Mathlib's Ext/cocycle roof formulas. The independence node now
cancels the augmentation and shift, reflects equality by Qh_map_bijective,
and extracts the top coboundary. Projectivity and the strict bound 0 are
explicitly justified. Both proof_deps are recomputed as unions of step uses.
Added four Mathlib API leaf nodes, without new Lean modules or holes. Updated
both split theorem docstrings to agree. Every delivered Lean signature and
proof is preserved; this repair changes documentation and DAG records only.

Repaired the already disputed `ExteriorAlgebra.intrinsic_ext_determinant_roof`.
Its old statement claimed that every quotient-linear Ext equivalence satisfied
one fixed normalization. Its corrected statement asserts existence of a
roof-normalized equivalence. The statement of
`ExteriorAlgebra.exists_intrinsic_koszul_ext_determinant` and every other existing
signature and visibility are unchanged.

The corrected roof theorem now has a complete Lean proof. Choose a fixed regular
generating sequence, its normalized comparison and its actual quotient
augmentation. Compose a roof-normalized Ext/dual-homology equivalence with the
comparison's homology isomorphism. For any other roof, represent its class on
the fixed resolution, use naturality of homology projection, compare equal roofs,
and apply the determinant normalization equation. All witnesses are used within
the existential theorem proof; no data definition chooses an arbitrary witness.

The intrinsic theorem derives quotient linearity for this selected equivalence
by lifting quotient scalars to A and using Ext scalar composition and A-linearity.
The separate multiplication theorem retains its signature and uses the same
argument. Existing comparison, augmentation, generator-change and localization
proofs are retained. Removed two proof imports and added two new proof imports.

Change record: `coord/changes/intrinsic-ext-determinant-roof-normalization.md`.
The roof, multiplication and parent DAG nodes now record the actual route.
No separate module is adapted, and no target statement or definition changes.

## Proved and sorry left

Closed the item's sole hole, `ExteriorAlgebra.intrinsic_ext_determinant_roof`
(node `lem-sc-koszul-ext-determinant-roof`), by a statement correction and
DECOMPOSITION, not a complete axiom-free proof. No sorry remains in the item.
All formerly proved declarations retain complete proofs.

Added exactly two named holes in separate modules:

- `ExteriorAlgebra.exists_koszul_ext_roof_representatives`, node
  `lem-sc-koszul-ext-roof-representatives`, module
  `Sheaf.RingTheory.KoszulExtRoofRepresentatives`. This computes Ext on ONE
  resolution with actual roof and cycle representatives; its statement contains
  no normal determinant or conormal comparison.
- `ExteriorAlgebra.koszul_roof_comparison_independent`, node
  `lem-sc-koszul-roof-comparison-independence`, module
  `Sheaf.RingTheory.KoszulRoofComparisonIndependence`. This compares normalized
  values of TWO already equal roofs; it asserts no Ext equivalence or existence
  of a determinant isomorphism.

Each has a source, a complete proof in words, a DAG node and exactly `by sorry`.
The split is strictly into the fixed-resolution Ext computation and the
change-of-resolution compatibility, rather than a renamed intrinsic theorem.
Holes closed: 1; holes added: 2. This is a decomposition, not positive net sorry
progress. Compilation of all three sandbox modules succeeds without warnings.

Edge cases were checked mathematically before stating the intermediate results:
r=0 has the empty generating sequence, I=0 and no incoming dual boundary; both
formulas reduce to evaluation of Hom(A,A). If I=A, the quotient and its restricted
determinant are zero and regularity makes the dual homology zero. No assumption
of a nonzero ring, proper ideal, positive length, or invertible coefficient matrix
has been added. Roof independence uses a generator lifting matrix and homotopy,
not an inverse matrix over A.

## No longer needed

Removed proof import `Sheaf.RingTheory.KoszulExtDualHomology` and its direct
proof dependency `lem-sc-koszul-ext-dual-homology` from the multiplication route.
Its existence-only equivalence did not identify any chosen equivalence with the
roof evaluation and could not determine the intrinsic normalization. The new
representative theorem supplies that missing, stronger fixed-resolution data.
The repaired plans no longer use `new-j3-ext-signed-dual-homology` or its
module `Sheaf.CategoryTheory.ExtSignedDualHomology`: its statement is only
Nonempty of an equivalence and supplies neither normalization nor a coboundary
criterion. Both direct proof edges are removed. The explicit signed differential
calculation and projective-resolution construction remain needed mathematics.

Removed the multiplication node’s direct proof edge to
`lem-sc-koszul-conormal-comparison-existence`; the roof theorem still uses it
transitively. This prunes an edge, not the comparison-existence module.

Removed redundant proof import `Sheaf.Paper.KoszulComplex`; the complex and its
boundary declarations are already supplied by the public statement imports.
Its node `def-weil-pbc-koszul-complex` is still needed and retained in the DAG.

The old proof edge from the roof node to its parent is removed: it was a cycle,
not a valid proof dependency. No unit statement or unit step is bypassed. Global
unreachability of these modules is for the maintainer's closure ledger to decide.

## Where the brief, the DAG or earlier work was wrong

The prior roof statement was false, as its existing STATEMENT-DISPUTED comment
already recorded. Quotient linearity cannot distinguish e from -e. A concrete
edge case is A=Q, I=0 and r=0: the identity roof must evaluate to +1, whereas
negating the equivalence evaluates it to -1. The corrected existential
normalization is what the unchanged intrinsic theorem and Stacks Tag 0BQZ need.

The old roof node depended on the parent intrinsic statement while the parent
Lean proof applied the roof theorem. The new proof dependencies are acyclic.
The existing Ext/dual-homology theorem gives only Nonempty of an equivalence,
without component formulas or augmentation normalization, so applying it cannot
prove the roof formula. The two new statements isolate the missing information.

`tools/downstream.py --uses intrinsic_ext_determinant_roof` finds only this module
as a user among its 299 transitive importers. No external user needs adaptation.
The target-facing intrinsic theorem retains its existing statement, and the unit
record has no realized node that this route would bypass. Sources were read at
Stacks Tags 0BQZ and 0BQY; the local literature file named in the old node is
absent on this machine. LeanFinder and source searches found the generic Mathlib
projective-resolution APIs; LeanSearch returned Internal Server Error.

## New nodes

`lem-sc-koszul-ext-roof-representatives` records the fixed-resolution computation
with actual signed-dual cycles and roof representatives. Its source is the local
finite free Hom computation in Tag 0BQZ; the proof details retain evaluation
information omitted by the existing existence-only equivalence.

`lem-sc-koszul-roof-comparison-independence` records equality of normalized values
of equal roofs across generators. Its proof follows intrinsic determinant
classes in Tags 0BQY/0BQZ: exterior-power lifting, projective-resolution homotopy,
reduction of boundaries modulo I, and the conormal determinant pairing.

Removed the unused public import of `KoszulExtRoofRepresentatives` from the
new `KoszulRoofComparisonIndependence` module during second reading. Its signature
needs only its remaining public imports.

Both are below the existing affine Koszul node in the same chapter and unit.
The signature correction is recorded in
`coord/changes/intrinsic-ext-determinant-roof-normalization.md`.

The repair adds four Mathlib leaves (no new holes):

- `lem-sc-projective-ext-cocycle-roof-formulas`: ProjectiveResolution's Ext
  equivalence, extMk_surjective, and the actual derived roof formulas.
- `lem-sc-hom-single-cocycle-component-formulas`: evaluation of Hom cochains
  into a single object, signed differential, cocycles and boundary criterion.
- `lem-sc-hom-cocycle-homotopy-quotient-formulas`: the cocycle quotient and
  its bijection with homotopy classes, with the zero/boundary criterion.
- `lem-sc-module-homology-quotient-formulas`: the explicit module homology
  kernel/image quotient and its cycles/projection equations.

The existing `lem-pc-ring-derived-map-representative` already records exactly
Qh_map_bijective, so no duplicate node is added for it. The existing
`lem-sc-bounded-above-projective-kprojective` records the required projectivity
criterion. Whole-DAG and blueprint searches found no equivalent nodes for the
four new leaves. Their Lean records point to existing Mathlib declarations.


## Earlier second reading (a previous round; superseded)

Repair addendum for X-06699 C3/C4 (worker source audit; a fresh independent
second reading is still required). The prior assertions in points 3 and 5 that
the plans were complete were too strong: the Nonempty statement of
new-j3-ext-signed-dual-homology does not imply any component formula or equality
criterion for roofs. It is removed from both repaired steps and both dependency
unions. The prior second-reading conclusions are retained below as history of
the returned delivery, not as certification of this repair.

C3: Read Projective/Ext.lean:47,54,145,186,214 and
HomotopyCategory/HomComplexSingle.lean:145,156,168,301,325,363. New Mathlib leaves
record the Ext equivalence, actual cocycle/roof formulas, component evaluation,
and differential/boundary formulas. The evaluation e_r sends cocycle differences
in B exactly to BL. F([c]) is defined as the actual cycles inclusion inverse
followed by homologyPi, and the moduleCatHomologyIso projection formulas give
well-definedness, injectivity and surjectivity. The representative formula uses
that same F; no arbitrary equivalence is used. Ext.smul_hom and the roof formula
establish scalar compatibility for this particular construction.

C4: Used the existing Mathlib leaf lem-pc-ring-derived-map-representative for
CochainComplex.IsKProjective.Qh_map_bijective at DerivedCategory/KProjective.lean:43,
and lem-sc-bounded-above-projective-kprojective for the justification at
HomotopyCategory/KProjective.lean:113. The exterior bases give projective terms;
embeddingDownNat gives strict bound 0. Cancel the common shift and precompose
by Q(epsilon_f), then use u followed by epsilon_g = epsilon_f. Reflection through
quotientCompQhIso and Qh injectivity gives equal homotopy classes. The new
Hom-cocycle quotient leaf plus toSingleMk_mem_coboundaries_iff gives the top
component d_(r,r-1) followed by b for r>0; E_f^1=0 handles r=0. The sign can be
absorbed into b and boundary evaluations lie in I. This uses no inference from
the existence-only Ext equivalence. Checked both proof_deps unions exactly.

1. **Interfaces: PASS with the declared correction.** Read the full module and
   its diff against the repository. Compared the complete signatures of all
   twelve existing public/private theorems byte for byte: only
   `ExteriorAlgebra.intrinsic_ext_determinant_roof` changes. Its recorded
   existential correction repairs the valid Q, I=0, r=0 negation counterexample.
   The target-facing intrinsic theorem and all other signatures and visibility
   remain identical. No definition changes. A fresh source search finds the sole
   caller in this module, already adapted; the base DAG has no roof-node citers.
   Replaced the change record's reformatted Old signature with the verbatim one.

2. **Kernel checks: PASS as a decomposition.** Compiled all three delivered
   modules through lcompile.py, without errors or warnings. Compiled scratch
   copies with `#print axioms` for every public and private theorem. Only
   propext, Classical.choice, Quot.sound and the expected sorryAx occur.
   In particular the quotient augmentation and generator-comparison theorem
   are axiom-clean; the intrinsic roof, multiplication and parent still depend
   on named holes. Exactly the two reported new public theorems have `by sorry`;
   no hole in data, unsafe declaration or nonstandard axiom is introduced.
   Witnesses of existence are selected inside theorem proofs, never used to
   define arbitrary data. No existing false statement is counted as proved.

3. **Split statements: PASS.** Read both signatures, docstring arguments and
   nodes, and the cited Stacks Tags 0BQZ/0BQY. Fixed-resolution representatives
   compute Ext and signed dual homology, without a determinant; equal-roof
   independence compares values, without constructing any Ext equivalence.
   Both are strictly parts of the argument and both are used in the reduction.
   Checked r=0 (I=0, Hom evaluation), r=1 (boundary values are multiples of f),
   zero ring and I=top (zero quotient), and change of generators by a lifting
   matrix that need not be invertible over A. The coboundary sign is a unit and
   disappears modulo I. Independent LeanFinder search for maps from bounded
   above projective complexes, qualified Loogle search for
   CategoryTheory.ProjectiveResolution.extEquivCohomologyClass, and msearch grep
   for extMk_eq_zero_iff/extMk_hom/extMk_surjective found the generic Mathlib APIs.
   Read those APIs and the existing signed-dual theorem: they do not retain the
   required normalized component equation or compare conormal values on roofs.
   Source searches under lean find no existing exact statement. Neither hole
   has a direct short proof from the current existence-only APIs.

4. **Route and pruning: PASS after repair.** Read the proof top down: choose a
   normalized fixed-resolution comparison, represent each roof class, use
   homology-projection naturality, transport equal roof values, then apply the
   determinant normalization. Quotient linearity follows for the same chosen e.
   The unit sk-thm-picard-duality has no realized nodes bypassed by this route.
   Compared every old proof_deps set with the delivery: added the omitted report
   entry for the multiplication node's removed direct comparison-existence edge;
   it remains needed transitively. Removed the unused public representative-module
   import from KoszulRoofComparisonIndependence and recompiled successfully.
   Retained ExteriorPower.Basic in the representatives module after a removal
   trial showed its statement needs zeroEquiv. Pruning here describes removed
   imports and proof edges, not a claim of globally unreachable modules.

5. **Metadata: PASS.** Checked the three changed nodes and two new nodes against
   their Lean declarations, natural-language arguments and proof routes. The new
   signatures are verbatim. Each proof_deps is the union of its proof steps' uses;
   sources, origin, search records, creation, blueprint, chapter, unit and Lean
   fields are present. The roof correction has its change record and
   statement_change, and removes the old cyclic dependency on the parent.
   Recorded the corrected roof signature verbatim in its lean record as well.

Second reading changed only an unused import, the change record's Old formatting,
the roof node's Lean-signature formatting, and the report/pruning documentation.
The corrected roof remains a decomposition: zero new axiom-free proofs of the
one originally open declaration; two split holes; net hole count minus one.


## Second reading by A4

Independent second reading of the X-06699 repair, 2026-10-13.

1. Interfaces: PASS with the declared statement correction. Compared the whole
   delivered item with this machine's repository version. All eleven other
   existing declaration signatures and their visibility are unchanged; only
   intrinsic_ext_determinant_roof has the recorded existential correction.
   The target-facing exists_intrinsic_koszul_ext_determinant is unchanged.
   The Q, I=0, r=0 negation counterexample refutes the former universal claim.
   The change record includes the old and new signatures and its sole caller;
   a fresh rg search of the source tree confirms that caller is in this item.
   No definition or target statement is changed.

2. Proof and kernel: PASS as a decomposition. Compiled all three sandbox modules
   with lcompile.py --all, without errors or warnings. Compiled scratch copies
   with #print axioms for all fourteen declarations, including private helpers.
   Only propext, Classical.choice, Quot.sound and expected sorryAx occur.
   The quotient augmentation and generator-comparison theorem are axiom-clean.
   The only direct holes are exists_koszul_ext_roof_representatives and
   koszul_roof_comparison_independent, each a named public theorem whose whole
   proof is by sorry. No forbidden declaration or data hole occurs. Choices of
   witnesses are inside theorem proofs; no arbitrary data definition is added.

3. Split statements: PASS. Read both complete signatures, docstring arguments,
   their DAG plans, and Stacks Tags 0BQZ/0BQY. The representative statement is
   the fixed-resolution Ext calculation with actual evaluation, without the
   conormal determinant. Independence is compatibility of two already equal
   roofs, without constructing an equivalence. They are strictly separate
   parts of the argument and both are used. Checked r=0 (empty sequence, I=0,
   no incoming boundary), r=1 (boundaries evaluate into (f)), zero rings and
   I=top (zero quotient). A generator lifting matrix need not be invertible.
   Fresh LeanFinder search for maps from bounded above projective complexes,
   qualified Loogle search for extMk_surjective, msearch grep for the cocycle
   boundary and roof formulas, and rg in the project's Koszul modules found
   the generic APIs but no existing normalized specialization. Read the actual
   Projective/Ext, HomComplexSingle, HomComplexCohomology, ModuleCat homology
   quotient and Qh_map_bijective APIs. The differential sign is a unit; its
   image agrees with the signed-dual boundary image, also at rank zero.
   The existing signed-dual equivalence has no representative equations.
   Neither new hole has a direct short closure from its exposed statement.

4. Route and pruning: PASS. Read the proof from the intrinsic theorem down:
   select the normalized equivalence on one resolution; represent the roof
   class; use naturality of homology projection; transport equal roof values;
   apply the conormal normalization formula. Quotient linearity is proved for
   that same selected equivalence. Read sk-thm-picard-duality.realized: it has
   no realized nodes bypassed here. Compared old and new proof_deps for all
   three existing nodes and verified every removed edge is reported under
   No longer needed. The main removed imports are proof imports; the two new
   imports are also proof imports. New-module public imports supply their
   signatures. Global module pruning remains the maintainer's closure check.

5. Metadata: PASS after the small repair below. Every proof_deps set is exactly
   the union of the step uses. Read all nine delivered node records and checked
   their declarations, sources, proof routes and required new-node fields.
   The four API leaves name actual Mathlib component, roof, quotient and
   boundary declarations. The two split nodes have matching signatures,
   source proofs, searches and the item's chapter/unit. The corrected roof
   has its change record and statement_change; the former parent cycle is gone.

Second reading changed no Lean code. Removed an irrelevant copied reference to
mk_sub and sub_eq_zero from mathlib_match.how in the projective Ext roof,
Hom-single component and module-homology quotient API leaf nodes. Added this
independent certification. This remains a statement correction and decomposition:
zero new axiom-free proofs of the one originally open declaration, two split
holes, and holes closed minus holes added equal to -1.
