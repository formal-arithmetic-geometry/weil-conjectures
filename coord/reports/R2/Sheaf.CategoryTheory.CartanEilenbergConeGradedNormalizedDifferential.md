## What changed

Proved the unchanged declaration
CategoryTheory.Functor.cartanEilenberg_cone_graded_normalized_differential in
Sheaf.CategoryTheory.CartanEilenbergConeGradedNormalizedDifferential.
Its original public import remains; two proof-only imports provide the proved
retained-summand calculations:
Sheaf.CategoryTheory.CartanEilenbergConeGradedAugmentationRepresentative and
Sheaf.CategoryTheory.CartanEilenbergConeGradedResolutionRepresentative.

The augmentation calculation cancels the monic filtration inclusion, expands
mappingCone.inl_v_d, and kills the d_K term through the next filtration step.
The resolution calculation expands the flipped total differential, identifies
the coefficient-one resolution term, factors the signed horizontal term through
the next step, and kills it by the cokernel relation. For p<b it evaluates the
zero resolution column. Neither calculation assumes a comparison isomorphism.

The main proof uses mappingCone.ext_from, the normalization equations, the two
representative calculations, and extension formulas. It explicitly covers
m=p-1, m>=p, negative resolution degrees, and p<b. Dependent degree transports
are proved by equality elimination, without arbitrary choices.

Updated the item's node proof, proof_deps and proof_origin. Added matching nodes
for both new proved lemmas. No existing statement, definition, or visibility
changed. No other existing module was adapted.

## Proved and sorry left

Closed the single original hole:
CategoryTheory.Functor.cartanEilenberg_cone_graded_normalized_differential
(lem-sp-cartan-eilenberg-cone-graded-normalized-differential).

Both added declarations are proved:
CategoryTheory.Functor.cartanEilenberg_cone_graded_augmentation_representative
(lem-sp-cartan-eilenberg-cone-graded-augmentation-representative) and
CategoryTheory.Functor.cartanEilenberg_cone_graded_resolution_representative
(lem-sp-cartan-eilenberg-cone-graded-resolution-representative).

No sorry remains in any delivered module. Holes closed: 1. Holes added: 0.
This is a proof, not a decomposition into unproved intermediate statements.
All three files compile locally. The delivery dry run checks every declaration's
axioms and the complete set in dependency order.

## No longer needed

No repository import or module is pruned. The normalized-iso module remains
needed for CartanEilenbergConeGradedNormalized; its existence theorem is not
applied by this proof. The original definition dependencies remain needed
through the representative modules, so moving their direct DAG edges is not
claimed as pruning.

Removed the earlier sandbox-only arithmetic-shift module and its draft node:
CartanEilenbergConeGradedNormalizedDifferentialShift /
lem-sp-cartan-eilenberg-cone-graded-normalized-differential-shift.
The shift equality is proved directly by omega. Those drafts were never part
of the repository and do not count as pruned library modules.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped before combining the summand calculations and
left the main proof unfinished. Its augmentation calculation was useful and
was checked and retained; the resolution calculation and the complete main
proof are now written. The earlier compiled-snapshot absence is resolved:
the normalized-iso dependency is available in the published local library.

The source route is retained. Stacks Tags 012X and 0133 were read, including
the coefficient-one differential for the second filtration and the canonical
augmentation. Their omitted quotient calculation is expanded using Mathlib's
cone and total differential identities. The unit's realized statement and
steps are unchanged; no unit-realized node is bypassed.

LeanSearch returned an Internal Server Error, recorded as unavailable.
LeanFinder, Loogle, Mathlib grep, and repository searches found the generic
cone and total identities used, but no existing retained-representative lemma.
A search of the imported blueprint found no duplicate column-filtration node.

## New nodes

lem-sp-cartan-eilenberg-cone-graded-augmentation-representative:
a proved lemma for the differential of a specified lift of K^p in cone degree
p-1. Its conclusion identifies only the augmentation component after taking
the graded quotient. No lower-bound vanishing assumption is needed.

lem-sp-cartan-eilenberg-cone-graded-resolution-representative:
a proved lemma for specified lifts of I^{p,r} and I^{p,r+1}. Its conclusion
identifies only the resolution component after taking the graded quotient.
The lower-bound hypothesis handles columns p<b; for p>=b the next-step
factorization handles the horizontal component. The cases r=0, p=b, and zero
columns are included in the Lean proof.

Both nodes contain self-contained statements, source references, complete
proof steps, recorded searches and exact Lean signatures. No change record
is needed: existing interfaces are unchanged.


## Second reading by R2

1. PASS: compared the existing module with the repository using diff, and
   compared its theorem signature byte for byte. Only the proof, local
   elaboration options, and two plain proof-only imports changed. No existing
   definition, declaration visibility, or statement changed; no adaptation or
   change record is needed.
2. PASS: independently compiled all three modules in dependency order with
   lcompile.py (4.1 s, 8.3 s, 4.6 s). No warning, error, sorry, axiom, unsafe,
   opaque, implemented_by, or extern occurs in the delivered Lean files.
   Independently printed axioms for all three theorems in an import-only probe;
   the results contain only propext, Classical.choice, and Quot.sound.
   Both factorizations are constructed through image subobjects; no arbitrary
   data is chosen from an unproved existence theorem.
3. PASS: no unproved statement is split off. Both new lemmas are proved,
   strictly partial calculations for specified lifts, without comparison
   isomorphisms. Checked their signatures against their nodes and read their
   complete docstring proofs. Checked m=p-1, r=0, p=b, p<b, negative resolution
   degrees, and the empty interval boundary. Independent LeanFinder search
   for a filtered-quotient summand differential found the generic total
   identities already used. Loogle confirmed mappingCone.inr_f_d; a fresh
   Mathlib grep and repository/upstream searches found no duplicate quotient
   calculation or shorter complete proof.
4. PASS: the main proof reduces by mappingCone.ext_from, uses the two
   representative calculations, and proves all degree transports by equality
   elimination. The three public imports in each new module supply its
   signature; both new imports of the item are proof-only. No library import
   is removable from this delivery. The old direct proof dependencies
   def-sp-cartan-eilenberg-presentation, def-sp-double-complex-total,
   def-sp-filtered-complex-subquotients, and def-sp-filtration move behind
   the representative nodes and remain used; none is pruned. The original
   normalized-iso module supplies the normalization definition, and its
   existence theorem is not invoked. Read the unit record: its realized
   statement and step lists are already empty in the repository; this
   delivery does not alter them or bypass any unit-realized node. Checked
   the second-filtration coefficient-one differential against Stacks 012X
   and the canonical augmentation against Stacks 0133.
5. PASS: all three node Lean signatures match the actual modules verbatim;
   each proof_deps equals the union of the steps' uses. The existing node
   changes only proof, proof_deps, and proof_origin. Both new nodes have
   source, proof, search records, creation, blueprint, unit/chapter and Lean
   records. Their proof steps follow the image factorization, monic
   cancellation, total/cone differential calculation, and cokernel relation
   actually used by Lean.

Second reading changed only this report: recorded the independent checks,
listed all four old direct proof edges that remain transitively necessary,
and noted the pre-existing empty realized lists. No proof repair was needed.
