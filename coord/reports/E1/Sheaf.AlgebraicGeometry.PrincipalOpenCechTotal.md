## What changed

Partial proof delivery for `Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal`.
Seven existing named theorem holes are closed, with their statements and all existing
visibility unchanged. No new theorem holes, modules, definitions, or nodes are added. The existing node's
proof and proof_origin now record the partial realization checked by the second reader.

Sections preserve addition definitionally. The principal-open inclusions use
`Finset.mul_prod_erase`, `PrimeSpectrum.basicOpen_mul_le_right`, and `le_iSup`.
The degree identities use `Finset.card_erase_add_one`, integer arithmetic, and
singleton cardinality. The differential is constructed as a linear map from its
displayed value: additivity is checked pointwise using finite-sum distributivity,
and scalar compatibility uses linearity of each map and commutativity of scalars.

The functor is constructed explicitly from componentwise linear maps. A proved
private helper `AlgebraicGeometry.principalCech_transport_naturality` handles the
equality transports between degrees. Vertical compatibility is the coefficient
chain-map equation, mapped through sections. Horizontal compatibility combines
that transport identity with naturality of `modulesSpecToSheaf.map`. Identities,
composition, and addition hold pointwise. The specified formula after object
equality transports follows by proof irrelevance and reflexivity.

The theorem's existing, unused existential binder `hC` triggers the unused-variable
linter once its proof is filled. A declaration-local linter option suppresses that
warning without changing its binder or type. An extra transparency option supports
the existing definitional identification of scheme modules with sheaves of modules.

The module compiles cleanly through the required `lcompile.py` file check.
Searches through the required `msearch.py` leanfinder, loogle, and grep interfaces
were run. Loogle found `PrimeSpectrum.basicOpen_mul`; semantic search returned
basic-open identities but no complete Cech construction. Local source searches
confirmed that the other principal-Cech declarations import this module, so using
them here would introduce a cycle.

## Proved and sorry left

Closed 7 of the original 11 holes (all names below are in `AlgebraicGeometry`):

- `affineOpenSections_additive_proof`
- `principalCechIntersection_erase_le`
- `principalCechIntersection_singleton_le`
- `principalCech_erase_degree`
- `principalCechDifferential_exists`
- `principalCechFunctor_exists`
- `principalCech_singleton_degree`

Four original named theorem holes remain untouched, all attached to
`def-sc-principal-open-alternating-total`:

- `principalCechDifferential_square`
- `principalCechAugmentation_exists`
- `principalCechAugmentation_quasiIso`
- `principalCechDerivedComparison_exists`

Added holes: none. Split off holes: none. The private transport helper is proved.
The functor proof still depends on the existing square-zero theorem through the
explicit total-complex construction; closing the functor hole does not close that
dependency. The four remaining statements retain their original source and proof
in words, and are not relabelled or moved into new modules.

## No longer needed

Removed import `Mathlib.Data.Finset.Sort`: the construction indexes finite subsets
and uses filter cardinalities; it never sorts them. The clean compile confirms
that none of its declarations is needed as a direct import.

Also removed the unused direct public import
`Sheaf.AlgebraicGeometry.DerivedCategory`: none of its scheme-derived-category
declarations occurs in this module, and the remaining imports supply the generic
derived-category declarations used by the existing signatures. A scratch compile
without this import and the final file compile both pass.

No DAG nodes are pruned; the removed Sheaf module can still be reached through
other imports in the library. The node retains
empty `proof_deps`; the new proofs use Mathlib and existing definitions of this
same module. Its previously empty proof plan now records those completed steps. No dependency route or unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The assigned node's `proof` and `proof_deps` are both empty, contrary to the brief's
expectation of numbered proof steps with named dependencies. Its declaration
docstrings supply the construction plan used here. The unit record
`sk-thm-picard-duality` has no realized nodes for its statement or steps; this
delivery changes neither the unit nor its route.

The singleton-open theorem's docstring says the union is contained in each
singleton's covering space, whereas its actual type and subsequent explanation
correctly put each singleton principal open inside the union. The proof follows
the unchanged Lean type. The second reader corrected this docstring direction; no source or statement changed.

The public-import removal and elaboration/linter options are recorded in
`coord/changes/principalCechTotalImports.md`. No dependent module is adapted.

## Second reading by E1

1. Compared the complete module diff and every existing declaration signature with
   the repository version. All existing signatures, visibility, definitions, and
   instances are unchanged. No target statement or hypothesis changed. The
   exported-import removals and elaboration options have a change record.
2. Compiled the module locally through lcompile.py with no errors or warnings.
   A scratch copy with #print axioms checked all eleven original theorem holes:
   the six elementary/linear results use only propext, Classical.choice and
   Quot.sound (the singleton degree needs just propext and Quot.sound). The
   functor theorem additionally uses sorryAx from the original square-zero
   obligation; the four untouched open theorems also use sorryAx. There are
   exactly four sorry tokens, all in the reported named theorems; no forbidden
   declarations or holed definitions were introduced. The constructed differential
   and functor are fully specified, rather than arbitrary existence witnesses.
3. No statements or holes were split off. The proved private transport helper is
   equality induction, not an assumption. Checked empty-cover, singleton, absent
   erased-index, and zero-ring cases: the finite subset formulas remain valid.
   Independent searches for additive evaluation, equality transports, and generic
   alternating complexes found supporting Mathlib declarations but no shorter
   replacement for the displayed componentwise total functor. Loogle's unqualified
   eqToHom query was rejected as an unknown identifier, so it supplies no verdict.
   Existing principal-Cech comparison modules depend on this module and cannot
   serve as upstream proofs. The four open original obligations require the
   remaining construction/comparison arguments and are not claimed as closed.
4. Read the proof from the functor down through its linear maps and degree/open
   identities. It follows the stated construction and uses elementary Mathlib
   identities directly; no duplicate split-off or unit step is substituted. Removed
   the additional unused DerivedCategory direct import after a successful scratch
   compile. All old proof_deps were empty, so there is no unreported removed node.
   The unit sk-thm-picard-duality and its empty realized fields are unchanged.
5. Read the node and unit records against the Lean. Repaired the node's empty proof
   and null proof_origin to record the seven closed holes, the componentwise
   functor reduction, and explicitly the four remaining original obligations.
   proof_deps remains empty, since the new proofs use Mathlib and same-module
   declarations. No node statement, stmt_deps, lean record, or unit route changed.

Second-reading changes: corrected the singleton-open docstring's inclusion;
removed the unused DerivedCategory import; updated its change record and pruning
report; recorded the partial proof route on the existing node. No proof repair was
needed and no new hole was added. Seven of eleven original holes are closed;
six closed results are independent of sorryAx and the functor reduction still
uses the original square-zero hole.
