## What changed

Proved `AlgebraicGeometry.finite_exactHom_degreeZero_lift` from an algebra-linear derived
mate and canonical single-complex counit transport. Its signature and public imports stay
identical. The proof explicitly constructs gamma from the exact-composition comparison
and the derived identity g_* followed by scalar restriction equals f_*; it does not choose
an arbitrary isomorphism from the factorization theorem. The retained Hom-model comparison
iH is unnecessary for this adjunction-theoretic lifting. Its binder remains unchanged;
the unused-variable linter is scoped off for this theorem, with an explanatory comment.
Additivity of H follows from the specified adjunction. No evaluation normalization is used.

Added `Sheaf.AlgebraicGeometry.FiniteExactHomDerivedMate`, whose public theorem is proved.
Its private categorical helper constructs the adjunction mate, proves bijectivity of
composition on Hom from the fully faithful image, and uses an essential-image witness to
construct both inverse equations. The affine derived equivalence and the specified-right-
adjoint quasi-coherence theorem supply those hypotheses.

Added `Sheaf.AlgebraicGeometry.FiniteExactHomSingleCounitTransport` for the remaining
single-complex calculation. The main module combines the two parts with a proved private
categorical counit-transport lemma, naturality along e0 and eL, and hc. Updated the item's
node and supplied a node for each new public theorem. No existing interface changed and
no other group's module was adapted.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.finite_exactHom_degreeZero_lift`
(node `lem-sc-finite-exact-hom-degree-zero-lift`): 1 of 1 original holes closed by reduction.
The item's module has no remaining sorry.

Also proved `AlgebraicGeometry.finite_exactHom_derived_mate`
(node `lem-sc-finite-exact-hom-derived-mate`) from existing declarations, with no new hole.
The private helpers `adjunctionMate` and `scalarCounitTransport` have complete proofs.

Added exactly one hole:
`AlgebraicGeometry.finite_exactHom_single_counit_transport`
(node `lem-sc-finite-exact-hom-single-counit-transport`). Its proof is exactly `:= by sorry`;
its docstring and node describe the canonical g_* single comparison, reflection through
scalar restriction, the fully faithful degree-zero lift, and the derived counit equation.
This is a decomposition, not a claim that the full finite-duality argument is sorry-free.

## No longer needed

Removed direct proof imports from the item's module:

- `Mathlib.CategoryTheory.Functor.Derived.Adjunction`: the supplied library derived
  adjunction implementation imports this infrastructure transitively.
- `Sheaf.AlgebraicGeometry.FiniteAffineDerivedEquivalence`: used in the proved new derived
  mate module instead; this module/node is still needed transitively.
- `Sheaf.AlgebraicGeometry.FiniteScalarRightAdjointQCoh`: used in the proved new derived
  mate module instead; this module/node is still needed transitively.
- `Sheaf.AlgebraicGeometry.AffineSinglePushforwardUnitIso`: used in the remaining new
  single-transport module instead; this module/node is still needed transitively.
- `Sheaf.AlgebraicGeometry.FiniteAffineDerivedFactorization`: neither new module imports
  it. Its node `lem-sc-finite-affine-derived-factorization` is not needed on this route:
  its existential conclusion does not fix the canonical comparison needed here, so the
  proof constructs that comparison directly from the existing composition infrastructure.

Also removed unused experimental proof imports from the new modules:
`Mathlib.CategoryTheory.Adjunction.Restrict` from the derived-mate module and
`Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful` from the single-transport module.
The generic mate argument uses the basic adjunction hom equivalences directly.

No claim is made that another target does not independently need a listed module. The
public statement imports were retained. The unit's realized lists are empty; no unit
statement or realized proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing dependency signatures do not give the two counit-compatible intermediate
conclusions as stated theorems. The derived mate part is now proved; the remaining canonical
single-counit calculation is isolated with weaker, independent hypotheses: it assumes only
an affine morphism, arbitrary L, exact H and a supplied derived isomorphism, and mentions
no geometric right adjoint a, R, comparison, e0 or eL. Thus it is strictly the degree-zero
transport step, not the original theorem under another name.

The specialized scalar-restriction exactness lemmas require derived-category instances
for a second syntactic presentation of the algebra sheaf. Explicit universe/instance
arguments resolve this. Generic categorical helpers avoid repeatedly unfolding large
sheaf and derived-adjunction definitions during the final naturality calculation.

LeanFinder found generic full single-functor and derived-adjunction infrastructure;
Loogle found uniqueness-of-right-adjoint declarations; the logged Mathlib grep found no
right-derived single comparison under the searched names. LeanSearch returned an internal
server error and is recorded as unavailable. Blueprint searches for finite duality and
degree-zero lift found no duplicate blueprint node. The local Stacks sources were absent;
the source statements were read at the official Stacks Project pages for Tags 0AX2, 0AX3
and 0AVW.

The new statements allow zero modules, empty schemes, and rank-zero algebras: the derived
mate proof uses only Hom equivalences and the essential image, and the single-transport
statement uses canonical comparisons and full faithfulness. The gamma equality in the
latter excludes arbitrary rescaling of the factorization.

## New nodes

`lem-sc-finite-exact-hom-derived-mate` records the proved comparison at a bounded-below
input. It is in `Sheaf.AlgebraicGeometry.FiniteExactHomDerivedMate`; its proof uses the
existing affine derived equivalence, finite scalar-right-adjoint quasi-coherence and
derived-adjunction infrastructure, followed by the explicit proved categorical argument.

`lem-sc-finite-exact-hom-single-counit-transport` records the remaining single-complex
lifting and counit compatibility in `Sheaf.AlgebraicGeometry.FiniteExactHomSingleCounitTransport`.
It has a complete proof in words and exactly one named public sorry. Its canonical gamma
is specified by equality with the exact-composition construction. No change records are
needed, since no existing statement, definition, visibility or public import changed.

## Second reading by U3

1. **Interface and accidental changes.** I compared the delivered target module with the repository version. The target theorem signature and all existing declaration signatures are byte-for-byte unchanged. The two additional modules contain only the newly recorded declarations, and no definition or target statement was changed.

2. **Proof and axioms.** I compiled all three delivered modules with the sandbox compiler. The target and derived-mate theorem have no `sorry`; the sole remaining `sorry` is the named `finite_exactHom_single_counit_transport` theorem, exactly as listed above and documented by its node. No forbidden declarations occur. The completed proofs use the categorical mate construction, fully faithful/essential-image arguments, and the canonical comparison transport; the remaining hole is isolated at the single-complex transport step.

3. **New statements.** I checked both added theorem statements against their Lean declarations and nodes. The derived-mate statement has the exact hypotheses used by its proof and gives precisely the required algebra-linear isomorphism and counit equation. The single-counit transport statement is a strictly smaller reduction: it removes the geometric adjunction data and isolates the canonical single-complex lifting and counit identity. Its hypotheses permit zero and rank-zero cases and do not add an arbitrary witness or weaken the conclusion. Searches recorded in the nodes found no duplicate upstream declaration.

4. **Pruning and imports.** The target proof uses the new mate and transport modules plus the existing derived RHom infrastructure. Removed imports are listed under `## No longer needed`; the removed factorization node is not used by the canonical route. Proof-only imports in the new modules are plain `import`, while statement imports remain public. The unit route is preserved because no unit statement or realized step is bypassed.

5. **DAG consistency.** The target node proof and `proof_deps` follow the delivered proof, and each new public theorem has a matching split node with source, proof, dependencies, Lean record, and docstring. The report's proved/sorry counts agree with the files: one original target hole and the derived-mate hole are closed, and one named transport hole remains.

I added this second-reading record only; no code or statement repair was needed after compilation.
