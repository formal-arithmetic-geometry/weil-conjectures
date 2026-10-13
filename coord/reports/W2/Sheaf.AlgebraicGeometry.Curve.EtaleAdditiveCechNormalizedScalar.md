## What changed

Replaced the ill-typed earlier scalar-action split with two new modules:
`EtaleAdditiveCechCommonRepresentative` and `EtaleAdditiveCechScalarTransport`.
The original theorem signature, visibility and normalization definition are unchanged.
Its proof chooses a global cycle using the homology projection epi, obtains a common
augmentation representative, and applies normalization before and after scalar transport.
Both new statements have one named theorem each. The copied normalization module is
byte-for-byte identical to the repository and is present only for local compilation.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Scheme.Modules.etaleAdditiveCech_normalized_scalar`.
Added two holes, a decomposition rather than a net proof:
- `AlgebraicGeometry.Scheme.Modules.additiveCech_common_representative`, node
  `new-w2-additive-cech-common-representative`.
- `AlgebraicGeometry.Scheme.Modules.additiveCech_scalar_transport`, node
  `new-w2-additive-cech-scalar-transport`.

The upper proof and both new signatures compile locally. Neither intermediate assumes
an edge equivalence or normalization; the first proves existence of common augmentation
classes, the second transports supplied common classes. Zero degree, zero/one scalars,
empty families and empty intersections are covered by the arguments in the docstrings.

## No longer needed

Removed the earlier attempt's unsubmitted module
`Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalizedScalarLemmas` and its two
unsubmitted nodes `new-w2-normalized-edge-linearity` and `new-w2-sheaf-homology-scalar`.
They never became library dependencies. No existing library module or planned node is
pruned: the canonical-data dependency and the original augmented-complex route remain.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt used `r • x` on additive sheaf cohomology without a structural
ring-module instance. Annotating r does not repair this missing instance. Its split
also placed two statements in one module, gave only vague proof sketches, and did not
update the upper node's proof dependencies. The replacement uses scalar multiplication
only on the ordinary ModuleCat Cech homology, where it is already defined.
Existing abstract total-comparison and affine-column declarations do not state the
actual alpha/beta component equations required by normalization. The new statements
isolate exactly those component-level existence and transport arguments.

## New nodes

`new-w2-additive-cech-common-representative`: existence of a common augmentation
representative, from injective Cech rows and affine coefficient acyclicity.

`new-w2-additive-cech-scalar-transport`: transport of supplied common representatives
by an augmentation-preserving resolution lift, with the Ext and coefficient class
identities. It has no affine-cover or normalized-equivalence assumption.

No statement or definition changes, forced adaptations or change records.

## Second reading by W2

1. **Interfaces: pass.** Compared every existing sandbox module with the repository
   using diff. Normalization is byte-for-byte identical. The scalar module adds
   three private imports and replaces only its theorem proof: the existing signature,
   visibility, definitions and docstring are unchanged. The two representative
   modules are new. There are no interface changes or forced adaptations.
2. **Proof and trust: pass.** Compiled the delivered modules through lcompile.py,
   and checked scratch copies with `#print axioms` for all three theorem names.
   The only axioms are propext, Classical.choice, Quot.sound and the expected
   sorryAx from open statements. The upper theorem has no local sorry; the two
   new theorems have exactly their reported named holes. No definitions are added,
   and no prohibited declarations or attributes occur. Existential witnesses are
   eliminated inside a proof, never used to define arbitrary data.
3. **Split statements: pass as a decomposition.** Common representatives require
   only that the two augmentation images represent a common total class; they do
   not assert scalar compatibility or assume a normalized edge. Transport is a
   coefficient-functoriality statement for supplied representatives, with no
   affine-cover or normalized-edge hypothesis. Its proof uses an actual resolution
   comparison lift, not a scalar action on additive sheaf cohomology. In degree zero
   the augmentation-preserving lift is strict and there are no boundaries. Zero
   and unit scalars use the same comparison equations. An empty covering of X
   forces X empty; arbitrary empty families in transport give zero coefficient
   and total complexes without asserting that X is empty. Repeated opens and empty
   intersections preserve the formulas. Both new docstrings give complete
   mathematical arguments and matching nodes. Independent leanfinder, loogle and
   grep searches found cycle constructors, injective-resolution comparison maps
   and homology linearity, but no duplicate of either component-level statement.
4. **Route and pruning: pass.** Read the actual double-complex construction,
   canonical comparison, row augmentation, affine-column and total-comparison
   declarations. The abstract Nonempty total isomorphism does not identify the
   fixed alpha/beta components; substituting it alone would not prove normalization.
   Both new statements remain substantial open formalization tasks, so this is
   one upper hole closed and two lower holes added (net -1), not a net proof.
   All imports of the scalar module serve its signature or proof and proof-only
   imports are plain imports. The old proof_deps contains only canonical-data
   existence, which is retained: no old dependency is pruned. The unit sk-thm-p1
   realized statement and four steps remain unchanged; this reduction stays below
   its Artin–Schreier structure-sheaf comparison route.
5. **DAG agreement: pass.** The existing node changes only proof, proof_deps and
   proof_origin. Its steps match the actual cycle lift, first normalization,
   transport and second normalization. Each new Lean signature equals its node's
   lean.statement verbatim; each proof_deps is exactly the union of its step uses,
   and all dependencies exist. Both new nodes carry source, proof, origin,
   searches, split status, creation record, blueprint ancestry, chapter and unit.

Changed only review documentation and new-node metadata: added independent search
records and corrected scalar-transport proof_origin to describe coefficient
naturality without affine vanishing. The Lean proof required no repair. Neither
new hole could be closed by a direct existing theorem; both require constructing
and checking the specified augmentation chain maps.
