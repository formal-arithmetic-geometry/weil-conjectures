## What changed

Constructed `affineFiniteFreeModelComplex` explicitly using associated sheaf, affine-chart
restriction, extension along `embeddingDownNat`, and inverse open-site equivalence. The target
now uses this fixed complex. Added its strict-perfectness theorem and proved the derived
comparison using Mathlib's extension, single-complex, exact-functor, and localization APIs.
The target signature is unchanged. All changes are confined to the item's sandbox.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.exists_affine_finite_free_perfect_model` by a
reduction. Added one hole: `AlgebraicGeometry.affine_finite_free_perfect_core`, node
`lem-affine-finite-free-perfect-core`. This is exactly the finite-basis and boundedness part,
with no sheaf to resolve, quasi-isomorphism, or derived-category conclusion.

`AlgebraicGeometry.affine_finite_free_perfect_comparison` is proved without holes, independently
of freeness and boundedness. The explicit complex definition contains no postponed proof and
chooses no witness from an unproved existence statement. Net holes closed minus added: zero;
the target is decomposed, not claimed to be axiom-free through its remaining dependency.

## No longer needed

Second reading removed `PerfectComplex` from the new construction module, replacing it
with `Sheaf.Paper.DerivedHomMayerVietoris`, which supplies `moduleRings`. It also removed
the redundant `PerfectComplex` import from the new comparison module.

The old direct proof dependencies are all accounted for: `lem-weil-pbc-spec-tilde-free-module`
and `def-pc-perfect-complex` remain under the strict-perfectness core;
`def-pc-derived-category` remains under the comparison and in the original signature;
`def-weil-pbc-module-chain-complex-homology` remains in the explicit construction and
original signature. They are replaced as direct edges by the three new nodes, not
claimed as globally pruned modules.

Removed the item's redundant proof import `Sheaf.AlgebraicGeometry.DerivedCategory`; its
statement definitions remain supplied by `PerfectComplex`. No existing DAG dependency is
claimed globally pruned: the original finite-free sheafification lemma is still needed by the
remaining strict-perfectness proof, and the homological-complex and derived-category notions
are still used by the construction and the proved comparison.

The old sandbox existential-model construction and the arbitrary-model comparison have been
replaced. No arbitrary strictly perfect representative is chosen or assumed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox comparison was false: it identified the resolution with every strictly
perfect complex, regardless of its relation to K. For example, choose a nonzero rank-one
sheaf on Spec of a field, its single resolution, and L the zero complex; their degree-zero
homologies differ. The replacement comparison is about the explicit transported K only.
The former existential core was also insufficient to connect a selected L to K. Both issues
are fixed before delivery. Previously recorded searches and placeholder Lean signatures were
replaced with real recorded searches and signatures read by the project's parser.

The prior missing `AffineAlgebraModuleAdjunctionUnitIso.lean` import-cycle failure no longer
appears in the current dry run. No tool or repository file was edited to work around it.

## New nodes

`def-affine-finite-free-model-complex` records the explicit construction. Its data is entirely
Mathlib constructions, including zero-object extension. Source: Tag 068C's resolution argument.

`lem-affine-finite-free-perfect-core` states strict perfectness of that construction, with a
complete finite-basis and boundedness proof in its docstring (Tags 068C and 08C4). This is the
only remaining hole; zero ring, empty open, zero ranks, and r = 0 are included.

`lem-affine-finite-free-perfect-comparison` records the proved extension/localization comparison
(Tags 068C and 05RU). It is valid for any supplied quasi-isomorphism and needs no finite-free
assumptions. Searches found Mathlib's generic comparison lemmas, which the proof uses directly.
No existing signature or interface is changed, and no forced adaptations are necessary.

## Second reading by E1

1. Compared the delivered item with the repository using `diff -u`: only its proof and
   two plain proof imports changed. The existing declaration signature and docstring are
   byte-for-byte unchanged. The other three modules and their nodes are new; there is no
   existing definition or interface change and no change record is needed. Verdict: pass.
2. Compiled all four modules locally in import order with `lcompile.py`. Scanned for
   forbidden declarations and hollow definitions. Only the named strict-perfectness core
   has `sorry`; the explicit complex uses genuine Mathlib constructions, with no witness
   selected from a postponed existence proof. Ran `#print axioms` for all four public
   declarations in a temporary scratch module: construction and comparison use only
   `propext`, `Classical.choice`, `Quot.sound`; core and item also use `sorryAx`.
   The scratch module was removed before delivery. Verdict: pass, subject to the core hole.
3. Read the core statement and full proof docstring against `Scheme.IsStrictlyPerfect`.
   Extension has bounds [-r,0]; finite bases give finite free sheaves via `tildeFinsupp`,
   `mapFreeIso`, unit preservation and coproduct preservation. Empty open, zero ring,
   zero ranks and r=0 cause no exception. The core omits M, q and the derived comparison,
   and asserts a property of one explicit complex, so it is a strict part of the argument,
   not an existential restatement. Repeated searches with different words using LeanFinder,
   Loogle, recorded grep and repository rg; only generic APIs were found. Closing the core
   requires implementing finite-basis transport as well as extension bounds, beyond a
   few-minute repair. Verdict: valid decomposition, zero net holes removed.
4. Read the comparison morphisms from source to target: extend q, compare the extended
   single, apply the inverse site equivalence, and invert under Q. The unit and
   overFunctorEquiv compare exactly the restricted sheaf. Generic Mathlib lemmas already
   provide the shortest comparison route. Removed redundant new-module imports. All old
   dependency edges are accounted for above. Read the unit record and its realized fields;
   the finite-resolution argument remains within the existing finite-duality route and no
   unit statement or step is bypassed or edited. Verdict: pass.
5. Checked all four node records against their Lean declarations and constructions.
   Existing node changes are restricted to proof, proof_deps and proof_origin/lean fields;
   the new nodes have source, provenance, three search kinds and Lean records. The core
   carries the finite-free sheafification dependency; the item uses precisely the explicit
   complex, core and comparison. Verdict: pass.

Second reading changed only the redundant imports, added independent search records and
completed the dependency-accounting and review report. No mathematical statement changed.
