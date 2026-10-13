## What changed

Replaced the proof hole of
`AlgebraicGeometry.schemeGlobalHom_shiftedHypercohomology_equiv` with a complete
Lean composition of two comparisons. The original statement and visibility are
unchanged.

Four private helpers in the item's module are proved without any new holes:
`unitToGlobalEquiv`, `globalSectionsUnitIso`, `globalSectionsZeroIso`, and
`globalSectionsShiftIso`. Evaluation at 1 and restriction from the top open
construct the ordinary global-section comparison. Right derivation commutes
with exact scalar-forgetting, and exact scalar-forgetting commutes with
cohomology. Combining these APIs with the derived global-section shift and the
homology shift gives a natural isomorphism for arbitrary derived sheaf K:
the underlying H^k(RΓ(K)) group is H^0(X,K[k]). Thus the global-section part is
proved independently of internal Hom and needs no K-flat representative.

The one remaining internal-Hom shift comparison is stated in the new module
`Sheaf.Algebra.Homology.DerivedInternalHomShiftComparison`. It compares derived
sheaf objects, before global sections or cohomology, and contains no module-valued
RΓ or universe for module-derived localization. Applying hypercohomology to its
isomorphism and composing with `globalSectionsShiftIso` proves the original
additive equivalences. The two categorical naturality equations, evaluated on
an element, prove the original second-variable naturality.

Added proof-only imports of the new module,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`, and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`. Existing public imports stay.
Updated the original DAG node's proof, proof_deps and proof_origin accordingly.
The original module/declaration docstrings are preserved; their representative-based
proof description explains the historical route, while the DAG records the actual route.

The main theorem has a scoped, documented heartbeat limit of 800000: elaborating
the equivalence between site and ringed-space presentations exceeds the default
heartbeat budget. Compilation remains below the prescribed 60-second file limit.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.schemeGlobalHom_shiftedHypercohomology_equiv`
(node `lem-sc-global-hom-shifted-hypercohomology`). No sorry remains in its module.

Added one hole:
`CategoryTheory.derivedInternalHom_shift_comparison`
(node `lem-pur-derived-internal-hom-shift-comparison`), whose proof is exactly
`:= by sorry` in its own new module. The docstring gives the signed reindexing,
differential calculation, inverse, resolution descent and naturality argument.
This is a decomposition, not a net hole reduction: one hole closed and one added.
The evaluation and derived-global-section steps, including their naturality,
are fully implemented in Lean. No definition contains a sorry or chooses an
arbitrary witness from the new existence theorem; its witness is eliminated only
inside the proof of the original theorem.

Both modules compile together in import order. The item's module compiles without
warnings. The dry run additionally checks every added declaration with the
maintainer's axiom/sorry probe and the stage-3 preflight.

## No longer needed

Removed these proof-only imports from the item's module:

- `Sheaf.Algebra.Homology.KFlatResolution`
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`
- `Sheaf.Algebra.Homology.QuasiIsoHomComplexMap`

The original comparison's direct proof dependencies no longer include
`lem-pc-kflat-resolution`, `lem-pur-hom-kflat-into-kinjective`,
`lem-pur-rhom-well-defined`, `prop-pur-kinjective-resolutions-exist`, or
`def-pur-hom-complex`. The first two are not needed anywhere in this reduction.
The other three remain dependencies of the internal-Hom construction or of the
new shift lemma, rather than separate global-section obligations. In particular,
`QuasiIsoHomComplexMap` remains transitively imported by `DerivedInternalHom`;
its direct import was redundant. No claim is made that these modules become
unreachable from every other target path.

## Where the brief, the DAG or earlier work was wrong

The listed dependency statements provide resolution comparisons and
quasi-isomorphism invariance but no signed shift comparison of the internal
Hom complex. That step therefore needs the new node. It does not obstruct
implementing the rest of the argument.

The original plan unnecessarily selected a K-flat representative for the global
comparison. Evaluation at the unit gives an isomorphism of ordinary functors;
right derivation plus exact scalar-forgetting gives the global comparison on
all derived sheaves directly. K-flatness of Hom inputs and K-injectivity of the
resulting Hom complex are unnecessary for this step.

The new shift lemma was checked mathematically at m=n=0 (identity signs and
reindexing), m=n with odd m (alternating signs compensate the differential),
negative m,n (integer parity gives the same sign identities), zero arguments,
and unbounded complexes (only reindexing products is used). There are no added
boundedness, quasi-coherence, or universe-identification hypotheses.
The unit record's realized statement/steps are empty; no realized unit node is
bypassed, and the original finite-duality/shifted-Hom route above this item stays.

## New nodes

`lem-pur-derived-internal-hom-shift-comparison`, in
`dag/nodes/sec-picard-framework/lem-pur-derived-internal-hom-shift-comparison.json`,
is the relative-degree shift isomorphism of internal derived Hom, natural in its
second argument. Its Lean declaration is
`CategoryTheory.derivedInternalHom_shift_comparison` in
`lean/Sheaf/Algebra/Homology/DerivedInternalHomShiftComparison.lean`.
It is strictly an internal derived-sheaf step: neither global sections nor
cohomology nor module-valued localization appears in its statement. The original
theorem still requires the proved evaluation, right-derivation, scalar-forgetting,
and cohomology-shift comparisons. Blueprint searches and library/Mathlib searches
found no matching general statement; LeanSearch was unavailable and this is
recorded without a negative verdict. No statement correction, forced adaptation,
or change record is needed.

## Second reading by T4

1. **Unchanged interface: pass.** Compared the delivered item with the repository
   using `diff -u`. The entire existing theorem signature, its visibility,
   universe parameters, both category-instance hypotheses, all integer degrees,
   additive-equivalence conclusion and second-variable naturality equation are
   byte-for-byte unchanged. Both existing public imports remain unchanged.
   There is no existing definition change, adaptation or change record.

2. **Proof and axioms: pass as a decomposition.** Independently compiled both
   modules in import order with `lcompile.py --all`: clean, 35.0 and 38.5 seconds.
   A scratch copy with explicit `#print axioms` for every private helper and the
   two public theorems compiled in 22.8 seconds. `unitToGlobalEquiv`,
   `globalSectionsUnitIso`, `globalSectionsZeroIso` and `globalSectionsShiftIso`
   use only `propext`, `Classical.choice`, `Quot.sound`. The main theorem and
   `derivedInternalHom_shift_comparison` additionally use `sorryAx`, as reported.
   There is exactly one source `sorry`, the named split theorem. No forbidden
   declaration or attribute, hollow definition, or arbitrary existence-witness
   definition was added. The split theorem's witness is eliminated inside a proof
   of a proposition, rather than used to define public data.

3. **Split statement and search: pass.** Read the new Lean module and its entire
   node, together with `DerivedInternalHom`, `HomComplex` and
   `RingedSiteZerothHypercohomology`. The new statement isolates an isomorphism of
   derived sheaves, with only the second-variable naturality used by the parent;
   it does not restate the parent's global cohomology equivalence. Its small-site,
   commutative-ring sheaf and derived-category hypotheses match the construction.
   Read [Stacks Section 21.34](https://stacks.math.columbia.edu/tag/0A8X)
   for product terms, differential and representative invariance, and
   [Tag 08JA](https://stacks.math.columbia.edu/tag/08JA) for the historical
   global comparison. The signed shift argument is the worker's calculation
   from those definitions, not a claim that 08JA states this shift theorem.
   In degree k the source postcomposition coefficient is (-1)^(n-m),
   whereas the target coefficient is (-1)^n; their ratio is (-1)^m.
   For precomposition the source coefficient is -(-1)^k and the target
   coefficient is -(-1)^(k+m), with the same ratio. Multiplication by
   (-1)^(m*k) therefore commutes with both differential terms.
   Tested m=n=0, m=n=1 with nonzero differential, m=-1,n=2, zero inputs,
   characteristic two, and complexes concentrated in degrees a,b: both sides
   concentrate in degree b-a+m-n. Reindexing products imposes no boundedness.
   Postcomposition commutes with signs and reindexing; K-injective representative
   maps give naturality after localization. The docstring gives this full route.
   Repeated LeanFinder, Loogle and library/Mathlib searches with different terms;
   results are recorded on the new node. Ordinary HomComplex shifts do not supply
   this sheaf-valued comparison. Closing the split requires a chain-isomorphism
   construction and localization descent, not a short application of an existing
   declaration, so it remains explicitly open.

4. **Route and pruning: pass.** Read the proof from its final composition back to
   evaluation at 1. The naturality proof composes the evaluated naturality of
   `globalSectionsShiftIso` with the image of the internal-Hom naturality equation.
   Exact scalar-forgetting supplies the degree-zero comparison, and the derived
   shift API supplies arbitrary degrees without choosing a Hom representative.
   Both public imports are required by the signature. Each added proof-only
   import is justified: the exact-functor composition/homology API, the derived
   global-section shift instance, module K-injective-resolution instances, and
   the new comparison, respectively. The new module's public import is required
   by its statement. `No longer needed` lists all five old proof dependencies
   absent from the new direct dependency list and all three removed imports,
   without claiming globally unreachable modules. Read
   `dag/units/sk-thm-picard-duality.json`: its realized statement and sole step
   have empty node lists. No realized unit node or chapter route is bypassed.

5. **DAG agreement: pass.** The existing node changes only `proof`, `proof_deps`
   and `proof_origin`; its statement and Lean signature record are unchanged.
   Its steps accurately describe the private comparisons and final composition.
   `proof_deps` is the union of their cited nodes. The new node's Lean statement
   matches the new theorem verbatim, and its source, proof, search records,
   creation provenance, blueprint ancestry, chapter and unit are present.
   Its dependencies supply the Hom complex, K-injective resolutions and
   representative invariance needed by the documented proof, without a cycle
   back to the parent.

**Second-reading changes:** added independent search results to the new node
and this concrete review record. No Lean proof, statement, definition or import
needed repair. The accounting remains one original hole closed and one strictly
smaller hole added: net zero, a decomposition rather than a complete proof.
