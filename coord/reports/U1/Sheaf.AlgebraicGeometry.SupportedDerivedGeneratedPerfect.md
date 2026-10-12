## What changed

The signature, universes, public imports, definitions, and existing docstrings of
`Sheaf.AlgebraicGeometry.SupportedDerivedGeneratedPerfect` are unchanged. Its proof now
applies `AlgebraicGeometry.supported_perfect_generator` to the closed complement of V,
uses `AlgebraicGeometry.perfectObjectCompact` on the resulting perfect E, and supplies
the resulting triangulated closure, compactness, support, and shifted-Hom detection
facts to `AlgebraicGeometry.supported_derived_generated_perfect_core`.

The new module `Sheaf.AlgebraicGeometry.SupportedDerivedGeneratedPerfectCore` isolates
the remaining construction for a **given compact supported detector**; it neither
constructs a perfect generator nor proves compactness of perfect objects. Its theorem
is a strict part of the argument after those two steps, rather than the original
existence statement under another name. It does not require V to be quasi-compact or Y
to be quasi-compact/quasi-separated, since the needed triangulated closure, compactness,
and detection facts are explicit hypotheses. It has a source and a complete proof in
words, including support preservation, transfer of compactness to the supported full
subcategory, the small-Hom universe check, rotation, and prepending zero.

Proof imports were moved to their remaining user, and unnecessary explicit imports of
DerivedCategory and Products in the new module were removed. All new proof-only imports
are plain `import`. `DerivedQCohDirectSums` is public in the new module because its
canonical coproduct structure occurs in the compactness hypothesis.

## Proved and sorry left

Original hole closed syntactically:
`AlgebraicGeometry.supported_derived_generated_perfect`
(node `lem-sc-supported-derived-generated-perfect`). There is no sorry in the item module.

New hole added:
`AlgebraicGeometry.supported_derived_generated_perfect_core`
(node `lem-sc-supported-derived-generated-perfect-core`), whose complete proof body is
`by sorry`. No other holes were added. This is a **decomposition, not a completed proof**:
one original hole is replaced by one strictly smaller hole: the local named-hole count
is one closed minus one added. No positive ledger progress is claimed.
The original theorem still depends on this open theorem and on open imported results.

Both modules compile cleanly through lcompile.py. Scratch copies with `#print axioms`
show exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for each delivered
theorem. They contain no new definitions, axioms, unsafe code, opaque declarations,
implemented_by, extern, or hidden/admitted proof fragments.

## No longer needed

Removed from the item's direct imports:
`Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums`,
`Sheaf.AlgebraicGeometry.DerivedQCohDirectSums`,
`Sheaf.CategoryTheory.CompactGeneratorsBuildObjects`, and
`Sheaf.CategoryTheory.WeakTriangulatedGenerator`.

Removed from the item's direct proof_deps:
`lem-pc-derived-ambient-direct-sums`, `lem-pc-derived-qcoh-direct-sums`,
`lem-pc-compact-generators-build-objects`, and `def-pc-generators`.
These four nodes remain required by the open core theorem; their modules are retained
there (WeakTriangulatedGenerator is supplied by the public import of
CompactGeneratorsBuildObjects). They are not globally pruned. PerfectObjectCompact and
SupportedPerfectGenerator remain directly used. No module is claimed to leave the
targets' import closure; pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The first worker's core theorem had no compactness, perfectness, support, or
triangulated-closure hypothesis for E/the supported category, despite using these in its
proposed proof. The detector hypothesis alone did not justify that argument. The new
node's natural-language statement simply repeated the original existence theorem and
thus did not match its Lean statement. It also copied the original node's review and
split-report metadata and claimed old searches that were not this node's actual
searches. These faults are repaired in the sandbox, without changing an existing Lean
statement or definition. No change record is required: the corrected statement is new
and has no landed users.

The telescope theorem `CategoryTheory.compactGenerators_buildObjects` has coproduct
universe max w v. To obtain the required Type u indices independently of the localization
Hom universe, its application must use a category with u-small Hom sets. K-injective
resolutions on the small ringed site of opens identify the Homs with quotients of
u-small chain-map sets. The core docstring and node include this check.

Existing tools used below the unit level are `lem-pc-stalk-direct-sums` for the missing
stalk/coproduct comparison and `prop-pur-kinjective-resolutions-exist` for that Hom-size
check. The latter is a tool from sec-smooth-purity, not a replacement of this unit's
route. Its Lean theorem was read: it applies to every small commutative ringed site,
with no finiteness or Noetherian hypothesis, so it applies to the opens of Y. No tool_uses
field was written; that is the maintainer's field.

## New nodes

`lem-sc-supported-derived-generated-perfect-core` now states the construction from a
given compact supported detector, exactly matching its Lean declaration and the
remaining steps of the source argument. Its source is Stacks duality.tex,
`lemma-when-sheafy`, proof of (3) in Section [0E4G](https://stacks.math.columbia.edu/tag/0E4G),
and derived.tex, `lemma-write-as-colimit`, [09SN](https://stacks.math.columbia.edu/tag/09SN).
Its support/generator input is obtained in the original theorem from
[0A9A](https://stacks.math.columbia.edu/tag/0A9A); compactness is obtained from the already
stated perfectObjectCompact. The new node has honest search results and no inherited
review records. The original node changes only proof, proof_deps, and proof_origin.

## Second reading by U1

1. **Interface preservation: pass after repair.** Read the repository module whole and
   compared it with the sandbox using diff. The existing theorem signature is byte for
   byte unchanged, as are its existing docstring and public imports. Changes are confined
   to its proof and plain proof imports. The complement argument uses openness to show
   closedness, double complement to recover hV, and y not in the complement iff y in V
   to match the support of E and Q. No existing statement was weakened or strengthened.

2. **Kernel/holes: pass as decomposition.** Both files compile cleanly in import order.
   Scratch copies print only the three standard axioms plus sorryAx, which is expected
   from the named open core and remaining imported holes. The item has no sorry; the
   core has exactly one public named theorem with proof `by sorry`. No definitions or
   forbidden trust escapes were added, and no data is chosen into a definition from an
   unproved mere-existence theorem. The remaining hole is reported explicitly above.

3. **New statement: repaired; mathematical reduction passes.** The original new theorem
   lacked the hypotheses its proof used; the new node also restated the item. Replaced
   that statement by the given compact/support/triangulation/detection version, and
   supplied those hypotheses from existing declarations in the original proof. The
   docstring explains the full reduction from 09SN, including shifts of coproducts,
   zero prepending, and the conjugacy of 1-s checked on every coprojection. Checked
   V empty (the whole quasi-coherent category), V all of Y (only zero supported Q),
   Q zero (the zero sequence and empty coproducts), E zero (detection forces every
   supported object to be zero), and positive/negative shifts. No extra finiteness or
   boundedness is needed. Schemes and their module sheaves remain in universe u; the
   chosen localization Hom universe w is handled by the small-Hom step.

   Searched lean/Sheaf and lean/WeilConjectures, the upstream WeilConjectures and
   Comparator trees, and Mathlib. In particular DerivedQCohPerfectGeneration calls
   the present item, so using it here would be circular; CompactGeneratorsBuildObjects
   is the general construction, with its initial sum and differently oriented triangles,
   and does not already give this supported ambient/cofan statement. New msearch queries:
   LeanFinder "triangulated subcategory supported perfect compact generator telescope
   coproducts" returned only T-structure declarations; grep
   "homotopy.?colimit|compact.*generat|generat.*compact" in CategoryTheory returned no
   matches. LeanSearch for the compact weak-generator sequential construction returned
   HTTP 500, recorded as unavailable rather than a successful no-match search. No exact
   existing declaration closes the remaining transport/construction in a few minutes.

4. **Route/pruning: pass.** Read the 0E4G proof of (3), 0A9A, and 09SN, and the precise
   statements of supported_perfect_generator, perfectObjectCompact,
   derivedAmbientDirectSums, derivedQCohDirectSums, and compactGenerators_buildObjects.
   The original construction and compactness steps are now Lean applications of those
   first two declarations. The latter's canonical coproduct structure matches the
   core's letI compactness hypothesis. The remaining plan is carried by the core,
   not discarded. All four old proof_deps no longer directly used by the original
   theorem are listed above and retained below. The unit sk-thm-picard-duality has
   realized.statement=[] and realized.steps=[[]]; it is unchanged. Blueprint searches
   for telescope and supported perfect found no duplicate of this construction; the
   new node records the nearest ancestor lem-sc-finite-duality and its full via chain.
   No unit step or chapter route was bypassed, and no global pruning is claimed.

5. **DAG agreement: repaired and passes.** The original node now records the exact three
   proof applications: generator, perfect compactness, and the core. Its proof_deps are
   their union. The core node's statement matches the supplied E/Q and all hypotheses,
   with no spurious existence of a perfect generator. It has a verbatim Lean signature,
   source, proof steps, union proof_deps, honest logged searches, created record,
   blueprint reference, chapter/unit and lean record. The earlier copied reviewed,
   reviewed_lean and split_report fields were removed from the new node.

Changes made by this reading: supplied the missing compactness/support/triangulation
hypotheses; proved compactness in the caller; removed unused direct proof imports;
expanded the open theorem's complete docstring proof; rebuilt the new node and updated
the original node's proof fields; corrected source labels, searches, blueprint via chain, an explicit T-complement=V reference,
and the report's progress accounting. No existing signature or definition changed.
