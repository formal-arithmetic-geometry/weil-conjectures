## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.coherent_artin_rees` by a complete Lean
reduction to one affine geometric comparison. Its signature and public imports are unchanged.
The proof obtains finite affine sections by the existing public theorem
`AlgebraicGeometry.Scheme.Modules.coherent_affine_sections_finite`, applies Mathlib's
`Ideal.exists_pow_inf_eq_pow_smul` to the image of the subsheaf on each affine, extracts a
finite affine cover, and chooses `Finset.sup` of its bounds. The module formulas at `c` and
`n` and the identity `(n-c)+(c-k)=n-k` prove that the larger common bound works. The empty
cover uses bound zero without an inhabitedness assumption.

A proved private helper descends membership in a monomorphism's section range: local
preimages agree on overlaps by injectivity, then glue. This descends the affine comparison
to every open. The final inclusion follows from the already proved
`AlgebraicGeometry.formalModuleQuotient_factor` applied to the pullback projection to `G`,
and the pullback commutativity identity.

Repair of the maintainer's duplicate-statement return: removed the copied private
`AlgebraicGeometry.Scheme.isFiniteType_over` theorem and its elaboration options.
The matching theorem in `CoherentKernelCokernelLocallyNoetherian` is private, so instead
of copying or changing its visibility, the proof now imports and applies the stronger
public `coherent_affine_sections_finite` result already in the library. This removes
the need for the direct `QuasicoherentFiniteTypeAffine` proof import. No interface
change or adaptation is made. `WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator`
supplies the proved naturality and repeated-restriction identities used by gluing.

Added `Sheaf.AlgebraicGeometry.ArtinReesAffineComparison`. Its one statement compares a
fixed equality in the affine section modules with the equality of subsheaves on subopens.
It assumes neither Noetherianity nor coherence nor the existence of an Artin-Rees bound.
It therefore isolates the geometric part, while the module Artin-Rees argument, increase
of the bound, compactness, global descent, and the final inclusion are all proved here.

Validation: both delivered modules compile through `lcompile.py`; all imports only needed
by proofs are ordinary imports. Searches: Loogle found the precise module Artin-Rees
lemma; LeanFinder found ideal-sheaf extensionality, not this module comparison; grep found
only the module theorem and a private affine-range argument. LeanSearch was unavailable
(HTTP Internal Server Error), recorded as unavailable rather than as no match.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.coherent_artin_rees`
(node `lem-weil-pbc-coherent-artin-rees`) by decomposition, not a sorry-free proof of its
axiom closure. Added exactly one hole:
`AlgebraicGeometry.Scheme.artin_rees_affine_comparison`
(node `lem-weil-pbc-artin-rees-affine-comparison`). Its proof is exactly `:= by sorry` in
its own new module, with a complete proof in words. There are no holes in private helpers,
definitions, or the original module. Thus one original hole is closed and one is added;
net hole reduction is zero, with substantial algebraic and global glue proved.

Edge cases checked for the new statement: empty affine open, zero modules and subsheaf,
zero ideal, unit ideal, `c=0`, `n=0`, `c=n`, and `n<c`. The comparison itself is valid for
arbitrary exponents, since it is conditional on the explicit affine submodule equality
and uses truncated subtraction on both sides. The main theorem only applies it when
`c ≤ n`. Affine restriction and the equivalence preserve the empty and zero cases.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian` and the corresponding
proof dependency `lem-weil-pbc-coherent-kernel-cokernel-locnoeth`. Neither coherence nor
finite generation of `G` is needed: module Artin-Rees accepts any submodule of the finite
module `F(U)`. This prunes that argument from this theorem's proof route. It is not a claim
that this module becomes unreachable from every other target.

Removed these direct proof imports from the item, moving their geometric use to the new
comparison item's plan:

- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`

Their nodes remain needed by the affine comparison, as do
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-module-restriction-open-immersion-colimits`, and
`def-weil-pbc-coherent-formal-module`. No claim of pruning those transitive dependencies
is made. The repair additionally removes the direct proof import
`Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine` and replaces its direct DAG
dependency `lem-weil-pbc-quasi-coherent-finite-type-affine` with
`lem-weil-pbc-coherent-affine-sections-finite`. The affine criterion remains a dependency
of the comparison's plan; this is only direct-route pruning.
The existing public `CoherentFormalModule` import remains because it is part of the
item's public interface. No blueprint unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan unnecessarily proved the subsheaf `G` coherent and its affine sections
finite. The module Artin-Rees theorem only needs `F(U)` finite. The revised DAG records the
actual proof, including the proved larger-bound calculation and the explicit sheaf-gluing
argument. The source and target statements remain unchanged.

The returned delivery correctly identified a duplicate private finite-type restriction
proof. The earlier report and second reading incorrectly accepted reproducing this
private helper. The repair uses the library's public finite-affine-sections theorem
and removes the duplicate entirely. The previous second-reading record was removed
because it describes the superseded proof; a fresh independent reading is required.

The local literature checkout is absent on this machine. Read the source directly at
https://stacks.math.columbia.edu/tag/01YA; its proof is precisely reduction to module
Artin-Rees using a finite Noetherian affine cover. No source error was found.

## New nodes

`lem-weil-pbc-artin-rees-affine-comparison`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-artin-rees-affine-comparison.json`, records
only the geometric transport for fixed exponents on one affine open. Its proof plan uses
the existing ideal-product, cokernel/image, kernel, restriction and affine equivalence
nodes. It does not assume or assert an Artin-Rees bound. Blueprint searches for
`Artin-Rees` and `affine.*sections` found no imported blueprint node stating this fact;
the nearest blueprint ancestor is `thm-weil-pbc-finite-etale-lifting`, through 01YB's
uses of 01YA. No change record is needed: no existing statement, definition, universe,
or visibility changed.



## Second reading by U4

1. **Interfaces: PASS.** Diffed the delivered item against the repository version.
   The existing `coherent_artin_rees` signature is byte-for-byte identical, and its
   public import is unchanged. Only its proof, proof imports and proof docstring changed;
   the two added private helpers expose no interface. The comparison is a new theorem
   in its own new module. No definition, target statement or visibility was changed,
   and no change record or forced adaptation is required.
2. **Proof and axioms: PASS as a decomposition.** Independently compiled both modules
   with `lcompile.py --all`, without errors or warnings. Scratch copies with
   `#print axioms` show only `propext`, `Classical.choice` and `Quot.sound` for
   `app_injective` and `range_of_locally_range`; the original theorem and new comparison
   additionally use `sorryAx`, as expected for the remaining geometric comparison.
   The only textual hole is the whole proof of the named public comparison theorem.
   There are no new definitions, arbitrary data witnesses from unproved existence,
   forbidden declarations or hidden partial-proof holes. Choosing module bounds uses
   the proved Mathlib Artin-Rees theorem; the final factor is used only as a witness
   inside a proof, not to define data.
3. **Split statement: PASS.** Read the comparison, its full docstring and new node.
   On an affine, exactness and the quasi-coherent module equivalence identify the two
   inclusions with the specified submodules of F(U). Equality of these submodules
   gives compatible equality of subsheaves, hence equality on all subopens. This
   argument does not need Noetherianity or finite generation. Checked empty affines,
   zero modules, zero and unit ideals, zero exponents, equal exponents and n<c:
   both sides use the same truncated exponent, and the module equality is an explicit
   hypothesis. The comparison supplies no bound and proves no global compactness or
   descent, so it is strictly a geometric part of the argument, not a renamed item.
   Repeated searches using the different query "quasi-coherent module subobjects
   determined by global sections on affine open" (LeanFinder),
   `Ideal.exists_pow_inf_eq_pow_smul` (Loogle), and
   `pullback.*quasicoherent|range.*restriction|subobject.*sections` (grep).
   Searched repository Lean sources for affine range and subobject comparison as well.
   Results contain the exact module Artin-Rees lemma and related private helpers,
   but no existing public theorem with this comparison's statement. These searches
   are recorded by `msearch.py` in the sandbox search log. Closing the geometric
   comparison would require further formal affine transport, not a short application
   of any match found.
4. **Route and pruning: PASS.** Checked the finite affine subcover, `Finset.sup`
   bound (including empty cover), the increase-of-bound identity, local lifting and
   gluing in both directions, and the final pullback factorization. Proof-only
   imports are ordinary imports; the comparison's public imports provide the
   definitions and quasi-coherence predicate in its signature, while its ordinary
   imports record the geometric plan. Compared all old `proof_deps` against the
   report's pruning list: the coherence-of-G and direct finite-type criterion routes
   are removed, the geometric dependencies move to the comparison, and the formal
   module definition remains publicly imported and transitively needed. No module
   is claimed globally unreachable. Read `dag/units/sk-thm-p1.json` and its `realized`
   statement and four steps; this below-unit reduction bypasses none of those nodes.
   Confirmed the source's finite-affine-cover reduction at
   [Stacks 01YA](https://stacks.math.columbia.edu/tag/01YA), with affine tensor and
   module equivalence facts in [01I8](https://stacks.math.columbia.edu/tag/01I8) and
   [01IC](https://stacks.math.columbia.edu/tag/01IC).
5. **DAG: PASS.** The existing node changes only `proof`, `proof_deps` and
   `proof_origin`. Its steps follow the actual Lean reduction, and its dependency
   list is their union. The new node has its source, complete geometric proof,
   searches, blueprint ancestry, chapter/unit, creation record and verbatim Lean
   signature. Its dependency union agrees with its proof steps. The original and
   new natural-language statements agree with their Lean signatures.

Second-reading changes: added this independent review record and repeated validation
and searches. No repair to the Lean proof or DAG was necessary. The delivery remains
one closed original hole and one new strictly smaller hole: a decomposition with zero
net hole reduction, not a completed proof of the original theorem's axiom closure.
