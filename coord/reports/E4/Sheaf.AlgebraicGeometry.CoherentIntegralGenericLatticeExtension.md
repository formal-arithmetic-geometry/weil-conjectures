## What changed

Completed `AlgebraicGeometry.Scheme.Modules.exists_generic_ideal_extension` in
`Sheaf.AlgebraicGeometry.CoherentIntegralGenericLatticeExtension`, with its exact original
signature, universes, visibility and docstring. All original public imports remain unchanged.
The proof follows all four steps of the existing node, and the unit realization is unchanged.
The node copy expands the ideal-power and stalk-transport proof steps to match the Lean.

The concrete lattice is `(IdealSheafData.vanishingIdeal (Z \ U)) ^ n`, constructed using the
existing ideal-sheaf power operation. Private proved helpers identify its module with the
recursive power via affine section ranges, distribute tensor products over the finite free
coproduct, establish coherence, and transport invertibility from a restricted stalk.
The extension comes from the existing `coherent_homs_over_open` theorem; its still-unproved
structural-data dependency remains an existing downstream item. No definition is introduced
or changed, and no data is chosen in a definition from an unproved existence theorem.

Added proof-only imports for the tensor-Hom adjunction, finite biproducts, monoidal coherence identities and closed-immersion
pushforward. The second reader removed the redundant direct imports of subobject
limits and finite generators; the required APIs remain available through retained imports. Retained the original affine ideal-product import. The separate helper module
left by the interrupted attempt was removed: all its lemmas are proved private helpers here.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_generic_ideal_extension`
(node `lem-weil-pbc-coherent-integral-generic-lattice-extension`).

There are no `sorry`s left in the item and no holes added anywhere. Every private helper
has a complete Lean proof. This closes the item from its existing dependencies, rather than
splitting its hole into new statements. It still depends transitively on the existing
`AlgebraicGeometry.Scheme.coherent_homs_over_open_data` hole and existing holes reached
through `AlgebraicGeometry.Scheme.Modules.isCoherent_kernel_cokernel_biprod_and_submodule`,
which this delivery does not own. The axiom check on the current compiled baseline confirms
`sorryAx` in those two used declarations, the private `ideal_coherent` helper and the item;
the other eight private helpers use only the three permitted axioms.

The compiler checked the complete file without warnings. The zero ideal power is handled
separately in the affine-range comparison; the finite coproduct argument also works with
`Fin 0`. Neither case needs an added hypothesis.

## No longer needed

No baseline proof-dependency node or module is pruned: all seven original proof dependencies
are used. No original import was removed. No unit statement or realized proof step is bypassed.
The second reader removed the newly added proof-only imports
`Mathlib.CategoryTheory.Subobject.Limits` and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`: their used APIs
are already public through the retained affine-products and closed-immersion imports.
These removals do not prune any baseline node or target-closure module.

Within the unfinished sandbox draft, `Sheaf.AlgebraicGeometry.IdealPowerFiniteFreeLattice`
is no longer a separate proposed module, and its imports of
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree`,
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic`,
`WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator` and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` are no longer direct
imports. The first is replaced by the narrower tensor-Hom adjunction import; the remaining
APIs are already publicly available through retained imports. The redundant direct import
of `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` was also removed from the
draft, since `ClosedImmersion` imports it publicly. These draft removals do not prune any
baseline node or target-closure module.

## Where the brief, the DAG or earlier work was wrong

The interrupted attempt had no report or node delivery and did not compile. It omitted
imports exposing the affine naturality and quasi-coherent-unit APIs, confused the categorical
`Limits.Sigma.map` with the type-level `Sigma.map`, assumed a coproduct-mono instance without
providing finite biproducts, and used incorrect comparison and unitor rewrite names and
orientations. These issues are repaired; the independent helper module has been eliminated.

The mathematical statement and original four-step plan are valid. Search found relevant
Mathlib coproduct and source tensor-Hom APIs, but no existing theorem with the full generic
ideal-lattice extension conclusion. No statement correction or forced adaptation is needed.


## Second reading by E4

1. **Interface unchanged: pass.** Compared the entire delivered module with the repository
   using `diff -u`. The sole existing theorem `exists_generic_ideal_extension` has its
   signature, universe, visibility and docstring byte for byte unchanged. No existing
   definition changed and no change record or forced adaptation is needed. The additions
   are nine private proved helpers, the target proof and proof-only imports.

2. **Proof and construction: pass.** Compiled the module locally with `lcompile.py`, with
   no error or warning, and searched its text for `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by` and `extern`: none occurs. A scratch copy printed the axioms of all
   ten declarations. Eight helpers use only `propext`, `Classical.choice`, `Quot.sound`;
   `ideal_coherent` and the item also use existing `sorryAx`. Separate dependency probes
   locate this in the existing coherent closure theorem and `coherent_homs_over_open`;
   the locally Noetherian coherence criterion, quasi-coherent kernel and closed-immersion
   pushforward theorems have only the permitted axioms. The ideal witness is the real
   construction `J ^ n`; maps and comparison isomorphisms are obtained within a theorem
   proof, and no definition chooses data from a mere unproved existence assertion.

3. **Split statements and small cases: pass.** No statements were split off, no new nodes
   and no new holes were added. Read the nine helper proofs. Affine range inclusion kills
   the cokernel projection by sheaf separatedness, then factors through its kernel; equality
   of the two subobjects supplies the power isomorphism. The zero power is explicitly the
   unit ideal. Tensor preservation of coproducts and unitors identify multiplication with
   the finite coproduct of the mono ideal inclusion, so its image is its source. Reindexing
   removes ULift without changing the rank. Empty `Fin 0` is allowed throughout. The
   coherence proof uses a quasi-coherent ideal submodule of the coherent structure module.
   The restriction-stalk helper transports bijectivity through `restrictStalkNatIso`, so
   the ambient module stalk map is invertible. No extra integrality or nonzero-rank
   assumption was introduced.

4. **Route, search and imports: pass after cleanup.** Read the integral-case paragraph of
   Stacks Tag 01YE at https://stacks.math.columbia.edu/tag/01YE (the local cited TeX is not
   present), and matched the complement ideal, extension by a power and finite-sum identity
   to the proof. Read the actual statements of `reduced_induced_closed_subscheme`,
   `quasi_coherent_ideal_zero_set_affine`, `coherent_homs_over_open`, the affine power-range
   clause, the coherent submodule clause and the locally Noetherian criterion. These give
   exactly the facts extracted in the four steps. Searched `lean/Sheaf` and the upstream
   algebraic-geometry/sheaf modules, and ran LeanFinder with the alternate query "An ideal
   subsheaf times a finite free sheaf is a finite coproduct of copies of the ideal subsheaf".
   Results were module finiteness and generating-section APIs, not a replacement for this
   conclusion. Upstream `freeTensorFreeIso` covers two free factors, not an arbitrary
   ideal factor. No shorter complete route was found. Removed the redundant proof imports
   `Mathlib.CategoryTheory.Subobject.Limits` and
   `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`, and recompiled
   successfully. All seven baseline proof dependencies remain used, so `No longer needed`
   prunes none. Read `dag/units/sk-thm-p1.json`: the item's four-step reduction is below
   the unit level and changes none of its statement or realized proof steps.

5. **DAG agreement: pass.** The node diff changes only the prose of proof steps 3 and 4,
   explaining the affine-range, tensor-coproduct and stalk-conjugacy arguments actually
   implemented. Its statement and Lean signature are unchanged. The union of `uses`
   still equals its unchanged `proof_deps`, and the source-based `proof_origin` remains
   appropriate. There are no new nodes to validate.

**Second-reading changes:** removed the two redundant added proof imports, corrected the
report's transitive-hole accounting to include the existing coherent closure dependency,
and added this independent reading. No mathematical proof or interface repair was needed.
