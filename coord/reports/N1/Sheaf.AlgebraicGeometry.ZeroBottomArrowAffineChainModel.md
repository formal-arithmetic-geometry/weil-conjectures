## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.zeroBottomArrow_affine_chain_model` in
`Sheaf.AlgebraicGeometry.ZeroBottomArrowAffineChainModel` with the original three-step
construction. The statement and its existing docstring are unchanged.

Two proved private helpers supply the missing glue. `exact_restriction_derived_iso` uses
uniqueness of left derived functors to compare the chosen derived pullback with the derived
functor of an exact restriction. `scheme_affine_representative` transports bounded finite-free
complexes to the localized site with `Modules.overEquiv`, applies the existing
`perfect_affine_map_representative`, and transports its chain map and factorization back.
The main proof restricts K, identifies the restricted M with B.X a using bottom homology,
constructs the actual single complex A, represents the conjugated arrow, and transfers its
bottom homology invertibility through `DerivedCategory.homologyFunctorFactors`.

Added proof-only imports for derived exact-functor functoriality, restriction of free sheaves,
exactness of restriction, and uniqueness of left derived functors. Updated the item's DAG
proof, proof dependencies, and proof origin to match these arguments. No new modules,
interface changes, or adapted consumers.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.zeroBottomArrow_affine_chain_model`
(node `lem-sc-zero-bottom-arrow-affine-chain-model`). No new holes are added, and no
`sorry` remains in the delivered Lean source. Both private helpers are proved.

The argument uses the existing `perfect_affine_map_representative`. At second reading,
the scratch `#print axioms` probe for the main theorem and both private helpers reports
only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The complete
proof compiled cleanly through lcompile.py and passed the delivery axiom probe.
The first preflight identified file-level elaboration settings and local instance registrations
as interface commands. Those settings were moved inside proof bodies, and exactness of the
composite restriction is now supplied by two local proofs. The final dry run checks this
version; the second reading is reserved for the next worker.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology` and
removed `lem-pc-derived-open-pullback-homology` from the item's proof dependencies.
That theorem compares individual objects rather than maps; the proved natural exact
restriction comparison supplies what this proof needs. Its private import closure,
including its additional K-flat resolution argument, is not needed through this item.
Also removed `Sheaf.AlgebraicGeometry.DerivedPullbackComposition` and
`lem-pc-ringed-spaces-derived-pullback-composition`: composition of ordinary exact restrictions
and functoriality of `mapDerivedCategory` suffice here. Its composition-invertibility and
coherence proof modules are unnecessary through this item. Other public imports and the
affine-representative dependency stay.
Whether any module is unreachable from all targets is a maintainer closure calculation.

## Where the brief, the DAG or earlier work was wrong

The original route requires naturality of exact-open homology but its stated open homology
lemma only gives object isomorphisms. The delivery proves the needed natural comparison
instead of extracting unsupported naturality from that lemma. This repairs the glue without
changing a statement.

The affine-site derived localization can use `HasDerivedCategory.standard` in its own
morphism universe. Exact-functor derived functoriality supports different source and target
morphism universes, so a transported localization in the specified universe w is unnecessary.
The target's universe and all its hypotheses remain unchanged. The unit's theorem-of-cube
route is preserved. Rank zero, arbitrary integer a, and empty schemes impose no added
hypotheses.

## Second reading by N1

1. Compared the complete delivered module with the repository version. The existing
   theorem signature is byte-for-byte identical, as is its docstring. The only new
   declarations are proved private helpers; there are no definition, visibility,
   public-import, or consumer changes and no change record is needed.
2. Read both helpers and the main proof. The comparison uses the left-derived
   universal property recorded by `exists_derivedPullback`, not arbitrary existence
   data. A and B are explicitly constructed as a single complex and a termwise
   restriction. The affine lift uses fullness of the induced derived equivalence,
   then conjugates the transported chain map by the complex counit. The final
   homology isomorphism follows by naturality of Q's homology factorization. No
   forbidden declaration or local sorry occurs in the source.
3. No statements or holes were split off. Both private statements are proved.
   Checked rank zero (the free cofan is empty), arbitrary integer a (only predecessor
   and successor arithmetic is used), and the empty scheme (hx has no witness).
   Searched the library for natural derived/open-restriction comparisons and
   Mathlib for left-derived uniqueness and exact-functor factorization. The public
   `singleComplexOpenPullbackIso` uses a different restriction realization and
   imports the general derived-composition module being pruned; it does not shorten
   this proof's import closure. The existing affine representative theorem is used.
4. All added imports serve explicit proof declarations or exactness instances;
   both retained public imports serve the unchanged signature. The two old proof
   dependencies removed by the new proof are both listed under No longer needed.
   The unit record is unchanged: this item is a subordinate chain-model tool, not
   the unit statement or a replacement of the theorem-of-cube route. Its existing
   realized fields were not modified.
5. Compared the DAG files: only proof, proof_deps and proof_origin changed.
   The two recorded dependencies are exactly the chosen derived-pullback data and
   the existing affine representative theorem. The three proof steps match the
   restriction, single-source construction, and affine chain lift in Lean.

The scratch copy compiled without errors or warnings through lcompile.py. Explicit
`#print axioms` checks of both private helpers and the main theorem each showed exactly
`propext`, `Classical.choice`, and `Quot.sound`; none showed `sorryAx`.

No mathematical or Lean-source repair was needed. Second reading changed only this
report, adding the independent comparison, edge-case and pruning checks and updating
the axiom evidence against the current compiled dependencies.
