## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassDescent`
with a complete Lean reduction, without changing its signature. The proof constructs the
canonical opposite-indexed diagram and limit cocone from transition coherence. It proves
the sheaf-colimit comparison monic using existing affine eventual vanishing and the
filtered sheaf-colimit representative theorem. It combines that with local surjectivity,
uses balancedness of module sheaves to obtain an isomorphism, transports the colimit
universal property, and applies the representative theorem to obtain the requested section.
The representative theorem supplies the finite-cover gluing step, twice; affine restriction
reflects monomorphisms through the dense-subsite equivalence from Mathlib.

Added `Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi`, with one public
intermediate theorem isolating local surjectivity of the canonical sheaf-colimit comparison.
This is strictly a part of the argument: epimorphy alone gives only local lifts and does
not give a section on the entire affine object. The existing eventual-vanishing theorem
is needed to prove monicity before global representatives can be recovered. Both the
original node and the new node describe the actual reduction.

Compiled the new module and the original module with `lcompile.py`. The main proof has
no sorry, no anonymous holes, and no new data definitions. Its remaining obligations are
named imported theorems. All new indexing diagrams are constructed explicitly; no arbitrary
witness of an unproved existence theorem is used to define data.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Etale.exists_higher_image_affine_class_rep`
(`sbc-lem-higher-image-affine-class-descent`). Its proof is complete from named declarations.
No sorry remains in the item's module.

Added one hole:
`AlgebraicGeometry.Etale.epi_higher_image_colimit_comparison`
(`sbc-lem-higher-image-colimit-comparison-epi`). Its proof is exactly `by sorry`, with source
and complete natural-language proof in its docstring and node. This delivery is a
one-for-one decomposition, not a net sorry reduction. It uses the existing obligations
`higher_image_over_transition_coherence` and `exists_higher_image_affine_class_eq_zero`
without changing them, and the existing proved `etale_section_colimit_representative`.
No claim about the global sorry ledger is made.

Edge cases checked mathematically for the new statement: an empty scheme has zero
higher-image sections; a zero coefficient ring causes no exception; negative degrees of
these degree-zero sheaves vanish; the cofiltered index is nonempty; a constant diagram
has its usual canonical comparison; arbitrary compatible object isomorphisms eK and eB
only conjugate the comparison, so epimorphy is invariant under them. No finiteness,
flatness, torsion, or additional assumption is added.

## No longer needed

Removed these direct proof imports from the original module:
- `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`
- `Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit`
- `Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings`
- `Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

Second reading also removed the redundant new direct import
`Mathlib.CategoryTheory.Balanced`; balancedness is already available through the
required module-sheaf imports.

The old direct `proof_deps` removed from this node are:

- `lem-weil-pbc-filtered-category-exists-directed-final`
- `lem-weil-pbc-colimit-constant-connected-diagram`
- `lem-weil-pbc-inverse-image-composition`
- `lem-weil-pbc-injective-module-abelian-acyclic`
- `lem-weil-pbc-etale-cohomology-limit-complex-systems`
- `sbc-lem-higher-direct-image-presheaf`
- `lem-weil-pbc-sheaves-colimit-sheafification`
- `lem-weil-pbc-etale-qcqs-cofinal-finite-coverings`
- `lem-weil-pbc-filtered-colimits-commute-finite-limits`

The cohomology-continuity, injective-acyclicity, inverse-image composition, connected
constant-colimit, and directed-reindexing nodes remain below the new local-surjectivity
node or the existing vanishing node. Finite-cover refinement and finite-limit/filtered-
colimit interchange are supplied by the existing representative theorem. They are not
independent direct steps of this module anymore. No whole module is claimed to have
left the targets' closure; these are direct-import removals, not whole-closure pruning.
The public transition import remains unchanged. The parent higher-image-limit theorem
and affine-continuity module are not imported: their proofs depend on the current item.

## Where the brief, the DAG or earlier work was wrong

The original plan's second step combines several bridges not directly provided by the
listed declarations: forgetting constant-ring module coefficients, natural comparison
of higher-image presheaves, and compatibility with the derived-unit transitions.
The new node isolates precisely their local-surjectivity conclusion. The finite-cover
argument already exists as `etale_section_colimit_representative`; restating it would
duplicate existing work. No statement is disputed or changed. The unit record has no
realized nodes at this level, and the unit/chapter route is preserved.

The compiled local cache initially lacked the existing affine-class-vanishing module.
For local verification its unchanged repository source was compiled in the sandbox;
its unchanged source copy was removed afterward. Only the compiled local dependency
remains in the sandbox build cache; this delivery does not include that module.
Stacks sources are not present in this clone, so the cited primary source pages for
[09Z1](https://stacks.math.columbia.edu/tag/09Z1),
[03Q8](https://stacks.math.columbia.edu/tag/03Q8),
[0EZM](https://stacks.math.columbia.edu/tag/0EZM), and
[03FD](https://stacks.math.columbia.edu/tag/03FD) were read online.

## New nodes

`sbc-lem-higher-image-colimit-comparison-epi` records local surjectivity of the canonical
map from the stage higher-image sheaf colimit to the limit higher image. Its module is
`lean/Sheaf/AlgebraicGeometry/HigherDirectImageColimitComparisonEpi.lean`. It is the
local-surjectivity portion of steps 1–2 of the original plan, before global finite-cover
gluing. The node has the same chapter and unit as the item and identifies the blueprint
ancestor `sbc-lem-higher-direct-image-limit`. Mathlib searches were actually run through
`msearch.py`: LeanSearch was unavailable with HTTP 500; LeanFinder returned unrelated
condensed/coherent/module-sheaf results; grep returned no higher-image epi comparison.
No change record is needed because every existing signature and definition is unchanged.

## Second reading by H2

1. Compared both delivered modules with the repository and checked the existing node
   field differences. The existing theorem signature is byte-for-byte unchanged;
   the existing public import remains unchanged. There are no changed definitions,
   added hypotheses, weakened conclusions, or change records. The added module contains
   only one genuinely intermediate statement. Verdict: pass.
2. Compiled both modules through lcompile.py. The only textual sorry is the named
   `AlgebraicGeometry.Etale.epi_higher_image_colimit_comparison`; no forbidden axiom,
   unsafe/opaque declaration, foreign implementation, or hollow definition occurs.
   Scratch copies with #print axioms for both delivered theorems showed exactly
   propext, Classical.choice, Quot.sound, and sorryAx. The latter is expected from
   the explicitly reported new and existing imported obligations. K and B are explicit
   constructions; their proof fields use transition coherence, not an arbitrary
   existence witness to select data. Verdict: pass as a decomposition, not an
   unconditional proof or a net hole reduction.
3. Read the split-off statement, its full docstring argument and node against
   [09Z1](https://stacks.math.columbia.edu/tag/09Z1),
   [03Q8](https://stacks.math.columbia.edu/tag/03Q8),
   [03FD](https://stacks.math.columbia.edu/tag/03FD), and
   [0EZM](https://stacks.math.columbia.edu/tag/0EZM).
   Local lifting follows from cohomology-presheaf continuity and sheafification;
   injective-module abelian acyclicity removes any flatness requirement. Negative
   degrees and empty objects have zero sections; the cofiltered category is nonempty;
   identity systems and conjugation by eK/eB preserve the comparison and epimorphy.
   The new conclusion supplies only local lifts. The main proof separately uses
   eventual vanishing to obtain an isomorphism and finite-cover gluing to obtain
   the demanded global affine representative, so this is a strict part of the
   argument rather than a renamed target. Independent msearch LeanFinder, Loogle,
   and grep queries used scheme-limit local lifts and colimit.desc epimorphisms;
   no matching theorem was found (the first Loogle query had an unresolved short
   identifier; the fully qualified retry returned no hits). Read related abelian
   limit-affine-class-representative and upstream fixed-morphism filtered-colimit
   results: neither gives this module-valued varying-scheme canonical comparison
   without substantial new bridges. The hole cannot be closed in a few minutes
   using these results. Verdict: pass.
4. Read the proof from its requested section downward and checked the explicit
   functor laws, cocone naturality, affine kernel argument, faithful dense-subsite
   reflection, balancedness, and transport of the colimit property. Both uses of
   the existing representative theorem are necessary for this reduction. Kept the
   planned imports in the new unproved module; made its Abelian import nonpublic
   after a successful compilation check, and removed the redundant direct Balanced
   import from the main module after a successful compilation check. Listed all nine
   old proof dependencies removed from the main node explicitly. The unit
   sk-lem-failure-field has empty realized statement/step lists, and its route
   has not been bypassed. Verdict: pass.
5. Checked the new Lean signature verbatim against its node, both proof_deps
   against the union of step uses, sources, chapter/unit, creation/blueprint metadata,
   and the proof_origin records. Only proof, proof_deps, and proof_origin differ
   in the existing node. Corrected its third step from elementary=true to false:
   it invokes the new non-elementary local-surjectivity obligation. Verdict: pass.

Second reading changed the visibility of the new module's Abelian import, removed
one redundant Balanced import, corrected one DAG elementary flag, and completed
pruning documentation. The mathematical reduction and all theorem signatures remain
as submitted. One original hole closed, one hole added: a one-for-one decomposition.
