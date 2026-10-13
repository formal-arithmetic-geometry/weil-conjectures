## What changed

Repaired the returned delivery for
`Sheaf.AlgebraicGeometry.ProperFlatSingleLocalFiniteTor`.
Removed the duplicate private `AlgebraicGeometry.flatOver_restrict` theorem and
replaced it in place with the proved private
`AlgebraicGeometry.flatOver_openImmersion_square`. This is a genuine generalization:
for schemes X,T,Y,B, open immersions i:Y→X and j:B→T and a map p:Y→B with
`i ≫ f = p ≫ j`, restriction of an f-flat module along i is p-flat.
The square need not be a pullback; Y can be a proper open subscheme of the inverse
image of B. The main proof applies this to the canonical restriction square.

The existing helper in `FiniteAffineCechModelPerfect` is private and inaccessible
to importers. That module also imports `ProperFlatSingleDerivedDirectImagePerfect`,
which imports this item, so importing it would create a cycle. Instead the
new general argument transports section flatness through the base open immersion's
section-ring isomorphism and uses the commutative square to identify scalar actions.
It is proved without holes. Added proof imports `Mathlib.RingTheory.Flat.Stability`
and `Mathlib.RingTheory.RingHom.Flat` for flatness transitivity and flatness of a
ring isomorphism. The original public theorem signature, docstring, and public
imports remain unchanged. No other module or interface was changed.

The original completed proof constructs the finite affine Čech model, composes
the derived comparisons, proves K-flatness and bounds tensor homology. Its six
proof imports and the proved private tensor-vanishing helper remain. Updated the
existing node's first proof step and proof_origin to describe the generalized glue;
its proof_deps are unchanged. No new node or change record is needed for the private
proved helper. Removed the old second-reading section, which audited the returned
version, so the second reader can audit this repair independently.

Validation: the repaired complete module compiles with `lcompile.py` without
warnings. The exact returned `import_prune_check.py` check now passes (exit 0).
`deliver3.py H2 Sheaf.AlgebraicGeometry.ProperFlatSingleLocalFiniteTor --no-push`
prints OK; only the independent second reading remains. Nothing was pushed.
The generalized argument uses no nonemptiness or nonzero-ring assumption:
empty source/base schemes and zero modules are included. The finite interval
construction also includes empty covers.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.properFlat_single_local_hasFiniteTorDimension`
(node `lem-pc-proper-flat-single-local-finite-tor`).
Both private helpers `AlgebraicGeometry.flatOver_openImmersion_square` and
`AlgebraicGeometry.tensor_homology_isZero_of_term_isZero` are proved.
There are no remaining local sorries, new holes or split statements.
The existing `finiteAffineCechModel_derivedComparison` dependency still has
transitive holes; this delivery does not claim to close them.

## No longer needed

Removed the duplicate private `AlgebraicGeometry.flatOver_restrict` declaration.
No imports or original proof-dependency nodes are pruned: all nine original nodes
remain used. `FiniteAffineCechModelPerfect` is not imported and was never an import
or proof_deps of this item; it is not claimed as globally pruned.
Every added import supplies a declaration used by this proof.

## Where the brief, the DAG or earlier work was wrong

Return point 1 is repaired by generalizing the duplicate theorem in place, rather
than renaming or restating the same fact. The earlier delivery copied a private
restriction helper and the old second reading incorrectly accepted this duplication.
The replacement has four arbitrary schemes and a commutative square, with no
pullback requirement, and has a different, strictly more general conclusion.
Its proof genuinely handles base section-ring isomorphisms that need not be identities.
There is no mathematical discrepancy in the item, no target change, and no forced
adaptation of another module.

## Second reading by H2

1. Compared the sole delivered Lean module with the repository using `diff` and
   checked its public signature and public imports byte for byte by script: PASS.
   All hypotheses (proper, locally of finite presentation, quasi-compact,
   independent derived localizations, finite presentation and relative flatness of
   F, and the supplied affine open) and the exact finite-Tor conclusion are unchanged.
   No definition or other existing declaration is modified. No change record is needed.
2. Compiled the current module with `lcompile.py`: PASS, no warnings (11.1 seconds).
   Rebuilt the stale scratch Audit.lean from the actual repaired file and compiled it.
   Both private helpers and the explicit finiteAffineCechModel have only propext,
   Classical.choice and Quot.sound. The public theorem additionally uses sorryAx,
   already reachable through finiteAffineCechModel_derivedComparison; the open
   direct-image comparison itself has only the standard axioms. There are no local
   sorries, forbidden declarations, or data definitions in the delivered file.
   The cover comes from the actual affine cover and finiteSubcover, and P from the
   explicit construction, not from an arbitrary witness of an unproved existence
   theorem. The two chosen isomorphisms are used only to witness a proposition;
   they do not define new data visible downstream.
3. No statements were split off and no holes were added: PASS. Read the generalized
   open-immersion-square proof: affine opens map to affine opens; the square gives
   the needed containment, the base appIso transports flatness, and the appLE
   composition identity identifies the scalar actions. It does not assume a
   pullback square or nonempty schemes. Identity immersions, a smaller source
   open, the empty base/source, and zero modules are covered. The tensor helper
   uses the termwise tensor isomorphism and zero middle term of the homology short
   complex, valid in every degree including negative degrees. Searched with
   `rg` for flatness under open restriction and tensor homology vanishing, and
   independently queried msearch Loogle for Module.Flat.trans and grep for
   IsFlatOver/mapBifunctorSingle₂Iso. Existing restriction helpers are private;
   FiniteAffineCechModelPerfect also imports this item indirectly. The public
   affine-chart restriction theorem has a different conclusion (postcomposition
   with isoSpec). No accessible theorem gives this arbitrary square statement.
   The related tensor helper in PerfectPseudoCoherentLocallyFiniteTor is private.
4. Read the proof from its conclusion back through the finite interval, K-flatness,
   explicit Cech model and the two representing comparisons: PASS. All six geometric
   and homological proof imports and both ring-flatness imports supply declarations
   actually used; none needs public visibility. All nine old proof_deps remain used,
   so `No longer needed` correctly claims no pruned node or module. The proof keeps
   the unit's bounded flat Cech route, rather than replacing it with a finite-free
   or perfectness assertion. The unit's realized fields are empty in the repository
   already; this delivery neither changes them nor bypasses a recorded realization.
   The bound [0,r] includes r=0; the cover equality forces the source empty in that
   case. No shorter available direct-image theorem was found.
5. Compared the node JSON with the repository and read all nine dependency Lean
   records against the actual uses: PASS. Only proof and proof_origin change;
   proof_deps and the node's statement/Lean statement stay unchanged. The three
   proof steps describe precisely the cover and flatness construction, localization
   and restriction comparisons, and termwise tensor vanishing in the Lean proof.
   No new node is required for the proved private glue.

Second reading changed no delivered Lean proof or node: the repaired argument was
correct. Refreshed the obsolete scratch axiom audit (which still contained the
returned flatOver_restrict proof) and added this independent review. Closed one
original local hole, added zero holes, split off zero statements; transitive open
comparison dependencies are explicitly not claimed proved.
