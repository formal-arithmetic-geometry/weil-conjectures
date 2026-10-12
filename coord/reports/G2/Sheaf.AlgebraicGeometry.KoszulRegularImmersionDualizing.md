## What changed

Completed the proof of AlgebraicGeometry.koszulRegularImmersion_dualizing without changing
its signature or its existing docstring. Added two independent intermediate modules:
KoszulRegularImmersionDualizingProperty supplies quasi-coherence of the explicit determinant;
KoszulRegularImmersionAlgebraDual supplies its comparison with an ambient scalar right adjoint
in the derived category over i_* OZ. Neither intermediate mentions the geometric right adjoint.

The target proof uses exists_affine_derivedHom_evaluation_counit to obtain the ambient right
adjoint, finite_duality_derived_hom for its algebra-valued comparison with the given geometric
adjunction, and finite_affine_derived_equivalence to descend the composed isomorphism. Both
preimageIso operations are written out: first the full-subcategory inclusion, then the affine
equivalence. Closed immersion implies finite by Mathlib; the Noetherian and bounded-below
hypotheses are discharged in Lean. The direct-image-algebra derived category uses its standard
localization, with the target's independently chosen derived categories unchanged.

Updated the parent node's proof, proof_deps and proof_origin to this exact route. Added only
private proof imports to the existing module. All three delivered modules compile, in import
order, through lcompile.py without warnings. No definitions, existing statements, targets or
public imports of existing modules changed.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.koszulRegularImmersion_dualizing, node
lem-sc-smooth-proper-diagonal-koszul-dual. Its proof contains no sorry.

Added precisely two holes, each in a new public theorem with proof exactly `:= by sorry`:

- AlgebraicGeometry.koszulRegularImmersion_dualizing_property,
  node lem-sc-koszul-normal-determinant-qcoherent, in
  lean/Sheaf/AlgebraicGeometry/KoszulRegularImmersionDualizingProperty.lean.
- AlgebraicGeometry.koszulRegularImmersion_algebraDual,
  node lem-sc-koszul-regular-immersion-algebra-dual, in
  lean/Sheaf/AlgebraicGeometry/KoszulRegularImmersionAlgebraDual.lean.

This delivery is a decomposition: one upper hole closed and two lower holes added (net -1
before any import-closure pruning). It does not claim a proof without remaining dependencies.
The first statement is only a quasi-coherence property and has no right adjoint. The second
is an algebra-valued local comparison and has no geometric adjunction or geometric right
adjoint. The complete finite-duality composition and recovery on Z are in the target's proof.
Existing dependencies, including the affine derived equivalence and ambient scalar adjunction,
retain their existing holes; this delivery neither changes nor adds those holes.

Checked edge cases against the argument: empty Z gives zero objects; rank zero gives the
structure sheaf in degree zero; a principal regular equation gives the normal line in degree
one; differing ranks on components are handled by clopen extension by zero. Noetherian Z is
quasi-compact, so the locally constant rank has finite image. The algebra theorem supports
independent morphism universes on Z, Y and the direct-image algebra.

## No longer needed

Removed the proof import Sheaf.AlgebraicGeometry.KoszulRegularImmersionDerivedHom and the
parent proof dependency lem-sc-koszul-regular-immersion-derived-hom. Its scalar-valued global
isomorphism does not provide the algebra-linear derived map required for descent, and also
shares a single derived-category universe between Z and Y. The new algebra comparison goes
directly to its existing local dependencies: the finite-free Koszul model, intrinsic
quotient-linear dual-Koszul calculation, affine module correspondence and affine cohomology.
The old global scalar comparison module is not needed by this item's proof branch; other
consumers may still need it, so no whole-library deletion is proposed.

The finite-affine and finite-duality proof imports remain, because their declarations are
used explicitly. Every existing public import remains. No unit statement or unit step is
bypassed, and no other existing node or module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox contained the original single sorry and a copy of the unchanged DAG node;
it had no completed reduction or report.

The original DAG's third step requires an isomorphism in the algebra-derived category.
The existing koszulRegularImmersion_derivedInternalHom signature yields only an isomorphism
in D(OY), although its node and docstring describe algebra compatibility. Scalar restriction
is not fully faithful in derived categories, so that displayed scalar isomorphism cannot
simply be lifted. The delivery isolates the actual missing algebra-valued computation and
uses finite_duality_derived_hom's algebra-valued component phi, then descends through the
stated equivalence. It does not assume full faithfulness of Ri_*.

LeanSearch returned Internal Server Error for both new statements; the nodes record this as
unavailability with no search verdict. LeanFinder, Loogle, Mathlib grep and searches of both
library roots found no existing exact theorem. Generic quasi-coherence instances and
right-adjoint uniqueness are relevant tools but do not close either intermediate statement.
The local literature checkout lacks duality.tex on this machine; the statement and proof
of Stacks Tags 0BR0 and 0BQZ were read from the authoritative Stacks website.

## New nodes

lem-sc-koszul-normal-determinant-qcoherent records the quasi-coherence of the constructed
rank-stratified normal determinant. Its proof in words derives local conormal freeness from
first Koszul homology vanishing, takes the normal determinant on each rank stratum and
identifies zero-differential cohomology with the quasi-coherent terms.

lem-sc-koszul-regular-immersion-algebra-dual records the ambient scalar right-adjoint value
computed as algebra-valued derived Hom. Its proof in words keeps the quotient action in the
intrinsic Koszul determinant comparison, glues the cohomology maps before truncation, and
transports to any specified scalar right adjoint by uniqueness. It is independent of the
quasi-coherence theorem and of the geometric right adjoint. No change record was needed.

## Second reading by G2

1. Compared the existing module with the repository using diff and the declaration parser.
   Verdict: its existing signature and docstring are byte-for-byte unchanged; only its proof
   and plain proof imports differ. No definitions or target statements changed. The existing
   node differs only in proof, proof_deps and proof_origin. Both new node signatures match
   their Lean statements verbatim.
2. Compiled all three modules locally in import order through lcompile.py: no errors or
   warnings. A scratch module printed axioms of all three delivered declarations: exactly
   propext, Classical.choice, Quot.sound and sorryAx. Only the two named split-off theorems
   contain sorry; no forbidden declaration or hollow definition was added. Existential
   choices of adjoints and equivalences occur inside a proposition proof, not in definitions.
   Verdict: a valid reduction conditional on the reported open statements, not a closed proof.
3. Read both new statements and their complete docstring arguments against Stacks Tags
   [0BQZ](https://stacks.math.columbia.edu/tag/0BQZ) and
   [0BR0](https://stacks.math.columbia.edu/tag/0BR0), and read the intrinsic quotient-linear
   Ext comparison in KoszulRegularSequenceDualComplex. Checked empty Z, rank zero, a
   principal nonzerodivisor and disjoint components of different ranks. Verdict: true and
   needed, strictly separate parts of the argument. The property theorem has no adjunction;
   the algebra theorem has no geometric right adjoint or descent conclusion. Independent
   LeanFinder search used "quasi coherent exterior power locally free conormal sheaf regular
   embedding"; Loogle searched rightAdjointUniq; Mathlib grep and searches of both library
   roots found no exact replacement. Generic right-adjoint uniqueness does not compute its
   value, and the old scalar-valued theorem does not supply an algebra-derived morphism.
   Neither remaining hole can be closed in a few minutes with the available interfaces.
4. Traced the actual isomorphism composition from finite-duality's algebra-valued phi through
   the algebra computation, then both fully faithful preimageIso operations. Verdict: the
   finite-duality, Koszul-computation and affine-descent route is preserved. The unit's
   realized arrays are empty and unchanged; no registered unit realization is bypassed.
   The old derived-Hom node is the only removed old proof dependency, and it and its module
   are listed under No longer needed. Required statement imports and used proof imports
   remain; the new algebra module's plain imports record its unresolved proof route.
5. Checked the parent dependencies against the invoked declarations, each new dependency
   union against its proof steps, sources, blueprint ancestry, creation records and verbatim
   Lean records. Verdict: the nodes agree with the Lean and the reported decomposition.

Changed only the algebra theorem's proof docstring and the matching new-node proof step:
made explicit that rank strata are clopen in Z, need not be clopen in Y, and their
characteristic sections split algebra-module complexes by orthogonal idempotents of i_* OZ.
Canonical truncations are applied to those summands before taking the finite sum. This
clarifies the global comparison without changing any statement, proof term or hole count.
The original hole closed is koszulRegularImmersion_dualizing; the two holes added remain
koszulRegularImmersion_dualizing_property and koszulRegularImmersion_algebraDual.
