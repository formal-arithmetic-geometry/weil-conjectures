## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`
to a bounded flat Cech model with an upper-bounded finite-free resolution, followed by
local shortening of that resolution in degree zero. The original module now constructs
its neighbourhood and finite-free complex from these statements, transports the cartesian
square through the smaller open inclusion, and composes the two homology isomorphisms.
Every existing signature, definition, visibility and public import is unchanged.

Added proof-only imports `Sheaf.AlgebraicGeometry.ProperFlatCechModel` and
`Sheaf.AlgebraicGeometry.FlatModelFiniteFreeShortening`. Each new module contains one named
public theorem with a whole-proof sorry, source, detailed proof and node. No definition
chooses data from an unproved existence assertion.

The complete sandbox set compiles locally in import order, including the unchanged
perfect-locus proof. The two unchanged dependency source files in the sandbox are byte-identical
to the repository and compile into the local overlay; they produce no delivery diff.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`
(node `lem-pc-universal-finite-free-complex`, newly recording the existing declaration).
This is a decomposition, not a sorry-free proof: it closes one hole and adds two.

The original hole left untouched is
`AlgebraicGeometry.Scheme.Modules.finite_sections_higherDirectImage`
(covered by the affine finiteness clause of `lem-pc-coherent-hi`). The already complete
`isFinitePresentation_higherDirectImage` and perfect-locus proofs are unchanged.

Added holes:
- `AlgebraicGeometry.Scheme.Modules.exists_proper_flat_cech_model`
  (`lem-pc-proper-flat-cech-model`): geometric construction, approximation, and
  pseudo-coherent finite-free upper-bounded resolution.
- `AlgebraicGeometry.Scheme.Modules.exists_local_finiteFree_shortening`
  (`lem-pc-flat-model-finite-free-shortening`): general local truncation of that resolution
  with homology comparisons after arbitrary pullback.

Edge cases checked mathematically: for d=0 the shortening replaces Q by its flat,
finitely presented degree-zero opcycles; zero modules use rank zero; negative resolution
terms are permitted and must be removed by the second theorem. On a nonaffine base only
a neighbourhood is asserted, and on a non-quasi-compact base there is no uniform d.
Only degree-zero opcycles need a new local free trivialization, because every remaining
Q term is already finite free. No constancy of ranks across neighbourhoods is assumed.

## No longer needed

None. All original imports are retained and support unchanged statements or proofs.
In particular the existing perfect-locus imports must stay. This delivery does not bypass
the coherence unit: it implements its Cech, Noetherian approximation and Mumford shortening
steps. Its coherent-hi branch and its classical finiteness dependencies remain needed.
No existing node or module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The original module's finite-free-existence theorem has a unit-level blueprint citation
but no node with it as its primary Lean declaration. The new proved node records that
existing statement and the actual two-step reduction. No statement correction is made.

Several related derived/perfect interfaces import the aggregate DirectImage module,
which already reaches this item. They cannot be imported here without a cycle. Other
interfaces are on ModuleCat or the alternative derived module carrier; neither directly
supplies the ordinary scheme-module complex and pullback comparisons needed here.
The new statements expose those missing interfaces without altering the shared carriers.

The local compiled baseline omits the existing perfect-locus dependencies. The sandbox
contains byte-identical source copies, now compiled locally with the complete set. These
are unchanged existing dependencies, not new statements or substitutions, and are not
part of the committed diff.

## New nodes

`lem-pc-proper-flat-cech-model` records the bounded flat Cech construction plus
pseudo-coherent upper-bounded resolution. Its complex C need not be finite free, while
Q may be unbounded below, so this is strictly a part of the original argument.

`lem-pc-flat-model-finite-free-shortening` is a general algebraic replacement theorem for
C,Q and has no proper morphism, coefficients on X, or higher direct images. Its opcycles,
local freeness and derived pullback argument is the remaining algebraic step.

`lem-pc-universal-finite-free-complex` records the existing upper declaration and its
compiled combination of the preceding two statements. It is proved and adds no hole.
All three inherit the coherence unit and cite its part (a). No change records are needed.


## Second reading by F2

1. Compared all delivered modules with repository sources. The item differs only by two
   plain proof imports and the body of `exists_isFiniteFreeComplex_higherDirectImage`.
   Every existing signature, definition, docstring, visibility and public import is byte
   identical. Both perfect-locus dependency copies are byte-identical and add no diff.
   No change record is needed. Verdict: pass.
2. Compiled the complete five-module sandbox set with lcompile.py in import order:
   all files compile without errors or warnings. The item retains exactly its named
   affine-finiteness hole; each new statement module has exactly one whole-theorem hole.
   No new definition or forbidden declaration is present. Explicit axiom checks and the
   delivery probe check the combined theorem and both new lemmas; sorryAx is expected
   from the two open statements and existing open dependencies. Verdict: pass, decomposition.
3. Read both statements and their complete docstring arguments. Checked Stacks 0A1H,
   0B91(2), 064U and 0653 against the hypotheses. Properness supplies separatedness for
   affine intersections; finite presentation supplies quasi-coherence and approximation;
   relative flatness gives the bounded flat Cech terms. In the shortening lemma Q need
   not be bounded below: stalkwise K-flatness and negative tensor vanishing make its
   degree-zero opcycles flat, and finite presentation makes them finite projective.
   The cokernel is quasi-coherent because Q has finite free terms, so local freeness
   applies even though C was not assumed quasi-coherent. For d=0 only these opcycles
   remain; zero terms have rank zero. Empty bases have no point t. Arbitrary nonaffine
   pullbacks are handled locally, with no global rank or degree bound asserted.
   Independent grep, LeanFinder and Loogle searches found projectivity of flat finitely
   presented modules, K-projective complexes and truncation quasi-isomorphisms, but no
   theorem closing either full interface. Read AffinePseudoCoherentLift and the ring
   finite-free-model theorem: their derived carriers and conclusions do not supply the
   ordinary scheme-module comparisons. Both new statements are strictly parts of the
   original argument, not renamings. No arbitrary witness is used in a definition.
   Verdict: pass; neither remaining geometric/algebraic interface closes in a few minutes.
4. Read the proof from its target down: choose C,Q, shorten to P, transport the square
   using homOfLE_ι, and compose the two homology isomorphisms. All original imports
   support unchanged signatures or the perfect-locus proof. Both additions are plain
   imports. No old proof dependency is dropped. The coherence unit's realized statement
   and step lists are empty on this baseline, and remain untouched; the Cech,
   Noetherian approximation and Mumford-shortening route is retained. Verdict: pass.
5. Compared the three nodes' Lean signatures, proof steps, dependency unions, sources,
   chapter/unit and creation records with the modules. The upper node records exactly
   the two calls of the Lean proof; each open statement has its own matching node.
   Clarified the geometric node's descent step: bounded-complex descent applies to F
   in degree zero on X, not to generally infinite Cech terms. The actual map Q→C comes
   from the affine ring resolution, then termwise sheafification. Verdict: pass after repair.

Changed only this DAG proof-step explanation and this report (including stale compile
status and the explanation of unchanged sandbox dependency copies). Kept the Lean proof
and all statements. Net holes closed minus added is 1 - 2 = -1: this is a decomposition,
with no pruned module, and no claim of net proof progress.
