## What changed

The signature of `AlgebraicGeometry.affineSections_finiteTorDimension_of_stalkwise` is unchanged.
Its proof now chooses a finite polynomial presentation with Mathlib, obtains a bounded
projective polynomial-ring resolution, restricts it to a flat base-ring resolution, and
computes Tor from that resolution. Vanishing above the bound follows from the zero tensor
term and zero homology. Composition of scalar restrictions is handled by the actual ring
homomorphisms and their isomorphism, so no scalar-action identification is assumed.

Added two modules, each with one public theorem:
`Sheaf.AlgebraicGeometry.AffinePolynomialResolutionOfStalkwise` states the bounded polynomial
resolution step. `Sheaf.Algebra.Homology.FlatResolutionTorComparison` proves the general
flat-resolution Tor comparison using the existing tensor bicomplex, double-complex cokernel
homology comparison, and Tor symmetry. Its augmentation and cokernel helpers are constructed
explicitly and all their proofs are complete.

All three files compiled cleanly together through lcompile.py. No signatures or definitions
of existing declarations changed. No forced adaptations are needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.affineSections_finiteTorDimension_of_stalkwise`
(node `lem-pc-affine-sections-finite-tor-of-stalkwise`).

New proved theorem: `ModuleCat.flatResolution_torComparison`
(node `lem-pc-flat-resolution-tor-comparison`), with no local sorry.

One new hole remains:
`AlgebraicGeometry.affinePolynomial_boundedResolution_of_stalkwise`
(node `lem-pc-affine-polynomial-resolution-of-stalkwise`). This is a decomposition,
not a sorry-free proof of the assigned theorem: one upper hole closed and one lower hole added.
The lower theorem supplies a bounded projective polynomial resolution; it does not assert
base-ring Tor vanishing. The complete Lean proof combines it with flatness under restriction,
the independently proved Tor comparison, and homology vanishing.

## No longer needed

No original imports were removed: PerfectMorphism and Mathlib.AlgebraicGeometry.Noetherian
are needed by the unchanged statement. No DAG nodes or modules are pruned. The old proof dependencies
`def-pc-scheme`, `pqf-def-locnoeth`, and `def-pc-perfect-morphism` are no longer
listed as proof steps: they remain statement dependencies, available through the retained
public imports. The updated proof dependencies list the two actual proof steps.

The second reader removed three redundant proof imports from the new module
`Sheaf.Algebra.Homology.FlatResolutionTorComparison`:
`Mathlib.LinearAlgebra.TensorProduct.RightExactness`,
`Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed`, and
`Mathlib.Algebra.Homology.HomologicalComplexAbelian`. These are already available through
retained imports. `Mathlib.CategoryTheory.Monoidal.Closed.Braided` stays: removing it loses
the preservation of cokernels and epimorphisms by tensorRight.

## Where the brief, the DAG or earlier work was wrong

The DAG's single long step names only definitions. It does not provide a Lean theorem for the
polynomial-perfectness or flat-resolution comparison step. The proof follows that mathematical
route and makes its two interfaces explicit. The unit's realized statement and step lists are
empty; this delivery neither changes them nor bypasses a realized unit step.

Stacks Tags 069C, 068X, 068W, 00LY and 00M3 were read online because the literature source
checkout is absent on this machine. No statement error was found. The polynomial-resolution
statement allows the empty affine source, zero base ring, and zero variables: a zero algebra
has the zero projective resolution; a nonzero algebra over the zero ring is impossible. For
zero variables the argument specializes to a quotient of A. The flat comparison includes
j=0 and arbitrary unbounded nonnegative flat resolutions; the first-quadrant argument uses
only the finitely many terms at each homology degree.

Searches used msearch.py (LeanFinder, Loogle, grep and LeanSearch), rg on both library roots
and the DAG, and blueprint_refs.py. LeanSearch returned Internal Server Error. Loogle's Tor
query returned no hits. LeanFinder returned polynomial/finite-type and projective-dimension
results, and projective-resolution Tor computations and flat tensor exactness, but no exact
statement of either new theorem. The existing Tor symmetry and double-complex comparison
were used to prove the flat comparison, rather than left as another hole. Blueprint searches
for flat resolution, polynomial presentation, projective resolution and 068W found no matching
module-level assertion. The ancestor tool returned None for the newly created parent; the
new nodes inherit the parent's explicit lem-sc-finite-duality ancestry and via chain.

## New nodes

`lem-pc-affine-polynomial-resolution-of-stalkwise`, in
`lean/Sheaf/AlgebraicGeometry/AffinePolynomialResolutionOfStalkwise.lean`, records the
polynomial perfection part of Tag 069C: pseudo-coherence over the Noetherian polynomial ring,
local perfection by 068X, gluing by 068W, and conversion to a bounded projective resolution.
Its declaration is the sole remaining hole. Its source and complete proof are in the docstring.

`lem-pc-flat-resolution-tor-comparison`, in
`lean/Sheaf/Algebra/Homology/FlatResolutionTorComparison.lean`, records the proved general
flat-resolution comparison. Its proof uses the existing tensor bicomplex and two established
comparison theorems. The two new nodes are in the assigned chapter and unit. No change record
is needed because no existing statement or definition changed.

## Second reading by U4

1. Compared every delivered module with the repository. Only the assigned module exists
   there; its theorem signature, documentation, namespace, universes, and public imports
   are byte-for-byte unchanged. The two other modules and their declarations are new.
   The existing node changes only proof, proof_deps, and proof_origin. No existing definition,
   statement, target, or public interface is changed. Verdict: pass.
2. Read the three proofs and all augmentation/cokernel helpers. Compiled the complete set
   through lcompile.py. The only direct sorry is the reported public theorem
   AlgebraicGeometry.affinePolynomial_boundedResolution_of_stalkwise. No prohibited
   declaration or hollow definition is present. A scratch axiom check shows only propext,
   Classical.choice, and Quot.sound for ModuleCat.flatResolution_torComparison; the affine
   theorem and polynomial-resolution theorem additionally use sorryAx. The resolution P is
   eliminated inside a proposition proof, not chosen as data in a definition. Verdict: pass
   as a decomposition, not a completed sorry-free proof of the assigned theorem.
3. Checked the new polynomial statement against Stacks 069C, 068X, and 068W, including the
   Noetherian pseudo-coherence hypothesis, scalar compatibility, and bounded-below condition.
   Empty source gives the zero resolution; a zero base forces the coordinate algebra to be
   zero; n = 0 gives a quotient of the base. Finite projective resolutions need no positive
   cochain-degree tail: splitting the exact projective tail gives the asserted augmentation.
   The remaining hole is strictly the polynomial-projective-resolution part; the target
   additionally needs restriction to flat base modules and the proved Tor computation.
   Checked the flat comparison in degree zero and for zero modules and arbitrary nonnegative
   resolutions against Stacks 00M1 and 00M3. Repeated searches with different terms using
   msearch LeanFinder, Loogle, and grep, and rg on both library roots and Mathlib. Found local
   projective-dimension bounds and projective-resolution tools, but no stalkwise polynomial
   criterion or existing general flat-resolution Tor comparison. The local dimension theorem
   requires a common bound and cannot supply one from point-dependent bounds. There is no
   short closure of the remaining polynomial hole from these declarations. Verdict: pass.
4. Followed the proof downward: Mathlib finite polynomial presentation, polynomial resolution,
   exact scalar restriction, flatness transitivity, Tor comparison, zero tensor term, zero
   homology, and transport through the actual scalar-composition isomorphism. The comparison
   uses already proved double-complex and Tor-symmetry theorems. Removed three redundant
   proof imports after compiling each cumulative removal in scratch. Checked all old
   proof_deps explicitly under No longer needed; no DAG module becomes prunable. Read
   dag/units/sk-thm-picard-duality.json and its realized statement/step lists (empty).
   No unit route or realized step is replaced. Verdict: pass.
5. Checked every node's verbatim Lean statement, declaration/module/file record, source,
   creation/ancestry/chapter/unit fields, and the union of proof-step uses against proof_deps.
   All agree. Existing proof metadata describes the actual reduction; the new comparison
   metadata records the tensor bicomplex, double-complex comparison, and Tor symmetry.
   Verdict: pass.

Changes made: removed redundant imports of
Mathlib.LinearAlgebra.TensorProduct.RightExactness,
Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed, and
Mathlib.Algebra.Homology.HomologicalComplexAbelian from the new flat-comparison module;
removed one extra blank line in the assigned module; expanded No longer needed to name the
three old proof dependencies individually. No mathematical proof or statement was rewritten.
A trial private import of ModuleCat.Projective was reverted: the public Tor' statement needs
its HasProjectiveResolutions instance, so the original public import is correct.
One original hole closed and one new hole added: net zero, with an independently proved
Tor-comparison theorem. No DAG modules pruned.
