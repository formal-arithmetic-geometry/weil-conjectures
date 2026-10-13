## What changed

Proved `ModuleCat.polynomial_successor_tor_bound` with its signature unchanged.
Its proof follows the original canonical induced-module presentation, scalar-extension
comparison, and long exact Tor sequence. Added two fully proved modules:
`Sheaf.RingTheory.PolynomialInducedPresentation` constructs the actual maps and proves
short exactness, and `Sheaf.RingTheory.FlatScalarExtensionTorComparison` proves a Tor
comparison isomorphism for every flat ring map. Both are proof-only imports of the item.
The original public imports and all existing public signatures remain unchanged.

The presentation proof transports the polynomial monomial basis to the last-variable
presentation. In coefficient sequences its differential is shift minus coefficientwise
variable action. A maximal-support argument proves injectivity, and an explicit correction
identity proves exactness. No data is chosen from an unproved existence theorem.
The scalar comparison extends a projective resolution and supplies an actual chain
isomorphism using the existing proved tensor restriction-extension comparison.
The private long-exact-sequence helper reuses the proved `resolutionSES` helper through
`import all Sheaf.Paper.TorLongExactFirstVariable`; it does not copy that construction.

Read Weibel, Chapter 4, Corollary 4.3.6 and Theorem 4.3.7, pp. 101–102, including
sequence (*) and its coefficient proof:
https://math.mit.edu/~hrm/palestine/weibel/04-homological_dimension.pdf .
Theorem 4.3.7 is phrased for global dimension; this delivery uses its actual presentation
and projective-resolution argument to prove the specified Tor statement.

All three delivered Lean modules compile together without warnings through `lcompile.py`.
Explicit `#print axioms` for the original theorem and both new theorems reports exactly
`propext`, `Classical.choice`, and `Quot.sound`; no imported `sorry` remains in their proofs.
The proof works in degree zero for the comparison and with n=0, d=0, zero modules,
and zero rings. The nonempty-support argument is entered only for a nonzero sequence;
it never assumes the coefficient ring or coefficient module is nontrivial.

## Proved and sorry left

Closed the item's one hole:
`ModuleCat.polynomial_successor_tor_bound`
(node `lem-pc-polynomial-successor-tor-bound`).

Also fully proved the two new statements:
`ModuleCat.exists_polynomial_induced_presentation`
(node `lem-pc-polynomial-induced-presentation`) and
`ModuleCat.nonempty_flat_scalar_extension_tor_iso`
(node `lem-pc-flat-scalar-extension-tor-comparison`).

No `sorry` remains in any delivered module. Holes closed: 1. Holes added: 0.
This is a proof from existing project declarations, not a decomposition into new holes.
The existing proved theorem `Module.exists_free_resolution_ses_split`
(node `lem-weil-pbc-free-resolution-ses-split`) is a dependency of the library's
`resolutionSES` construction; this delivery reuses it unchanged.

## No longer needed

No original import, planned node, or planned module was removed: the original node had
an empty `proof_deps` and the proof retains its mathematical route.
No new unproved presentation, scalar-comparison, or general Tor long-exact-sequence
statement is needed. The new presentation and comparison are fully proved, and the
last step is a proved private helper using the existing horseshoe construction.

During development removed redundant proof imports
`Mathlib.LinearAlgebra.FreeModule.Finite.Basic`,
`Mathlib.Algebra.Polynomial.Module.Basic`, and
`Mathlib.Algebra.Homology.Additive`; these were never imports of the repository version.
The narrow `Mathlib.LinearAlgebra.Finsupp.VectorSpace` supplies polynomial freeness.
The second reading also removed redundant proof imports from the item:
`Mathlib.Algebra.Homology.HomologySequence`, `Mathlib.RingTheory.Flat.Basic`,
and `Mathlib.RingTheory.RingHom.Flat`. Their declarations are already available
through the retained imports; the item compiles after removing all three.

## Where the brief, the DAG or earlier work was wrong

The original node marked its entire multi-page plan non-elementary but supplied no
proof dependencies. It is now updated to name the proved presentation, the proved
flat-extension Tor comparison, and the existing free horseshoe statement. No existing
statement or definition was wrong or changed.

The unit's `realized.statement` and `realized.steps` are empty. This delivery keeps
its canonical polynomial-resolution route; it changes no unit record or target.
The existing free horseshoe theorem is used as a general algebraic tool from another
unit. The existing natural tensor comparison is likewise a general algebraic tool;
neither replaces a step realized by a unit.

LeanSearch was unavailable (Internal Server Error), recorded without a mathematical
verdict. LeanFinder, Loogle, and repository/Mathlib searches found the tensor-basis,
flatness, and change-of-rings ingredients used in the complete proofs.

## New nodes

`lem-pc-polynomial-induced-presentation` records the canonical length-one presentation
by two copies of the induced module. It is strictly the algebraic exact-sequence step,
has no Tor hypothesis or conclusion, and is fully proved in its own module.

`lem-pc-flat-scalar-extension-tor-comparison` records the independent homological
comparison for arbitrary flat ring maps, arbitrary modules, and all natural degrees.
It contains no polynomial successor bound and is fully proved in its own module.

Both nodes have complete proof steps, the source, all three kinds of search, and
verbatim Lean signatures. No change record or forced adaptation is required.

## Second reading by U2

1. **Interface: pass.** Compared every delivered module against its repository path.
   The two helper module paths are new. The item's diff consists only of plain proof
   imports, two private proved helpers, and replacement of its single `sorry` proof.
   The signature of `ModuleCat.polynomial_successor_tor_bound`, its docstring,
   namespace, universes, and all original public imports are byte-for-byte unchanged.
   No definition or existing statement is changed; no change record is needed.

2. **Proof and trust: pass.** Read all three modules and compiled them locally through
   `lcompile.py --all`. No errors or warnings occurred. Searched the delivered Lean
   files for sorry, axiom, unsafe, opaque, implemented_by, extern, and skipKernelTC:
   none occurs. The sequence endomorphisms are genuine linear-map constructions;
   delta and pi are explicitly constructed from scalar action, scalar extension,
   and the adjunction counit. The comparison uses a projective resolution and the
   already proved natural tensor comparison, not an unproved existence witness.
   Independently printed the axioms of all three public theorems in a scratch audit;
   each uses only `propext`, `Classical.choice`, and `Quot.sound`.

3. **New statements: pass; no new holes.** Read Weibel, Chapter 4, Corollary 4.3.6
   and Theorem 4.3.7, pp. 101–102, including sequence (*) and its coefficient proof
   at https://math.mit.edu/~hrm/palestine/weibel/04-homological_dimension.pdf .
   The presentation statement is exactly the short exact sequence used there, with
   arbitrary commutative A, n, and S-module M, transported to the last variable.
   It has neither a Tor hypothesis nor a Tor conclusion. Checked the single-sequence
   correction recurrence and the maximal-support coefficient: both work without
   cancellation, nontriviality, or injectivity of the variable action. In particular,
   n=0 gives the ordinary one-variable presentation; M=0 and the zero ring give zero
   sequences. The comparison statement generalizes the source's flat projective-
   resolution argument to a flat homomorphism; no faithful flatness is used.
   Its chain isomorphism is natural by the tensor comparison and braiding equations,
   and restriction commutes with homology. Degree zero is included, including for
   a zero algebra. Both new declarations have full proof docstrings and matching nodes.
   Independently searched LeanFinder for “change of rings Tor flat algebra induced
   module Shapiro lemma” and “polynomial module resolution shift minus endomorphism
   exact sequence”, and searched repository/Mathlib homology and polynomial sources.
   No existing theorem gives either complete statement. Inspected the nearby
   `isZero_tor_restrictScalars_of_flat`: it transfers vanishing in the other direction
   and does not replace the comparison needed here. Existing tensor comparison and
   horseshoe constructions are reused, rather than duplicated.

4. **Route and pruning: pass after import cleanup.** The main proof first constructs
   the induced presentation, kills both induced terms by the flat comparison, and
   uses the connecting homology map to kill the quotient's Tor. For i>d+1, the
   predecessor j satisfies j>d, also when d=0. Read `resolutionSES` in
   `Sheaf.Paper.TorLongExactFirstVariable`: its degreewise splitting is built from
   `Module.exists_free_resolution_ses_split`, and tensoring preserves this splitting.
   Thus the helper uses an actual short exact sequence of complexes. No shorter
   existing complete result was found. Removed the three redundant proof imports
   listed under No longer needed and recompiled successfully. All original imports
   stay; the original `proof_deps` was empty, so there are no old omitted dependencies
   to list. Read `dag/units/sk-thm-picard-duality.json`: its realized statement and
   steps are empty. The delivery retains the canonical polynomial-resolution route
   and bypasses no realized unit step. No project module is claimed pruned.

5. **Nodes: pass.** Compared the item's node with the repository: only `proof`,
   `proof_deps`, and `proof_origin` differ. Its dependencies match the presentation,
   comparison, and horseshoe actually used. The comparison node cites the existing
   natural tensor comparison, whose statement supplies precisely the isomorphisms
   and naturality equation used in the chain map. The presentation is proved directly
   with Mathlib sequence and basis operations. Both new nodes have source, proof
   steps, search records, creation provenance, blueprint ancestry, chapter/unit,
   and verbatim Lean signatures. No target, unit record, or unrelated node is edited.

Second-reading changes: removed three redundant proof imports from the item,
recorded those removals here and under No longer needed, and explicitly marked the
unavailable LeanSearch service as unavailable in both new nodes' search records.
The mathematical proof needed no repair. Closed 1 original hole, added 0 holes;
the two new helper statements are fully proved, not split-off open obligations.
