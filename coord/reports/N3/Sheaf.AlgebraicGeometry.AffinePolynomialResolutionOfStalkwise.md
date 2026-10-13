## What changed

Closed the proof body of AlgebraicGeometry.affinePolynomial_boundedResolution_of_stalkwise
without changing its signature or existing docstring. Its proof constructs finite generation
from the surjection, takes a finite subcover of projective-dimension loci, obtains one global
bound with Mathlib's local-to-global criterion, and uses the existing proved
ModuleCat.projective_resolution_ext_degree to obtain the actual bounded resolution.

Added Sheaf.AlgebraicGeometry.AffinePolynomialLocalizedFiniteProjectiveDimension for the
strictly pointwise part of the original argument, and Sheaf.RingTheory.ProjectiveDimensionLocusOpen
with a complete Mathlib-only induction proving openness. Added only private proof imports to
the item (the second reader removed the redundant Polynomial.Basic import), and updated its node's proof, proof_deps and proof_origin. No existing interface changed.
All three delivered modules compile without warnings in under five seconds each.

## Proved and sorry left

Hole closed: AlgebraicGeometry.affinePolynomial_boundedResolution_of_stalkwise
(lem-pc-affine-polynomial-resolution-of-stalkwise), one of one original holes.

Also proved: ModuleCat.isOpen_hasProjectiveDimensionLE_locus
(lem-pc-projective-dimension-locus-open) and the item's private
finite_projectiveDimension_of_localized helper. The openness proof handles the Shrink model
of localizedModule explicitly, then inducts on the finite projective presentation kernel.

Hole added and sole remaining delivered sorry:
AlgebraicGeometry.affinePolynomial_localized_finiteProjectiveDimension_of_stalkwise
(lem-pc-affine-polynomial-localized-finite-projective-dimension).
It asserts only prime-dependent bounds, not a global bound or a global resolution.
Its docstring contains the pointwise proof and its source, including the localization outside
ker(g), the compatible affine stalk identifications, and Tag 068X.

This is a decomposition (one upper hole closed, one strictly smaller hole added), not an
axiom-free proof of the entire item. No sorry remains in the item or in the locus theorem.
No definition or arbitrary witness is introduced. The zero module, empty spectrum, n = 0,
d = 0 and unbounded Krull dimension are all accommodated by the statements and proof.

## No longer needed

The second reader removed the redundant added private import
Mathlib.RingTheory.Polynomial.Basic; its instances are already available through
the proof imports. This removes no original dependency or old module.

No original import, existing node or existing module is pruned: the original public imports
are still needed by the unchanged statement. The original global bounded-perfect-complex
construction and positive cochain-tail cancellation are replaced by the finite-subcover proof
and the existing proved Ext/resolution bridge. Those plan steps had no separate named nodes.
Only ProjectiveResolutionExtDegree is imported for the bridge; neither
ProjectiveResolutionExtCharacterization nor ProjectiveResolutionExtAllDegrees is imported.
The proof needs no RingPseudoCoherentFiniteTorPerfect or derived-category model module.
These are avoided routes, not claims that their modules are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The item's DAG steps cited only definition nodes; there was no stated theorem for the
pointwise use of Tag 068X or the global use of Tag 068W. Searches found no existing
pointwise affine-polynomial criterion that could be imported without a cycle. The missing
pointwise step is now a named node. The global step is proved rather than postponed.
Mathlib already contains the open free locus and fixed-bound projective-dimension
local-to-global theorem, which make the explicit finite-cover argument possible.
LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle, source grep and
whole-blueprint searches were performed. Sources 069C, 068X, 068W, 068V and 00NX were read online.
The source files named in the unit's literature path are absent from this local checkout;
the unit record itself was read, and its realized fields are empty. No unit or chapter route
is changed. The Ext/resolution bridge is a fully proved generic tool from sk-thm-p1,
used only for the final resolution conversion, without importing another unit's main result.
There is no forced adaptation or change record, since existing signatures and visibility stay
identical and all added imports in the existing module are private.

## New nodes

lem-pc-affine-polynomial-localized-finite-projective-dimension: the pointwise polynomial
localization part of 069C, before compactness or any global bound. Its new module contains
one public theorem with its entire proof exactly `by sorry`. This is the sole split-off hole.

lem-pc-projective-dimension-locus-open: the fixed-bound openness fact, proved in full by
induction using Mathlib's open free locus, finite presentations, exact localization, and
projective-dimension shifting. Its new module is sorry-free and depends only on Mathlib.


## Second reading by N3

1. Unchanged interfaces: PASS. Diffed every delivered module against the read-only
repository. Only the item already exists; its existing declaration signature and
visibility are byte-for-byte unchanged. The existing node changes only proof,
proof_deps and proof_origin. No existing definition or target was altered; no
change record or forced adaptation is necessary. The two other modules are new.

2. Proof and axioms: PASS as a decomposition. Compiled all three files in import
order with lcompile.py, without warnings. Scratch copies with #print axioms show
only propext, Classical.choice and Quot.sound for the locus theorem and the
private compactness helper. The original theorem additionally uses sorryAx,
through the reported pointwise theorem; that split-off theorem also uses only
these four axioms. The sole delivered sorry is exactly the named public
AlgebraicGeometry.affinePolynomial_localized_finiteProjectiveDimension_of_stalkwise.
There are no definitions, arbitrary witness choices, unsafe declarations, axioms,
opaque declarations, extern attributes or kernel-checking bypasses in the delivery.

3. Split-off statement: PASS. Independently read Stacks Tags 069C, 068X and 068W
online and the actual HasStalkwiseFiniteTorDimension definition. The pointwise
statement is precisely the local polynomial-ring step of 069C, before the global
bound and resolution. A surjective g identifies primes containing ker(g) with
source points; compatibility identifies the A-local action with the stalk action.
The other localizations are zero. All fibres of A_p to R_q are localizations of
polynomial rings over residue fields and have global dimension at most n, as
068X requires. No finite Krull-dimension hypothesis is needed. Checked n = 0,
zero algebra, empty charts/spectrum and d = 0: zero localizations allow d = 0;
the compactness proof handles an empty finite subcover by its defined sup.
The theorem's complete proof docstring and node agree. This is a strictly smaller
pointwise conclusion, not a renamed global bounded-resolution assertion.
Independent LeanFinder query "finite Tor dimension under a polynomial algebra
quotient after prime localization" and Loogle query
'"HasProjectiveDimensionLE", "localizedModule"' found no replacement for the
pointwise bridge. Targeted rg searches of both Lean roots and Mathlib's local
projective-dimension code found the localization and fixed-bound criteria, not
the stalk-to-polynomial bridge. AffineSectionsFiniteTorOfStalkwise already depends
on this item, so cannot serve as its proof. Closing this remaining hole requires
formalizing the stalk identifications and 068X, not a short application of an
existing theorem. No extra hole was introduced during this reading.

4. Route and pruning: PASS after import cleanup. Read the original dependencies,
the fully proved ProjectiveResolutionExtDegree bridge, the local-to-global Mathlib
criterion and the unit sk-thm-picard-duality record. The unit's realized statement
and step lists are empty and no unit/chapter record or required route is changed.
The actual proof establishes finite generation, uses the pointwise bridge,
proves fixed-bound openness by finite-presentation kernel induction, takes a
finite subcover, and uses the existing Ext/resolution bridge. No original
proof_dep was removed, so "No longer needed" omits no old node. All original
public imports remain needed by the interface. The new locus module needs its
public Prime.Topology import: removing it makes IsOpen privately imported and
the signature fail to compile. The item's added Polynomial.Basic import is
redundant with its proof imports and was removed after a successful scratch
compile. This cleanup prunes no old node or globally unreachable module.

5. Node agreement: PASS. Checked both new nodes' self-contained statements,
sources, proof steps, proof_origin, search records, creation metadata, blueprint
ancestry, chapter/unit and Lean records. Their Lean signatures occur verbatim
in their respective files and each proof_deps is the union of its steps' uses.
The item's three revised DAG steps describe exactly its finite generation,
compactness/local-to-global and Ext/resolution proof. The proved openness node
records the same base case and localized kernel induction as the Lean proof.

Changes by this reader: removed the redundant private import
Mathlib.RingTheory.Polynomial.Basic from the item and added this review. Kept the
correct proofs, statements and nodes. Original holes closed: one; holes added:
one, the named pointwise theorem above; net hole reduction: zero (decomposition).
