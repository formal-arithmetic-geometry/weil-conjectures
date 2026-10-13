## What changed

Proved `AlgebraicGeometry.principalCechDifferential_square` in
`Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal`. The proof expands the total
square into vertical-square, horizontal-square, and mixed terms. Every helper
is private and proved: vertical square-zero uses `F.d_comp_d`; horizontal
cancellation uses `Finset.sum_involution` on ordered distinct deletion pairs;
mixed cancellation uses naturality and the change of the vertical sign.
Restrictions and equality transports compose by functoriality and equality
induction. No existing signature, definition, visibility, or import changed.
The node's proof and proof_origin now record the completed square-zero argument.

## Proved and sorry left

Closed one of the two original holes:
`AlgebraicGeometry.principalCechDifferential_square`
(node `def-sc-principal-open-alternating-total`). This is a proof, not a
decomposition: every private helper is proved, and zero holes were added.
`#print axioms` for the completed theorem reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The complete module compiles without
warnings under the prescribed single-file compiler.

The sole remaining sorry is
`AlgebraicGeometry.principalCechAugmentation_quasiIso`
(node `def-sc-principal-open-alternating-total`), unchanged. No other sorry
is introduced by this delivery. Empty covers and singleton deletion cases
are included in the proof through empty sums and the explicit zero branches.

## No longer needed

No existing import was removed; all three original public imports remain.
No existing dependency node or module is pruned from the import closure.
The square-zero argument does not need to import
`Sheaf.AlgebraicGeometry.PrincipalCechHorizontalSquare`,
`Sheaf.AlgebraicGeometry.PrincipalCechColumns`,
`Sheaf.AlgebraicGeometry.PrincipalCechBicomplexComparison`, or
`Sheaf.AlgebraicGeometry.PrincipalCechFiniteColumnModel`.
The related horizontal-square proof informed the elementary swap calculation,
but no declaration from those modules occurs in the delivered proof.
There are no new modules or nodes.

## Where the brief, the DAG or earlier work was wrong

The node's previous proof_origin said square-zero was still unproved; this
is now updated. The existing principal-column horizontal-square theorem is
not an importable shortcut: its module already imports this module, so an
import here would create a cycle. Its categorical row index also differs
from the total-coordinate index used here. The direct coordinate proof
avoids both problems and preserves the unit route.

The other original hole concerns all K-injective complexes on the union of
the principal opens. The existing general finite-cover K-injective theorem
uses a covering of an entire scheme, global-ring scalars, increasing tuples,
and a categorical total. Applying it here would still require restriction to
the union and an augmentation-compatible comparison to these finite-subset
A-module coordinates. The delivered square-zero proof does not assume this
comparison or modify the remaining theorem.

## Second reading by V3

1. Compared the delivered module with the repository version. Existing declarations and signatures are unchanged; only the square-zero proof and its private helpers were added.
2. Compiled the module with the prescribed `lcompile.py`; it succeeds without warnings. The remaining sorry is only `principalCechAugmentation_quasiIso`; no axioms or unsafe constructs were added.
3. The square-zero statement is unchanged and the helper lemmas are private, true, and strictly internal to the coordinate cancellation. No new nodes or split-off statements were added.
4. The proof follows the total-complex route: vertical square, horizontal pair cancellation, and mixed cancellation. No imports were removed because all public imports remain used by the module interface.
5. The DAG node proof and proof_origin describe the completed square-zero calculation; no unit realized step was bypassed.

Changed only the proof body and private helper lemmas; no definitions, signatures, imports, or DAG statements were changed.
