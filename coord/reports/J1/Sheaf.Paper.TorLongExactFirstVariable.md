## What changed

Proved `CategoryTheory.tor_long_exact_first_variable` in
`Sheaf.Paper.TorLongExactFirstVariable`, preserving its signature and visibility.
The proof follows the existing node's direct resolution route. Private, fully proved
helpers turn the linear free resolutions from `Module.exists_free_resolution_ses_split`
into Mathlib projective resolutions and compatible chain maps, retaining the degreewise
splittings and augmentation squares. No resolution data is chosen from an unproved theorem.

Tensoring each degreewise splitting gives a short exact sequence of complexes.
Mathlib's homology sequence supplies the connecting map and both low-degree exactness
statements. The resolution comparison isomorphisms identify the degree-one maps with
`Tor'`; the canonical degree-zero homology isomorphisms identify the remaining maps
with tensor maps. A private exactness transport lemma proves the two required
`Function.Exact` statements. Tensor right exactness and surjectivity prove the tail.

Naturality uses the short-complex morphism induced by the natural transformation
`- ⊗ g`, Mathlib's `HomologySequence.δ_naturality`,
`ProjectiveResolution.leftDerived_app_eq`, and a proved naturality lemma for the
canonical degree-zero identification. The resolutions are fixed before the second
variable is introduced.

Added proof-only imports of `Mathlib.Algebra.Homology.HomologySequenceLemmas`,
`Mathlib.Algebra.Homology.HomologicalComplexAbelian`,
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`,
`Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed`,
`Mathlib.CategoryTheory.Monoidal.Closed.Braided`, and
`Mathlib.LinearAlgebra.TensorProduct.RightExactness`.

The file compiles locally without warnings. Every line is at most 100 characters.
No existing public declaration, docstring, definition, or public import was changed.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.tor_long_exact_first_variable`
(node `lem-weil-pbc-tor-long-exact-first-variable`).
All private helpers are fully proved. No holes were added or split off, and no
`sorry` remains in the delivered module. This is a proof, not a decomposition.

## No longer needed

None. No imports were removed and no planned dependency nodes or modules were
pruned. The five original proof dependencies remain the resolution construction,
Tor definition, resolution-map comparison, tensor right exactness, and the snake
lemma through Mathlib's homology-sequence implementation. The unit's realized
statement and proof steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical errors found. The existing free-resolution theorem already has a
complete proof, but its interface is families of module types and linear maps;
Mathlib's Tor comparison lemmas require bundled projective resolutions. The delivery
provides that bridge explicitly, including the augmentation quasi-isomorphisms.
The generic homology-sequence API also supplies naturality directly, so the proof
need not repeat the elementwise snake-map calculation in the node's prose.

The required searches were performed with `msearch.py` LeanFinder and Loogle,
and local searches of Mathlib and the source library. No ready-made long exact
sequence for `Tor'` was found; the available homology sequence and the existing
free-resolution construction suffice. No new nodes or interface adaptations are needed.


## Second reading by J1

1. Compared the complete module diff with the repository. The signature of
   `CategoryTheory.tor_long_exact_first_variable`, its docstring, visibility, and
   public imports are byte-for-byte unchanged. No definitions used by its statement
   changed; no change record is needed.
2. Compiled the delivered module successfully with `lcompile.py` (5.5 seconds,
   no warnings). A scratch copy with `#print axioms` reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`. There are no holes or forbidden declarations
   in the module. `resolutionOfExact` constructs the chain complex from the given
   differentials and proves its augmentation a quasi-isomorphism using range/kernel
   equalities. `resolutionSES` uses the already proved free-resolution theorem;
   its chosen resolutions are not witnesses of an unproved existence claim.
3. No statements were split off. Read each private helper: augmentation squares give
   the comparison maps, the degreewise splitting identities give short exactness
   after tensoring, and `exact_of_iso` transports exactness without changing maps.
   The original hypotheses are all retained: injectivity of u, surjectivity of v,
   and Function.Exact u v feed the resolution construction. The main proof gives
   both exact pairs adjoining delta, tensor right exactness and surjectivity, and
   naturality for every linear g. Resolutions are fixed before N is introduced,
   so the existential family is coherent. Zero modules and split sequences require
   no additional hypotheses or choices depending on N.
4. The shortest available route uses Mathlib's homology sequence, resolution
   comparisons, and degree-zero isomorphism rather than repeating a snake chase.
   Tested deletion of each of the six added proof-only imports in scratch copies:
   every deletion fails with a missing theorem or finite-colimit-preservation
   instance. No import is pruned. Read `dag/units/sk-thm-p1.json`: the item is a
   generic tool below the unit's realized steps and changes none of their routes.
5. Read node `lem-weil-pbc-tor-long-exact-first-variable` in full. Its proof and
   five proof dependencies agree with the implementation: split resolutions,
   Tor definition, resolution-lift comparison, tensor right exactness, and the
   snake lemma via Mathlib's homology-sequence implementation. The origin already
   records this direct first-variable route (065P and 0111), not Tor symmetry.
   No new node is needed and no old proof dependency is unused.

Changed only this report by recording the second reading. No Lean or DAG repair
was needed; the existing proof closes the one original hole and adds none.
