## What changed

Replaced the hole in `CategoryTheory.quasiIso_ringedKoszul_roosComparison` by the
K-injective telescope argument. The proof obtains the proved telescope-to-colimit
quasi-isomorphism with both defining legs, applies the existing
`quasiIso_homComplex_map` with the identity coefficient map, and transports the
result across an isomorphism of arrows.

The algebraic identifications are separated into two new modules, with one public
statement each. `RingedKoszulFiniteHomTower` asserts finite Koszul evaluation as
an isomorphism of the complete strict inverse diagrams. `TelescopeHomRoosArrow`
asserts the general signed telescope-Hom identification, including the actual
comparison arrow. Both hold for arbitrary coefficient complexes, without any
K-injectivity or quasi-isomorphism hypothesis or conclusion. Thus neither is the
original quasi-isomorphism obligation under another name. The delivered result is
a decomposition, not a net hole closure.

The item retains its original statement and both public imports; the three added
imports are private proof dependencies. No adopted source-library file changed.

## Proved and sorry left

Closed the original direct hole in
`CategoryTheory.quasiIso_ringedKoszul_roosComparison`
(node `lem-weil-pbc-ringed-koszul-roos-inclusion`) by a complete assembly proof.

Added two direct holes, each exactly the whole proof of its named public theorem:

- `CategoryTheory.exists_ringedKoszul_finiteHomTower_iso`, node
  `lem-weil-pbc-ringed-koszul-finite-hom-tower`.
- `CategoryTheory.telescopeHom_roos_arrow_iso`, node
  `lem-weil-pbc-telescope-hom-roos-arrow`.

There are zero direct holes left in the item module and two in the new modules.
This closes one upper hole and splits off two lower holes, for net minus one.
The existing Hom-invariance theorem may itself depend on other project holes;
those were neither changed nor counted as closed.

## No longer needed

The assembly does not use
`CategoryTheory.exists_ringedKoszul_colimitHom_ordinaryLimit_iso` or its module
`Sheaf.CategoryTheory.RingedKoszulColimitHomOrdinaryLimit`, node
`lem-weil-pbc-ringed-koszul-colimit-hom-ordinary-limit`. Removed this node from the
item's proof dependencies. Its unit-normalized limit isomorphism supplies no
finite-stage evaluation or telescope normalization; the new general arrow lemma
uses the universal property directly and the finite tower evaluation supplies the
actual strict tensor transitions. This is local pruning only; that existing
module is preserved for its other consumers.

No existing Lean import was removed and no existing module was withdrawn. The
item's statement still uses the two original public imports. Its proof still uses
the telescope comparison and K-injective Hom-invariance dependencies. The Hom
complex and explicit Roos comparison definitions are used through the imported
interfaces and new nodes. No unit statement or unit proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original dependency
`exists_ringedKoszul_colimitHom_ordinaryLimit_iso` only gives a limit isomorphism
normalized at the unit. It does not expose an isomorphism of strict diagrams or
its finite-stage projections, so its declaration cannot directly supply the
finite evaluation naturality claimed in step 2 of the item's original plan.
The revised DAG records the precise finite tower and general signed arrow steps.

Edge cases of both new statements were checked mathematically: the empty Koszul
list uses the unit evaluation and tensor unitor; zero and invertible generators
require no division; the general arrow lemma handles constant and zero sequences
and assumes neither exact products nor K-injectivity. A different choice of the
tower isomorphism changes both induced limit and product isomorphisms coherently,
so its normalization need not be separately assumed.

## New nodes

`lem-weil-pbc-ringed-koszul-finite-hom-tower` is stated in
`Sheaf.CategoryTheory.RingedKoszulFiniteHomTower`. It isolates finite evaluation and
naturality in the actual Koszul transitions, for arbitrary coefficients, before
any limit or quasi-isomorphism argument.

`lem-weil-pbc-telescope-hom-roos-arrow` is stated in
`Sheaf.Algebra.Homology.TelescopeHomRoosArrow`. It isolates the ordinary algebraic
Hom-colimit/product universal properties, signed cone coordinates and both
canonical legs. Its hypotheses include no quasi-isomorphism and its conclusion
asserts only an isomorphism of arrows. Sources and complete natural-language
proofs accompany both statements. There are no existing interface changes needing
a change record.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
