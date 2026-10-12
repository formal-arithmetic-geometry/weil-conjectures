## What changed

The existing `AlgebraicGeometry.Scheme.exists_fieldSection_of_invariant_germ` now composes
finite Galois representation with finite Galois descent. It proves germ injectivity locally:
a pointed refinement of the one-point spectrum is a singleton cover, so separatedness makes
restriction injective. Its existing signature is byte-for-byte unchanged. No definition changed.

Added `Sheaf.AlgebraicGeometry.Sites.FiniteGaloisGermRepresentative` and
`Sheaf.AlgebraicGeometry.Sites.FiniteGaloisInvariantGermDescent`, each with one documented
open theorem and one node. Their imports into the original module are proof-only imports.
The previously returned duplicate `FieldGermInjective` module and node are absent.

## Proved and sorry left

Closed the original syntactic hole in
`AlgebraicGeometry.Scheme.exists_fieldSection_of_invariant_germ` (1 of 1 original holes).
Its proof still depends on the following two newly added holes:

- `AlgebraicGeometry.Scheme.exists_finiteGalois_germ_representative`, node
  `lem-exc-field-invariant-germ-representative-construction`.
- `AlgebraicGeometry.Scheme.exists_fieldSection_of_finiteGalois_invariant_representative`, node
  `lem-exc-field-invariant-germ-representative-identification`.

This is a decomposition, not an axiom-free proof or a net hole reduction: one hole closed,
two added, net minus one. The local injectivity argument is proved without another hole.
There are no definitions, arbitrary data witnesses chosen in definitions, or additional sorries
in this delivery. Scratch `#print axioms` checks on all three declarations show only
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from the open theorems.

## No longer needed

The original module no longer directly imports
`Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`,
`Sheaf.AlgebraicGeometry.Sites.FiniteGaloisSectionsDescent`,
`Mathlib.FieldTheory.Galois.GaloisClosure`, or
`Sheaf.FieldTheory.GaloisAutomorphismExtension`. They remain needed through the two new modules;
no upstream library module is claimed pruned from the targets' import closure.

The old direct proof dependencies below move into the split nodes, rather than disappearing
from the mathematical argument:

- `lem-weil-pbc-etale-covering-composition` (descent).
- `lem-weil-pbc-etale-fibre-discrete-separable-points` (construction).
- `lem-weil-pbc-finite-set-in-finite-galois-subextension` (construction).
- `lem-exc-galois-automorphism-extension` (descent).
- `lem-exc-finite-galois-sections-descent` (descent).

`def-weil-pbc-geometric-stalks`, `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`, and
`def-weil-pbc-etale-sheaf-of-sets` stay as dependencies of the local injectivity proof.
Removed the redundant `Mathlib.FieldTheory.KrullTopology` public import from the new descent
module: `fixingSubgroup` is already provided by `Galois.Basic`. The original module's public
imports remain unchanged. The discarded duplicate injectivity module/node was never landed.

## Where the brief, the DAG or earlier work was wrong

The prior delivery duplicated the private `fieldGerm_injective` in
`FieldSectionsStalkInvariants`, which imports this item and cannot be used here without a cycle.
The argument is correctly local now. The worker's node still cited the removed injectivity
node in a proof step despite omitting it from `proof_deps`; the second reader repaired this.
The earlier report did not account for the relocated direct imports/dependencies or the net
hole increase. The second reader corrected both counts and the pruning claim.

## New nodes

`lem-exc-field-invariant-germ-representative-construction` represents an arbitrary germ over
a finite Galois field containing L. It uses no action or descent. Its complete docstring proof
uses the stalk representative, the finite separable point component, factorization into Ks,
and finite Galois enlargement; the node records those dependencies and searches.

`lem-exc-field-invariant-germ-representative-identification` descends a given finite Galois
representative with injective germ map and fixed germ. Its docstring uses extension of
automorphisms, injectivity, restriction to Spec L, finite Galois sections descent, and
naturality. It does not construct the initial representative or prove injectivity.
No statement/definition change records are required.

## Second reading by G3

1. Compared the existing module with the repository by `diff` and independently compared
   the complete theorem signature as exact text. Verdict: unchanged binders, hypotheses,
   conclusion, namespace and visibility; no existing definitions altered. The two other
   modules are new. Public imports of the existing module are unchanged.
2. Compiled all three modules in import order through `lcompile.py`, with no errors or
   warnings. Compiled a scratch copy with `#print axioms` for all three declarations:
   only the standard three axioms and the expected `sorryAx`. Exactly the two named
   intermediate theorems contain `sorry`; no forbidden declarations or hollow definitions.
   Read the local proof: the refinement has an Omega-point, hence maps onto Spec E; the
   singleton-cover sheaf condition really implies the equality of the original sections.
3. Read Stacks [04JM](https://stacks.math.columbia.edu/tag/04JM), direct proof, and
   [03QW](https://stacks.math.columbia.edu/tag/03QW), the lift-change action. Construction
   requires no invariance; a finite separable residue-field embedding factors through Ks,
   and adjoining conjugates of finite bases contains both it and L. Descent starts with
   that representative and injectivity, extends each L-automorphism of E to Ks and Omega,
   and applies finite Galois descent over L. These are distinct proper parts of the original
   argument. Checked L=K, E=L when Galois, separably closed K (also imperfect), and the empty
   sheaf: a germ hypothesis excludes the empty case; purely inseparable parts cause no
   change to separable embeddings or the extension argument. Ran fresh Loogle `sheafFiber`,
   LeanFinder cofinal-Galois-neighbourhood and finite-Galois-germ-descent searches, and grep
   with Galois/stalk/germ/cofinal/descend terms. No independent replacement theorem found.
   Read upstream/local uses of `toPresheafFiber_jointly_surjective`, Hilbert90 descent APIs,
   and `FieldEquivariantGermsOnePoint`; the latter depends on this item through
   `FieldSectionsStalkInvariants` and cannot shorten this proof without a cycle.
   Existing private embedding/injectivity helpers are not duplicated as new declarations.
4. The proof follows the direct finite-Galois route. The unit `sk-prop-h2` and its `realized`
   record are unchanged: this item is a lower tool and realizes no unit statement or step.
   Kept the original public import interface, classified imports of the split theorems as
   proof-only, and removed one redundant public import in the new module. All five old
   dependencies moved out of the direct proof are listed above, and the three used by local
   injectivity are retained. No whole-module closure pruning is claimed.
5. Read all three nodes with the Lean open. Repaired the parent proof steps and the union
   `proof_deps` to describe construction, local injectivity, and descent, removing the stale
   deleted-node citation. `proof_origin` now explicitly records decomposition. The two new
   node signatures agree with their Lean, docstrings explain their full arguments, their
   recorded dependencies implement those arguments, and their search records are present.

Second reading changed the parent DAG proof/dependencies/origin, added the missing module
source docstrings, removed the redundant new KrullTopology import, and corrected this report.
It did not change any theorem signature or the worker's correct Lean proof.
