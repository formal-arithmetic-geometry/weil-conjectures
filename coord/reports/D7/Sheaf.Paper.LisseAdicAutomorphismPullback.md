## What changed

Prove the remaining coefficient-transformation existence theorem in
`Sheaf.Paper.LisseAdicAutomorphismPullback`. First prove that the integral
pullback/scalar comparison commutes with the canonical scalar unit and composite
comparisons, by evaluating on local tensor generators and cancelling index casts.
Rationalize these two equations using the pure-tensor formulas. A generic proved
constructor assembles the resulting strong transformation, with exactly the
prescribed components and inverse scalar comparisons. Preserve the original
algebraic-closure hypothesis and suppress its unused-section-variable warning
locally for the completed existence theorem.

Repair `Sheaf.Paper.LisseAdicSheaves`: the coefficient diagram is constructed from
its explicit tensor unit and associativity comparisons. Expose the existing
comparison constructions and their generator formulas. The former arbitrary
choice from nonemptiness specified only objects and arrows and could not justify
the prescribed naturality constraints. This repair retains those objects/arrows,
the integral/rational categories, and all existing written public signatures. It reopens
the statement review of targets using the algebraic coefficient construction.

Cache the existing coefficient and Hom structures and name the inherited integral
category. The integral full subcategory and rational Hom tensor are semireducible
definitions of the same types. Disable the redundant reflexive-quiver inference
path during each file and restore it at the end. These changes avoid repeated
conversion through the lissity predicate and tensor instances. The scalar construction
uses the inherited ring instances directly, avoiding repeated comparison with named
copies of the same structures. Scalar-extension records use the named level/Hom
interfaces during elaboration, without expanding their implementations. Avoid generating
unused constructor-injectivity lemmas and size functions for the coefficient records.
No source-library
module or target statement is changed.

The item adds a proof import of `Sheaf.Paper.LisseAdicSheaves`.
The repaired coefficient module exposes the imports needed by its now-public
construction data. Both existing DAG nodes record the completed argument.
Change record: `coord/changes/D7-canonical-lisse-coefficient-coherence.md`.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.Scheme.automorphismLisseCoefficientTransformation_exists`
(node `def-wf-lisse-adic-automorphism-pullback`).

Newly proved intermediate equations include
`integralAutomorphismScalar_unit`, `integralAutomorphismScalar_comp`,
`rationalAutomorphismScalar_unit`, and `rationalAutomorphismScalar_comp`.
All construction and formula declarations exposed in the coefficient module
are proved. No holes are added, no statements are split off, and no `sorry`
remains in either changed module: one hole closed, zero added.

Verification: the complete item compiles in 32.6 seconds. Its `#print axioms`
contains exactly `propext`, `Classical.choice`, and `Quot.sound`; in particular,
there is no admitted dependency. The repaired coefficient module compiles with
saved library artifacts in 56.8 seconds. All 70 downstream modules compile
against the repaired definitions, including
the scalar fibre API, fibre paths, monodromy equivalences, completed systems and
the source-library zeta-function consumers. No adaptation is needed; unchanged
verification copies are excluded from this delivery.

## No longer needed

None. No module or DAG node is withdrawn. The declared dependencies and the
unit route remain needed. No imports are removed. Unused compiler-generated
constructor-injectivity lemmas and size functions for the four coefficient-data
records are suppressed; there are no textual consumers of those generated names.

## Where the brief, the DAG or earlier work was wrong

The outstanding theorem's statement correctly requires the identity-on-tensors
scalar constraints. The old coefficient-diagram definition chose an arbitrary
pseudofunctor from an existence theorem fixing only objects and arrow functors.
That specification did not fix its unit and composition constraints, so the
required strong transformation could not be derived for that arbitrary choice.
The existing node already recorded this dispute. The repair constructs the
canonical diagram from the fully proved tensor comparisons instead of changing
the automorphism theorem's statement.

Edge cases follow from the actual generator equations: identity automorphisms,
identity coefficient inclusions, level zero, empty schemes, and permutations of
connected components. Composite and ramified inclusions use the proved source-index
composition equality; the only remaining transports cancel by equality-proof
irrelevance. There is no assumption of connectedness or trivial ramification.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
