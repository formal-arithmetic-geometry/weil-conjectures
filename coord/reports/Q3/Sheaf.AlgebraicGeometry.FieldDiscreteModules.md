## What changed

Retained work was checked against the current sources. All seven delivered Lean
modules compile, and `deliver3.py --no-push` passed the preflight on 2026-10-19
(`scratchpad/resume-active-dry-run.log`, dry-run commit `3106cf346d`). The delivery
is classified CODEX because it adds six proved support modules and their nodes.
The axiom probe for `FieldModuleSectionsInvariants` timed out after 60 seconds;
the tool reports that the maintainer reruns this probe. Its ordinary compile
passed. The remaining axiom probes reported no forbidden axiom. Earlier
compile-service failures are recorded in the scratchpad.

Proved `AlgebraicGeometry.Scheme.etaleModuleSheaves_equiv_discreteGModules` with its
original signature. Apply the existing abelian equivalence at the algebraic closure
of the separable closure, transport scalar endomorphisms, obtain the natural linear
sections-to-invariants comparison, and transport the stalk comparison back to the
separable closure. The action formula follows by extending a Galois automorphism
and comparing the extended lifts and their germs.

Six new support modules contain complete constructions and proofs: `ScalarObjects`,
`ScalarModuleSheaves`, `ScalarDiscreteRepresentations`, `ScalarStalkTransport`,
`SepClosedEtalePointComparison`, and `FieldModuleSectionsInvariants`. Their nodes
record the argument and the exact Lean signatures. No existing definition or
statement changes and no consumer adaptations are required. All new imports of
the item are proof imports. The item's existing public imports are preserved.

The sources read are Stacks Project etale-cohomology.tex, Lemmas
`lemma-equivalence-abelian-sheaves-point` (04JQ) and `lemma-global-sections-point`
(04JM), and the current blueprint field-discrete-modules statement. The point
comparison uses the already proved source-library separably closed lifting and
field-map cancellation theorems. The existing internal-module transport result
uses explicit internal addition and products; the scalar-object construction here
instead transports ring homomorphisms into endomorphism rings of already additive
objects, retaining the given abelian comparison without rebuilding group laws.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Scheme.etaleModuleSheaves_equiv_discreteGModules`
(node `lem-exc-field-discrete-modules`). Holes closed: 1 of 1. Holes added: 0.
There are no `sorry`s in any delivered Lean module and no split-off holes.
The proof uses the existing declared abelian and set-valued sections equivalences;
this is a proof from those declarations, not a claim that their entire dependency
closure is already free of holes.

Proved the support declarations
`CategoryTheory.ScalarObject.equivalence`,
`CategoryTheory.ScalarObject.moduleSheafEquivalence`,
`CategoryTheory.ScalarObject.discreteRepEquivalence`,
`CategoryTheory.ScalarObject.scalarStalkTransport`,
`AlgebraicGeometry.Scheme.sepClosedEtaleStalkIso`, and
`AlgebraicGeometry.Scheme.nonempty_iso_etaleModuleSections_invariants`, together
with their concrete construction maps and germ compatibility lemmas.

## No longer needed

Removed the item's proof imports:

- `Sheaf.AlgebraicGeometry.EtaleFieldGsets`: reached through the abelian equivalence;
  the item has no separate use of its scheme/G-set classification.
- `Sheaf.AlgebraicGeometry.Sites.EtaleSheavesGsetsPoint`: the existing abelian
  equivalence and sections-invariants theorem already provide the needed interfaces.
- `Sheaf.CategoryTheory.DiscreteModulesAbelian`: the theorem's signature requests
  an equivalence, a stalk isomorphism, a sections isomorphism, and an action formula;
  it has no separate abelian-structure or enough-injectives conclusion.
- `Sheaf.RepresentationTheory.DiscreteContinuousCohomology`: no derived-functor
  assertion occurs in the statement being proved.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: Mathlib point germ comparisons supply
  the colimit facts used here.

Accordingly the item's direct proof dependencies no longer include
`lem-exc-etale-sheaves-gsets-point`, `lem-exc-etale-field-gsets`,
`def-weil-pbc-etale-site`, `def-weil-pbc-geometric-stalks`,
`def-exc-continuous-cohomology`, `lem-exc-discrete-modules-abelian`, or
`prop-weil-pbc-geometric-stalks-exact`. Definitions needed by the unchanged
statement remain in `stmt_deps`; set-valued and abelian prerequisites remain in
the supporting nodes that actually use them. No whole-library pruning is claimed
for a module that is still needed elsewhere. The unit `sk-prop-h2` has no realized
statement or proof step in this item; its route is unchanged.

Three retained exploratory modules (`FieldModuleGaloisStalkFunctor`,
`FieldModuleGlobalSections`, `FieldModuleStalkEquivalence`) are unnecessary and
are kept only in the sandbox scratchpad, outside the delivery.

## Where the brief, the DAG or earlier work was wrong

The retained earlier work had no report or DAG records and its scalar-object
support did not compile. The original theorem was still `sorry`. Repaired
endomorphism-ring additivity and explicit scalar parameters and assembled the
actual theorem proof rather than delivering the exploratory files.

The existing abelian equivalence is stated at an algebraically closed extension,
whereas this item uses the separable closure itself. This requires the explicit
separably closed point comparison and the calculation on changed lifts; simply
specializing the abelian theorem to Ks is unavailable for an imperfect field.
The existing sections theorem also requires the larger field to be algebraic;
choosing the algebraic closure of Ks satisfies that hypothesis.

Edge cases checked mathematically: a separably closed imperfect field is allowed;
the Galois group may be trivial; the coefficient ring and the sheaf may be zero;
no nonzero element or positive characteristic assumption is used. The support
scalar constructions work for arbitrary rings, and the module stalk comparison
uses commutativity only for scalar sheaf maps. No finiteness assumption is added.

## New nodes

`lem-exc-scalar-objects-equivalence`: transport a ring map into an endomorphism
ring through a fully faithful additive equivalence; prove essential surjectivity
by conjugating along the counit. Module `Sheaf.CategoryTheory.ScalarObjects`.

`lem-exc-scalar-module-sheaves`: interpret scalar endomorphisms sectionwise and
reflect the sheaf condition through the forgetful functor. Module
`Sheaf.CategoryTheory.ScalarModuleSheaves`.

`lem-exc-scalar-discrete-representations`: restrict to integer representations or
recover the module action from scalar endomorphisms; carriers and stabilizers
are preserved. Module `Sheaf.CategoryTheory.ScalarDiscreteRepresentations`.

`lem-exc-scalar-stalk-transport`: combine the preceding equivalences; naturality
for scalar maps proves linearity, and the forgetful stalk comparison preserves
the germ action formula. Module `Sheaf.CategoryTheory.ScalarStalkTransport`.

`lem-exc-sep-closed-etale-point-comparison`: a field extension between separably
closed points gives natural bijections on lifts and hence stalk isomorphisms
with a proved germ formula. Module
`Sheaf.AlgebraicGeometry.SepClosedEtalePointComparison`.

`lem-exc-field-module-sections-invariants`: upgrade the existing set-valued
sections-invariants comparison to a natural module-linear isomorphism using the
terminal germ and the supplied action formula. Module
`Sheaf.AlgebraicGeometry.FieldModuleSectionsInvariants`.

All six results are proved. Their records include the LeanSearch, Loogle or
LeanFinder, and grep searches from this sandbox. No exact module-stalk transport
interface was found; the proof uses the available component lemmas. Sources are
04JQ for scalar transport, 04JM for sections, and 04FN for point comparison.
No change record is needed because existing signatures and definitions are
unchanged.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
