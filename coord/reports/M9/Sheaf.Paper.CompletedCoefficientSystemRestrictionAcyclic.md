## What changed

Filled `WeilConjectures.CompletedCoefficientPushforward.systemRestriction_push_acyclic`
using the sequence-site presentations and scalar-restriction acyclicity on sections.
All additions to the assigned module are private proof helpers and proof imports;
its public statement and public imports are unchanged. Updated its DAG proof route.
Large coefficient sheaves remain folded locally, and the component isomorphisms have
an explicit section API, so their construction is not unfolded throughout the proof.
The proved generic section-evaluation lemma is in the new module
`Sheaf.CategoryTheory.CoefficientRestrictionSectionEvaluationAcyclic`; it is a genuine
slice argument, independent of coefficient systems and tower pushforward. It was
extracted after local definition optimizations because the delivery compile exceeded
the per-file limit. Both modules contain zero holes.

The generator normalization identifies the supplied finite coefficient isomorphisms
with the canonical ones, making the completed projections a compatible sequence-ring
map. The supplied evaluation and transition identities identify the full restriction
functor with scalar restriction on the sequence site. A K-injective resolution of
the restricted complex is then a quasi-isomorphism on every section complex: restrict
to the corresponding slice and apply scalar-restriction acyclicity of global sections.
Tower pushforward evaluates these same complexes over pro-etale base changes, so it
preserves that resolution's quasi-isomorphism. Naturality of the supplied derived unit
and its computation on the resolution finish the proof.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.CompletedCoefficientPushforward.systemRestriction_push_acyclic`
(node `lem-pur-completed-coefficient-system-restriction-acyclic`).
Before extraction, the complete theorem's axiom check returned exactly `propext`,
`Classical.choice`, and `Quot.sound`. Profiling commands and diagnostic output commands
were removed for delivery. Both files then compiled successfully in import order
without warnings. The extracted helper theorem
`SheafOfModules.coefficientRestrictionSectionsEvaluation_quasiIso` is also fully proved.

One original hole closed; zero holes added; zero split-off statements; zero holes left
in the assigned module. The private helpers are proved, not assumed. No shared
statement or definition changed.

## No longer needed

The former planned dependency `lem-pur-diagram-ring-restriction-pushforward`
(`Sheaf.CategoryTheory.DiagramRingRestrictionPushforward`) is not used by this proof:
sectionwise detection replaces a separate derived diagram-pushforward comparison.
The former direct dependency
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
(`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`) is now used through
the existing scalar-restriction sections theorem, rather than directly specialized to
tower pushforward. Neither module is withdrawn: other consumers and source-library
obligations remain. No original import was removed; proof dependencies were not yet
imported in the original item. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No disputed statement. The DAG's ringed-topos argument is valid in principle, but
specializing it directly to the two sequence-site presentations requires unnecessary
transport of derived models. The existing sectionwise scalar-restriction theorem
provides a shorter implementation, followed by naturality of the supplied unit.
The proof does not assume scalar restriction preserves K-injective complexes.

## New nodes

`lem-coef-restriction-sections-evaluation-acyclic`, in
`lean/Sheaf/CategoryTheory/CoefficientRestrictionSectionEvaluationAcyclic.lean`, proves
scalar-restriction acyclicity on sections of every object by passing to its slice and
applying the existing global-sections theorem. This is a strictly smaller, proved
step of the argument; no new proof obligation or `sorry` is introduced. No change
record is needed: no existing shared interface changed.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
