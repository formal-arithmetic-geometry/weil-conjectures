## What changed

Proved `WeilConjectures.CompactSupportCondensedRealization.fieldRefinement_comp`
for the original chosen refinement maps. The argument uses the existing derived
pullback associativity law and the original unique open-unit normalization.
Two new, fully proved generic composition modules establish composition of normalized lifts
and composition of compatible adjunction mates. Private helpers handle the
refinement equality transports and assemble the resulting natural transformations.
The final public proof rewrites to the assembled presentation and applies its
composition law. The DAG records this route; no new hole is introduced.

The return functor of `fieldPushComp` is written with the existing,
definitionally equal `fieldDerivedLowerStar` name; its constructor body is
unchanged. The original geometric functor bodies, local data-instance choices,
and final exported instance registrations are unchanged. The new proof section
keeps named constructions irreducible while using proved APIs. Whole-transformation
and component identities are kept separate to avoid expensive definitional
comparisons of derived functors.

To keep compilation within the file limit, generic identity, shift,
coefficient-composition and normalized-lift naturality helpers move unchanged to
`Sheaf.CategoryTheory.CompactSupportIdentityCalculus`. The formerly private
`normalized_identity_lift` is now the proved
`CategoryTheory.normalizedIdentityLift`; the existing identity proof calls it
under that name. Other extracted helpers remain private and are used through
`import all`.

The original concrete constructions and their already proved coherence laws move
to `Sheaf.Paper.CondensedCompactSupportProjectionCore`, with zero holes. The item
publicly imports this core and retains both original holed theorem declarations,
now with the composition theorem proved. All 61 original public declarations keep
their names. Their signatures retain the original types, with only the named,
definitionally equal `fieldPushComp` return-type presentation described above; their DAG attachments are divided between the core
and the item. Every original public import is retained in the item. The original
instance registrations remain verbatim at its end; the new composition proof
activates the same existing local cache instances. No data construction changes.
The core's private normalization-specification helper is also proved locally in
the item for use by composition.

The change is recorded in
`coord/changes/J3-condensed-refinement-composition-proof-context.md`.
Validation: compile result `a2a715f29da4acabf4ec147f` compiled all five delivery
modules, all four direct consumers, and the axiom printer successfully, within
the required limits and without delivery-source warnings. The unchanged consumer
copies and axiom printer were removed after validation. A declaration-table check
confirmed all 61 original public names remain, every original public non-theorem
body matches exactly, and every recorded Lean signature matches its declaration.
The only textual signature change is the existing functor-name presentation of
`fieldPushComp` described above. No profiling options remain.

## Proved and sorry left

Original holes: 2. Closed: 1. Added: 0. Split off: 0.

Closed: `WeilConjectures.CompactSupportCondensedRealization.fieldRefinement_comp`,
at node `def-pur-condensed-compact-support-projection`.

Retained unchanged:
`WeilConjectures.CompactSupportCondensedRealization.condensedProjection_refinement`,
at the same node. This is the only sorry left in the delivered module; the new core
and all three new generic modules have zero holes. The proof
of composition uses the original `fieldProperOpen_existsUnique`; its existing
geometric dependency `condensedOpen_restrictedCounit_isIso` is not proved here.
Every newly added private helper has a complete proof and introduces no hole.

`#print axioms` for `CategoryTheory.unitNormalizedLift_comp`,
`CategoryTheory.conjugateComposition_app`, and
`CategoryTheory.normalizedIdentityLift` reports only `propext`,
`Classical.choice`, and `Quot.sound`. The completed `fieldRefinement_comp`
also reports `sorryAx`, inherited from the existing geometric dependency above;
this delivery does not claim that dependency is closed.

## No longer needed

None. No public declaration, existing module, or declared mathematical dependency is pruned.
The generic private identity and shift helpers are relocated to a proof module;
they remain proved and used, and are not a pruning.
The former direct proof imports listed below move with their proofs. `Core`
means `Sheaf.Paper.CondensedCompactSupportProjectionCore`, and `IdentityCalculus`
means `Sheaf.CategoryTheory.CompactSupportIdentityCalculus`. All remain required
in the import closure.

| Former direct proof import | Current proof module |
|---|---|
| `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` | Core |
| `Sheaf.AlgebraicGeometry.OpenCoefficientSquareActionIdentification` | Core |
| `Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift` | IdentityCalculus |
| `Sheaf.CategoryTheory.DerivedExactSquareComposition` | Core |
| `Sheaf.Paper.CondensedOpenRestrictedCounit` | Core |
| `Sheaf.Paper.ConstructibleCokernelsExtensions` | Core |
| `Sheaf.Paper.ProperIntegralRationalScalarComparison` | Core, IdentityCalculus |
| `WeilConjectures.CategoryTheory.Adjunction.ConjugatePaste` | IdentityCalculus |
| `WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionIdIso` | IdentityCalculus |
| `WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor` | Core, IdentityCalculus |
| `WeilConjectures.CategoryTheory.DerivedExactCompositionComparison` | Core, IdentityCalculus |
| `WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed` | Core |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars` | Core, IdentityCalculus |

The existing scalar flatness, shift, coefficient identity and composition,
refinement identity, and naturality arguments retain their original dependencies.
The original construction dependencies are now attached to the core node; the item
uses that core node. This relocates the existing dependency route and prunes no
mathematics. The unit route is unchanged.

The library search found
`CondensedRing.boundedConstructibleLowerShriekRefinementIso'_trans`, but it needs
finiteness coefficients, finite-type schemes over a field, and Cartesian open
squares. It does not state this arbitrary-condensed-ring, arbitrary-refinement
normalization. The already proved
`CondensedRing.leftDerivedUpperStarComp_assoc_app` supplies the shorter formal
route used here; no geometric base-change theorem is needed beyond the existing
unique-existence theorem.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy was found. The composition clause is formal once the
original normalized lift exists uniquely and derived pullback composition is
associative. Both prerequisites already have declarations, so this delivery
requires no new split-off statement. The argument is valid for empty opens,
identity refinements, zero inputs, and arbitrary coefficient rings allowed by
the original theorem: it only uses category laws, adjunction identities,
naturality, and the existing uniqueness property.

## New nodes

`lem-pur-unit-normalized-lift-composition` attaches the fully proved generic
`CategoryTheory.unitNormalizedLift_comp` in
`Sheaf.CategoryTheory.UnitNormalizedLiftComposition`. It isolates the
restricted-counit composition, the two unit normalizations, and uniqueness;
no geometric assumption is added. The identity, zero-object and empty-category
cases use the same formal calculation.

`lem-pur-conjugate-composition-components` attaches the fully proved generic
`CategoryTheory.conjugateComposition_app` in
`Sheaf.CategoryTheory.ConjugateCompositionComponents`. It evaluates the
conjugate of a commuting square, with the four specified mate presentations.
It supplies the compositor equation, rather than assuming refinement composition.

The proof-context change is recorded in
`coord/changes/J3-condensed-refinement-composition-proof-context.md`.

`lem-pur-compact-support-identity-calculus` attaches the existing, fully proved
identity-normalization argument as `CategoryTheory.normalizedIdentityLift` in
`Sheaf.CategoryTheory.CompactSupportIdentityCalculus`. The module also holds the
unchanged private shift, scalar-identity, coefficient-composition and normalized-lift
naturality calculations extracted from this item.
No new hypothesis or selected object is introduced by this extraction.

`def-pur-condensed-compact-support-projection-core` attaches the original concrete
constructions and their already proved scalar, naturality, and refinement-identity
laws to `Sheaf.Paper.CondensedCompactSupportProjectionCore`. Its primary declaration
is the unchanged `WeilConjectures.CompactSupportCondensedRealization.condensedProjection`;
its other 58 declarations are listed in the node. The original node retains the
two theorem attachments in the item. This is a source-file split with zero holes,
not a new mathematical assumption or a restatement of the remaining hole.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
