## What changed

Filled the four remaining proofs in
`Sheaf.AlgebraicGeometry.EtaleNormalizedMatesCompositionPasting`, preserving all existing
statements, definitions and public imports; all previously completed clauses remain proved.

The base-change pasting and composition-restriction proofs first transport global support
coherence to the specified compactifications and then take actual mates. Private categorical
helpers prove the requisite identities by adjunction hom-bijections and counit naturality.
The support coherence helper and composition-restriction proof locally treat the specified
exchange and compositor maps as irreducible to prevent elaboration from expanding their
large constructions. The attribute scopes end with those proof sections. Profiling also
identified repeated general compactifiability searches; the support helpers now use local
instances obtained directly from their supplied compactifications. Replaced the existing
`simp?` call in pullback pasting with its suggested explicit simplification.
The proved exact-derived sum mate theorem, exact identity calculation and categorical
conjugacy/pasting helpers were placed in
`Sheaf.AlgebraicGeometry.EtaleExactSumBaseChangeMate` after profiling and local transparency
improvements, to keep the item within the 60-second file limit. This adds
no holes. The already proved inverse-image square-pasting calculation was similarly
extracted as `Sheaf.AlgebraicGeometry.EtaleExactPullbackSquarePasting`, with its unused
finiteness, Noetherian and etaleness hypotheses omitted from the new theorem only. The
original clause and all its binders remain verbatim. Open restriction uses the existing arbitrary-square compactification/sum base-change diagram,
the identification of the constructed graph comparison with that comparison, and exact-derived
descent of the ordinary sum mate calculation. Its final step applies mate refinement.

Composition is reduced to the left-adjoint geometric compatibility in the new module
`Sheaf.AlgebraicGeometry.EtaleSupportSumCompositor`; the combining proof uses horizontal
cancellation, conjugacy and the existing sum-composition counit theorem. Added private proof
imports of this module and the graph geometric base-change module, and used `import all` to
reuse proved private comparison, transport and mate-refinement helpers. The mate-refinement
calculation is reused directly from `EtaleSupportExchangeRightMate`. Updated the item's
proof plan and proof dependencies to match these calculations.

Validation: `lcompile.py --all` accepted all four delivered Lean modules. Static checks
confirm all 14 original declaration signatures and public imports are unchanged, the DAG
proof dependencies match the cited steps, and the only remaining hole is the named new
geometric lemma.

## Proved and sorry left

Closed all four original holes:

- `AlgebraicGeometry.Etale.etaleNormalizedMates_composition` (decomposed through the new lemma).
- `AlgebraicGeometry.Etale.etaleNormalizedMates_baseChange_pasting`.
- `AlgebraicGeometry.Etale.etaleNormalizedMates_composition_restriction`.
- `AlgebraicGeometry.Etale.etaleNormalizedMates_openRestriction`.

Also proved `AlgebraicGeometry.Etale.etaleExactSumBaseChangeMate` and
`AlgebraicGeometry.Etale.etaleExactPullbackSquarePasting` in their new modules.
No sorry remains in the item. Added one hole:
`AlgebraicGeometry.Etale.etaleSupportSumCompositor`, node
`lem-pur-etale-support-sum-compositor`. It is the geometric Step 1 before taking any
right-adjoint conjugates, with no right-adjoint choices in its statement. Thus the delivery
closes four original holes and splits off one strictly simpler statement; the composition
clause is a decomposition. Existing dependencies may still contain their own sorries.

## No longer needed

Removed the item's direct proof imports of
`Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition` and
`WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation`: their consumers moved to
`EtaleExactSumBaseChangeMate`, which imports them. Also removed the direct imports
`Sheaf.CategoryTheory.ExactDerivedTransformationPasting` and
`WeilConjectures.SixFunctors.BaseChange.Pasting`; the extracted calculations import them. These modules remain in the import
closure. No original DAG dependency, module or unit step was pruned. Generic mate laws
supply the categorical calculation but still require geometric support compatibility.

## Where the brief, the DAG or earlier work was wrong

The ordinary sum base-change mate theorem is available, but its existing derived version
uses `derivedEtaleLowerShriekMapAdjunction`, constructed by
`mapDerivedCategoryAdjunction`. The item's specified sum adjunction is constructed by
localizing complexes (`onDerivedCategory`); these are not definitionally the same
adjunction. The proof descends the ordinary counit equation directly with the existing
exact-derived finite-pasting theorem, retaining the adjunctions in the statement.

Step 1's geometric identification of the actual support compositor with nested sum
composition is not exposed as a directly applicable equation in the existing declarations.
The new node isolates precisely that step. No statement is disputed or weakened.

## New nodes

`lem-pur-etale-support-sum-compositor` in
`dag/nodes/sec-smooth-purity/lem-pur-etale-support-sum-compositor.json`, realized by
`Sheaf.AlgebraicGeometry.EtaleSupportSumCompositor`, states that the specified proper/open
compositor followed by the constructed graph comparison equals the horizontal graph
comparisons followed by the exact nested-sum compositor. Its docstring and node give the
support-family normalization, summand calculation, exact descent and compactification
transport argument. Identity arrows, empty sources and zero coefficients require no
additional hypotheses. No change records or adaptations of other existing modules.

`lem-pur-etale-exact-sum-base-change-mate` in
`dag/nodes/sec-smooth-purity/lem-pur-etale-exact-sum-base-change-mate.json`, realized by
`Sheaf.AlgebraicGeometry.EtaleExactSumBaseChangeMate`, is fully proved. It supplies the
exact sum base-change mate equation for the specified adjunctions localized from complexes.
Its private categorical helpers also supply the item's successive base-change pasting,
conjugacy and refinement calculations. Its private exact identity calculation supplies the
existing identity clause; these relocations add no statements with holes.

`lem-pur-etale-exact-pullback-square-pasting` in
`dag/nodes/sec-smooth-purity/lem-pur-etale-exact-pullback-square-pasting.json`, realized by
`Sheaf.AlgebraicGeometry.EtaleExactPullbackSquarePasting`, is fully proved by the existing
finite exact-derived pasting argument. The original pullback-pasting clause applies it.
The extracted theorem requires no finite, Noetherian, separatedness or etaleness hypotheses.
This reorganization adds no holes and changes no existing signature.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
