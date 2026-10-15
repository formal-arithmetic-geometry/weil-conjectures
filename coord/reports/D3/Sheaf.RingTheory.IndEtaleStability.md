## What changed

Proved `RingHom.indEtale_principalZariski_stability` in
`lean/Sheaf/RingTheory/IndEtaleStability.lean`, with its exact signature and all original
public imports unchanged. The proof reuses fully proved source-library results for ind-etale
base change, composition, cancellation and weak etaleness, and for weakly etale composition.

Private, fully proved helpers construct tensor products of principal-localization blocks,
prove these blocks compose and spread over filtered colimits, and apply the existing
`MorphismProperty.IsStableUnderComposition.ind_of_le_isFinitelyPresentable` theorem.
A direct pushout universal-property argument handles filtered colimits in the arrow category
with varying source rings. The proof explicitly supports empty finite products, zero rings
and zero denominators. No other module or public definition changes.

The only added proof import is `Mathlib.RingTheory.Localization.Pi`.
Updated the theorem's proof documentation and its DAG node's `proof`, `proof_deps` and
`proof_origin` to record the actual route. The unit realization is unchanged.

## Proved and sorry left

Closed: `RingHom.indEtale_principalZariski_stability`
(node `lem-weil-pbc-ind-etale-stability`), the module's only original hole.
All ten conjuncts are proved. Added holes: none. Remaining holes in delivered modules: none.
Every new private helper is fully proved, and all data definitions are concrete constructions.

The single-file compiler passes without warnings. `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`; in particular the theorem has no dependency
on an unproved declaration. The public theorem signature is textually unchanged.

## No longer needed

Removed proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Mathlib.CategoryTheory.Limits.HasLimits`
- `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`
- `Sheaf.AlgebraicGeometry.EtaleAlgebraFilteredColimitDescent`
- `Mathlib.RingTheory.Etale.Pi`
- `Mathlib.CategoryTheory.Limits.MorphismProperty`
- `Sheaf.RingTheory.EtaleSectionIdempotentSplitting`
- `Sheaf.RingTheory.FilteredColimitOfFactorization`
- `Sheaf.Algebra.Category.ModuleCat.FilteredColimitFlat`
- `Mathlib.Algebra.Category.Ring.FinitePresentation`
- `Mathlib.RingTheory.Flat.Stability`
- `Mathlib.RingTheory.RingHom.Flat`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Mathlib.RingTheory.Flat.Localization`

The following original planned proof nodes are unnecessary for this item's proof:

- `def-weil-etale-morphism`
- `lem-weil-pbc-etale-algebra-filtered-colimit-descent`
- `lem-weil-pbc-etale-base-change-finite-limits`
- `lem-weil-pbc-etale-composition-cancellation`
- `lem-weil-pbc-etale-section-idempotent-splitting`
- `lem-weil-pbc-factorization-criterion-filtered-colimit`
- `lem-weil-pbc-filtered-colimit-flat-modules`
- `lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit`
- `lem-weil-pbc-flat-module-base-change`
- `lem-weil-pbc-flat-ring-map-comp`
- `lem-weil-pbc-flat-ring-map-iff-flat-affine`
- `lem-weil-pbc-localization-flat`

In particular, this item no longer imports the four Sheaf modules
`Sheaf.AlgebraicGeometry.EtaleAlgebraFilteredColimitDescent`,
`Sheaf.RingTheory.EtaleSectionIdempotentSplitting`,
`Sheaf.RingTheory.FilteredColimitOfFactorization`, and
`Sheaf.Algebra.Category.ModuleCat.FilteredColimitFlat`.
The maintainer can prune their obligations wherever no other target dependency reaches them.
The retained proof nodes are the ind-etale/principal definition, categorical colimits,
elementwise filtered colimits, and etale finite products.

## Where the brief, the DAG or earlier work was wrong

The original plan duplicated substantial theory already proved in the source library.
In particular, ind-etale stability, relative cancellation and weak etaleness require no new
scheme descent or diagonal-idempotent proof here. For principal ind-Zariski composition,
the generic source-library ind-property composition theorem applies once finite blocks are
shown to compose, to be finitely presented and to spread. The arrow-category colimit clauses
are proved directly with pushouts, so the planned Sheaf factorization criterion is unnecessary.
No statement or definition was found false or changed. No new nodes, split-offs, forced
adaptations, withdrawn files, or change records are needed.

## Second reading by D3

1. **Statement and signatures.** Compared the delivered module with the repository version. The
public theorem signature and all existing declaration interfaces are unchanged byte for byte;
only proof documentation, proof code, and proof-only imports changed. The node statement remains
unchanged.

2. **Proof and axioms.** Compiled the delivered module with `lcompile.py` without errors or
warnings. Audited the theorem and every private helper in the module with `#print axioms`; the
only axioms are `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`s, axioms,
unsafe declarations, opaque declarations, or hollow definitions.

3. **Split statements and dependencies.** No statements were split off and no new nodes were
created. The proof uses concrete finite-product localization constructions, the source-library
ind-property theorem, and explicit filtered pushout colimits. The removed imports and obsolete
planned nodes are listed above; no retained dependency is a restatement of the target.

4. **Pruning and route.** Checked the proof from the target downward. Existing ind-etale and
weakly-etale APIs close those clauses directly; principal ind-Zariski clauses use the explicit
block construction and generic ind-property composition theorem. All unused proof-only imports
are recorded under `No longer needed`, and the unit and node route are retained.

5. **Edge cases and DAG agreement.** Checked empty finite products, zero rings, zero denominators,
and varying-source filtered diagrams in the construction. The node proof, dependencies, origin,
and Lean declaration agree with the delivered proof; no definition or target statement changed.

Changed during this second reading: appended this audit section only. No mathematical repair was
needed.
