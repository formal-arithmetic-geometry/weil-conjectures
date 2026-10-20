## What changed

Proved `SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization`
in `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`, preserving its statement
and every existing public declaration. The ordinary and derived composition comparisons
are the left-adjoint mates of the canonical restriction comparisons. The ordinary unit
formula and linearity give both tensor formulas. The global derived Hom comparison gives
compatibility with the prescribed counits on all homotopy-category inputs; cancellation
then gives intermediate computation on flat-term K-flat inputs. Computation for the
presented counit follows by uniqueness from the existing derived change-of-rings pair. Exact-functor coherence
and mate coherence give associativity, with explicit transports of ring-map equalities.
A separate, proved private calculation derives coefficient-square pasting from associativity.

Added private proof imports of Mathlib's adjunction composition API, the ordinary
coefficient adjunction, the derived coefficient Hom comparison, and the existing exact
functor coherence API. All auxiliary lemmas are private and proved. Restriction exactness instances are local.
The proof-scope change is recorded in
`coord/changes/Y6-successive-derived-quotient-normalization-proof-scope.md`. The generic exact
coherence calculations follow the already proved private calculations in
`Sheaf.CategoryTheory.FlatScalarTowerCoherence`; they require exactness only of restriction,
so the coefficient maps need not be flat. Updated the node's proof and direct dependencies.

Kept sheafified tensor definitions locally irreducible after their defining declarations,
and proved their scalar-action API explicitly. The restriction comparison also has an
explicit section-action lemma and remains locally irreducible in the final assembly. This controls unnecessary unfolding during
proof elaboration without changing any public definition or reducibility attribute.

Validation uses single-file `lcompile.py` compilation and the delivery tool's axiom
audit and preflight. The proof has no remaining holes.

## Proved and sorry left

Closed the one original hole in
`SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization`
(node `lem-sfb-successive-derived-quotient-normalization`). No holes added, no split-off
statements, and no `sorry` remains in the delivered module. The proof uses the existing
named ordinary coefficient adjunction, derived change-of-rings, and global derived Hom comparison
declarations; this delivery does not claim to close their own remaining dependencies.

## No longer needed

Removed these direct proof imports:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.Paper.RingedTopoiTensorSections`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`

Removed the corresponding direct planned proof dependencies
`lem-pc-kflat-resolution`, `lem-weil-pbc-ringed-topos-kflat-pullback`,
`def-weil-pbc-ringed-tensor-section-calculus`, `lem-weil-pbc-site-derived-tensor-descent`,
`lem-weil-pbc-localization-universal-property`, and `def-pur-sheaf-tensor-product`.
The existing tensor construction still supplies the meaning of the statement; no new
section-calculus theorem is needed to prove the formulas from the normalized units.
K-flat resolutions and related theory may remain dependencies of the imported coefficient
results. No module is withdrawn or deleted, and no upstream declaration is removed.
The direct proof dependency `lem-pur-sheaf-ring-derived-coefficient-adjunction` is also
removed: the ordinary adjunction is obtained directly and K-flat computation is transported
by the universal property's uniqueness. Its existing public import is preserved.
The obsolete top-level tool approvals for K-flat resolution, K-flat pullback preservation,
explicit resolving-class descent, and the bundled derived coefficient adjunction are removed;
the approval for derived change of rings remains.

## Where the brief, the DAG or earlier work was wrong

The original argument is valid, but a shorter route uses the already declared global
Hom comparison and normalized adjunctions. It avoids constructing another localization
comparison or proving K-flat preservation again. Associativity of coefficient maps must
be transported explicitly through the arbitrary presentation family; treating differently
parenthesized maps as interchangeable during elaboration is insufficient. The unit's
route and the existing statement are unchanged. No statement dispute or definition repair
is required.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
