## What changed

`Sheaf.Paper.PurityFiniteKummerLevel.finiteKummerLevel` now has a complete Lean proof
from two strictly smaller geometric statements. Its statement is unchanged token for token.
The arithmetic, finite coefficient basis, uniqueness, termwise derived comparison, root-limit
base-change map and normalized base-change square are proved in this delivery.

The eleven existing comparison definitions were moved verbatim to
`Sheaf.Paper.PurityFiniteKummerDefinitions` to let the geometric statements use them without
creating an import cycle. The item publicly reexports them and retains all its original
public imports. No adopted source-library file is changed. Change record:
`coord/changes/A9-finite-kummer-definition-location.md`.

The normalized base-change theorem is proved in
`Sheaf.Paper.PurityKummerNormalizedBaseChange`. It constructs the root-limit map by taking
the adjoint of a limit cone over the existing natural root tower map; it does not assume
inverse image preserves infinite limits. It defines the source comparison by conjugation
and proves its pure-tensor normalization using adjunction naturality and constant-ring
quotient naturality.

Validation: all five delivery modules compiled in import order through `lcompile.py`.
The final compile is rerun after metadata and docstring adjustments. All copied definitions
were compared byte for byte with the original block. The main theorem signature was compared
token for token. Compilation remained below the per-file limit; busy-server responses were
retried, not treated as compiler failures.

## Proved and sorry left

Original item holes: 1. Closed body: `WeilConjectures.PurityFiniteSetting.finiteKummerLevel`.
New geometric holes: 2. This is a decomposition with substantial proved arithmetic and
compatibility arguments, not an axiom-free proof of the original item. Net holes: -1 closed
minus added, equivalently one additional hole. There is no `sorry` in the item itself.

The two remaining `sorry` declarations, each in its own module with a source and full
natural-language proof, are:

- `WeilConjectures.PurityFiniteSetting.kummer_normalized_projection`
  (`lem-pur-kummer-normalized-projection`): only the canonical projection isomorphism,
  assuming the already-proved coefficient ideal equality. It does not repeat the arithmetic,
  finite-basis, uniqueness, derived or base-change conclusions.
- `WeilConjectures.PurityFiniteSetting.kummer_root_tensor_base_change`
  (`lem-pur-kummer-root-tensor-base-change`): only finite-root tensor pullback and its unit
  normalization in the constant-ring-sheaf presentation. It has no Tate-limit comparison,
  source-line comparison or commuting square.

The new public theorem
`WeilConjectures.PurityFiniteSetting.kummer_normalized_base_change` is proved from the
second geometric statement. Its root-limit map, source-line isomorphism and tensor square
contain no additional holes.

Proved private arithmetic helpers: `kummer_prime_power`, `kummer_positive`, `kummer_ideal`,
`kummer_log_prime`, `kummer_log_uniformizer`, `kummer_minimal`, `kummer_quotient`,
`finite_basis_quotient`, `kummer_basis_rank`, `kummer_finite_basis`. In particular the
rank ef computation uses the finite residue field characteristic and the prime-power ideal
quotient cardinality formula; it is not an assumed rank statement.

Proved private sheaf helpers: the scalar-extension adjunct is injective;
`kummer_comparison_unique` follows by applying it twice; `secondMap_comp` and `secondMap_id`
prove tensor functoriality; `kummer_derived` proves a degreewise isomorphism and therefore the
stated quasi-isomorphism. The base-change module also proves `root_limit_base_change` and
constant-ring map naturality. Private helper definitions contain real constructions only.
No new axioms or definition holes are introduced.

## No longer needed

The following direct imports were removed from the item. Some remain available transitively
or are used by geometric dependency nodes; no claim is made that they disappear from every
target's whole import closure:

- `Sheaf.Paper.PurTwistSheafLocallyFree`
- `Mathlib.CategoryTheory.Limits.HasLimits`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Paper.ConstantTwoTermResolution`
- `WeilConjectures.Algebra.Homology.BoundedFlatReplacement`
- `Sheaf.Paper.KFlatConeComparison`
- `Mathlib.AlgebraicGeometry.Scheme`
- `WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Mathlib.AlgebraicGeometry.Gluing`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Mathlib.CategoryTheory.Yoneda`
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`

The following former direct proof-dependency edges were removed from the item node. Root
representability and local-model prerequisites remain under the two geometric nodes as needed;
they were not deleted or withdrawn. The original unit route remains at this item.

- `lem-pur-twist-sheaf-locally-free`
- `def-coefficient-twists-detailed`
- `def-pur-sheaf-inverse-limit`
- `def-pc-flat-sheaf-modules`
- `lem-pc-bounded-above-flat-kflat-site`
- `def-weil-derived-tensor`
- `lem-pur-constant-two-term-resolution`
- `lem-pc-kflat-bounded-flat-replacement`
- `lem-pur-kflat-cone-comparison`
- `def-weil-affine-spectrum`
- `def-pur-roots-of-unity-sheaf`
- `lem-sbc-root-split-away-cover-etale`
- `def-weil-pbc-site-comparison-morphism`
- `lem-weil-pbc-proetale-subcanonical`
- `def-pc-fibre-product`
- `lem-weil-pbc-scheme-morphism-gluing`
- `def-weil-etale-morphism`
- `def-weil-proetale-inverse-image`
- `lem-galois-yoneda-hom-bijection`
- `lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection`
- `def-pur-roots-of-unity-inverse-image`
- `lem-pur-tate-inverse-limit-base-change`
- `lem-pe-constant-left-module-inverse-image`
- `prop-weil-pbc-proetale-constant-exact`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`

The constant two-term resolution, bounded-flat replacement, K-flat cone comparison and
derived-pullback arguments are unnecessary for the exact recorded
`KummerDerivedCompatible` predicate: tensor with an isomorphism is already a degreewise
isomorphism. The finite integral basis is taken directly from `PurTwistIntegralBasis`, so
this arithmetic calculation does not need the larger Tate-local-freeness conjunction.

The unit-route imports `ProEtaleSiteComparison` and
`IntrinsicCoefficientTwistsUnrestricted` are retained. The direct DVR proof import is
retained because its theorem is used in the arithmetic proof.
All original public reexports are retained to preserve consumers. No Lean module is
withdrawn, and no adopted source declaration is removed. Thus this packet claims proof-route
pruning, not a verified count of globally unreachable modules.

## Where the brief, the DAG or earlier work was wrong

The first delivery attempt was refused because the new nodes omitted the required
LeanSearch kind from their records (LeanFinder and Loogle count as one kind). The
actual LeanSearch logs already existed; those records are now included. The preflight
also identified two unit-route imports, which are retained. Nothing was pushed by that
attempt. No statement was found false and no target was changed. The DAG's derived-resolution route
proves more than the current termwise quasi-isomorphism predicate requires. The simpler
isomorphism argument suffices for this exact Lean statement; it does not claim to prove the
stronger flatness and resolution assertions separately.

`PurTwistRootLocalModels` supplies unspecified reduction isomorphisms, not the required
normalization by the root projection. It cannot simply be applied as that canonical
comparison. The projection lemma retains the genuine kernel and normalized-isomorphism
argument. `RootsOfUnityInverseImageIso` supplies a natural tower map for arbitrary morphisms,
but asserts invertibility of its finite-root adjunct only for scheme isomorphisms; it is
therefore insufficient for arbitrary base change by itself.

`FiniteRootSiteComparison` supplies a suitable normalized finite-root base-change result
in fixed-coefficient module sheaves. The retained finite-root tensor lemma is the transport
to our constant-ring sheaf-of-modules presentation, including arbitrary local scalar
sections and the canonical module unit. The corresponding constant-ring module equivalence
and pullback-encoding declarations were read and are recorded as its dependencies. The
transport has not been completed in Lean; it is reported honestly as a hole.

Edge checks for the geometric statements: N=0 is the positive exponent ell; the kernel-shift
argument uses N+1 coordinates. For empty schemes all module sheaves involved are zero.
Identity base change gives the adjunction identity comparison. No nonempty-base hypothesis
is used. A coefficient map a is a unital homomorphism out of ZMod and is fixed by integer
casts, so no unproved arbitrary choice of scalar action is made. The normalized comparison
family chosen inside the theorem proof is uniquely determined by its displayed formula.

A broad DAG closure check encountered the existing unrelated cycle
`lem-pc-ring-hom-extension-differential` /
`lem-pc-ring-hom-extension-differential-adjacent`. Neither node is edited here. A separate
reachability check confirmed that no cycle passes through any node this packet changes
or introduces. This is reported for maintainer attention.

## New nodes

`def-pur-kummer-comparison-data` records the unchanged eleven definitions in their new
module. It has no hole. Its extraction is documented in
`coord/changes/A9-finite-kummer-definition-location.md`.

`lem-pur-kummer-normalized-projection` isolates blueprint proof steps 3--4. It assumes the
coefficient ideal equality proved in the item and retains only the canonical geometric
projection and scalar-associativity comparison. It has one hole.

`lem-pur-kummer-root-tensor-base-change` isolates the finite-root tensor part of steps 9--11,
using the existing finite-root site comparison and coefficient-presentation equivalences.
It has one hole, and does not duplicate the whole item's base-change predicate.

`lem-pur-kummer-normalized-base-change` is proved. It combines the finite-root tensor result
with the proved coordinate limit map, conjugation of isomorphisms and tensor normalization.

All new nodes retain the item's chapter and unit and point back to
`lem-pur-finite-kummer-level` as blueprint origin. Search records include LeanSearch, Loogle/LeanFinder and grep, copied from the actual
Mathlib search logs, with no claim of an exact Mathlib sheaf-comparison match.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
