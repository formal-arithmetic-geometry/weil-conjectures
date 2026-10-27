## What changed

The signature and public imports of
`Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons` are unchanged. Its proof now
preserves K-flatness using the existing exact slice restriction theorem, preserves flat
terms by the local equational criterion, and descends a natural ordinary total-tensor
comparison through the product K-flat localization. The descended comparison satisfies
the required representative square by cancellation of the two tensor-model comparisons
and the restriction localization isomorphism. The proof assembles this tensor comparison
with normalized Hom and source/slice Koszul comparisons.

`Sheaf.Algebra.Homology.RingedTensorKoszulExistence` proves, for arbitrary specified
`CoefficientTensorModels`, the existence and pure-section normalization of Koszul
exchange. It uses the already proved native tensor comparison, native symmetry square,
and total-complex generator formula. Fully faithful whiskering through the K-flat
localization transports native symmetry to the caller's tensor model. This construction
is applied separately on the original site and on its slice, with independent derived
category universes.

Two new modules isolate the remaining ordinary total-tensor restriction and normalized
derived Hom constructions. They contain no data definitions or additional hypotheses.
All additions stay under `Sheaf`; no existing module besides the item is changed. Local
irreducibility attributes keep categorical structures from being unfolded in these
proofs; the attributes do not change any importer's elaboration environment.

Validation: `lcompile.py --all` compiled all four modules without errors or warnings.
The final Koszul existence and assembly compiles took 40.6 s and 34.4 s respectively;
every file is below the 60 s limit. All temporary profiling options and timing code
have been removed.

## Proved and sorry left

The existing hole in `CategoryTheory.ringedSlice_normalizedComparisons` is replaced by a
complete assembly proof. This is a decomposition, not a complete proof free of the new
obligations: one original hole is closed and two smaller holes are added, net minus one.

`CategoryTheory.ringedTensor_koszul_exists` is proved with no new holes, and proves both
Koszul clauses of the original item. The preservation of K-flatness and flat terms, the
derived tensor descent, its naturality, and the tensor localization square are also
proved in the item.

Exactly two holes remain in this delivery:

- `CategoryTheory.ringedSlice_totalTensorComparison_exists`, node
  `lem-weil-pbc-ringed-slice-total-tensor-comparison`: the ordinary chain comparison,
  natural in both complexes and normalized on actual pure tensor generators. This has
  no derived categories, closed tensor structures, K-flatness, Hom, or symmetry clauses.
- `CategoryTheory.ringedSlice_homComparison_exists`, node
  `lem-weil-pbc-ringed-slice-hom-comparison-existence`: the derived internal-Hom comparison
  and its local-family and fixed augmentation normalization. This has no tensor models,
  tensor restriction, flatness, or Koszul clauses.

Both are public named theorems, each in its own new module, with proof exactly
`:= by sorry`, source citations, and complete natural-language proofs. Zero and
unbounded complexes and empty covers introduce no missing hypotheses.

## No longer needed

No original Lean import is removed, and no module is withdrawn. The original item
imported only its statement models. The new proof imports only the three new modules,
the existing K-flat restriction and flatness criterion modules, the proved K-flat
localization helper, and Mathlib's product localization API.

The item's former direct proof dependencies replaced by the new route are:

- `def-pc-tensor-complex-sheaves`
- `def-pur-derived-internal-hom`
- `def-pur-hom-complex`
- `def-pur-localized-ringed-site`
- `def-weil-presheaf-modules-sheafification`
- `lem-cbc-sieve-slice-sheafification`
- `lem-pc-kflat-resolution`
- `lem-pur-kinjective-restrict-localized`
- `lem-sfb-localized-site-tensor-restriction`
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-site-derived-tensor-descent`
- `prop-pur-kinjective-resolutions-exist`

The general topoi pullback theorem and the earlier general descent statement are
unnecessary for this proof: exact restriction, the ordinary total comparison and the
proved K-flat localization suffice. Several remaining entries are still needed in the
proof plans of the two smaller obligations or in already proved native infrastructure;
this delivery does not claim they can be removed from the library. In particular it
removes no adopted source declaration. The unit route is preserved: the same tensor,
Hom and signed-exchange constructions prove the same normalized comparison statement.

## Where the brief, the DAG or earlier work was wrong

The plan describes the correct mathematical constructions, but does not supply their
fully normalized existence assertions as directly applicable declarations with the
item's independent site, coefficient and derived-category universes. The existing
ordinary/derived Hom restriction comparison APIs use a single small universe and a
common derived-category universe; they cannot directly discharge the present
augmentation and local-component square. Also, the current Lean attachment of
`lem-weil-pbc-ringed-internal-hom-exact-restriction` names a shift API rather than this
normalized existence statement. No statement is disputed or weakened here.

The existing proved K-flat restriction theorem is stronger than the plan needs: it
preserves all K-flat complexes, without a flat-term hypothesis. Flat terms restrict by
transporting the local relation witnesses through `Sieve.overEquiv`; no new K-flat
resolution or general pullback construction is required in the assembly.

The K-flat restriction theorem and the local flatness criterion are used as generic
tools from other units. The former supplies preservation for the identical slice
functor; the latter supplies the local relation characterization for the identical
module category. Neither replaces a step of the biduality unit. The normalized Hom
node similarly uses the independent-universe K-injective restriction theorem as a
generic resolution tool. No shared definition or interface is changed.

## New nodes

`lem-weil-pbc-ringed-tensor-koszul-existence` records the proved transport of native
Koszul exchange to any specified K-flat tensor model. Its proof uses the existing
native symmetry square, generator formula and proved K-flat localization helper.

`lem-weil-pbc-ringed-slice-total-tensor-comparison` records the ordinary total-tensor
restriction construction, the tensor/totalization part of the parent's second proof
step. Its proof plan restricts the normalized module tensor isomorphism on each
summand, commutes slice restriction with sheafified coproducts, and checks the two
signed differential terms and naturality.

`lem-weil-pbc-ringed-slice-hom-comparison-existence` records the Hom part of the parent's
second proof step. Its proof plan identifies relocalized local Hom families, uses
K-injective restriction, descends the natural comparison, and obtains both fixed
augmentation comparisons by inverting the fixed augmentation Hom maps.

The parent node's proof, proof dependencies and proof origin follow the Lean assembly.
No change record is needed: no existing signature, definition or public import changes.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
