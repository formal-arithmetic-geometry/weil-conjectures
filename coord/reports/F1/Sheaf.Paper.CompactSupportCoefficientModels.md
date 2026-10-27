## What changed

Proved nine of the twelve original theorem holes in
`Sheaf.Paper.CompactSupportCoefficientModels`. This is a partial proof delivery:
three existing named theorem holes remain unchanged, and no holes or public
statements are added. The sixteen existing public declaration signatures, all
three coefficient-data definitions, and all public imports are unchanged.
Two proved private helpers express projection/quotient compatibility.

The constant-category, tower, limit and chi clauses use the existing normalized
comparison declarations. The arithmetic clause uses the finite-module adic
completion API, Krull intersection for a proper ideal in a Noetherian local ring,
the already proved integral-basis helper, and the already proved quotient-basis
helper. `import all` exposes these private proof helpers only to this proof;
no private declaration enters a public signature or data-definition body.
Ramification identifies the mapped ideal with the power indexed by e*n.
The coordinate-equivalence proof covers n=0, including the zero quotient ring.
The projection square excludes e=0 using 1 <= a <= e*n before using the existing
ramified square, and also covers the equal-level quotient.

Scalar preservation uses intrinsic scalar-extension constructibility and
transport across the normalized completed scalar comparison. The legacy
completeness comparison supplies the input of the existing Tor-bound theorem;
its unrestricted small-universe interface is met by constructing a finite-field
datum at a prime different from l. No field object is chosen from an unproved
existence statement. The final theorem transports the property of the existing
constructible compact-support functor values across their specified normalized
realizations, preserving both uniqueness/specification clauses.

Updated only proof-route fields and removed obsolete tool approvals in
`lem-pur-compact-support-coefficient-models`. The definition node is unchanged.
The existing unit route and every public statement are preserved.

Validation: lcompile.py compiled the final module without warnings in 45.3 s.
A separate textual check verified all sixteen signatures, three data definitions,
and public imports unchanged; there are no newly introduced lines over 100
characters. The delivery preflight supplies the independent compilation/axiom
checks. No statement, definition or external consumer changed, so no change
record or forced consumer adaptation is needed.

## Proved and sorry left

Closed nine original holes, all in namespace `WeilConjectures` and node
`lem-pur-compact-support-coefficient-models`:

- `compactSupportCoefficientModels_constant`
- `compactSupportCoefficientModels_constantTower`
- `compactSupportCoefficientModels_constantLimit`
- `compactSupportCoefficientModels_chi`
- `compactSupportCoefficientModels_arithmetic`
- `compactSupportCoefficientQuotient_square`
- `compactSupportCoefficientModels_inverseImage`
- `compactSupportCoefficientModels_scalar`
- `compactSupportCoefficientModels`

Three original named theorem holes remain in that same node:

- `WeilConjectures.compactSupportCoefficientModels_ordinary`
- `WeilConjectures.compactSupportCoefficientModels_moduleBalancing`
- `WeilConjectures.compactSupportCoefficientModels_furtherTensor`

Their original signatures, complete proof docstrings and sorry bodies are
unchanged. No holes are added or split off: 12 original, 9 closed, 3 left.
These proofs use the existing library declarations, including declarations
which may themselves still depend on sorry; this is a stage-3 reduction from
the supplied interfaces, not a claim that the full target is axiom-free yet.

## No longer needed

Removed these direct private proof imports:

- `Mathlib.RingTheory.PrincipalIdealDomain`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis`
- `Sheaf.CategoryTheory.FiniteFreeScalarCoordinates`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `Sheaf.Paper.FiniteFreeConstructibleScalarTransport`
- `Sheaf.Paper.SfIntegralCompactSupportConstructible`

The first two are unnecessary because the needed instances come from existing
coefficient constructions. The integral-basis construction is reused through
CompletedIntegralFiniteFree; this does not withdraw its underlying local-field
basis dependency. The coordinate/monoidal modules remain in the mathematical
plan for the three unproved clauses, but no completed proof here needs a direct
import of them. The last five imports implement the longer geometric route
bypassed by intrinsic constructibility and the already recorded compact-support
realization. Their public/transitive uses elsewhere remain valid.

Removed these direct proof dependencies and their matching obsolete tool approvals:

- `lem-weil-l-adic-extension-complete`
- `lem-sfb-local-field-integral-basis`
- `lem-weil-pbc-pid-noetherian-normal`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-kun-dimension-finite-type`
- `lem-weil-pbc-integral-stratified-perfect-characterization`
- `lem-weil-pbc-finite-free-constructible-scalar-transport`
- `lem-sf-integral-compact-support-constructible`

The first three are replaced by existing completion/basis/datum interfaces;
their transitive arithmetic work is not claimed unnecessary. The final five
are bypassed in this module by the shorter intrinsic/realization argument.
No whole module is deleted or claimed globally unreachable. No adopted
WeilConjectures declaration, attribute, signature, or import is removed.

## Where the brief, the DAG or earlier work was wrong

The planned stratified-perfect/Noetherian/dimension detour is unnecessary for
the scalar theorem because intrinsic scalar-extension constructibility already
matches its constructible property. Likewise the final theorem already asks
for the normalized compact-support realization whose codomain is the
constructible subcategory; transporting that object property suffices.
The original arithmetic plan can be assembled from existing proved private
basis helpers rather than reconstructing sectionwise coordinates.

The unrestricted legacy completeness predicate uses a small finite-field datum,
whereas the theorem's given datum has universe u. A genuinely constructed small
datum at another prime bridges that interface; no statement was weakened.
The broad existing DAG data-node attachments already have cycles through
unrelated compact-support consumers. The proof cites the actual owner of
compactSupportProjection_comp and the finite scalar-data owner of the ramified
square rather than attributing those declarations to the full comparison
statement. No new theorem or axiom was introduced to hide this coarse-ownership
issue. The three remaining tensor clauses retain their original plans for
subsequent work.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
