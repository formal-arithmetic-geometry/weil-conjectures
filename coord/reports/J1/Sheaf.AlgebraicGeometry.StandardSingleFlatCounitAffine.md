## What changed

Proved `AlgebraicGeometry.standardSingleFlatCounitOnOpen_affine` in the assigned
module, with its original signature and docstring unchanged. The model is the
explicit single complex of `(Scheme.Modules.pushforward (U.ι ≫ p)).obj N`.
Seven private proved helpers establish direct-image tensor flatness, affine
acyclicity by Cech dimension shifting, right-derived-unit invertibility, and
the pinned comparison for this fixed model.

The comparison uses `derivedBaseChange_unit_compatibility` and ordinary affine
base change, rather than constructing an alternating Cech model. All new imports are
proof-only. The existing DAG node now records this route. No other library
module or public interface changes, and no new definition or node is added.

## Proved and sorry left

Closed: `AlgebraicGeometry.standardSingleFlatCounitOnOpen_affine`
(node `lem-pc-standard-single-flat-counit-affine`), the item's only original hole.
Added holes: none. Sorries left in delivered Lean files: none.

This is a complete proof from existing library declarations, not a new
sorry decomposition. Dependencies may still rely on their own recorded holes.
All seven private helpers are proved without local holes: `affine_pushforward_isFlat`,
`injective_cech_acyclic`, `cokernel_cech_acyclic`, `affine_pushforward_epi`,
`affine_pushforward_rightAcyclic`, `affine_single_unit_iso`, and
`affine_single_counit_comparison`.

## No longer needed

No original import is removed: the public presentation import is needed by the
unchanged statement. Every added proof import is used.

The affine case no longer needs the planned dependencies
`lem-pc-affine-alternating-cech-model-flat`
(`Sheaf.AlgebraicGeometry.AffineAlternatingCechModelFlat`) or
`lem-pc-affine-open-pushforward-acyclic`
(`Sheaf.AlgebraicGeometry.AffineOpenPushforwardAcyclic`). They have been removed
from this node's proof dependencies and are not imported by this proof. This is
local pruning of the affine route; they may still be needed elsewhere.

Removed the earlier attempt's unused affine-model module and node, and its
unchanged copy of StandardSingleFlatCounitPresentation from the delivery.
No new comparison module is needed: its argument is proved privately here.

## Where the brief, the DAG or earlier work was wrong

The previous arbitrary-complex comparison was false: flatness and boundedness
alone do not relate K to N. Its retained existential flat-model statement was
also insufficient, since the zero complex always meets that statement. The new
proof constructs K from the actual direct image and pins both comparison
isomorphisms to the recorded derived units and the ordinary exchange map.

The original DAG's affine-open acyclicity lemma asks for an ambient separated
morphism and a module restricted from that ambient source. Neither is supplied
by this item's arbitrary affine source chart. Affine pushforward acyclicity applies directly to U.toScheme instead and
needs no ambient separatedness. The existing affine single-unit module cannot
be imported because DirectImage.AffineMorphism reaches this item through
FiniteFreeComplex. We prove affine vanishing locally from the lower proved
Cech and dimension-shifting tools, as FiniteAffineCechModelComparison already
does, and apply the noncyclic canonical acyclic-single comparison. The generic pinned unit compatibility theorem supplies the mate
calculation without any new geometric comparison assumption.

Existing results from other units are used only as tools:
`lem-pc-canonical-single-direct-image-comparison` identifies the specified unit
for acyclic modules; `lem-weil-pbc-affine-pushforward-base-change-isIso` provides
ordinary affine exchange; `lem-pc-derived-base-change-unit-compatibility`
provides the formal mate equation. The coherence unit's statement and realized
steps are unchanged. No unit-level route is bypassed.

Edge cases: zero terms use IsZero, so empty schemes and the zero module need no
nonemptiness assumption. No g-flatness is used, and the pinned pullback counit
is never inverted. Cancellation is only of the explicitly constructed affine
source identification e.

## Second reading by J1

1. Compared the delivered module with the repository version. The public theorem
   signature and docstring are byte-for-byte unchanged; only proof-only imports,
   private helpers, and the proof body were added.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or warnings.
   Searched the delivered source for `sorry`, `axiom`, `unsafe`, `opaque`,
   `extern`, and `implemented_by`; none occur. The proof uses only existing
   declarations and leaves no new holes.
3. Checked the proof route and its DAG node. The explicit single complex is
   constructed from the actual affine direct image, and the affine flatness,
   acyclicity, unit, exchange, and mate arguments are all used at the stated
   strengths. No split-off statement or new node is introduced.
4. Checked pruning and imports. The removed planned affine Cech-model and
   ambient-open-acyclicity dependencies are not used; all added imports are
   proof-only and used. The unit's realized route remains intact.
5. Checked edge cases and statement fidelity: zero terms and empty affines are
   handled by `IsZero`; no flatness of `g` or extra separatedness hypothesis is
   introduced; the pinned pullback counit is never inverted. The node proof and
   `proof_deps` now match the Lean proof.

Changed only the report by adding this review record; no Lean declarations or
statements were altered during second reading.
