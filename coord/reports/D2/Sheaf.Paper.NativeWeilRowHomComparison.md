## What changed

Proved the representative transport in Sheaf.Paper.NativeWeilRowHomComparison.
All construction is explicit and private: rowDegreeIso constructs inverse product
maps; rowIso checks the differential; rowIso_naturality checks both variables;
rowRepresentatives transports the supplied representative isomorphisms; sliceModel
identifies the ordinary source slice with the recorded bifunctorRHom by the
K-injective homotopy-category equivalence. rowCompatibility conjugates the supplied
chain comparison and proves its projection formula and localized square.
rowClosedModel assembles these data with the original m.hom, m.underlyingHom and
m.native. Both public conclusions use m.derived itself.

Removed the false native_row_hom_eta_eq and the parent proof's dependency on it.
No target statement, shared definition, upstream declaration or public import
changes. The two retained public theorem statements are unchanged.
The change record is coord/changes/D2-row-hom-remove-unfixed-comparison-equality.md.

The item compiled cleanly throughout proof development (approximately 16 seconds
without the axiom queries). The final validation also compiled the unchanged direct
importer Sheaf.Paper.NativeWeilClosedForgetful against this implementation. Its
unchanged temporary source copy was then removed from the delivery sandbox.
Compiler axiom queries show that both native_row_hom_data and
native_row_hom_comparison depend only on propext, Classical.choice and Quot.sound;
neither depends on sorryAx. The temporary queries were removed before delivery.

## Proved and sorry left

Closed by proof: AlgebraicGeometry.ProEtaleWeilSheaf.native_row_hom_data
(lem-sf-weil-native-row-hom-data).

Also supplied a complete new proof of the unchanged
AlgebraicGeometry.ProEtaleWeilSheaf.native_row_hom_comparison
(lem-sf-weil-native-row-hom-comparison), with all three HEq equalities reflexive.
Its old proof depended on the false normalization lemma; the new proof does not.

Removed, not proved: AlgebraicGeometry.ProEtaleWeilSheaf.native_row_hom_eta_eq
(lem-sf-weil-native-row-hom-eta-eq), because its universal claim is false.
Its node is preserved and its Lean attachment is explicitly null.

Initial holes: 2. Closed by proof: 1. Removed false holes: 1. Added holes: 0.
Sorries remaining in the delivered Lean module: 0. New split-off statements: 0.

## No longer needed

The false lem-sf-weil-native-row-hom-eta-eq and its Lean declaration are withdrawn.
The only DAG parent and the only Lean consumer were the main comparison in this
same item; both routes are replaced in this delivery. A search including the
quarantined sources found no other consumer. Neither it nor the transport data
lemma realizes a unit statement or proof step (the unit's realized lists are empty).
The main comparison now uses the concrete construction directly, so it also no
longer depends on the standalone, now proved lem-sf-weil-native-row-hom-data.

No import or whole module is removed. Both existing public imports are needed
for the retained statements. The proof does not need m.sign, m.sign_projection,
m.sign_naturality or m.native_normalization: the supplied StandardModel fields
suffice to prove sign transport generically. Those source-library interfaces
remain untouched; no adopted-source declaration is pruned.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the earlier split asserted that compatibility with arbitrary
NativeHomRepresentatives pins down the derived comparison. Given compatible
models and a comparison eta, negate every native representative isomorphism and
negate eta (hom and inverse). Representative naturality still holds. Both sides
of the compatibility square are negated, with the same projection-normalized
chain comparison. All other fields and both derived bifunctors stay identical.
The resulting eta differs on the nonzero coefficient-unit internal Hom at a
geometric point: coefficients have characteristic zero, so -1 differs from 1.
Thus the old native_row_hom_eta_eq cannot be proved. The new construction chooses
m.derived explicitly rather than asserting uniqueness for arbitrary choices.

The old DAG's one-line transport step concealed the ordinary sign map, its
chain/naturality proof, and the ordinary slice identification. These are now
proved in Lean, not split into additional existence assumptions. The current
blueprint's internal-Hom/evaluation paragraph and the unit route are preserved.
The proof works for all integer indices, including negative ones; sign inverses
use units_mul_self rather than any nonzero characteristic assumption. Products
and K-injective comparisons also cover zero complexes and the empty scheme.

The existing Mathlib leaf lem-weil-pbc-kinjective-hom-derived records the
K-injective full-faithfulness used in the slice identification. It is cited in
the updated proof dependencies; no new maintainer tool approval is written.
The equivalence and all chain-map representatives are existing proved library
constructions. No mathematical obligation is postponed by this delivery.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
