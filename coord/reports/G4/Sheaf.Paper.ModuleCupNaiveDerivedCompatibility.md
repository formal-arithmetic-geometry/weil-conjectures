## What changed

Repaired reviewer X-c21c2 (head c21c2ee3b), C1/C4: the K-injective target
node used three substantial facts without corresponding statement dependencies.
Added three public theorem modules for the actual global ringed-space map
p = toGlobalSectionsPoint X, with source-based proof docstrings and node records:
ModuleCupGlobalTensorPullback (Tag 079U), ModuleCupGlobalCounitComparison
(Tag 0FP1), and ModuleCupGlobalTensorComparison (Tag 0FP0).
The counit square is proved from Mathlib Adjunction.derivedε_fac_app; the
tensor isomorphism and tensor polygon are named remaining obligations.
ModuleCupKInjectiveTarget imports all three with plain import. Its docstring,
proof steps, uses and proof_deps now cite all three nodes explicitly.
No scheme-morphism lemma is substituted for p and no condition on X is added.

The following describes the existing reduction retained by this repair.
The helper and the main theorem now use the same named canonical lax localization
instance, moduleCup_sourceLax. The compiler launcher queues jobs for shared slots;
its elapsed times include queue waiting. The no-push dry run is rerun after these changes; the independent reader
reviews the repaired set separately. Nothing is pushed by this worker.

Replaced the sorry in AlgebraicGeometry.Scheme.Modules.moduleCup_naive_derived_compatibility
by a reduction to the explicit naive section tensor map and its calculation against
K-injective targets. The original theorem signature is preserved. moduleCup_globalComparison now
uses the definitionally identical component of moduleCup_comparisonNatTrans;
see coord/changes/module-cup-global-comparison.md. The new comparisonNatTrans construction assembles the
same components into a natural transformation; its naturality is proved directly.

ModuleCupNaiveMap constructs each degree map by Mathlib mapBifunctorDesc from the
existing tensorSectionsMap. Its cochain-map proof refers to the named chain identity.
The naive-map module proves the pure-tensor formula from ι_mapBifunctorDesc.
ModuleCupKInjectiveTarget states the natural derived pairing calculation with a
K-injective codomain. The importing proof chooses a K-injective resolution of K tensor L,
applies that calculation, uses comparison naturality and functoriality, and cancels R(Qq).
No complex data is chosen from an unproved mere-existence theorem in a definition.

## Proved and sorry left

Closed the original hole by a compiler-validated reduction:
AlgebraicGeometry.Scheme.Modules.moduleCup_naive_derived_compatibility
(lem-sc-module-cup-naive-derived-compatibility).

The retained delivery added two holes, each in its own new module:
- AlgebraicGeometry.Scheme.Modules.moduleCup_naiveMap_comm
  (lem-sc-module-cup-naive-map-chain): the signed differential identity for the
  explicitly constructed degree maps.
- AlgebraicGeometry.Scheme.Modules.moduleCup_exists_kinjective_target_pairing
  (lem-sc-module-cup-kinjective-target): construction of the natural derived pairing
  and its adjunction calculation with a K-injective target.

This repair adds two further named holes:
- AlgebraicGeometry.Scheme.Modules.globalRingedSpace_derivedTensor_pullback_comparison
  (lem-sc-module-cup-global-tensor-pullback): the actual global tensor pullback
  and its canonical derived tensor isomorphism, natural in both variables,
  with the ordinary evaluation normalization and K-flat normalization explicit.
- AlgebraicGeometry.Scheme.Modules.globalRingedSpace_tensor_comparison_diagram
  (lem-sc-module-cup-global-tensor-comparison): the full Tag 0FP0 polygon
  for arbitrary complexes, from the canonical K-flat normalization.

AlgebraicGeometry.Scheme.Modules.globalRingedSpace_derivedCounit_comparison
(lem-sc-module-cup-global-counit-comparison) is proved, with no new sorry.
It states the actual Tag 0FP1 square using the adjunction induced from the
ordinary adjunction and the canonical derived comparison maps.

All four remaining holes are listed above. The original item still has none.
This is a decomposition: one upper hole replaced by four lower holes, direct-hole net minus
three before pruning; the pinned ledger, rather than this direct count, determines
progress in the targets' import closure. It is not a complete axiom-free proof of the cup construction.
There is no sorry in the item's module and no sorry in any definition. The naive
map has concrete coproduct data; only its named chain identity is postponed.
The K-injective obligation does not construct the naive map or prove its formula,
and only calculates with K-injective codomains; the passage to arbitrary codomains
is the Lean naturality-and-cancellation proof in the item.

## No longer needed

Removed Sheaf.Paper.ModuleCupResolutionData from this item's imports. The acyclic
resolution and nonnegative pairing structures in that module are unused for this
unbounded six-object diagram. Replaced its transitive statement imports by direct
public imports of Sheaf.Topology.RingedSpaceModuleCohomology and
WeilConjectures.AlgebraicGeometry.Modules.TensorSection. The current direct importer ModuleCupEqualDerivedMapsClass publicly imports
ModuleCupResolutionRealization, which independently supplies the resolution data.

The original proof-dependency nodes def-pc-tensor-complex-sheaves,
def-pur-sheaf-tensor-product, and def-sc-ringed-space-module-cohomology remain
needed transitively by the two new obligations. No unit realization is removed,
and no claim is made that an entire module has left the targets' import closure.

Second-reading pruning: `ModuleCupGlobalTensorComparison` removes its redundant
imports of GlobalDerivedHom, DerivedTensorStructure, HomotopyCategory.OplaxMonoidal,
GrothendieckAbelian.Monoidal.FlatResolution, Mathlib Derived.Adjunction, and
KFlatPullback; these remain available through its defining pullback module.
`ModuleCupGlobalCounitComparison` removes the GlobalTensorPullback import and
its GlobalDerivedHom, DerivedTensorStructure, HomotopyCategory.OplaxMonoidal,
FlatResolution, and KFlatPullback imports, replacing them by the direct
signature providers and the module-category derived instance. Its unused
tensor instances are removed. Its proof no longer uses the nodes
lem-sc-module-cup-global-tensor-pullback or def-pc-ringed-spaces-derived-direct-image;
only the generic Mathlib leaf lem-sc-derived-adjunction-from-underived is a
proof dependency. Statement dependencies are unchanged.
`ModuleCupKInjectiveTarget` makes RightDerivedFunctor.KInjective a plain import,
since the calculation lemma is used only by the planned proof and its statement
types are already supplied publicly. The three former direct proof dependencies
of the item's node remain needed transitively, as explained above; they are
removed only from the item's own proof_deps. None of this establishes whole-module
pruning from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The earlier main proof had a generic Functor.map_comp rewrite that selected
Q on the right side rather than R on the left. The repaired proof uses a fully proved generic private cancellation lemma
(cancel_comparison), then the naturality of the transported comparison unit.
Local sheaf tensor instances use X.toRingedSpace.sheaf. Naming the canonical
source localization tensor instance once in the helper and using it in both
modules avoids costly comparison of two independently synthesized instances
under restricted elaboration transparency. This is concrete existing instance
data, with no new mathematical obligation.
An additional attempt to prove the signed chain identity reached the two
naturality summands but did not resolve their instance-unfolding obligations;
the named lower obligation remains, with its explicit construction preserved.

The original DAG had one long proof step naming only tensor and cohomology
definitions; those declarations do not supply the adjunction polygon calculation.
The original two new nodes did not make all their own obligations explicit.
Reviewer X-c21c2 correctly identified missing tensor compatibility and diagrams.
The three repair nodes now supply the precise missing statements: a natural
derived pullback tensor isomorphism, an induced-counit square, and the full
tensor polygon, rather than just K-injective computation or Q-tensor naturality.
The tensor isomorphism records the concrete global pullback through point
evaluation and its tensor/evaluation normalization, so its formal statement
also identifies the comparison needed for the naive tensor-of-sections map. Stacks Tag 0FKU
is the section tag; the compatibility lemma itself is Tag 0FP3. LeanSearch was
attempted for both new statements but returned Internal Server Error; that search
is recorded as unavailable, with no mathematical verdict. LeanFinder, Loogle,
and searches of Mathlib and both local library roots found no exact closing lemma.

Edge cases checked from the construction: zero sections map to zero by linearity;
nonadjacent differential degrees give zero; all integer summands, including
negative degrees, use the total tensor sign. Empty schemes and zero complexes
require no separate hypothesis. For the derived calculation the codomain, rather
than either input, is K-injective. Resolving inputs alone would not justify
cancellation, since global sections need not preserve their quasi-isomorphisms.

## New nodes

lem-sc-module-cup-naive-map-chain, in ModuleCupNaiveMap, isolates the signed
Leibniz identity for concrete coproduct maps. Its source is the naive product
construction immediately before Stacks Lemma 20.31.3.

lem-sc-module-cup-kinjective-target, in ModuleCupKInjectiveTarget, isolates the
natural derived cup and its evaluation against a K-injective chain target.
Its source is Stacks Tags 0B68 and 0FP3. It is used with a resolution q of the
actual total tensor codomain, followed by proved cancellation.

lem-sc-module-cup-global-tensor-pullback, in ModuleCupGlobalTensorPullback,
records Tag 079U for p = toGlobalSectionsPoint X. It supplies actual ordinary
pullback object/morphism formulas through point evaluation, a strong monoidal
evaluation adjunction, absolute left derivation, and the canonical natural
isomorphism L(A tensorᴸ B) ≅ LA tensorᴸ LB with K-flat normalization.
The tensor-of-sections/evaluation normalization fixes the ordinary tensor
constraint used in the K-injective argument. The diagram predicate in this
module is a concrete equality of comparison maps, with no postponed data.

lem-sc-module-cup-global-counit-comparison, in ModuleCupGlobalCounitComparison,
records Tag 0FP1 for the same global pullback. The displayed equation uses the
counit of the derived adjunction induced from the ordinary one, not an
arbitrary adjunction. It includes both comparison paths. It is already proved
by Mathlib's derivedε_fac_app. The postcomposition hypotheses are supplied by
the absolute K-flat comparison and the K-injective right derivation; they
impose no extra geometric condition on X.

lem-sc-module-cup-global-tensor-comparison, in ModuleCupGlobalTensorComparison,
records Tag 0FP0 for the same α and δ. It states the complete tensor polygon
for arbitrary integer complexes. Naturality and K-flat normalization of δ
are explicit hypotheses; the first repair node supplies both. Its complete
proof docstring describes K-flat resolutions, the naturality rectangle and
cancellation of the localized resolution maps. Zero complexes, negative
degrees, and non-flat p require no additional case or hypothesis.

Change records: coord/changes/module-cup-naive-derived-imports.md and
coord/changes/module-cup-global-comparison.md.

## Earlier second reading (a previous round; superseded)

The previous second reading covered the original three-module reduction. Its
claim that the K-injective target node's dependencies were complete was
superseded by reviewer X-c21c2's C1/C4 return. That reading did not cover the
three comparison statements added in this repair.

The independent second reader must review this repaired six-module set,
especially the global pullback formulas and ordinary evaluation normalization
in the Tag 079U node, the induced (rather than arbitrary) counit in the Tag
0FP1 square, and the canonical K-flat normalization in the full Tag 0FP0
polygon. This worker records no new independent-review verdict here.


## Second reading by G4

Independent second reader of the repaired six-module set, 2026-10-13.

1. **Interfaces: PASS.** Diffed the delivered compatibility module against the
   repository version. The raw signatures of `moduleCup_globalComparison` and
   `moduleCup_naive_derived_compatibility` are byte-for-byte identical. The only
   existing definition-body change is covered by
   `coord/changes/module-cup-global-comparison.md`. A scratch equality between
   the new body and the original transported-unit expression compiled by `rfl`.
   The named localization instance has the existing inferred data; its axiom
   probe has no `sorryAx`. Changes to `X.sheaf` versus
   `X.toRingedSpace.sheaf` expose the same sheaf. No Challenge statement or
   downstream declaration was changed. The unchanged direct importer
   `Sheaf.Paper.ModuleCupEqualDerivedMapsClass` compiled against the overlay.

2. **Proof and data: PASS as a decomposition.** All six delivered files compile
   cleanly through `lcompile.py --all`, in dependency order, within the per-file
   limit. Read the actual cancellation proof: q resolves the tensor codomain,
   Qq is invertible, R preserves that invertibility, and comparison naturality
   supplies precisely the postcomposition cancelled by `cancel_comparison`.
   The naive map has concrete coproduct degree maps, with only its commutation
   proof supplied by its named theorem. No data is chosen from any of the four
   unproved existence/compatibility statements. The choices of tensor-closed
   instances use the proved `SheafOfModules.tensorClosed`, whose proof constructs
   them. No forbidden declarations or anonymous/definition sorries occur.
   Explicit `#print axioms` checked all fourteen public declarations of this
   set: only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` where the
   four named open theorems or the naive-map commutation proof are used.
   The section map, its degree components, named localization instance,
   comparison natural transformation, comparison definition, diagram predicate,
   and proved counit square have no `sorryAx`.

3. **Split statements: PASS.** Read all four remaining statements and their
   source-based docstrings and nodes. The chain identity is precisely the two
   signed Leibniz summands and is zero outside adjacent degrees; negative degrees
   use the same integer sign. The K-injective lemma fixes the concrete naive map
   and restricts its calculation to a K-injective codomain. It leaves the actual
   arbitrary-codomain resolution/naturality/cancellation argument to the item;
   it does not restate the existential naive-map construction or its formula.
   The pullback lemma specifies the actual global ringed-space map, on objects
   and morphisms, with the ordinary counit normalization and the K-flat derived
   normalization. Its arbitrary existential data stay inside a theorem.
   The tensor polygon has both naturality and K-flat normalization; it does not
   infer the polygon from an arbitrary natural isomorphism. Resolving the two
   inputs and precomposing with the isomorphism L(Qq tensor Qr) proves the
   passage from its normalized case, without assuming that ordinary pullback
   preserves arbitrary quasi-isomorphisms. Zero inputs and the empty scheme
   impose no extra condition, and no flatness of the map p is required.
   Checked Stacks Tags 079U, 0FP0, 0FP1, and 0FP3 directly.
   Independent LeanFinder searches for differential compatibility, scalar
   extension and derived multiplication, Loogle for mapBifunctorDesc, and grep
   for derived tensor/counit comparisons found the existing coproduct formulas
   and generic counit factorization, but no immediate closure of a remaining
   hole. The upstream `leftDerivedTensorComparison` imposes exactness, so does
   not replace the unrestricted global pullback construction. No additional
   hole was introduced by this second reading.

4. **Route and pruning: PASS after repair.** The main proof uses the concrete
   naive-map formula and K-injective-target calculation, then the existing
   K-injective resolution theorem. The three old direct proof dependencies
   (`def-pc-tensor-complex-sheaves`, `def-pur-sheaf-tensor-product`, and
   `def-sc-ringed-space-module-cohomology`) are no longer direct proof steps;
   they remain used by the chain identity and other imported obligations.
   The removed resolution-data import is reported above. Read
   `dag/units/sk-prop-av-cube.json`: this auxiliary item is not itself a
   `realized` statement or step, and the general-cube unit route is unchanged.
   No whole-module removal from the targets' closure is claimed.
   Pruned the counit square's unused pullback/tensor/K-flat imports and unused
   tensor instances, retaining the imports needed for its actual signature and
   module-category derived instance. The tensor polygon now imports only its
   defining pullback module, which publicly supplies its signature dependencies.
   Changed the K-injective computation import to a plain proof import.
   Added the previously missing plain proof imports of
   `RingedSpaceTensorPullbackUnderived`, `RingedSpaceTensorPullbackAbsolute`, and
   `RingedSpaceDerivedAdjunctionGeneral` where the planned proofs cite them.
   `KFlatPullback` remains public because `tensorPullbackRingMap` occurs in the
   pullback statement; it is not merely a proof dependency there.

5. **Nodes: PASS after repair.** Checked each Lean statement verbatim against
   its `lean.statement`, every blueprint tag against its node, and the union of
   each proof step's uses against `proof_deps`. New nodes have the required
   source, searches, creation, chapter/unit and blueprint-origin records.
   The counit proof is the one-line Mathlib factorization specialization, so
   corrected its proof and proof_origin accordingly and pruned its proof_deps
   to `lem-sc-derived-adjunction-from-underived`. The pullback existence theorem
   and direct-image definition are not additional proof prerequisites for this
   generic factorization under the supplied instances. Other nodes retain the
   reviewed reduction and the source's mathematical steps.

Second-reader changes: restored the original signature whitespace, pruned
imports and unused counit tensor instances, added the three missing proof
imports, corrected the counit node's proof dependencies and origin, clarified
one change-record table entry and the report's direct-hole accounting.
The holes closed/added remain exactly those named in `## Proved and sorry left`:
one original hole closed by reduction, four lower holes added; no remaining
hole was closed or added by the second reader. This is a decomposition, not an
axiom-free proof of the cup construction. Only the pinned ledger determines
net progress in the targets' import closure.
