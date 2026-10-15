## What changed

Replaced the sole proof hole in
`Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison` with a complete Lean proof
from the strictly smaller replacement-acyclicity assertion in the new module
`Sheaf.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic`.
The existing public definitions, theorem signature, universes, and visibility are unchanged.

The proof constructs the unbounded direct-image comparison by right-derived descent,
proves its unit normalization on every homotopy complex, identifies it with the fixed
adjunction mate, and descends the already proved ordinary exchange cube. It separately
proves conservativity by the homology criterion. These arguments use proved private
helpers, with no private proof holes. Invertibility alone uses the new acyclicity assertion.
In particular the reduction does not assume that coefficient forgetting preserves
K-injectivity, and does not choose an arbitrary derived comparison from an unproved
existence theorem.

Added two private proof imports: the existing ordinary module/abelian exchange theorem,
and the new acyclicity module. Updated the parent DAG proof and its dependency list,
and added a node for the new assertion. No other existing module is adapted.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.unbounded_abelian_exchange_comparison` (the original
module's one hole). Its exactness/conservativity/homology clauses, unit normalization,
and exchange coherence are now proved. The invertibility clause is reduced to the
following smaller assertion.

Added and still sorry:
`AlgebraicGeometry.Etale.moduleAbelianForget_kInjective_directImage_quasiIso`, node
`lem-kun-module-abelian-kinjective-direct-image-acyclic`.
It concerns only a module K-injective complex I, an abelian K-injective replacement
j:UI -> J, and the quasi-isomorphism v_*j. It contains no derived comparison, mate,
unit-normalization equation, conservativity claim, or exchange square.

Thus this is a decomposition: one original hole closed and one new hole added, net zero
holes, rather than an axiom-free proof of the whole comparison theorem.

The remaining assertion is exactly the replacement computation in Stacks Tag 0D6J(3).
A second route is the last clause of the existing
`CategoryTheory.ringedToposDerivedPushforwardComposition`, applied first to coefficient
restriction and then to geometric direct image over constant integers. Scratch Lean
proofs verified extraction of that clause, integer/module encodings, both concrete
RingedToposMorphism constructors (with all operation and module-linearity identities),
transport of acyclicity through exact equivalences, and transport of module sheaves to
an equivalent ULiftHom site. The remaining work is assembling these identifications on
the lifted sites and applying the composition clause in the required universes.
A complete attempted assembly is in scratchpad/FullAcyclic.lean; it is not a delivery
file. Repeated unfolding of the encoding equivalences and concrete direct images made
that attempted assembly exceed the file limit. Generic proved conversion APIs and an
irreducible equivalence wrapper were tried; further interface optimization is needed.
The source also gives an alternative bounded-above-flat-roof tensor argument.
The delivered docstring and DAG provide the complete composition-based proof in words,
including the site-universe transport. No unfinished bridge is hidden in a definition
or asserted as an extra duplicate comparison theorem.

Edge checks: identity direct image preserves the quasi-isomorphism for arbitrary
complexes (compiled independently). Zero complexes, the zero ring, empty etale objects,
and arbitrary shifts introduce no additional hypotheses. A forgotten K-injective need
not itself be K-injective; the new assertion deliberately does not say so.

Validation: `deliver3.py F4 Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison
--no-push` printed OK for commit `6f89c6b61e`: both delivered modules compile, the axiom
probes ran, and preflight passes except for the second reading, which the next worker
writes. Nothing was pushed. The final comparison module also passed a prior clean
combined build in 45.5 seconds. The auxiliary absolute-derivability fact is explicitly
registered with `[local instance]` within this module's namespace.

## No longer needed

Second-reading cleanup: the new acyclicity module also omits the redundant public
import `Sheaf.AlgebraicGeometry.KInjectiveResolutions`; its only import already supplies
every declaration in its statement. A scratch copy without the import compiled.

Removed all five original private proof imports from the item module:

- `Sheaf.CategoryTheory.RingedSiteModules`;
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`;
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`;
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`;
- `Sheaf.CategoryTheory.DerivedCategory.AdjointSquareComparison`.

The following nine original direct proof-dependency nodes are no longer used directly
by the parent proof:

- `def-weil-sheaf-of-modules-category`;
- `lem-weil-pbc-exact-functor-derived-factorization`;
- `lem-weil-pbc-exact-functor-complex-cohomology`;
- `lem-weil-pbc-unbounded-derived-iso-cohomology`;
- `prop-weil-pbc-inverse-image-modules-exact`;
- `lem-weil-pbc-localization-universal-property`;
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`;
- `lem-weil-pbc-exact-functor-derived-functor`;
- `lem-kun-derived-adjoint-square-comparison`.

Their roles in the parent are replaced by the existing exact-derived-functor API,
K-injective derivability, explicit derived-adjunction normalization, and the new
acyclicity assertion. The composition node is still a dependency of the new node's
proposed ringed-topos proof: removing its parent import is not a claim that this
mathematics has been eliminated from the entire DAG. The constant-ring/module notions
likewise remain in that lower proof. No blueprint unit statement or realized proof step
is bypassed, and no existing module is withdrawn.

The following project modules and their attached nodes also drop out of this item's
proof route, including the composition route described for the new acyclicity node:

- `Sheaf.AlgebraicGeometry.EtaleInverseImageComparisonAddition` (`lem-weil-pbc-inverse-image-comparison-addition`);
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModuleActionLaws` (`lem-weil-pbc-inverse-image-module-action-laws`);
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModuleConstruction` (`lem-weil-pbc-inverse-image-module-construction`);
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModuleCounitLinearLift` (`lem-weil-pbc-inverse-image-module-counit-linear-lift`);
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModuleLinearCriterion` (`lem-weil-pbc-inverse-image-module-linear-criterion`);
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModuleMapLinearity` (`lem-weil-pbc-inverse-image-module-map-linearity`);
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModuleObject` (`lem-weil-pbc-inverse-image-module-object`);
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModuleUnitLinearLift` (`lem-weil-pbc-inverse-image-module-unit-linear-lift`);
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact` (`prop-weil-pbc-inverse-image-modules-exact`);
- `Sheaf.AlgebraicGeometry.EtaleInverseImageRingComparisonOperations` (`lem-weil-pbc-supplied-ring-comparison-operations`);
- `Sheaf.AlgebraicGeometry.EtaleInverseImageScalarAssociativity` (`lem-weil-pbc-inverse-image-scalar-associativity`);
- `Sheaf.AlgebraicGeometry.EtaleInverseImageScalarDistributivity` (`lem-weil-pbc-inverse-image-scalar-distributivity`);
- `Sheaf.AlgebraicGeometry.EtaleInverseImageScalarDistributivityLeft` (`lem-weil-pbc-inverse-image-scalar-distributivity-left`);
- `Sheaf.AlgebraicGeometry.EtaleInverseImageScalarDistributivityRight` (`lem-weil-pbc-inverse-image-scalar-distributivity-right`);
- `Sheaf.AlgebraicGeometry.EtaleModuleInverseImageTransport` (`lem-weil-pbc-etale-module-inverse-image-transport`);
- `Sheaf.AlgebraicGeometry.EtaleModuleRingIsoAdjunction` (`lem-weil-pbc-etale-module-ring-iso-adjunction`);
- `Sheaf.AlgebraicGeometry.EtaleModuleRingIsoTensor` (`lem-weil-pbc-etale-module-ring-iso-tensor`);
- `Sheaf.AlgebraicGeometry.ProductComparisonDistributivity` (`lem-weil-pbc-product-comparison-distributivity`);
- `Sheaf.CategoryTheory.CartesianScalarDistributivityTransport` (`lem-weil-pbc-cartesian-scalar-distributivity-transport`);
- `Sheaf.CategoryTheory.DerivedCategory.AdjointSquareComparison` (`lem-kun-derived-adjoint-square-comparison`);
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor` (`lem-weil-pbc-exact-functor-derived-functor`);
- `Sheaf.CategoryTheory.TransportScalarActionDiagrams` (`lem-weil-pbc-transport-scalar-action-diagrams`);

These are import-closure changes for this item; other targets may still reach them.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The ringed-topos interface requires equal object,
hom, and coefficient universes, while the small etale site has objects in Type (u+1)
and morphisms in Type u. Transport to ULiftHom with the induced topology resolves
this interface mismatch; the new node records this step. The original DAG's
abstract composition and adjoint-square route leaves a substantial concrete encoding
bridge before its declarations can be applied to this etale coefficient-forgetting
square. The delivery isolates its precise acyclicity consequence and proves the
remaining unbounded descent and coherence directly. The already proved ordinary
exchange identity avoids rebuilding the inverse-image coherence argument.

Profiling identified kernel checking of the final instantiated comparison theorem as
the main compile cost; a complete profiled run passed in 59.1 seconds. No compile limit
was raised, no proof was split into files to evade it, and no diagnostic options remain
in the delivered files.

## New nodes

`lem-kun-module-abelian-kinjective-direct-image-acyclic`, in
`dag/nodes/sec-smooth-purity/`, states the unbounded replacement-acyclicity assertion
above and attaches its one-theorem module. It has a complete source-based proof in
words, searches by LeanFinder, Loogle, and Mathlib grep, a recorded unavailable
LeanSearch attempt, and the parent's chapter,
unit, and blueprint ancestry. The whole-blueprint 0D6J search found only the different
vanishing-descends-retract assertion. The new lemma is a strict part of the argument,
not the original conjunction under another name. The record
`coord/changes/unbounded-abelian-exchange-proof-context.md` documents the added section
variables and explicit local registration required by the conservative command scanner.
Existing public signatures and definition bodies remain unchanged.


## Second reading by F4

Independent second reader, 2026-10-16. Read both delivered modules in full, their
repository counterparts, both DAG nodes, the original proof dependencies, the unit
`sk-prop-sf-kunneth-ordinary`, and the stage-3 contract. This is an accepted
one-for-one decomposition, not an axiom-free proof or a claimed net hole reduction.

1. **Visible declarations unchanged — pass.** Compared the item with the read-only
   repository using `diff`, then extracted the three existing declaration signatures
   and compared their bytes. All three are identical. The bodies of
   `moduleAbelianUnboundedUpperStarIso` and
   `moduleAbelianUnboundedLowerStarComparison` are also byte-identical. Auxiliary
   sections close before the original definitions; every added helper is private.
   The local absolute-derivability instance is a proved proposition and does not
   affect the existing public interfaces. The change record accurately describes
   the conservative command-level classification. No target or other existing
   module is changed.

2. **Proof and axioms — pass, with the declared lower hole.** Compiled both delivered
   files together with `lcompile.py --all`: both succeeded without warnings (the
   reported 61.2 seconds for the larger file includes wrapper/slot time; its fixed
   60-second compiler timeout was unchanged). The only `sorry` in delivery Lean is
   the named theorem
   `AlgebraicGeometry.Etale.moduleAbelianForget_kInjective_directImage_quasiIso`.
   There is no forbidden declaration, hidden proof hole, or hollow definition.
   Independent `#print axioms` probes show exactly `propext`, `Classical.choice`,
   and `Quot.sound` for both original public definitions, and those axioms plus
   `sorryAx` for the main theorem and the explicitly open acyclicity theorem.
   `derivedSquare` is constructed by universal right-derived descent, whose unit
   factorization determines the map; it does not choose arbitrary data from the
   open acyclicity statement. The proof uses that statement only to prove an
   isomorphism property of the already constructed comparison.

3. **Split-off assertion — pass.** Read the statement and proof of
   [Stacks 0D6J(3)](https://stacks.math.columbia.edu/tag/0D6J), including its
   replacement calculation, and the full signature and final normalization clause
   of `CategoryTheory.ringedToposDerivedPushforwardComposition` in the repository.
   They justify precisely the new assertion for an arbitrary ring, scheme
   morphism, unbounded module K-injective I, abelian K-injective J, and any
   quasi-isomorphism UI to J. No boundedness, flatness, properness, or preservation
   of K-injectivity is being assumed. The identity-morphism specialization compiles;
   zero complexes and the zero ring reduce to zero cohomology, and shifts and empty
   etale objects add no restrictions. The docstring explains the constant-ring and
   integer-module encodings, equal-universe site transport, exact-equivalence
   transport, and application of the composition clause. The new node matches the
   Lean theorem verbatim. Fresh LeanFinder, Loogle, Mathlib grep, and project-source
   searches found no duplicate: Loogle's `IsKInjective.quasiIso_iff` requires both
   objects K-injective in the same category, so cannot replace this assertion.
   Existing bounded-below comparisons do not cover its unbounded input. The
   assertion has no derived mate, unit equation, conservativity, or exchange
   coherence, and is strictly a part of the parent argument. Inspected the existing
   encoding assembly in `scratchpad/FullAcyclic.lean`; closing that bridge is not
   a short additional proof, so the documented hole remains.

4. **Top-down route and pruning — pass.** Checked the exact-derived homology
   argument, the absolute right-derived descent and its unit equation, the
   K-injective derivability test, the explicit derived unit/counit mate calculation,
   and the derived cube against their applications in the final proof. The cube
   reduces to the existing proved ordinary exchange theorem, rather than a new
   duplicate exchange assumption. The report lists all nine dependencies removed
   from the original `proof_deps` and all five removed private imports. The
   composition theorem remains below the new assertion; it is used as a generic
   tool, retaining the original route. The source import-graph check confirms all 22 listed modules remain removed even
   when the new assertion's planned proof-dependency imports are included. The unit's
   `realized` fields and its stated
   Kunneth/projection-formula route are unchanged. Kept the existing public imports
   and both new private proof imports of the item. Removed the redundant public
   import of `KInjectiveResolutions` from the new acyclicity module after a scratch
   copy compiled without it: its statement already has all required declarations
   through `ModuleAbelianDerivedDirectImageComparison`. No existing module is
   withdrawn; the listed closure pruning remains subject to the global ledger.

5. **DAG agreement — pass after metadata repair.** The parent's four steps describe
   the actual exactness, descent/acyclicity, mate-identification, and cube arguments;
   `proof_deps` is exactly the union of their `uses`, and `proof_origin` names the
   source and actual reduction. Its only modified fields are `proof`,
   `proof_deps`, and `proof_origin`. The new node has the correct source, ancestry,
   chapter, unit, declaration, searches, and full natural-language proof. A scan
   through all 395 nodes reachable from its statement/proof dependencies found no
   path back to the parent. Corrected the parent steps' `elementary` flags: these
   are substantive proved arguments, not one-line identities. Removed the new
   node's maintainer-owned top-level `tool_uses` and declared the generic composition
   use, with its reason, under `split_report.tool_uses`; the maintainer records
   acceptance. Added the new node's empty `lean_audit` placeholders and the fresh
   search results.

Second reading changed only the redundant import in the new module, the DAG
metadata/search records described above, and this report. It introduced no theorem,
proof hole, signature change, or definition change. Closed one original hole and
added one strictly smaller hole, net zero; the main theorem still rests on the
explicitly listed lower assertion. Required dry run and delivery follow this review.


Second-reader validation: `scratchpad/EdgeTests.lean` compiled successfully. The
required final dry run printed `OK (dry run)` for commit `c4ce6ed00e`, with both
modules compiled, axiom probes completed, and all preflight checks passing. Its
review class is CODEX because this delivery adds a node/module and the documented
local proof-context commands. No permission or unresolved review condition remains
for the authorized delivery command.
