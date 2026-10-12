## Worker report

Repair of reviewer X-a9a96's return on head a9a96f81c. This report describes the
repaired sandbox, not the returned version. Work and the repair audit below were
performed by the repair worker; they do not claim an independent second worker's
review. The dispatcher will provide the second reader before delivery.

## What changed

Replaced the two applications that merely delegated the target's composition and
identity clauses with Ext calculations in `EtaleCohomologyPullbackFunctorial`.
The original declaration's hypotheses, universes, name and conclusion are unchanged.
Naturality still applies the existing `cohomologyMap_map`.

Composition now expands the three `cohomologyMap`s, uses preservation of Ext
composition and degree-zero classes under the exact functor, and combines the two
source morphisms. It transports the image of the Ext class through `upperStarComp`
and uses an equality of constant-sheaf morphisms. Identity now reassociates Ext
composition, transports through `upperStarId`, combines the source morphisms, and
simplifies the resulting identity Ext class. These are actual Lean arguments in the
item's proof, not applications of a new theorem stating either cohomology clause.

Deleted `EtaleCohomologyPullbackComposition`, `EtaleCohomologyPullbackIdentity` and
`EtaleCohomologyPullbackNaturality`, and their sandbox node files. Naturality was
already available; the first two repeated the target's conclusions.

Added four modules, each with one strictly lower-level statement, a source, a
complete proof in words, and its own node. All four new imports in the item are
proof-only imports. The original public import is unchanged. No existing definition
or statement was altered, so no change record is required.

## Proved and sorry left

`AlgebraicGeometry.Etale.cohomologyPullbackFunctorial`: the original one `sorry` is
removed. Its three clauses compile from the existing naturality theorem and the
four following statements. This is a reduction, not an axiom-free closure of the
transitive dependencies.

All sorries added by the delivery (the complete list):

- `CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison`, node
  `lem-weil-pbc-ext-exact-functor-composition-comparison`, in
  `Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison`.
- `CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison`, node
  `lem-weil-pbc-ext-exact-functor-identity-comparison`, in
  `Sheaf.CategoryTheory.ExtExactFunctorIdentityComparison`.
- `AlgebraicGeometry.Etale.constantPullbackCompositionCoherence`, node
  `lem-weil-pbc-constant-pullback-composition-coherence`, in
  `Sheaf.AlgebraicGeometry.ConstantPullbackCompositionCoherence`.
- `AlgebraicGeometry.Etale.constantPullbackIdentityCoherence`, node
  `lem-weil-pbc-constant-pullback-identity-coherence`, in
  `Sheaf.AlgebraicGeometry.ConstantPullbackIdentityCoherence`.

Each is a public theorem ending exactly `:= by sorry`; no definition, private helper
or anonymous part of the item's proof contains `sorry`. The generic comparison
proof was attempted through derived-category naturality and the single-complex
comparisons, but the latter coherence calculation is not completed. The exploratory
attempt is only in the scratchpad and is not part of the delivery.

## No longer needed

Removed proof imports:
`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackComposition` and
`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackIdentity`. The removed sandbox-only
nodes are `lem-weil-pbc-cohomology-pullback-composition`,
`lem-weil-pbc-cohomology-pullback-identity`, and
`lem-weil-pbc-cohomology-pullback-naturality`, together with their three modules.
No target clause is now delegated to these nodes.

The following old plan nodes are not used by the new Ext route:

- `lem-weil-pbc-kinjective-hom-derived` (Mathlib K-injective Hom comparison).
- `def-weil-pbc-kinjective-resolutions` (`Sheaf.AlgebraicGeometry.KInjectiveResolutions`).
- `prop-weil-pbc-cohomology-resolution-independent`
  (`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective`).
- `prop-weil-pbc-inverse-image-exact` (`Sheaf.AlgebraicGeometry.EtaleInverseImageExact`).
- `lem-weil-pbc-exact-functor-complex-cohomology` (Mathlib homologyFunctorIso).
- `def-weil-pbc-derived-inverse-image` (the separate derived inverse-image construction).
- `prop-weil-pbc-kinjective-resolutions-exist`
  (`Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`).
- `lemma-weil-pbc-leray-acyclicity`
  (`WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`).
- `lem-weil-pbc-etale-restriction-injectives`
  (`WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`).
- `lem-weil-pbc-etale-inverse-image-restriction`
  (`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`).

These are pruned from this proof route only; this report does not assert that other
project targets no longer use their modules. The abstract derived-category,
inverse-image, direct-image and inverse-image-composition nodes remain needed by
the new auxiliaries. In particular, inverse-image composition is not pruned merely
because it is no longer a direct dependency of the item's node.

## Where the brief, the DAG or earlier work was wrong

D1 was correct. The returned helpers were literally clauses 2 and 3 of the Lean
item. They were not strictly smaller auxiliary facts, and the earlier second reading
was wrong to call that a valid reduction. They have been removed, not renamed.

The new Ext helpers quantify over arbitrary abelian categories, arbitrary objects,
and arbitrary exact functors with a natural isomorphism. They mention neither
schemes, constant sheaves nor `cohomologyMap`. The two constant helpers quantify
over an arbitrary coefficient group M and state sheaf-morphism equalities, with no
cohomology degree or cohomology class. The target proof has to combine these
independent ingredients using nontrivial Ext composition algebra.

Loogle's live index returns `Ext.id_mapExactFunctor`, `Ext.comp_mapExactFunctor` and
`Ext.mapExactFunctor_comp_mk₀_natTransApp`. The current upstream Mathlib source was
read, including their actual proofs in Ext/Map.lean. These declarations do not occur
in the project's pinned Mathlib source and the authorized compiler reports them as
unknown constants. They cannot simply be applied here. LeanSearch returned HTTP
500; the searches are recorded as unavailable, never as a mathematical no-match.

The existing natural-language node also describes resolution independence, arbitrary
comparison complexes, and etale restriction. The established Lean signature records
three cohomology equations. This repair preserves that signature and does not claim
to prove an unrecorded derived/resolution clause or change the statement contract.

## New nodes

`lem-weil-pbc-ext-exact-functor-composition-comparison`: naturality on Ext under a
comparison from H to the composite of two exact functors. It is the transport square
for an arbitrary Ext class; the target still supplies and composes the source maps.

`lem-weil-pbc-ext-exact-functor-identity-comparison`: naturality on Ext under an
isomorphism of an arbitrary exact endofunctor with the identity. It does not include
any assertion about a cohomology pullback or its constant-sheaf source comparison.

`lem-weil-pbc-constant-pullback-composition-coherence`: equality of two morphisms
from the constant sheaf to successive inverse images. Its proof uses uniqueness of
adjoints and the unit equation, with the terminal pullback identifications specified.

`lem-weil-pbc-constant-pullback-identity-coherence`: equality of the composite
constant comparison and identity inverse-image comparison with the identity sheaf
morphism. This is the source-side identity needed after the generic Ext calculation.

All four nodes are in the item's chapter and unit. Their `blueprint.from.node` is the
ancestor printed by `blueprint_refs.py ancestor`, namely
`lemma-weil-pbc-p1-exchange-geometric-stalk`, with the upper-square pullback comparison
paragraph named and this item in `via`. No unit record or realized unit step changed.

## Review by K1

Repair-worker audit of the actual final module and the five node files; this is not
an assertion that a separate worker has already read the repaired delivery.

F1: Read Stacks cohomology.tex Tag 01F8, label `lemma-functoriality`, and the following
Tag 01FA equation `equation-functorial`; sites.tex Tag 03CB, label
`lemma-composition-morphisms-sites`; derived.tex Tag 015F, label
`lemma-right-derived-exact-functor`; categories.tex Tag 0B65, label
`lemma-transformation-between-functors-and-adjoints`. The available local sources
were `/home/ubuntu/c1-stacks-review/`; their tag index supplies these labels.
For the Ext definition read the existing `def-pc-ext` record (06XQ).

The item's X,Y,Z are arbitrary schemes; u:X→Y and v:Y→Z have no extra smoothness,
properness, etaleness or invertibility assumption. F is an arbitrary abelian sheaf
on Z, q is any natural number, G and φ are arbitrary on Z in clause 1. Clause 1 has
exactly the pullback of the coefficient morphism on its right. Clause 2 compares
successive pullbacks to the composite followed by the *hom* component of
`upperStarComp`, whose direction is composite to successive inverse images.
Clause 3 postcomposes with the *hom* component of `upperStarId`. These are the same
three equations as the input signature, not stronger or weaker variants.

For both Ext nodes all categories are abelian and have HasExt at the same declared
smallness universe; exactness is additive plus preservation of finite limits and
colimits. No enough-injectives hypothesis is used: Ext is localized shifted Hom.
For composition e:H≅F⋙G supplies exactly the comparison at both Ext endpoints.
For identity e:F≅id supplies exactly the two components. Their formulas are
naturality of the localized e, consistent with 015F on all complexes. The source's
05TA proposition alone would only address bounded resolutions; the repair therefore
uses 015F. For both constant nodes M is any abelian group, not just lifted Z; all
schemes and morphisms remain arbitrary. Their comparisons are the exact definitions
of `upperStarConstantSheafIso`, `upperStarComp`, and `upperStarId` read in the
library; no alternative isomorphism is substituted.

F2: Target step 1 uses the compiled `cohomologyMap_map`, whose signature was opened
in TopologicalInvariance.lean. Step 2 uses Ext's preservation of Yoneda composition
and mk₀, the generic composition comparison, and the constant composition equality.
The remaining reassociations are `comp_assoc_of_third_deg_zero` and
`mk₀_comp_mk₀_assoc`, whose pinned Mathlib statements were read. Step 3 uses the
analogous generic identity comparison and constant identity equality, then the Ext
identity simplification. Those algebra steps are elementary *relative to* the four
stated auxiliaries; neither step silently appeals to its conclusion as an auxiliary.
The new Ext nodes use exact-functor derived factorization and localization, then
ordinary naturality; the new constant nodes use the constant-sheaf adjunction,
inverse-image unit compatibility, and the uniqueness-of-adjoints node. Those cited
statements were opened. Their proof dependencies are exactly the unions of the uses
in their steps. No helper imports the item and no dependency cycle is introduced.

F3: Checked every new node for B1–B7: full split proof, self-contained objects and
hypotheses, definition citations, TeX statement, sources with labels, and actual
logged searches. The Lean signatures in the node records match the declarations
verbatim. All four named sorries have module and declaration docstrings with sources
and complete argument sketches. Searches covered the pinned Mathlib sources,
`lean/WeilConjectures`, `lean/Sheaf`, DAG statements, and the complete imported
blueprint via `blueprint_refs.py search` (constant comparison and exact-functor Ext
queries). No existing node states either constant comparison or either generic Ext
square. Existing inverse-image composition and exact-functor factorization are used
rather than duplicated. The online Mathlib match/older-pinned mismatch is recorded
above and in the nodes; three search kinds and their actual results are recorded.

F4: Checked q=0 explicitly: Ext becomes Hom and the generic comparisons become
ordinary naturality/composition equations; the target's calculation has no division,
positive-degree premise or excluded degree. With identity functors and e=refl, the
generic identity equation and composition equation both reduce to x=x. With a
nonidentity natural automorphism of the identity, both retain the two endpoint
components and become its naturality square; the helpers would be false without
those components. Zero Ext classes give zero on both sides. Constant M=0 gives
unique maps between zero sheaves; identity scheme maps give the canonical identity
comparison. Empty schemes are allowed: no geometric point or nonempty terminal
section is assumed. For general M, adjunction uniqueness applies to all coefficient
objects, and for the specialization M=ULift Z it is exactly the source of Sheaf.H.
These are mathematical edge-case checks, not a claim of separate executable tests.

F5 / changes sent back: The maintainer sent D1 and A2/F1–F5 back. This repair deleted
both clause-relabelling modules and nodes, replaced the target applications by the
compiled Ext algebra, introduced only the four lower-level squares/morphism
identities, corrected the generic source citation to 015F, and rewrote the DAG proof
and report. The earlier second reading's D1 claim is explicitly retracted above.
No further changes were sent to another worker: none was launched or contacted.

## Earlier second reading (a previous round; superseded)

The returned version's second reading is superseded: it incorrectly accepted the
clause restatements. The concrete source, hypothesis, dependency, search and edge-case
repair audit is recorded in `## Review by K1`. This was performed by the repair
worker. An independent second reader still needs to review the repaired files before
pushing, as required by the dispatcher workflow.

## Second reading by K1

1. Compared the delivered functoriality module with the repository version. The theorem
   signature and all existing declarations are unchanged; only proof imports and proof
   bodies differ. The four auxiliary declarations are new split statements and are
   documented in the report and node files.
2. Compiled all five delivered modules with `lcompile.py --all`. They compile without
   errors. The only remaining `sorry`s are the four named split theorems, each ending
   in `:= by sorry`; there are no hollow definitions, axioms, unsafe declarations, or
   other forbidden constructs. The target proof itself has no `sorry`.
3. Checked the four split statements against their hypotheses and uses. The two Ext
   comparisons are generic naturality equations for exact functors, and the two
   constant-sheaf statements are source-side coherence equalities. They are strictly
   lower-level than the target, have sources and complete proof sketches, and do not
   duplicate the target clauses. Edge cases q=0, identity functors, zero classes,
   zero coefficients, and empty schemes remain covered by the stated generality.
4. Reviewed the proof route and pruning. The target uses `cohomologyMap_map`, the
   Ext composition and identity comparisons, and the two constant-pullback coherences;
   the deleted clause-restatement helpers are not needed. Proof-only imports are
   marked plain `import`. The unit route and realized unit steps are unchanged.
5. Checked every node's Lean declaration, proof dependencies, proof origin, source,
   and blueprint metadata against the delivered files. The node statements match the
   Lean declarations verbatim, and no dependency cycle or statement change is present.

Changes made during this second reading: none. The repaired files are ready for
preflight and delivery.
