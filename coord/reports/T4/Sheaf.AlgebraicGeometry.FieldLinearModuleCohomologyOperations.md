## What changed

In Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations, completed the proof of
AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtMap_bijective from one smaller geometric
obligation. The private fieldUnitSectionsEquiv constructs the global-section Hom equivalence.
scalarUnitHom_bijective identifies its scalar counterpart through evaluation at 1, the
constant-sheaf adjunction, and constantScalarUnitIso. The private extComparison_bijective
uses injective presentations and the two covariant Ext sequences to pass from this ordinary
Hom bijection to every Ext degree. Its algebraic proof follows the existing private generic
argument in CyclicDerivedHomComparisonBijective; that specialization is not imported because
it depends on different étale objects. The final proof identifies scalarFunctor with Mathlib's
terminal-open restriction followed by field restriction, transports preservation of injectives
through that isomorphism, and composes the Ext bijection with moduleExtEquiv.

Added proof-only imports of Sheaf.AlgebraicGeometry.FieldScalarRestrictionInjectives and
Mathlib.Algebra.FiveLemma. Added the former module with the
single fieldScalarRestriction_preservesInjectives statement. It concerns arbitrary ring
sheaves on a topological space and contains no Ext or cohomology assertion. Existing public
signatures, imports, definition bodies, and exported attributes are unchanged. Updated the
parent node's proof route and added the new obligation's node.

The full module compiled in 43.1 seconds after locally caching its two abelian-category
instances. Profiling, diagnostic prefixes, and isolated proof tests were confined to scratchpad;
no delivered file was split to meet the limit. The scope change is recorded in
coord/changes/fieldLinearComparisonProofScopeT4.md. The single-file limit was unchanged.

## Proved and sorry left

Closed the two original holes:
AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtMap_injective
(node lem-sc-field-linear-ext-map-injective), and
AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtMap_surjective
(node lem-sc-field-linear-ext-map-surjective).
Replaced the existing scalarCohomologyExtMap_bijective proof with the dimension-shifting argument.
The item's module now contains no sorry. Its existing statement is unchanged, including every
field, scheme, module, and degree; the argument includes degree zero, zero modules, and empty
schemes. All three new private helpers have complete proofs.

Added exactly one hole in a new module:
SheafOfModules.fieldScalarRestriction_preservesInjectives
(node lem-sc-field-scalar-restriction-injectives;
module Sheaf.AlgebraicGeometry.FieldScalarRestrictionInjectives).
Its complete proof in words constructs the tensor left adjoint, checks its exactness on stalks
over the field, and applies the injective lifting argument. The empty space and zero ring sheaf
are explicitly covered. It is strictly the injective-preservation part of the original plan:
it has no degree parameter and asserts no Ext comparison or cohomological bijectivity.

This is a decomposition: two original holes closed, one strictly lower hole added, net one hole removed.
The inherited moduleResolutionHomologyExtEquiv dependency is already proved in the repository;
its import remains needed by exists_moduleExtEquiv. No arbitrary data is chosen from the new
unproved theorem: it supplies only the proposition of injective preservation.

## No longer needed

No existing import, node, or module is pruned. Every existing proof-dependency import remains
needed by another already proved declaration of this multi-operation module. No import of
CyclicDerivedHomComparisonBijective, FlatModulePullbackExact, or the scalar-forgetful pullback
comparison modules is needed: their statements concern different categories or require the
present module, creating a cycle. None was added. The new argument uses the existing
module-resolution comparison and the single geometric obligation only. The blueprint unit's
statement and steps are preserved; sk-prop-av-cube.realized is empty in this snapshot.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction or target change was required. The original bijectivity
plan was accurate but did not provide the field-restriction injective theorem as a separate
Lean declaration. It is now stated explicitly. Exactness of restriction alone does not prove
its Ext comparison; the proof also needs preservation of injectives and the Hom bijection.
The existing flat-pushforward result is for schemes, so it cannot directly apply to the
constant-field ringed space on the same arbitrary topological space. The scalar-forgetful
inverse-image comparison results import this module and cannot be imported back.

The read-only repository has no literature/stacks-project directory on this machine.
WANTED: cohomology.tex Tag 02N5, modules.tex Tag 02N4, and homology.tex Tag 015Z,
for lem-sc-field-scalar-restriction-injectives. The statements and proofs were read on the
[Stacks Project](https://stacks.math.columbia.edu/tag/02N5), including its linked
[flat pullback](https://stacks.math.columbia.edu/tag/02N4) and
[adjoint injectivity](https://stacks.math.columbia.edu/tag/015Z) results. The source-specialization
proof is marked agent-written in the new node. LeanSearch was unavailable (Internal Server
Error); LeanFinder, Loogle, local rg, and blueprint searches were completed and recorded.

## New nodes

lem-sc-field-scalar-restriction-injectives states only that the explicitly recorded
terminal-open-plus-field-restriction functor preserves injective objects. Source: Stacks
02N5, 02N4, and 015Z, specialized to the identity of the underlying topological space with
constant field ring sheaf. The field hypothesis makes the tensor left adjoint stalkwise exact.
Its new module has one public theorem with whole proof := by sorry, and its declaration,
verbatim statement, source, complete proof, searches, ancestry, chapter, and unit are recorded.
No duplicate scalar-restriction node was found. The change record is
coord/changes/fieldLinearComparisonProofScopeT4.md.

## Earlier second reading (a previous round; superseded)

1. Compared every delivered module with the repository version. Existing declaration signatures and definition bodies are unchanged; the two former split declarations are retained as wrappers around the proved bijection.
2. Compiled both delivered modules with lcompile. The only remaining sorry is the named split theorem `SheafOfModules.fieldScalarRestriction_preservesInjectives`; no axioms, unsafe declarations, or hollow definitions were added.
3. Checked the new theorem statement against its node and source. It asserts only injective preservation for the explicitly displayed restriction functor, with no Ext or cohomology strengthening; its node and docstring are present.
4. Read the proof route and imports. The Ext comparison uses the existing module resolution theorem, the new injective-preservation obligation, and Mathlib's five-lemma machinery; no removable proof dependency was found.
5. The target and unit route are unchanged. The node proof and proof_deps record the new lower obligation, and the unit remains realized as before.

Changed the proof review only by restoring the original injective and surjective declarations as wrappers and documenting all users affected by the local cached instances in the change record.

## Second reading by T4

1. Compared the complete module with the read-only repository using diff, and independently
   compared every existing named declaration header through `:=` or `where`, ignoring
   comments but preserving header bytes. All existing headers agree; all existing definition
   bodies and public imports agree. The three new named helpers are private. The local
   abelian-instance caches and scalarSheaf transparency section agree with the change record
   and do not alter the instances or transparency exported to users. Verdict: unchanged
   mathematical interface, no target change or forced adaptation.
2. Independently compiled both delivered modules, in import order, with lcompile: clean,
   1.5 and 20.2 seconds. Compiled separate scratch copies with `#print axioms` for all three
   new helpers, the bijection and its injective/surjective projections, moduleExtEquiv,
   and scalarCohomologyExtEquiv. The helpers and moduleExtEquiv use only propext,
   Classical.choice, and Quot.sound. The comparison and its inverse additionally use
   sorryAx through the one named fieldScalarRestriction_preservesInjectives obligation.
   No forbidden declaration or hollow definition occurs. fieldUnitSectionsEquiv constructs
   its maps explicitly; the comparison inverse is determined by bijectivity, rather than
   chosen as an arbitrary witness. Verdict: sound reduction, with the reported single hole.
3. Read the new theorem and its node against Stacks Tags
   [02N5](https://stacks.math.columbia.edu/tag/02N5),
   [02N4](https://stacks.math.columbia.edu/tag/02N4), and
   [015Z](https://stacks.math.columbia.edu/tag/015Z). On the identical underlying space,
   alpha defines the constant-field action on each open. The tensor left adjoint uses
   R as a right k-module via multiplication by alpha and as a left R-module; these actions
   commute even for the stated RingCat, without requiring alpha to have central image.
   Its stalk tensor is exact over the field, and adjoint transposition gives the asserted
   injective extension. Checked a one-point space (ordinary scalar restriction), empty
   space, zero ring sheaf, and zero modules. The theorem has no Ext or degree assertion;
   it is strictly one part of the original comparison, with a full docstring proof and
   matching new node. Independent LeanFinder search used "An exact extension of scalars
   left adjoint on sheaves makes restriction of coefficients preserve injective sheaves";
   no exact match. Loogle could not resolve Functor.PreservesInjectiveObjects; this is
   unavailable evidence, not a no-match result. msearch grep found the general adjunction
   criterion, which still requires the unconstructed exact tensor left adjoint. Local rg
   covered both library roots, Mathlib module-sheaf change of rings, and the injective
   preservation API. FlatModulePullbackExact is only for schemes; the existing generic
   Ext comparison in CyclicDerivedHomComparisonBijective is private, and its public
   theorem concerns different etale objects. No reusable theorem closes this obligation
   in a few minutes. Verdict: true, needed, strictly smaller, and not a duplicate.
4. Read the comparison from the top down. The terminal-section equivalence and evaluation
   at 1 establish the exact degree-zero map, including its scalarUnitMorphism naturality.
   The successor step embeds F in an injective, maps its cokernel sequence by the already
   exact scalarFunctor, and applies the right-exact five-lemma with the induction
   hypothesis. Both squares are proved using Ext composition and extClass naturality;
   injective vanishing gives both final surjections. The final objectwise isomorphism to
   the displayed restriction functor supplies precisely the missing injectivity, then
   moduleExtEquiv supplies the existing cohomology comparison. No shorter public route
   or unused new import was found. The old proof_deps consist only of
   lem-sc-module-resolution-homology-ext, still used by exists_moduleExtEquiv, so
   `No longer needed` omits no old dependency. sk-prop-av-cube.realized is unchanged
   (empty statement and step arrays); no unit step has been bypassed. Verdict: correct
   route and pruning report.
5. Compared all four delivered node records with the Lean. The three existing nodes
   change only proof, proof_deps, and proof_origin. The parent retains the resolution
   dependency and adds the exact injective-preservation obligation; its proof-dependency
   list is the union of the recorded steps' uses. Both projection nodes depend on the
   parent, which does not depend back on either projection. The new node's field, space,
   ring sheaf, alpha, functor, and injectivity conclusion agree with the verbatim Lean
   signature, and its source, ancestry, searches, creation, and lean fields are present.
   Verdict: DAG agrees, with no statement change or dependency cycle.

No proof, statement, definition, import, or node repair was needed. This second reader
added this independent review and scratch axiom checks only. Counts remain two original
holes closed, one lower hole added, net one hole removed; this is a decomposition and
the resulting comparison still depends on that lower hole.
