## What changed

Proved the original continuousCoefficientImmersionRestriction theorem from constructed,
normalized completion, localization and pullback maps. Retained the earlier sandbox's
canonical pullback, coefficient naturality and composition equations. Completed all three
comparison modules: discrete constant sheaves and pointwise residue limits give completion;
the local denominator cover gives localization; preservation of finite constant towers gives
integral pullback invertibility. The localization universal property, canonical constant maps
and coefficient naturality then construct and verify the rational inverse.

Moved the existing definitions and construction laws verbatim to ContinuousCoefficientBasic,
publicly reexported by the original module, to resolve the dependency cycle with the comparison
modules. Existing public declaration names, signatures, visibility and data are retained. The original
main theorem's statement and docstring are unchanged. No consumer needs adaptation.

The resumed dry run timed out compiling completion. Profiling found repeated typeclass
inference through coefficient witness definitions. Local irreducibility for
Padic.coefficientExtensionIntegers, Padic.coefficientExtensionUniformizer and
Padic.coefficientExtensionIdeal keeps those witnesses folded during completion inference;
the complete module then compiled in 29.3 seconds. The definitions and public API are unchanged.

All six modules compiled together successfully. The final required dry run also checks the
delivery, declaration probes and axioms before push.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Scheme.continuousCoefficientImmersionRestriction.

Also proved all three obligations introduced in the earlier sandbox:

- AlgebraicGeometry.Scheme.continuousCoefficientCompletion
  (lem-weil-pbc-continuous-coefficient-completion).
- AlgebraicGeometry.Scheme.continuousCoefficientLocalization
  (lem-weil-pbc-continuous-coefficient-localization).
- AlgebraicGeometry.Scheme.continuousCoefficientPullback_isIso
  (lem-weil-pbc-continuous-coefficient-pullback-isIso).

Holes closed in the assigned module: one of one. Holes added: zero.
Every delivered Lean module has zero sorry. No unresolved split-off is delivered.
The canonical pullback, normalization, coefficient square and composition equations are proved.

## No longer needed

Removed original direct proof imports of ProEtaleImmersionLimitPreservation,
ProEtaleWeaklyEtaleLocalization, ProEtaleConstantRingMap and ExtensionIntegersDvr from the
original module. The first three modules are unnecessary throughout this proof:

- lem-weil-pbc-proetale-immersion-limit-preservation and its module are replaced by the
  already proved finite constant-tower inverse-image theorem.
- prop-weil-pbc-proetale-constant-ring-map and its module are unnecessary: the constant
  comparisons follow directly from the constant-sheaf and inverse-image adjunctions.
- lem-weil-proetale-weakly-etale-localization and its module are unnecessary: open fibre
  and denominator covers use the existing ProEt.mem_topology_of_openImmersion theorem in
  WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale. Removed this approved tool-use
  entry from the original node, and removed its imports from the comparison modules.

Completion uses the existing IntegersProfiniteTower theorem instead of reproving convergence
from ExtensionComplete and ExtensionIntegersDvr. Their local-field facts remain dependencies
of that existing theorem. ExtensionIntegersDvr also supplies the uniformizer facts used by
localization and rational restriction through the coefficient datum; it is not mathematically
pruned. No DAG module is withdrawn. Public imports defining the original API remain reexported.

## Where the brief, the DAG or earlier work was wrong

Returned-head repair (`c04f1e5123`): added all six consumers named by the landing tools
to the change record’s `## Users`: AdicSectionCanonicalModels, FiniteAdicImageNormalization,
FiniteAdicOpenSectionData, FiniteAdicOrdinarySectionData, FiniteAdicProperSectionData, and
FiniteAdicSectionRealizationCore (all in Sheaf.Paper). Their rational coefficient sheaf,
value and restriction-normalization declarations retain the original definitions and signatures
through the public reexport, so their statements and files require no adaptation.
Corrected the change record’s stale description of textual users to match this table.
Refreshed the transitive-user table against the current shared sources on 2026-10-20;
all 977 currently reported modules are recorded, including consumers added since the return.
Their use of the unchanged public reexport requires no adaptation.

The earlier sandbox had three unresolved comparison obligations. These are all proved here.
The completion draft needed an explicit discrete quotient topology and sectionwise limit
coercions. Localization needed explicit site objects and localization rings to avoid expensive
or failed inference. These were proof elaboration repairs; no definition data or statement
was weakened. The earlier report's two remaining holes are now closed.

The planned general immersion limit theorem is stronger than this coefficient argument needs.
The existing finite-tower theorem proves integral restriction for arbitrary scheme morphisms.
The assigned theorem retains every original hypothesis and its exact statement.

## New nodes

lem-weil-pbc-continuous-coefficient-completion: proved by discrete constant comparison and
the existing topological ring equivalence with compatible positive residues. Includes the
constant-section and pointwise-reduction normalization.

lem-weil-pbc-continuous-coefficient-localization: proved by the canonical fraction map and
the open cover where uniformizer powers make a rational section integral. Local bijectivity
and the sheafification adjunction give the normalized isomorphism.

lem-weil-pbc-continuous-coefficient-pullback-isIso: proved using the completion residue cones,
finite-tower preservation, and a constructed inverse on rational coefficients. The two inverse
equations follow from naturality and uniqueness on integral numerators. No hole remains.

lem-weil-pbc-continuous-ring-functions-sheaf: records the existing ring-valued
continuous-function sheaf construction moved verbatim to ContinuousCoefficientBasic.
Its sheafhood proof is complete; its public definitions are unchanged.

lem-weil-pbc-continuous-coefficient-pullback-composition: records the constructed
adjunct pullback and its proved composition and coefficient naturality equations in
ContinuousCoefficientPullback. Both support nodes have the same Bhatt--Scholze sources
as the original construction and add no holes.

Restored the original DVR tool-use approval, which localization still uses. The removed
weakly-etale-localization approval remains pruned. Added the three consumers introduced
since the earlier change record; their reexported definitions and statements are identical.

Change record: coord/changes/J3-continuous-coefficient-basic.md.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
