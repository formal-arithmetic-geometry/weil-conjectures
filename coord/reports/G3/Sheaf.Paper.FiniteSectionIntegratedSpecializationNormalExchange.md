## What changed

Proved AlgebraicGeometry.Etale.FiniteSmoothPurity.normalExchange_exists using
SectionReesBaseChange.base_change and SectionReesBaseChange.etale, transporting the
canonical base-change normal cone along the Cartesian-square isomorphism. The normal
comparison in each compatibility package is identified by cancelling its closed
zero-fibre immersion. Horizontal pasting and the zero-section equations finish the proof.
No new modules or lemmas are introduced.

Corrected the intermediate statement to bind hs : s ≫ g = id and hsprime : sprime ≫
gprime = id. These are part of the source's closed-section assumption, omitted by the
old signature and absent from Geometry. The only caller,
Sheaf.Paper.FiniteSectionIntegratedSpecialization.integratedSpecialization_baseChange,
already has both equations; its proof now passes them. Its statement and all target
statements are unchanged. The normal-exchange node has the complete corrected statement,
verbatim Lean signature, actual proof plan and dependencies, and statement_change with
all three DAG citers. The declaration's blueprint tag now names its own node.

Server validation: the item compiled in 7.4 seconds and its adapted direct importer
compiled in 29.3 seconds, both without warnings. The delivery tool performs the final
probe and related-module checks against the delivered overlay.

Change record: coord/changes/G3-normal-exchange-section-equations.md, including all
transitive consumers and the unchanged-statement checks.

## Proved and sorry left

The item had one hole, in AlgebraicGeometry.Etale.FiniteSmoothPurity.normalExchange_exists
(node lem-sp-finite-section-integrated-specialization-normal-exchange). Its corrected,
source-faithful section statement is now proved. The old false signature is not claimed
as proved. Zero holes remain in the item; zero holes are added; zero statements are
split off. The adapted parent had and retains zero holes. This is a statement repair
with a complete proof of the repaired assertion, not a decomposition.

## No longer needed

Removed public imports Sheaf.Paper.FiniteSmoothPurityMaps and
Sheaf.Paper.VectorPurityNormalization, and the proof import
WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange. Only the geometry
class is required in the statement, so import its owner FiniteRingSectionDeformation
directly. Add the private proof import SectionReesBaseChangeEtale.

No whole module or node is withdrawn: the parent independently imports both former
public dependencies and SmoothBaseChange. The node's old proof had no concrete
proof_deps to prune. There is no need to develop another normal-cone base-change theory,
conormal algebra map, or homogeneous-bundle comparison: the existing proved Rees results
already provide the geometric maps and zero-section compatibility. All unit steps stay.

Searches: msearch leanfinder for smooth-section normal-cone base change returned only
general smooth-base-change and differential results; loogle IsPullback returned no
identifier match; msearch grep found no exact match. Direct rg in the project found
SectionReesBaseChangeEtale.base_change and .etale, which close the proof.

## Where the brief, the DAG or earlier work was wrong

The earlier split's Lean signature did not actually say that s and sprime are sections.
Geometry asserts smoothness and compactifiability of deformation projections and regular
conormal data, but not s followed by g = id. Thus the original assertion is false.

Counterexample: take P=Spec k for a field, S=V=P disjoint-union P, s=id_V, and let g take
both components identically into the first component of S. Set Sprime=P, b the first
inclusion, Vprime=V, q=id_V, gprime the fold to P, and sprime the first inclusion. The
ambient square is Cartesian, and sprime followed by q equals b followed by s.
Both Geometry classes hold for d=0: for s=id the deformation is A1_S, while for sprime
it is A1_P disjoint-union Gm_P, etale over A1_P. Conormal modules are zero, symmetric
comparisons are isomorphisms, the empty regular sequences generate the centre ideals
on its components, and all required noetherianity and compactifiability properties hold.
The normal cone of s is the two-point V; that of sprime is the one-point P. The pullback
of the first normal projection g along b is two copies of P, so no one-point normal
cone can make the required Cartesian square. The repaired hypotheses exclude this
example and restore the closed-section assumptions of the cited blueprint proof.

The three DAG citers remain valid: the parent, specialization factor, and integration
factor already assume hs and hsprime. Only the parent calls normalExchange_exists.
Edge cases of the repaired proof: arbitrary nonflat b is handled by the existing Rees
base-change result; identity b uses its identity specialization; d=0 uses the same
normal isomorphisms; empty schemes require no points, choices of charts, or positivity.
No coefficient-ring assumption or new regularity assumption is introduced.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteSectionIntegratedSpecialization": "6534f4496b21388a957e04350082d463c29dfd1b", "Sheaf.Paper.FiniteSectionIntegratedSpecializationNormalExchange": "402903b7a059018c8d64ebfce625e85385c0f77c"}, "results": {}, "time": "2026-10-28T03:26:21+0800", "transitive": 0, "version": 1}
```

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
