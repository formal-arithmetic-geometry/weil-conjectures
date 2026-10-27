## Worker report

The module `Sheaf.AlgebraicGeometry.SpacePseudoCoherentPerfectApproximation` states
`AlgebraicGeometry.AlgebraicSpace.exists_perfect_approximation`. Its only proof is
`sorry`, as required for stage 2. No definition, helper theorem, dependency module,
or new node is introduced. The accepted stage-1 statement and proof remain unchanged.

The inherited BLOCKED ending concerned re-splitting Q42's accepted stage-1 work.
The current assignment is stage 2, the queue lists this node at stage 2, and its
current node has no Lean record. The explicit stage-handoff paragraph in
`coord/brief-stage2.md` section 0 authorizes continuing with `deliver2.py`.
No released repair note for this item was found.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Chosen universes | Explicit `universe u w`; `[HasDerivedCategory.{w} X.SmallModules]` allows arbitrary localization morphism universe. The existing affine etale model is small in `u`, with original coefficient universe `u`. No site/coefficient lift or equality with `w` is imposed. |
| Scheme S, algebraic space X over S | `{S : Scheme.{u}} (X : AlgebraicSpace S)`; the recorded full subcategory carries the fppf sheaf, representable diagonal and etale atlas. |
| Small etale structure sheaf and its module derived category | `X.SmallModules`, `X.DerivedModules`, and `X.smallStructureSheaf` are the already recorded affine-model constructions, equivalent to the original etale module topos. |
| Quasi-compact point space | `hqc : CompactSpace (Point X.obj.obj)`, with the recorded final etale point topology. CompactSpace means a finite subcover for every open cover and does not assert Hausdorffness. |
| Quasi-compact absolute diagonal | `hqs : X.IsAbsolutelyQuasiSeparated`; this existing affine-test definition is absolute, including over a non-quasi-separated base, rather than a condition only on X over S. |
| E an arbitrary derived object | `(E : X.DerivedModules)`; membership in D_QCoh is a conclusion. |
| Etale-local bounded-above finite-free pseudo-coherence | `hE : X.IsPseudoCoherent E`. The recorded definition uses covering sieves on the affine etale model, finite-free ranks depending on degree, local upper bounds, and quasi-isomorphisms to the restricted representative. |
| E has quasi-coherent cohomology | The first conjunct `X.derivedQCohProperty E` tests every integer cohomology after the actual inverse module equivalence, using the original `SheafOfModules.IsQuasicoherent`. |
| For every integer a | `∀ a : ℤ`, with no bound or sign restriction. |
| P and C belong to D_QCoh | `∃ (P C : X.DerivedQCoh)`; this is the full subcategory of the ambient derived category, not D(QCoh). |
| A distinguished triangle P to E to C to P[1] | The three existential maps `(u : P.obj ⟶ E) (v : E ⟶ C.obj) (δ : C.obj ⟶ P.obj⟦(1 : ℤ)⟧)` and `Triangle.mk u v δ ∈ distTriang X.DerivedModules`. |
| P is perfect | `SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w} X.smallStructureSheaf P.obj`; its existing local strictly perfect models are bounded and have degreewise finite-free retractions. |
| H^i(u) is an isomorphism for i greater than a | `∀ i : ℤ, a < i → IsIso ((DerivedCategory.homologyFunctor X.SmallModules i).map u)`. |
| H^a(u) is surjective | `Epi ((DerivedCategory.homologyFunctor X.SmallModules a).map u)` in the abelian category of module sheaves; this means sheaf surjectivity, not surjectivity on every chart's sections. |
| No Noetherian, separatedness, finite-type or base-ring assumption | The full signature contains only S, X, derived-category size, qcqs, E and pseudo-coherence. In particular no assumption is made about S. |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`, its
  small etale site, regular-functions structure sheaf and `Modules`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib's `SheafOfModules`, used in the recorded `SmallModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, localization and triangulated structure.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, defined by
  the Mathlib predicate `SheafOfModules.IsQuasicoherent`. The existing
  `derivedQCohProperty` uses this same predicate after the module equivalence.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`,
  `IsLocallyStrictPerfectComplexOfUniverses`; their degreewise package is
  `SheafOfModules.StrictPerfectCoefficientPackageOnSite` in
  `Sheaf.Paper.StrictPerfectPackageOnSite`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedQCohProperty`, `DerivedQCoh`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex`: `IsPseudoCoherent`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`
  on the recorded `Point` classes.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`; the proof's recorded Mathlib match is
  `DerivedCategory.HomologySequence.exact₂` (and its two companion exactness lemmas).
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`: `Triangle.mk`,
  `distTriang`, and the TR1 cone completion needed by the proof.

The metatheoretic `def-weil-size-convention` has no declaration to import. Other
proof-dependency nodes currently have no recorded Lean module or Mathlib match;
the module docstring retains their entire five-step proof plan and node names.
Existing statement dependencies arrive through the public imports of their owning
modules. Added four already-landed definition ids to `stmt_deps`:
`def-a1-space-point-topology`, `def-sfb-space-absolute-quasi-separated`,
`def-sfb-space-derived-module-calculus`, and
`def-sfb-space-pseudocoherent-complex`. No existing dependency is removed.

Sources opened: `literature/stacks-project/spaces-perfect.tex`,
`lemma-pseudo-coherent` (08JL), `definition-approximation-holds` (08HI),
`definition-approximation` (08HJ), and `theorem-approximation` (08HP).
For full support T = |X|, the complement is empty and the support condition is
vacuous. The approximation property's integer r works since pseudo-coherence
implies (a-r)-pseudo-coherence for every a. The cone belongs to D_QCoh by the
cohomology exact sequence and kernel/cokernel/extension closure.

Edge cases checked mathematically before writing: empty X and empty affine chart;
zero E and rank-zero free terms; arbitrary positive, zero and negative a; unbounded
below pseudo-coherent objects; varying local bounds and ranks; a non-Noetherian
space; an arbitrary, possibly non-quasi-separated base scheme. In the empty and
zero cases the zero triangle supplies the conclusion. No global boundedness,
finite presentation of cohomology, or sectionwise surjectivity was substituted.

Searches performed for this stage-2 statement:

- `msearch.py`, LeanFinder: “Pseudo coherent complexes on qcqs algebraic spaces
  admit perfect approximations in every degree”. Eight hits: scheme affine-limit
  lemmas and derived bounded-representative lemmas, none the desired statement.
- `msearch.py`, Loogle: `"PseudoCoherent"`. Zero hits.
- `msearch.py`, Mathlib grep: `perfect.*[Aa]pproxim|[Aa]pproxim.*[Pp]erfect`.
  Zero hits.
- `rg` over `lean/WeilConjectures`: pseudo-coherence and perfect approximation
  patterns. Existing scheme/ring pseudo-coherence and affine facts, no
  algebraic-space approximation theorem. Search for this exact node id: no hit.
- `rg` over `lean/Sheaf`: perfect approximation patterns and algebraic-space
  pseudo-coherence/derived/absolute-quasi-separated patterns. Found and reused
  the four recorded definition nodes above; no theorem states this result.
- Exact proposed name search over Mathlib, `lean/WeilConjectures`, and `lean/Sheaf`:
  no prior `exists_perfect_approximation` or
  `space_pseudocoherent_perfect_approximation` declaration.
- DAG scan matched the actual `lean.module` records to the existing definition
  nodes, avoiding new nodes for notions already supplied.

Validation: each compile uses `scompile.py` on the server. The first compile
identified the missing `Pretriangulated` namespace opening for `Triangle.mk`;
that opening was added and the two Mathlib statement imports made public.
The final server compile was clean (sandbox 8.7 s, owning module 6.9 s).
`deliver2.py --no-push` returned OK: the packet passes server preflight and
compilation. The only subsequent change is this validation report update.
No statement dispute or source correction is needed.

## Second reading by Q15

A separate reread of the node and the complete signature checked all rows of the
correspondence table, the free-model definitions and the finite-free splitting
package. The conclusion keeps E in the ambient derived category and proves its
quasi-coherence separately, quantifies a over all integers, and quantifies both
P and the actual cone vertex C in D_QCoh. The cohomology tests use the same map u
as the first arrow of the distinguished triangle. Absolute quasi-separatedness
and sheaf epimorphy avoid the two possible base/sectionwise mismatches. No
mathematical mismatch was found and no statement change was made. This was a
self-check; no additional agent was started, as the dispatch brief forbids it.
The maintainer's independent review remains the external second reading.
