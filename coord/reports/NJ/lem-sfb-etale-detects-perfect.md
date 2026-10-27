## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleDetectsPerfect` states
`AlgebraicGeometry.Scheme.Modules.isPerfect_iff_smallEtale_perfect`, with `sorry`.
Two new definition nodes record existing definitions; there are no new Lean
definitions or other postponed theorems. The natural-language
statement, proof and proof dependencies of the item are unchanged.

Hypothesis and conclusion correspondence:

- An arbitrary scheme is `(T : Scheme.{u})`; there is no geometric class assumption.
- Unbounded derived categories of all modules are `schemeDerivedCategory T` and
  `DerivedCategory (SmallEtaleModules T)`. The `HasDerivedCategory.{w}` instances
  choose their localization presentations, including the Zariski open slices used
  by `Scheme.IsPerfect`. The global scheme-indexed choices are the existing derived
  interface's parameters; these are size/presentation choices, not finiteness or
  quasi-coherence hypotheses. They are available in a common sufficiently large
  localization universe.
- The canonical epsilon tensor pullback is presented by
  `(d : DerivedEtaleZariskiEquivalenceData T)`. Its ordinary functor is literally
  `zariskiEtaleModuleExtension T d.context.continuous d.context.rightAdjoint`,
  the sheafified scalar-extension pullback of `zariskiEtaleOpenRingMap T`.
  The `context` consists of proofs only. The derived functor `d.extension` is
  characterized by `d.extension_factors` on the homotopy category localization.
  Hence this parameter is a presentation of the specified canonical functor,
  rather than an arbitrary map or an additional condition on T or A. The recorded
  theorem `derived_etale_zariski_equivalence` supplies these presentations for every
  scheme. The derived characterization determines the functor up to natural
  isomorphism; perfectness is invariant under that isomorphism.
- An arbitrary object of `D(O_T)` is `(A : schemeDerivedCategory T)`. In particular
  it is not an object of the full quasi-coherent subcategory. Although the data
  record has comparison properties for quasi-coherent cohomology, its extension
  has the entire unbounded derived category as domain and the present theorem
  makes no use of a quasi-coherence hypothesis on A.
- Zariski perfectness is exactly `Scheme.IsPerfect T A`, the recorded declaration
  of def-pc-perfect-complex, including bounded models of finite-free retracts on
  open neighbourhoods of every point.
- The converse topology and the equivalence are rendered by `↔` and
  `SheafOfModules.IsPerfectAtCoefficientSize (smallEtaleModuleRing T)
  (d.extension.obj A)`. This existing predicate means a representative K such
  that every site object admits a covering sieve on which K has bounded
  quasi-isomorphic models whose terms have finite-free splittings. The splittings
  use `StrictPerfectCoefficientPackageOnSite`. Its bounded intervals and finite
  ranks are existentially quantified inside each covering member. This is Stacks
  08G5, and equivalently the local derived-isomorphism formulation in the item,
  by the independent-representative statement immediately after 08G5.
- There is no quasi-coherence, global boundedness, quasi-compactness or
  Noetherian assumption. Site objects remain in Type (u+1), arrows and section
  modules in Type u; no equality of the site object and arrow universes is imposed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, including its
  locally affine condition and inherited locally ringed space.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, localizations of unbounded cochain complexes.
- `WeilConjectures.AlgebraicGeometry.PerfectComplex`: `Scheme.IsPerfect` and
  `Scheme.IsStrictlyPerfect` (the whole definitions and docstrings were read).
- `Sheaf.TraceFormula.ZariskiEtaleFunctorComparisonSquare`: the recorded
  `Scheme.Modules.zariski_etale_functor_comparison_square`, and its imported
  canonical `ZariskiEtaleModuleContext`, extension, restriction and adjunction from
  `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`.
- `Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence`:
  `DerivedEtaleZariskiEquivalenceData` and
  `ZariskiEtaleModuleContext.structureMap`, now owned by
  def-sfb-derived-etale-zariski-equivalence-data. The existence theorem remains
  a proof dependency only.
  The full signatures, defining fields, and normalization docstrings were read.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`, and its public
  imports: the strict-perfect representation and degreewise packages. Its
  max-universe perfectness interface cannot apply directly to the current
  section size u on an object-universe u+1 site. Instead the already landed
  `SheafOfModules.IsPerfectAtCoefficientSize` and its local predicate from
  `Sheaf.AlgebraicGeometry.ProperSupportTensorPerfect` give precisely this same
  definition with independent site and section universes. These real definitions
  are reused verbatim; no replacement notion is introduced. That module's
  proper-support theorem is not used. In particular the item has no new DAG
  dependence on that theorem (which transitively uses this item).
- `WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact`:
  `CategoryTheory.hasSheafify_addCommGrp_of_weak`. Its complete signature and
  proof/docstring were read. The module registers this existing theorem as an
  instance so the existing weak sheafification and locally-bijective criterion
  for every small-etale slice supply the full sheafification needed by the
  reused perfectness predicate. No sheafification binder was added.
- Plain proof import:
  `WeilConjectures.AlgebraicGeometry.PerfectOfPseudoCoherentLocallyFiniteTor`,
  `Scheme.isPerfect_of_isPseudoCoherent_of_hasLocallyFiniteTorDimension`.
  Its full signature and docstring were read. The ringed-site criterion,
  pseudo-coherence descent and Tor descent proof nodes currently have no Lean
  records, so there are no modules to import for them. They remain named in
  the docstring proof plan and in the unchanged proof_deps.

Relative to current main, stmt_deps gains the two new existing-definition owners,
plus the already landed strict-perfect package and sheafification interface.
The derived-equivalence theorem is no longer an added statement dependency;
its original proof dependency is retained. No statement, proof, or proof_deps
changed. Unchanged fields were compared with the current shared main node and
rebased from it. The signature matches the returned head's sandbox verbatim.

Sources checked: local `literature/stacks-project/spaces-perfect.tex`,
lemma-descend-perfect (08HG), and `sites-cohomology.tex`, definition-perfect
(08G5) and the following independent-representative lemma. Read the latest
blueprint unit's direct-image statement at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.md`.

Edge cases checked before writing: the empty scheme (Zariski pointwise condition
vacuous and étale empty covers allowed); the zero complex; rank-zero free modules
and empty products; complexes whose local bounds vary over an infinite disjoint
union, e.g. shifts of k on components Spec k. Both predicates allow the latter
without asserting any common bound. Arbitrary non-quasi-coherent objects remain
in the domain of the theorem. No characteristic restriction occurs.

Searches made with msearch.py NJ lem-sfb-etale-detects-perfect:

- leanfinder: "A complex of modules on a scheme is perfect if and only if its
  tensor pullback to the small etale site is perfect". Eight unrelated hits,
  mainly etale morphisms and base change, no matching theorem.
- loogle: "AlgebraicGeometry.Scheme.IsPerfect, SheafOfModules.IsPerfect".
  Zero hits (the service does not know the project's Scheme.IsPerfect).
- grep: "IsPerfect|StrictlyPerfect", CategoryTheory. Zero Mathlib hits.
- leansearch: "Perfect complexes descend along the canonical morphism from the
  small etale site to the Zariski site". Eight hits about morphism-property
  descent and the site itself; none is the derived perfectness assertion.
- rg in both lean/WeilConjectures and lean/Sheaf for IsPerfect, StrictlyPerfect,
  IsPerfectOnRingedSite, sitePerfect, and perfect/etale combinations: found the
  existing scheme definition, ringed-site packages, actual-section-size local
  predicate, and the characterized derived extension reused here, but no theorem
  detecting Zariski perfectness under epsilon. Item-id search found only proof
  docstrings citing the still-unstated item. Searched dag/lean_names_upstream.json
  for the item id as well; no recorded theorem.

Validation: scompile.py compiled both the sandbox and library names cleanly
(3.4 s and 3.0 s); the only postponed proof is the item's own theorem. The first
compile diagnosed the missing left-exact-sheafification instance; importing and
registering the existing size-independent theorem repaired it without changing
the statement or adding a mathematical hypothesis. Dry run: deliver2.py --no-push returned OK for commit 70ce8e21f6d: preflight
and per-file compilation passed; nothing pushed.

## Second reading by NJ

This is a separate rereading by the same dispatcher-started worker; no other
agent was started, as required by the task. The maintainer performs the
independent delivery review. I reopened the source node, the written Lean file,
the definitions of Scheme.IsPerfect, IsPerfectAtCoefficientSize and its local
predicate, and the fields of DerivedEtaleZariskiEquivalenceData. I checked the
arbitrary T and A binders, both directions of the iff, the actual canonical
ordinary extension, the localization factorization, and the location of the
bounds inside covering quantifiers. The use of a derived presentation d does
not make A quasi-coherent; that premise is absent. The site-perfect predicate
uses degreewise retractions with no chain-map requirement. No mismatch was
found. The source explicitly allows the non-globally-bounded example checked
above. The sheafification fix changes instance availability only. There is no
statement correction or disputed statement. The repair adds definition owners,
with existing:true records and no new Lean definitions. I reread both new nodes
against their exact existing definitions: the site node records both predicates,
and the derived-data node records the structure and its canonical structure map.
The finite-free packages, localization witnesses, normalized derived adjunction,
QCoh preservation and unit/counit fields are accounted for in the data node.


## Returned delivery repair

The maintainer returned immutable head 6915b645316d with two H2/H12 points.

1. Added def-sfb-ringed-site-perfect-at-coefficient-size, an existing:true
   definition record on Sheaf.AlgebraicGeometry.ProperSupportTensorPerfect,
   owning both SheafOfModules.IsLocallyStrictPerfectAtCoefficientSize and
   SheafOfModules.IsPerfectAtCoefficientSize. The item cites this definition.
   It does not cite lem-sfb-proper-support-tensor-perfect; that theorem's closure
   reaches this item, whereas the new definition's closure does not. The source
   of the actual predicates remains the existing module, as the return requests.
2. Added def-sfb-derived-etale-zariski-equivalence-data, an existing:true record
   on Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence, owning
   AlgebraicGeometry.Scheme.Modules.DerivedEtaleZariskiEquivalenceData and
   AlgebraicGeometry.Scheme.Modules.ZariskiEtaleModuleContext.structureMap.
   The item cites this definition instead of adding
   lem-sfb-derived-etale-zariski-equivalence to stmt_deps. The theorem is still
   in the original proof_deps. No assertion of existence or equivalence is used
   to type the statement. The genuine lem-sc-weak-sheafify-addcommgrp-left-exact
   statement dependency, which the reviewer passed, is retained.

The returned theorem's Lean text is unchanged. This repairs ownership rather
than merely rebasing or repushing. Both new nodes use the existing declarations;
the original modules and their theorem node records are not edited. A read-only
DAG traversal with the sandbox nodes overlaid found no route back to this item
from either new definition node.

## New nodes

`def-sfb-ringed-site-perfect-at-coefficient-size`: local strictly perfect
complexes and perfect derived objects at the actual section size, with independent
site object, morphism and coefficient universes. Source: Stacks 08G5. The record
owns both existing predicates in ProperSupportTensorPerfect, not that module's
theorem. LeanSearch found free sheaves and presentation notions, LeanFinder
found general bounded derived representatives, and Mathlib grep found no exact
predicate. Project and DAG grep found precisely these definitions in a theorem
module and only its theorem-node record, so this adds the missing definition
owner requested by the reviewer. The original strict-perfect package definition
node is reused as a dependency. No new data or proof is introduced.

`def-sfb-derived-etale-zariski-equivalence-data`: the exact existing type of
canonical derived epsilon adjunction data, and its ordinary structural scalar
map. Source: Stacks 08H8/071Q and Descent 03FH. The prose accounts for every field
of the existing structure: ordinary context, additivity, exactness, faithfulness,
the two whole-category derived functors, homotopy factorization, right-derived
universal property and K-injective comparison, normalized derived adjunction,
structure-map invertibility, QCoh preservation, and actual unit/counit
invertibility on QCoh. LeanSearch found general derived adjunctions; LeanFinder
found etale ring-algebra results; Mathlib grep found no exact type. Project/DAG
grep found this structure and structureMap in the theorem module, with ownership
only in that theorem's record. The new node records these existing declarations
without assuming the theorem's conclusion. No new Lean structure is introduced.

For both new nodes, mathlib_searches contains the verbatim launcher search output
(status, counts and full returned hit summaries) and exact rg output for dag/nodes,
lean/WeilConjectures and lean/Sheaf. Blueprint searches for perfectness and
"derived etale zariski" were also run; no independent owner of these exact
interfaces was found. The ancestor command reports blueprint.from.node = None;
the new records retain null and inherit the item's entire via chain prefixed
with the item, as required. Each has import_flags: [].

Edge cases reread for the new nodes: zero complex, rank zero and empty products;
cover-dependent bounds on non-quasi-compact sites; independent c/v/r universes;
no point or nonempty scheme assumption in the data type. These agree with the
unchanged consumer theorem. The existing definitions have real data, and the
new records do not assert or postpone any existence theorem.

Repair validation: scompile.py passed unchanged theorem under both sandbox and
library names (3.4 s / 3.0 s). The repaired five-file packet passed deliver2.py
--no-push at 2280dfecb16, including both existing:true definition probes.
