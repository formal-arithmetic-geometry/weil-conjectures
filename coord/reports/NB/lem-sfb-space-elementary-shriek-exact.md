## Worker report

The module `Sheaf.AlgebraicGeometry.ElementaryEtaleShriekExact` states
`AlgebraicGeometry.AlgebraicSpace.elementary_etale_shriek_exact`. The node statement,
proof, dependency lists, and source remain unchanged. There are no new nodes or
repaired dependency modules. Every helper belongs to this node's expressly specified
functors, counits, maps, or sequence. Both postponed theorems are clauses of this node:
`etaleModuleRestriction_isRightAdjoint` is its left-adjoint existence assertion, and
`elementary_etale_shriek_exact` is its full exactness and base-change assertion.
All definitions have real data; both theorem proofs are `sorry` with source and
step-by-step natural-language proofs.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base scheme and spaces are `{S : Scheme.{u}}`, `{X : AlgebraicSpace S}`,
  `{U V : AlgebraicSpace S}`. Their module categories are the recorded `X.Modules`,
  `U.Modules`, and `V.Modules`: sheaves over their actual small étale structure sheaves,
  with module carriers in universe u. No equality of independent site universes or
  enlargement of module carriers is imposed. The enlarged-site model is used only in
  the construction proof, through its existing equivalence for the original universe.
- `jU : U ⟶ X` is open by
  `hU : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) jU.hom.hom`.
  This is precisely the scheme-test predicate in `OpenSubspace`; an arbitrary open
  immersion presentation is used, avoiding an unnecessary choice of its isomorphic
  literal subfunctor. `jV : V ⟶ X` has `hV : IsEtale jV.hom.hom`, the recorded
  representable, scheme-test étaleness predicate. No quasi-compactness or separation
  binder appears.
- `E : ClosedSubspace X`, `hE : IsReduced (E.val : AlgebraicSpace S)`, and
  `hSupport : pointImage E.val.arrow.hom.hom = (pointImage jU.hom.hom)ᶜ` say exactly
  that E is the reduced closed complement. The support lemma supplies existence and
  uniqueness; quantifying its presentation does not impose a choice or an extra
  condition. `hIso : IsIso (Limits.pullback.snd jV.hom E.val.arrow.hom)` states
  that the projection V times_X E -> E is an isomorphism of sheaves, hence of spaces.
- `ElementaryEtaleSumExact` quantifies every overlap presentation T, a, b with
  `IsPullback a b jU jV`. Thus T is U times_X V and `a ≫ jU` is jT. It concludes
  the necessary étaleness witnesses for jU, a, and b, rather than assuming them.
  The composite witness gives jT étale.
- `pullback j hj` is the existing literal restriction on the small étale module sites.
  `etaleModuleRestriction_isRightAdjoint` asserts its left adjoint exists.
  `etaleModuleShriek` and `etaleModuleShriekAdjunction` use Mathlib's adjoint universal
  property. The proof constructs this adjunction by the already recorded extension
  presheaf followed by module sheafification on the localized enlarged ringed site.
  Representability bounds the lift index on a scheme chart in universe u. This is
  the unique left adjoint up to adjunction-compatible isomorphism, not a choice from
  mere unconstrained existence. In particular there is no independent arbitrary
  extension functor or arbitrary morphism binder.
- `EtaleModuleSumExact` asserts additivity, finite-limit preservation and finite-colimit
  preservation of restriction, shriek and `etaleModuleSum = pullback ⋙ shriek`.
  These are the exactness clauses for the three functors attached to U, V, and T.
  `ElementaryEtaleSumExact` additionally gives these three properties for the binary
  sum endofunctor. Identity is already exact and additive by the existing APIs.
- `etaleModuleSumCounit` is the selected adjunction's counit, not an unconstrained map.
  `etaleModuleRestrictionComp` is the identity on the underlying section modules.
  `etaleModuleSumMap` transposes restriction of the unit through that canonical
  composition comparison. Under composition of left adjoints it is precisely the
  extension-by-zero counit of the further slice restriction: on lift-indexed summands
  it reindexes by the given projection and applies the identity to the coefficient.
  Thus the construction retains both the canonical maps and their functor naturality.
- `elementaryEtaleSumDifferential` is `biprod.lift` of the map to U and the negative
  of the map to V. `elementaryEtaleSumEvaluation` is `biprod.desc` of their evaluation
  counits, so its signs are (+,+). `etaleModuleSumCongr` only transports equal
  structure arrows; `sq.w.symm` identifies the second overlap composite with jT.
- `∃ hz : d ≫ e = 0, (ShortComplex.mk d e hz).ShortExact` is the entire natural short
  exact sequence in the endofunctor category `X.Modules ⥤ X.Modules`, including the
  zero composite, monomorphism, middle exactness, and epimorphism. Its objects are
  exactly E_T, E_U ⊞ E_V, and identity. The binary biproduct instances are supplied
  by Mathlib's construction from the existing sectionwise finite products; no new
  abelian structure is chosen.
- The second main conjunct quantifies arbitrary X₁ and `h : X₁ ⟶ X`, both pullback
  squares, and their projections. It concludes étaleness of jV₁ and the same exact
  sequence on all modules on X₁. It also constructs a reduced closed complement E₁
  with the required support and isomorphism over it. E₁ is formed on X₁, not declared
  equal to the potentially nonreduced pullback of E. There is no flatness hypothesis
  on h, no use of exactness of h*, and no restriction on the base-change square.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, `EtaleSite`, `structureSheaf`, `Modules`, `isEtale_comp`, and `pullback`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`. Its preadditive, limit and morphism structures
  remain the original ones.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: the recorded general
  module operation interface is imported; its tensor inverse image specializes to
  the existing literal étale restriction, which is the statement's specified j*.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`, with exactly
  its scheme-test open-immersion condition used on jU.
- `Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport`:
  `exists_unique_reduced_closed_subspace`; its `ClosedSubspace`, `IsReduced`,
  `Point`, `pointImage`, and arbitrary-base-change support conclusion.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage` and the
  topology on the existing field-valued point classes.
- `def-weil-size-convention` is metatheoretic; its record has no declaration.
- Proof imports retain `AtlasEtaleRestriction` (including `smallEnlargedModuleEquivalence`
  and the entire `EnlargedEtaleRingedSite` interface), `LocalizedModuleExactForSystems`
  (`localizedSystemExtension`, `localizedSystemRestriction`, `localizedSystemExact`,
  and `localizedSystemAdjunction`), `ChartwiseEtalePermanence`
  (`chartwise_etale_permanence`), `AlgebraicSpaceFibreProductsEtaleCovers`
  (`fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`),
  `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
  (`SheafOfModules.extensionByZeroPresheaf`),
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
  (`PresheafOfModules.sheafification`), and
  `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
  (`CategoryTheory.moduleSheaves_colimits_forgetful`). The two geometric stalk proof
  dependencies currently have no Lean record and require no statement-time import.

Edge cases checked before writing: empty X and its zero module category; U empty
(then V is isomorphic to X); U=X (the complement is empty and V may be empty);
zero F; empty étale fibre over a point in U; infinite étale fibres over U; arbitrary
nonflat and nonreduced base change. In the singleton-open-fibre case the stalk maps
are c |-> (sum c,-c), (a,c) |-> a+sum c; their kernel calculation also covers an
empty V-fibre. Outside U the V-fibre is singleton, giving 0 -> 0 -> M -> M -> 0.
Finite support suffices for every infinite fibre. No statement fault or disputed
claim was found.

Searches for an existing exact statement (2026-10-24):

- msearch.py leanfinder, "Exact sequence of etale extension by zero restriction functors
  for an elementary distinguished square of algebraic spaces": eight hits, including
  `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.shortComplex_exact`; the
  latter is about free abelian sheaves of representables, not these structure-sheaf
  module endofunctors. No exact match.
- msearch.py leansearch, "Exact sequence of extension by zero functors for an elementary
  distinguished square": eight unrelated/general exact-sequence hits, no match.
- msearch.py loogle, "SheafOfModules.extensionByZeroPresheaf, ShortComplex.ShortExact":
  no hits, unknown project-specific first identifier. Its actual source was read.
- msearch.py grep, "extensionByZero|MayerVietorisSquare", CategoryTheory/Sites:
  ten generic Mayer-Vietoris hits; read `MayerVietorisSquare.shortComplex_shortExact`
  and its setup, confirming its different free-abelian-sheaf coefficients.
- rg searches for shriek, Shriek, elementary/exact, extensionByZero in project
  AlgebraicGeometry directories, and the item id in WeilConjectures: existing scheme
  or constant-coefficient shriek constructions, no module-endofunctor theorem for
  algebraic spaces. Additional name searches across Mathlib, WeilConjectures, Sheaf,
  and `dag/lean_names_upstream.json` found no conflicting helper names.

Source checked directly: `literature/stacks-project/spaces-perfect.tex`,
lemma-exact-sequence-lower-shriek (08GV), including its geometric-stalk proof,
and lemma-make-more-elementary-distinguished-squares (08GN), clause (2).
The module's proof docstrings retain every proof step from the node.

Compilation uses scompile.py only. Both the private sandbox module and the final
library module compiled cleanly under the default 60-second limit, with no warnings.

## Second reading by NB

The dispatched worker reread the complete node and the complete module after the
first successful compile; no second agent was started, as instructed. This is a
self-audit, with the independent review left to the maintainer as the brief specifies.
The audit checked the actual category and coefficient universe, scheme-test openness
and representable étaleness, reduced complement and its projection isomorphism,
all nine exact/additive functor clauses, the (+,-) and (+,+) maps, functor-category
short exactness, and arbitrary base change with a newly formed reduced complement.
No mathematical hypothesis was added or removed. Compiler-directed repairs replaced
an expensive definitional equality for iterated restriction by sectionwise identity
isomorphisms, constructed naturality via the whiskered adjunction Hom equivalence,
and supplied binary biproduct instances from existing finite products. These changes
preserve the stated objects and maps. No statement correction was required.
