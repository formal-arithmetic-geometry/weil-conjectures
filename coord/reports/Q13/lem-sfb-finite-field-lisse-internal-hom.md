## Worker report

The module `Sheaf.Paper.FiniteFieldLisseInternalHom` states
`AlgebraicGeometry.Scheme.finiteField_lisse_internalHom`, with `sorry` as its only
postponed theorem proof. Two helper functors spell out the two sides of the
cohomology formula and their maps; they compose existing constructions and contain
no postponed data. A fixed-universe instance specializes the existing locally
bijective criterion. There are no new mathematical notions or new nodes.

Source read: Bhatt--Scholze, *The pro-etale topology for schemes*, Lemma 6.7.13,
PDF text at the Internal Hom lemma, together with Stacks `sites-modules.tex`,
`example-dual` (Tag 0FNY, lines 4886ff). The Bhatt--Scholze lemma concerns more
general completed coefficients under quasi-excellence; as the node's proof_origin
explains, this item's finite-local-system case follows instead from the explicit
finite-free calculation, with no excellence or prime restriction. The module
docstring carries all five steps of the node's proof and names their dependencies.
No statement correction or disputed statement is necessary.

Hypotheses and clauses, individually:

- A finite field is `(A : Type u) [Field A] [Finite A]`.
- The Noetherian scheme is `(S : Scheme.{u}) [IsLocallyNoetherian S]
  [CompactSpace S]`: locally Noetherian plus quasi-compact, with no separation,
  excellence, characteristic or connectedness hypothesis.
- The site is exactly `ProEt.topology S`, on `S.ProEt`, with object universe
  `u+1` and morphism universe `u`. The coefficient is `proEtaleConstantRing S A`,
  the sheafification of constant `CommRingCat.of (ULift A)`.
- Module sheaves are the existing `proEtaleRingModules S (proEtaleConstantRing S A)`,
  transparently `ringedSiteModules` / `SheafOfModules`, with their usual abelian
  structure. `DerivedCategory.{u+2}` is the standard ordinary localization, with
  its existing `proEtaleRingModules_hasDerivedCategory` instance. No completion,
  etale-origin condition, or substitute derived category appears.
- L's given finite-dimensional local models are exactly
  `IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
  (fun M ↦ Module.Finite (ULift A) M) L`. This is the recorded covering/localized
  constant-module-sheaf predicate with the finite-dimensional specialization.
  The models and their dimensions may vary among cover members.
- The interval is `(a b : ℤ), a ≤ b`. Membership of N in B_A(S) with this interval
  is expanded, rather than newly defined: every `homologyFunctor _ r` value is
  `IsConstructibleProEtaleModuleSheaf S A`, and every value outside the interval
  (`r < a ∨ b < r`) is `IsZero`.
- The constructibility predicate is the recorded intrinsic constant-ring one:
  a positive finite `Stratification`, locally closed constructible strata,
  local constancy after the canonical module inverse image, and finite geometric
  module stalks. Over a finite field finite stalks/models are equivalently
  finite-dimensional. No alternative affine-local convention is substituted.
- `finiteFieldInternalHomCohomology S A r` is the composition of the opposite
  degree-zero single functor in L, the identity in N, the recorded
  `derivedInternalHomOfUniverses`, and `DerivedCategory.homologyFunctor _ r`.
  It is literally H^r RHom(L[0],N), using the ambient ringed-site construction.
- The first output conjunct asserts constructibility in every degree and the
  same outside-[a,b] vanishing. Together with the supplied a,b and a≤b these
  give exactly output membership in B_A(S) in the original interval.
- `finiteFieldDualTensorCohomology S A r` fixes the second argument of the
  existing `SheafOfModules.homFunctor` to `SheafOfModules.unit` of the underlying
  ring sheaf, namely A_S as its own module. It then uses the existing curried
  sheaf tensor on this dual and H^r(N). Thus its value is exactly
  Hom(L,A_S) tensor H^r(N); the tensor is sheafification of presheaf tensor.
- For every r the second output conjunct is `Nonempty (F ≅ G)` of FUNCTORS,
  restricted by `ObjectProperty.ι` to the full subcategory of pairs (L,N) with
  precisely the finite-model and bounded-constructibility hypotheses. Every
  morphism of pairs (a map L'→L and an arbitrary ambient map N→N') is retained.
  This asserts both contravariant naturality in L and covariant naturality in N,
  as well as the claimed isomorphism in every degree; it is not just unrelated
  objectwise isomorphisms. The restriction uses existence of some interval,
  independently of the first conjunct's specified interval.

Dependency declarations read and used:

| Dependency | Module and declaration |
| --- | --- |
| pro-etale site | `Mathlib.AlgebraicGeometry.Sites.Proetale`, `Scheme.ProEt`, `ProEt.topology` |
| constant sheaf | `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `CategoryTheory.constantSheaf` |
| module category | `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules` |
| ordinary derived category | `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`, `singleFunctor` |
| constructibility | `Sheaf.Paper.ProEtaleConstructibleSheaf`, `Scheme.IsConstructibleProEtaleModuleSheaf` |
| scheme | `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` |
| locally Noetherian | `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsLocallyNoetherian` |
| quasi-compact | `Mathlib.Topology.Defs.Filter`, `CompactSpace` |
| local constancy | `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`, `Scheme.IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses` |
| derived internal Hom | `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`, `CategoryTheory.derivedInternalHomOfUniverses` |
| sheaf Hom | `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`, `SheafOfModules.homObj`, `homFunctor` |
| ordinary derived cohomology | `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`, `DerivedCategory.homologyFunctor`, `homologyFunctorFactors` |
| sheaf tensor | `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, `SheafOfModules.cochainModulesMonoidal`, and its public localization tensor imports |

All separately recorded proof-dependency modules are imported without `public`:
`ProEtaleObjectInverseImageRestriction`, `ModulePullbackTensorIso`,
`LocalizedModuleExactForSystems`, `ProEtaleStalkConservative`,
`ProEtaleLisseFiniteModelsFromLisse`, `ProEtalePullbackLocallyConstant`, and
`ProEtaleFiniteModelStalks`. Statement dependencies already publicly importing their
primitive modules need no redundant imports. Here H^r is the Mathlib
`DerivedCategory.homologyFunctor` already included in the statement and
`mathlib_match` of `def-weil-abstract-derived-category`. The landed N5 record
`def-weil-derived-cohomology-sheaves` and its module
`Sheaf.Paper.SfCommonStageWeilCohomology` are retained unchanged.

The small-site object and morphism universes remain u+1 and u; modules live in u+1. Compilation diagnosed
an imported instance `WeilConjectures.integralCoefficientAbLocallyBijective` with
an undetermined auxiliary coefficient universe. The public helper
`finiteFieldInternalHom_locallyBijective` explicitly applies the existing
`SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u+1,u,u+1}`.
This supplies precisely the same Prop-valued class, with no new assumption,
new axiom, equality of site universes, local instance, or new proof obligation.
Both cohomology helper functors have real compositional data.

Semantic edge cases checked: L=0 (rank-zero models, allowed by Module.Finite),
N=0, empty S (a covering and empty strata remain allowed by the recorded
predicates), a=b (one potentially nonzero degree), negative and shifted intervals,
disconnected S with different model ranks, and every finite characteristic. Over
Spec of a field the formula reduces to the usual finite-dimensional dual-tensor
Hom formula. No uniform global rank, nonempty S, a≥0, or invertible characteristic
hypothesis has slipped in. The case a>b is excluded exactly as in the node.

Searches actually run:

- `msearch.py ... leanfinder`: “Derived internal sheaf Hom from a finite dimensional
  locally constant sheaf over a finite field preserves bounded constructible
  complexes and has cohomology dual tensor cohomology”. Eight hits, all condensed
  or light-condensed locally constant-module functors/closed structures; none is
  the pro-etale ambient derived same-interval statement.
- `msearch.py ... loogle`: `"SheafOfModules", "homObj"`. One presheaf module-structure
  instance, not the statement.
- `msearch.py ... grep`:
  `(lisse|LocallyConstant).*(derivedHom|derivedInternalHom)|(derivedHom|derivedInternalHom).*(lisse|LocallyConstant)`.
  No Mathlib match.
- `rg` in `lean/Sheaf` and `lean/WeilConjectures` for bounded constructibility,
  lisse/internal-Hom combinations and the proposed declaration names, plus the
  node id in `WeilConjectures`. Existing bounded-constructible and etale
  perfect/internal-Hom statements are different interfaces; no exact statement
  or copy of the two formula functors was found. The new names were also checked
  against `dag/lean_names_upstream.json`.

Validation: the module passed `scompile.py` against the server's live published
library, sandbox and library passes, with no error or warning. The final dry-run
and delivery results are recorded by the prescribed delivery wrapper.

## Returned-delivery repair

For return L on immutable head `286e974576f7` (H13/H4), removed the
dependency-node replacement from the packet. The only delivered node is
the item, whose `lean.note` now explains the existing ordinary derived
cohomology functor provided by `def-weil-abstract-derived-category`.
Removed the former dependency-module repair section and corrected the
cohomology dependency discussion above. No mathematical statement or
dependency changed. The retained Lean file is byte-identical to the saved
returned packet (SHA256
`7fa684716623dbefeaedb8b7e600ab5e65b554f73866ba6cd87c5b2f4bbf11c4`).
Compared the item with current main: all fields other than `lean` agree.

Repair validation: `scompile.py Q13 lem-sfb-finite-field-lisse-internal-hom`
compiled the unchanged module cleanly in both sandbox (12.6 s) and library
(8.8 s) passes. The initial saved-packet dry run passed at `62f488d7d78`;
the repaired packet is separately checked and delivered below.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
