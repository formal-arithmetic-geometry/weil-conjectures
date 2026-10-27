## Worker report

The module `Sheaf.Paper.IndetaleSupportedHullContinuity` states exactly
`AlgebraicGeometry.ProEtale.indetale_supported_hull_continuity`, with the whole proof
`sorry`. No definition, auxiliary theorem, dependency repair, new node or statement
correction is introduced. The item's node changes only in `lean`.

Source read: the item's complete statement and eight-step proof; all fifteen statement
dependency nodes and their recorded interfaces; the current blueprint's
`sec-six-functors-basics/sk-prop-sf-comp-coherence/det-sf-comp-coherence-cocycle.proof.md`,
refinement paragraph; and `coord/pefw-upstream-framework.md`. This is an explicitly
agent-formulated conditional obligation. As the node says, an exact reference remains
WANTED: Hemo--Richarz--Scholbach Sections 3--4 give the setting and Lemma 5.3(1) only
bounded input continuity, not inverse-limit continuity in the source scheme. The
module docstring preserves that limitation and the theorem docstring carries all eight
proof steps, including their named dependencies.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The condensed commutative coefficient is `Λ : Sheaf (coherentTopology Profinite.{u})
  Ab.{u + 1}` with `[MonObj Λ] [IsCommMonObj Λ]`. The five alternatives of `hΛ`
  are exactly finite discrete A killed by an ℓ-power, ℤ_ℓ, O_E, ℚ_ℓ and finite E.
  `Finite A`, `DiscreteTopology A`, `IsTopologicalRing A` and
  `∃ n, ∀ a, (ℓ ^ n) • a = 0` implement the finite coefficient assumptions.
  The nonfinite alternatives use `Profinite.continuousMapRingObj` and
  `Profinite.padicIntegersRingObj`, with their existing adic topologies.
  Coefficients are identified by isomorphisms of monoid objects of condensed abelian
  groups, preserving addition, multiplication and unit. No algebraic-closure case is
  admitted. Finite E is represented in the fixed algebraic closure, as in the source's
  coefficient convention and the adjoining coinduction declarations. Every abstract
  finite extension embeds there and transports along its topological field isomorphism;
  E is not restricted to a particular degree or chosen presentation. The independent
  finite-ring and extension parameters in the prose only select these alternatives;
  neither has any further occurrence in the assertion.
- `condensedRingObj Λ W` and `condensedRingObj Λ V` are the pulled-back Λ_W and Λ_V.
  `Mod` is the actual internal module-object category; `DerivedCategory` is its
  ordinary uncompleted derived category. There is no completion subcategory or
  assumption of completeness of L.
- `ScalarModelSupportChain X W` is the existing finite chain. Its constructors
  `nil`, `openStep`, `closedStep` include the empty chain, require quasi-compactness
  of open arrows, and require compactness of the complementary open for closed
  arrows. The actual ordinary extension is `p.extension Λ`, composing the recorded
  open lower shriek and closed lower star in the correct order.
- `HasFiniteConstantLocalModel Λ W L` is precisely the recorded scheme-site
  finite scalar local-model predicate: on a pro-etale cover, pullback from a finite
  presentation on the condensed point. Its scalar-matrix presentation uses discrete
  constant scalar modules, not arbitrary locally varying coefficient matrices.
- `supportedModelHull Λ V` is the dependency's intersection of all full replete
  classes with zero, shifts, triangle extensions, retracts, all small derived products,
  and strict filtered colimits having one common termwise lower bound. Its definition
  quantifies over `I : Type (u + 1)` with `SmallCategory I` and `IsFiltered I`, and
  uses localization `DerivedCategory.Q` of the termwise colimit. No closure is replaced
  by an unrestricted derived colimit, coproduct closure or completion.
- `hetale` universally quantifies S and T in `Scheme.{u}`, with both `CompactSpace`
  and `QuasiSeparatedSpace` instances, and then every e with `Etale e`,
  `QuasiCompact e`, `QuasiSeparated e`. It also quantifies every support source W,
  support chain p and module L, assuming only its finite scalar local-model property.
  Its conclusion is the specified membership for the actual `Re_*((JL)[0])`.
  Λ is fixed outside these quantifiers. S and T are not restricted to a selected
  affine presentation or its stages.
- U and V have the four qcqs space instances; b has `QuasiCompact b` and
  `QuasiSeparated b`. No weak-etaleness hypothesis on b is inserted.
- `hcharts` existentially supplies `n : ℕ` and `D : Fin n → U.Opens`.
  `∀ x : U, ∃ a, x ∈ D a` is the finite open-cover condition, and
  `IsAffineOpen (D a)` makes every domain chart affine. For each chart the existential
  Va and f give an affine open Va of V, a map `(D a).toScheme ⟶ Va.toScheme`,
  and the factorization equation `(D a).ι ≫ b = f ≫ Va.ι`.
  `proAffineEtale f` is the recorded presentation predicate. Since domain and target
  are affine here, `proAffineEtale_iff_appTop` identifies it with the ind-etale
  condition on the actual ring map, exactly a small filtered colimit of finitely
  presented etale algebras. No particular index category, sequential presentation,
  finite presentation of b, or descent of L to one stage is imposed.
- The concluding W, p, L and hL quantify every supported finite scalar local model
  over U. `(DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj L)` is
  `(JL)[0]`; `CondensedRing.moduleObjectDerivedPushforward Λ b` is the actual
  total right derived composite of module direct image, and membership in
  `supportedModelHull Λ V` is precisely the requested conclusion.
- The explicit universe u retains the existing small pro-etale site (object universe
  u+1, morphism universe u), coefficient universe u+1 and the hull's indexing universe.
  All universes and variables are explicit (`autoImplicit false`). No site object and
  morphism universe equality or new smallness/nonemptiness assumption is added.

Dependency declarations used, read with their source signatures and docstrings:

- `Sheaf.Paper.LocalizingAdmissibleCoefficients` supplies the continuous/adic coefficient
  constructions and the established coefficient convention. The six-way
  `IsLocalizingAdmissibleCoefficient` itself includes Qbar, so the five-way assumption
  is displayed directly, exactly as in `EtaleSupportedModelCoinduction` and
  `ProetaleSupportedModelCoinduction`; using that six-way predicate would be wrong.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `AlgebraicGeometry.Scheme.smallEtaleTopology`; the actual assertion's etale property
  is `AlgebraicGeometry.Etale` from `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt` and `Scheme.ProEt.topology`, exposed by the framework.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, used by the support-chain constructors.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek`;
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar`, both used by p.extension.
- `Sheaf.Paper.ProfiniteFiniteConstantLocalModel`, the dependency's current recorded
  module, publicly exposes `AlgebraicGeometry.ProEtale.HasFiniteConstantLocalModel`
  from `Sheaf.Paper.CondensedConstantConstructibility`; its profinite-slice companion
  is not substituted for the scheme-site notion.
- `Sheaf.Paper.SupportedModelHull`:
  `AlgebraicGeometry.ProEtale.ScalarModelSupportChain`, its `extension`,
  `IsSupportedModelHullClass`, and `supportedModelHull`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`:
  `AlgebraicGeometry.proAffineEtale`; its `proAffineEtale_iff_appTop` and
  `proAffineEtale_Spec_iff` confirm the affine ind-etale interpretation.
- The size and scheme-conventions nodes are recorded metatheoretic conventions,
  not missing declarations. They are rendered by the explicit universes and actual
  Mathlib qcqs/affine/morphism notions, respectively.

All currently recorded proof-dependency modules are plain imports, including the
integral tower, scalar completeness, finite discrete comparison, rational lattice
reconstruction and derived triangulated interfaces. The two classical-hull proof nodes
have no recorded Lean module at the time of writing; the proof plan names them without
inventing a duplicate theorem. Statement dependency modules are public imports.

Edge cases checked before writing and again after elaboration:

- n=0 is allowed; the chart-cover formula then holds exactly for an empty U.
  There is no `Nonempty U`, `Nonempty V` or positive n assumption.
- `ScalarModelSupportChain.nil` gives the identity extension, including on empty schemes.
- Rank-zero and torsion scalar presentations are permitted by the existing finite
  presentation predicate. No finite freeness, torsion-freeness or Tor-amplitude
  condition is imposed on L.
- The zero finite ring is allowed (power n=0 can kill the zero ring); the coefficient
  disjunction does not assume `Nontrivial A`.
- Every small presentation index allowed by the fixed size convention is retained
  in `proAffineEtale`; `IsCofiltered` includes nonemptiness of a presentation, but
  no countability or chosen stage is imposed. Empty covers and nonempty filtered
  presentation categories are distinct conditions.
- The premise and conclusion both use ordinary uncompleted direct image, and the
  lower-shriek operation appears only on open support-chain edges.

Searches (2026-10-25):

- `msearch.py ... leanfinder` query: "Conditional supported finite scalar model hull
  continuity of derived pushforward along morphisms locally affine ind etale,
  assuming etale supported coinduction". Eight hits, concerning etale composition,
  affine-local ring-map properties, etale sites and etale loci; no matching theorem.
- `msearch.py ... leansearch` query: "Derived direct image of a supported finite
  scalar local model belongs to the supported model hull for a locally affine ind
  etale morphism assuming etale coinduction". Eight hits, concerning
  `sourceAffineLocally`, formal etaleness and ordinary finite/etale morphism
  infrastructure; none is this statement.
- `msearch.py ... loogle` query:
  `AlgebraicGeometry.proAffineEtale, AlgebraicGeometry.ProEtale.supportedModelHull`.
  Zero hits; the remote Mathlib index reports unknown project identifier
  `AlgebraicGeometry.proAffineEtale`. The local source was therefore read directly.
- `msearch.py ... grep` query:
  `supportedModelHull|indetale_supported|ScalarModelSupportChain`. Zero Mathlib hits.
- `rg -n` for the same pattern in `lean/WeilConjectures` and `lean/Sheaf` finds
  the existing hull definitions and adjacent etale/proetale coinduction and descent
  statements, but no conditional locally affine ind-etale theorem. Their signatures
  were read to distinguish their hypotheses from this one.
- `grep -rn "lem-sfb-indetale-supported-hull-continuity" lean/WeilConjectures`
  returns no match; `rg` in `lean/Sheaf` finds only the downstream theorem's proof
  docstring citation. No exact pre-existing declaration was found.

No statement dispute or correction. The exact-reference caveat is inherited explicitly
from the node rather than resolved by claiming a stronger source theorem.

Validation: the prescribed `scompile.py NQ lem-sfb-indetale-supported-hull-continuity`
compiled the complete module successfully in sandbox mode (18.2 s) and as its library
module (15.7 s), with no error or unexpected warning. No local/global build was run.

## Second reading by NQ

A separate in-thread pass reopened the node and the complete theorem signature after
compilation. The dispatch instruction forbids starting other agents, so this section
records that second pass transparently; the maintainer performs the independent review.
The prime and five coefficient alternatives, all-scheme etale quantifiers, each qcqs
binder, finite affine cover, affine target factorization equation, proAffineEtale
predicate, every support chain and finite scalar model, and the actual ordinary derived
image/hull conclusion match the node clause by clause as detailed above. The underlying
support-chain and hull definitions were reread as well: their empty-chain case and
common-lower-bound strict-colimit closure are retained. In particular, neither the
sixth Qbar coefficient nor a weak-etale hypothesis on b has slipped in. No mismatch
was found and no signature change was needed. All eight proof steps are present in
the theorem docstring; the theorem remains unproved, as stage 2 requires.
