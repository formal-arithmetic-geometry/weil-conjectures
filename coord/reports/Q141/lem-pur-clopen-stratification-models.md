## Worker report

The module Sheaf.AlgebraicGeometry.ClopenStratificationModels states the node in five
named theorems. All five proofs are `by sorry`; no definitions or new axioms are added.
The main record is isConstructibleProEtaleModuleSheaf_iff_clopen, with the other four
clauses listed in lean.declarations. The informal statement and dependencies are unchanged.

Hypotheses and clause correspondence:

- A scheme X is `(X : Scheme.{u})`. The finite set of components is `(I : Type v)
  [Finite I]`, with an independent index universe and without a Nonempty assumption.
  The schemes and maps are `Xi : I → Scheme.{u}` and `j : ∀ i, Xi i ⟶ X`.
  `[∀ i, IsOpenImmersion (j i)]` and `[∀ i, IsClosedImmersion (j i)]` give exactly
  the two specified immersion properties. `hdisjoint` is pairwise disjointness of
  their ranges and `hcover` is their union equal to the whole underlying space.
- An input immersed stratification is the recorded `FiniteLocallyClosedStratification`.
  It contains a finite Fin n index, locally closed disjoint covering subsets, actual
  scheme domains, immersions and their range equalities. `hS` supplies constructibility
  of every image; no noetherian hypothesis is introduced.
- clopenStratification_pullback uses `pullback (S.immersion n) (j i)` as the stratum
  scheme and `pullback.snd` as its immersion into Xi i. Its five conjuncts assert
  immersion, locally closed image, constructible image, pairwise disjointness and
  coverage. These are the stratification conditions, listed directly to retain the
  exact Fin S.n indexing and the actual fibre-product scheme structure.
- clopenStratification_union uses the finite index `(Σ i, Fin (S i).n)` and maps
  `(S p.1).immersion p.2 ≫ j p.1`. Their domains are definitionally the original
  `(S p.1).domain p.2`. The same five conjuncts give the union stratification;
  there is no choice of reduced structures or replacement stratum schemes.
- Any finite commutative ring is `(A : Type u) [CommRing A] [Finite A]`, with no
  Nontrivial assumption. `F : proEtaleRingModules X (proEtaleConstantRing X A)` is
  a sheaf over the constant ring sheaf, using the recorded ringed-site modules.
  All restrictions along scheme maps are `proEtaleConstantModulePullback`, the
  published inverse image followed by tensor extension along the canonical
  constant-section coefficient map. This is the ordinary operation, not a derived
  operation, and no arbitrary coefficient comparison is quantified over.
- For pullback of models, `R n`, `W n`, `a n` and `hc n` give the original covering
  family of each stratum, indexed in Type (u+1) as required by the site. `M n r`
  is the given module over ULift A, `hfinite` asserts finiteness as a set, equivalent
  to finite module generation for finite A. `he` is the supplied module-sheaf
  trivialization on the localized ringed site using proEtaleConstantModuleSheafOver.
  The conclusion of clopenStratification_pullback_models uses precisely
  `(proEtaleBaseChange (pullback.fst (S.immersion n) (j i))).obj (W n r)` and the
  original `M n r`. The sheaf on the left is `b^* j_i^* F` with b = pullback.snd.
  It supplies covering arrows to the terminal object and membership in precoverage
  for those exact base-changed objects. Terminal arrows are unique, so no choice
  of an unrelated cover is hidden by the existential binder.
- For union of models, `R i n`, `W i n`, `a i n`, `hc i n`, `M i n`, `hfinite`
  and `he` are the component strata's given covers and finite module models of
  `s^* j_i^* F`. clopenStratification_union_models asserts module isomorphisms for
  `(s ≫ j_i)^* F` on exactly `W i n r`, with exactly `M i n r`. The schemes on
  both sides are the original stratum domains, so the unchanged arrows `a` and
  the unchanged coverage proof `hc` continue to be the supplied covers.
- isConstructibleProEtaleModuleSheaf_iff_clopen uses the intrinsic ring-sheaf
  constructibility predicate publicly exported by the dependency's recorded
  ProEtaleFixedModuleConstructible module. Its definition requires a positive
  finite immersed constructible partition, local constancy, and finite geometric
  module stalks. The conclusion is exactly the iff with its value on each ordinary
  restricted sheaf, without a common bound or any extra stalk condition.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.OpenImmersion: AlgebraicGeometry.IsOpenImmersion.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion and Morphisms.Immersion:
  AlgebraicGeometry.IsClosedImmersion and IsImmersion.
- Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification:
  Topology.FiniteLocallyClosedStratification and
  AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification.
- Mathlib.Topology.Constructible: Topology.IsConstructible, and the proof lemmas
  IsConstructible.preimage_of_isOpenEmbedding (005J) and
  IsConstructible.image_of_isOpenEmbedding (09YD).
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt, ProEt.topology and precoverage.
- Mathlib.CategoryTheory.Sites.ConstantSheaf: CategoryTheory.constantSheaf.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules, the
  transparent abbreviation of Mathlib SheafOfModules. Used through proEtaleRingModules.
- Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations, ProEtaleOperations and
  ProEtaleInverseImage: proEtaleConstantRing, proEtaleRingModules,
  proEtaleConstantModulePullback and the canonical constant coefficient comparison.
- Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses publicly imports the original
  local-constancy interface, in particular proEtaleConstantModuleSheafOver. The
  independently sized variant and the original agree at t=u; no new notion is defined.
- Sheaf.Paper.ProEtaleFixedModuleConstructible publicly imports
  Sheaf.Paper.ProEtaleConstructibleSheaf.IsConstructibleProEtaleModuleSheaf (in namespace
  AlgebraicGeometry.Scheme), the intrinsic predicate accepting this F. The fixed
  ModuleCat predicate itself is not applied to a ring-sheaf module.

The available recorded proof-dependency modules are plain imports:
WeilConjectures.ConstructibleSheaf.Pullback (Scheme.Stratification.pullback);
ProEtaleOrdinaryPullbackComparison (AcyclicHypercover.compositionIso);
ProEtaleConstantRingComposition (proEtaleCoefficientInverseImageMap_comp);
ProEtalePullbackLocallyConstant (proEtaleConstantModulePullback_locallyConstant);
ProEtaleLisseFiniteModelsFromLisse (finite_models_of_fixed_lisse);
ProEtaleFiniteModelStalks (ProEtale.finite_geometricStalk_of_finite_models);
ProEtaleObjectInverseImageRestriction (proEtaleObjectInverseImageRestriction).
The docstrings explain their use in the six proof steps of the node, including
constant-ring composition coherence and the localized-site restriction comparison.
No missing dependency module is required: the recorded modules export the intrinsic
variants and the finite locally closed stratification needed by these signatures.

Sources opened: literature/stacks-project/topology.tex, labels
lemma-open-immersion-constructible-inverse-image and
lemma-quasi-compact-open-immersion-constructible-image; and
literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-def-sf-operations/def-weil-finite-torsion-constructibility.md.
The former give constructibility under open restriction and retrocompact open image;
the latter gives the finite locally closed constructible partition and finite-stalk
condition. The node supplies the immersed-scheme and chosen-model extension.

Edge cases checked: I empty forces X empty by hcover and does not require any component.
Fin S.n can be empty; its covering equation then forces its base empty. Empty strata,
empty fibre products, and empty cover members are admitted. No Nonempty, Nontrivial,
nonzero rank, noetherian or quasi-compact assumption appears. The positive-stratum
constructibility convention still admits the empty scheme using one empty stratum
and the zero model; this is explained in the main theorem's proof docstring. The
coefficient zero ring and zero modules are included. An arbitrary finite Type v is
permitted for I; the sigma index is finite without imposing a scheme-size restriction.

Searches, all via the prescribed msearch.py Q141 lem-pur-clopen-stratification-models:

- leanfinder: "Finite clopen partitions of schemes transport constructible immersed
  strata and the same finite pro-etale module models and covering objects" returned
  eight unrelated affine-limit and scheme-cover declarations; no exact statement.
- loogle: "AlgebraicGeometry.Scheme, IsClopen" returned only
  Scheme.Hom.QuasiFiniteAt.isClopen_singleton_asFiber; no stratification/model statement.
- grep: "clopen.*stratif|stratif.*clopen" returned zero Mathlib hits.
- leansearch: "Constructibility of finite module sheaves on the pro-etale site is
  equivalent to constructibility on each piece of a finite clopen partition" returned
  eight generic SheafOfModules finite-type/presentation results; no exact statement.
- rg of the same clopen/stratification pattern in lean/WeilConjectures and lean/Sheaf
  found only proof discussion in FiniteClopenDerivedDecomposition,
  PerAdicNormalizedFibreComparisons, QcqsRationalIntegralLocalizingGenerators and
  FiniteNormalClopenConstructibleModule. None states this node's clauses.
- grep of the item id in lean/WeilConjectures returned no hits. Searches for all five
  proposed declaration names in both source roots and dag/lean_names_upstream.json
  returned no hits.

Validation: the prescribed scompile.py compiled both the sandbox probe and the final
library module cleanly (43.2 s and 18.6 s respectively). No source signature change,
STATEMENT-DISPUTED flag, or new/dependency node is needed.

## Second reading by Q141

This is a second pass by the same dispatched worker, not an independent agent review:
the dispatcher's explicit instruction prohibits starting agents. Independent review
is left to the maintainer as the task brief specifies.

Reopened the node and all five signatures. The partition assumptions are explicit in
all five. The geometry uses the recorded finite locally closed stratification plus
constructibility, rather than silently adding a noetherian hypothesis or changing the
scheme structures. The sigma-indexed maps in the union theorem have the unchanged
domains. The model conclusions contain the original M and the actual base-change functor
applied to W; the union conclusion contains the exact input W without an existential
replacement. The nested ordinary module pullbacks have the correct orientation: first
j_i^*, then the stratum pullback. The final iff uses the intrinsic predicate exported by
the recorded module, not its incompatible fixed-ModuleCat sibling. Empty index families
and the positive-stratum convention were checked separately as above. No mismatch was
found in this rereading and no statement correction was made.
