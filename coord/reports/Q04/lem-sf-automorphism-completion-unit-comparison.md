## Worker report

Item: `lem-sf-automorphism-completion-unit-comparison`.
Module: `Sheaf.Paper.AutomorphismCompletionUnitComparison`.
Declaration: `AlgebraicGeometry.Scheme.automorphism_completion_unit_comparison`.
It is a statement with `sorry` as its entire proof. No definitions or axioms are added.
No repair note for this item was present in `coord/repair-notes`.

### Hypotheses and clauses

- An arbitrary scheme is `X : Scheme.{u}`. The ring is `A : Type (u + 1)` with
  `[CommRing A]`; the small pro-etale site's object and morphism sizes remain u+1/u.
- `d : AdicCoefficientDatum A` includes the ideal, Noetherianity, finite generation,
  additive torsion of A/I, perfectness of all positive quotients, and finiteness of
  those quotient sets. These are the fields of `CompleteCoefficientDatum` and
  `AdicCoefficientDatum`; no extra assumption of completeness of A is imposed.
- `r`, `a : Fin r → A`, and `ha : Ideal.span (Set.range a) = d.ideal` are precisely
  an arbitrary finite generating tuple, including the empty tuple when I = 0.
- The completed coefficient ring is the published `pbcAdicCompletion X d`, the
  limit of the actual finite continuous-function coefficient sheaves. The ambient
  category is `PbcCompletedDerived X d`, the derived category of its module sheaves.
  It is the `reductionDerivedCategory X (completedReductionCoefficient X d)` model
  used by the recorded intrinsic-completion interface, with identical module data.
- `e : Aut X` is the scheme automorphism. `pbcIsoAmbientPullback e.hom d` is H:
  exact ordinary module pullback descended through localization, not completed
  pullback. It uses the existing `completedCoefficientMap`, built by `limit.lift`
  with components the inverse-image projections followed by the finite constant
  comparisons. `pbcIsoCoefficientMap_isIso` supplies its invertibility.
- G is `pbcActualDerivedPush e.hom d`, the ordinary derived module direct image.
  `(pbcActualDerivedAdjunction e.hom d).ofNatIsoLeft
  (pbcIsoOrdinaryDerivedComparison e.hom d)` is the actual module adjunction
  descended to derived categories and transported to the exact H model.
  The first two conjuncts assert invertibility of all its unit and counit
  components, hence the stated ambient adjoint equivalence.
- The completion reflector and complete subcategory are the existing
  `wfCompletion` and `WfCompleteCategory X d r a ha`. The latter is exactly the
  full subcategory `WfIsComplete`, invertibility of the published intrinsic unit
  at the localization's chosen genuine representative. The existential hH/hG
  assert preservation of this full subcategory by both actual functors; they are
  conclusions, not additional hypotheses.
- The two `ObjectProperty.lift` terms are the literal restrictions of H and G:
  objects keep the ambient objects and maps keep the ambient maps. The adjunction
  `adj` between them is required to have precisely the ambient Hom transpose,
  expressed by `(adj.homEquiv M N f).hom = ...homEquiv M.obj N.obj f.hom`.
  Its unit and counit are required to be isomorphisms. This specifies restriction
  of the actual adjoint equivalence, not an unrelated equivalence of categories.
- The last conjunct quantifies over every M, every cochain representative C of M
  with its realization `real`, and every representative D of HM with `realH`.
  `intrinsicCompletion ... M C real` and `intrinsicCompletionUnit ... M C real`
  use the specified product/signed mapping-fiber Koszul complex and the (u,0) map.
  The `∃! c` type is precisely H(LM) ≅ L(HM) with these representatives. Its
  predicate is `H.map (intrinsicCompletionUnit ... C real) ≫ c.hom =
  intrinsicCompletionUnit ... D realH`, exactly the unit equation in the node.
- Every tuple and every pair of representatives are universally quantified.
  There is no constructibility, boundedness, Noetherianity of X, or scheme
  dimension restriction. There are no unbound implicit variables or universes.

### Dependency declarations read and used

- `Sheaf.Paper.AdicCoefficientDatum` and its published support modules:
  `AdicCoefficientDatum`, `AdicCoefficients.completedRing`,
  `completedReductionCoefficient`, `reductionDerivedCategory`; the existing
  completed-ring presentation `pbcAdicCompletion` and `PbcCompletedDerived`
  are the same recorded model used by `wfCompletionReflector`.
- `Sheaf.Paper.IntrinsicCompletionCompleted`:
  `completedKoszulFiber`, `completedKoszulUnitComplex`,
  `completedIntrinsicCompletion`, `completedIntrinsicCompletionMap`, and
  `IsCompletedIntrinsicallyDerivedComplete`. Its public presentation transport
  `Sheaf.Paper.IntrinsicCompletion` provides the `intrinsicCompletion`,
  `intrinsicCompletionUnit`, and `IsDerivedCompleteIntrinsic` declarations
  used verbatim in the theorem.
- `Sheaf.Paper.WeilCompletedTensorReflector`: `WfIsComplete`,
  `WfCompleteCategory`, `wfCompletionObj`, `wfCompletionUnit`,
  `wfCompletionReflector`, and `wfCompletion`. The recorded specialization
  already handles separate small-site object/Hom universes.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `isoSectionwiseInverseImage_equivalence` and its canonical constant-ring
  and exact module transport declarations supply the proof's site equivalence.
- `Sheaf.Paper.PbcQbarCompletedPullback` publicly retains
  `Sheaf.Paper.CompletedTowerPullback`: `completedFiniteCoefficientMap`,
  `completedCoefficientComponent`, `completedCoefficientMap`, and
  `completedModulePullback`. This item uses the completed structure map and
  ordinary pullback, not the Qbar specialization named by the current record.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`:
  `SheafOfModules.module_pullback_pushforward_adjunction`. Its existing actual
  small-pro-etale specialization in `Sheaf.Paper.PbcCompletedPullbackActual`
  provides `pbcActualModuleAdjunction`, normalized on tensor-unit sections, and
  `pbcActualDerivedAdjunction`, constructed from that very adjunction with its
  universal derived pair. This is a published specialization, not a new interface.
- Added landed statement dependency `def-wf-automorphism-completed-transport`,
  `Sheaf.Paper.PbcAutomorphismTransport`: `pbcIsoCoefficientMap_isIso`,
  `pbcIsoModulePullback`, `pbcIsoAmbientPullback`,
  `pbcIsoModulePullback_eq_completed`, `pbcIsoOrdinaryDerivedComparison`.
  These declarations supply exactly the canonical H and its normalized
  comparison to the ordinary derived pullback; no new notion is introduced.
- Proof-only imports: `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`
  (`exists_scalarExtensionRingIso`),
  `Sheaf.Paper.WeilCompletedKoszulLimitComparison`
  (`completed_fiber_strict_limit_comparison`),
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
  (`CategoryTheory.Functor.mapDerivedCategory`), and
  `Mathlib.Algebra.Homology.BifunctorShift` (`CochainComplex.mapBifunctor`).
  The general inverse-image interface is publicly retained by the site-equivalence
  module. All recorded statement and available proof interfaces are imported.

### Searches and reuse decision

- `msearch.py ... leanfinder "An automorphism of a scheme preserves derived complete
  completed coefficient modules and commutes uniquely with Koszul completion
  preserving its unit"`: eight algebraic adic-completion hits, no sheaf-derived
  completion statement.
- `msearch.py ... leansearch "derived completion natural unit automorphism pullback
  sheaves"`: eight module pullback/adjunction hits, no full statement.
- `msearch.py ... loogle "Functor.mapDerivedCategory, Adjunction, IsEquivalence"`:
  zero hits; the short identifier was unknown to the search service. Read the full
  declaration `CategoryTheory.Functor.mapDerivedCategory` in Mathlib source instead.
- `msearch.py ... grep "completion.*[Ii]so|[Ii]so.*completion" CategoryTheory`:
  zero hits.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib for completion and
  automorphism names; the item-id search on both project roots found no attached
  declaration. The upstream root only had an unrelated completion-automorphism
  comment in `TorsionControlledFormalRestriction`.
- `Sheaf.Paper.WeilTensorProduct.wfPullbackCompletion_exists` (declaration namespace
  `AlgebraicGeometry.Scheme`) already states the unique comparison at chosen
  canonical representatives. Its signature and proof were read, as were
  `wfIsoPullback_complete`, `wfCompletePullback`, and the private
  `wfPullback_preservesComplete`. No existing public declaration states this full
  node: G-preservation and the actual restricted adjoint equivalence are absent
  from the public comparison, and its representatives are fixed. Therefore an
  `existing: true` binding to that theorem alone would omit clauses. The delivery
  adds one theorem packaging exactly the full statement, using the lower published
  constructions. It does not import the parent `WeilTensorProduct` module, whose
  proof this split lemma is intended to support.

### Edge cases and source check

Read the node's blueprint source `main-20261015/.../def-wf-tensor-product.md`,
its agent-written eight-step specialization, and the recorded dependencies.
The source is the tensor Frobenius sentence; the node supplies its automorphism
and explicit-unit specialization. No statement correction was needed.

For e = identity the coefficient map fixes the same quotient scalars and the
comparison is the unique unit-compatible identity transport. For r = 0 and I = 0,
all Koszul factors are the tensor unit; the constant tower's fiber has the diagonal
unit, and the same assertion applies. The statement allows zero or repeated
entries of a generating list, the zero ring and zero module, and the empty scheme.
It places no lower boundedness condition on C or D. Both realizations are arbitrary
isomorphisms, so even a different realization of the same complex is covered.
The unit equation correctly includes the inverse realization via the published
`intrinsicCompletionUnit`, rather than silently identifying Q(C) with M.

No new nodes, dependency repairs, statement faults, or disputed assertions.

## Second reading by Q04

The dispatcher explicitly forbids starting other agents and delegates independent
review to the maintainer. No independent second reader is claimed here.
The worker's separate clause audit above checks the final declaration against the
node: both preservations, ambient and restricted adjunctions, normalization of
Hom transposes, uniqueness and all representatives. All underlying objects and
canonical maps are reused. The maintainer's independent delivery review remains
separate from this worker audit.

### Validation

The prescribed scompile.py compiled the module in both its sandbox and library
module locations without errors or unexpected warnings. The final module, including
its explicit dependency imports, passed deliver2.py --no-push: `OK (dry run): commit
f62934a5a17 passes the preflight and compiles; nothing pushed`. The wrapper staged
exactly this report, the item node, and its module. The declaration contains one
postponed proof and no helper definitions. A local JSON comparison confirmed that
only lean and the authorized added statement dependency changed; the recorded
signature matches the source verbatim. Only the prescribed scompile.py and
deliver2.py wrappers were used for compilation and delivery checks.
