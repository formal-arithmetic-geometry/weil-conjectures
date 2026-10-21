## Worker report

Item: `lem-sfb-constructible-local-tor-etale-origin`.
Module: `Sheaf.AlgebraicGeometry.ConstructibleLocalTorEtaleOrigin`.
Declaration: `AlgebraicGeometry.ProEtale.constructible_localTor_iff_etaleOrigin`.
The sole theorem is stated with the whole proof `sorry`; its docstring gives all five
steps of the node's proof. There are no new definitions, new nodes, or statement changes.

The statement is the equivalence in the node, on the existing equivalent coefficient-sized
small site models. The derived inverse image is written explicitly on a representative,
using the existing canonical `constructibleComparisonComplexPullback`. This avoids adding
a new choice of derived functor or changing the coefficient universes.

Hypotheses and clauses, in order:

| Node text | Lean rendering |
| --- | --- |
| X is a scheme | `(X : Scheme.{u})` |
| X is quasi-compact | `[CompactSpace X]`, with no Hausdorff condition |
| X is quasi-separated | `[QuasiSeparatedSpace X]`, the recorded equivalent scheme condition |
| A is a discrete commutative Noetherian ring | `(A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]`; discreteness means constant sheaf coefficients and does not require a topological-ring structure |
| Small etale and pro-etale sites | `smallModelComparisonEtaleTopology.{u,v} X` and `coefficientProEtaleModelTopology.{u,v} X`, the already recorded AsSmall-equivalent presentations of the original sites |
| Constant coefficient ring sheaf | `ConstantCompletion.constant` on each of those topologies, literally the existing `constantSheaf` applied to `CommRingCat.of A` |
| Module sheaves and unbounded derived categories | `ConstantCompletion.Mod` is `ringedSiteModules` of the underlying ring sheaf, and `ConstantCompletion.D` is `DerivedCategory` with `HasDerivedCategory.standard` |
| Arbitrary M in the pro-etale derived category | The sole object binder M has precisely `ConstantCompletion.D` of the pro-etale constant ring; no boundedness, completeness, constructibility or origin binder is present |
| Every cohomology sheaf is constructible | `∀ q : ℤ, IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A ((coefficientModelCohomology _ q).obj M)` |
| For every site object U | `∀ U : coefficientProEtaleSiteModel.{u,v} X` |
| A covering family of U | `∃ S : Presieve U, Sieve.generate S ∈ coefficientProEtaleModelTopology X U`; the arrows selected by S form the family, with no finiteness restriction |
| A separate Tor interval on each covering member | `∀ V f, S f → ∃ a b : ℤ, HasCoefficientModelTorAmplitude ... a b` |
| Restriction to the actual slice ringed site | The ring is `(ConstantCompletion.constant ... A).over V`, and the object is `(coefficientModelSliceRestriction ... V).obj M` |
| Ordered bounds and every degree-zero module on that slice | `HasCoefficientModelTorAmplitude` begins with `a ≤ b` and tests every slice module M, inserted with `HomologicalComplex.single ... 0`, on every K-flat representative |
| Vanishing for all q outside the interval | That predicate requires `IsZero` of the actual total-tensor cohomology for every `q < a ∨ b < q` |
| Conditions (1) and (2) are equivalent | The outer connective is `↔`, with the constructibility and local Tor conditions joined by `∧` on its left |
| A bounded constructible etale derived object C | `∃ C : ConstantCompletion.D (ConstantCompletion.constant (smallModelComparisonEtaleTopology X) A), IsCoefficientBoundedConstructibleEtale X A C ∧ ...`; the recorded predicate requires constructibility in every degree and vanishing outside an ordered finite interval |
| C has a uniform finite Tor interval | `∃ a b : ℤ, HasCoefficientModelTorAmplitude _ C a b`, testing every degree-zero etale constant-ring module, with `a ≤ b` inside the predicate |
| The canonical isomorphism nu_X^* C ≅ M | `∃ P : ConstantCompletion.Cx ...`, `Nonempty ((ConstantCompletion.Q _).obj P ≅ C) ∧ Nonempty ((ConstantCompletion.Q _).obj ((constructibleComparisonComplexPullback X A).obj P) ≅ M)` |

The final representative witness is an expression of the specified inverse image, not an
additional mathematical assumption: Q is essentially surjective, so every C has such a P.
The comparison complex functor is the existing termwise module Kan-extension/sheafification
inverse image along the canonical constant-section ring map. The localization
factorization in `constructibleComparison` identifies Q of its value on P with the
canonical derived inverse image of C. Exactness makes this independent of P, including
unbounded representatives. No arbitrary morphism, mere Nonempty functor, or alternate
tensor construction is used. Existential quantifiers retain the possibility that C has
many representatives and that its Tor interval differs from its cohomology interval.

Dependency declarations read and used, directly or through the recorded interfaces:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`, through
  `QuasiSeparatedSpace X` and their recorded equivalence for the terminal scheme morphism.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and `Scheme.Etale`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `Scheme.ProEt.topology`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`, via
  `ConstantCompletion.constant` in `Sheaf.Paper.ConstantCompletionEquivalence`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, via
  `ConstantCompletion.Mod` in `Sheaf.Paper.ConstantCompletionEquivalence`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory`, via `ConstantCompletion.D`, `ConstantCompletion.Cx`, and
  `ConstantCompletion.Q` in `Sheaf.Paper.ConstantCompletionEquivalence`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison` specifies the original geometric morphism.
  The coefficient-model presentation is the transported inclusion and canonical
  ring/module pullback in `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonData`:
  `constructibleComparisonRingMap`, `constructibleComparisonPullback`, and
  `constructibleComparisonComplexPullback`. These are existing real constructions.
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`:
  `ProEtale.proEtaleClassicalSheavesModules` supplies exactness of the original module
  comparison; imported through the finite-Tor comparison proof dependency.
- `Sheaf.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules`:
  `Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf`.
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`:
  `ringedDerivedRestrictionGeneral` and `ringedDerivedRestrictionSized`, via
  `CategoryTheory.coefficientModelSliceRestriction` in
  `Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `overMap`, and `overFunctorMap`; rings use `Sheaf.over`
  and the topology is `GrothendieckTopology.over`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`:
  `ProEtale.derivedTensor`, the fixed-scalar presentation of the K-flat tensor.
  The intrinsic-ring presentation used by the recorded Tor predicate is the actual
  `ringedKoszulTensor` total tensor, tested on `IsKFlatIndependentCoefficients` models.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`, via
  `CategoryTheory.coefficientModelCohomology`, already supplied by the landed
  `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude` module.
- `Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules`:
  `Scheme.IsCoefficientBoundedConstructibleEtale` and
  `Scheme.IsCoefficientConstructibleEtaleModule`.
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`:
  `CategoryTheory.HasCoefficientModelTorAmplitude`,
  `Scheme.HasCoefficientProEtaleTorAmplitude`, and
  `Scheme.HasFiniteCoefficientProEtaleTorAmplitude`. Only the already recorded universal
  K-flat tensor test is used, on both the etale and pro-etale ringed sites.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`, the etale
  fixed-scalar presentation of the same K-flat total tensor; imported through the
  finite-Tor comparison.

Proof dependencies are imported: `hasFiniteCoefficientProEtaleTorAmplitude_iff_locally`
in `Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal`, `constructibleComparison` in
`Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`, and
`finiteTorComparisonNoetherian` in
`Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`, together with the
recorded pro-etale tensor module. The local-global module is public because its actual
slice-restriction construction occurs in this theorem's signature.

Source and edge checks:

- Read local `literature/stacks-project/proetale.tex`,
  `lemma-compare-constructible-derived` (Tag 09AL) and
  `lemma-describe-constructible-complexes` (Tag 09C2), including its proof's uniform
  interval and the small omitted Tor-descent argument. The proof plan uses exactly the
  node's recorded comparisons to isolate these steps; no derived completeness is added.
- Empty X: an empty covering presieve is permitted when covering; no `Nonempty` or
  nonzero hypothesis occurs. The zero derived object has an ordered interval, e.g. [0,0].
- Zero ring and zero object: neither `Nontrivial A` nor nonvanishing is required; both
  sides allow the zero complex and its zero representative.
- The unit A_X and its shifts: a one-degree Tor interval is allowed (`a = b`), and bounds
  are arbitrary integers, covering positive and negative shifts.
- A module such as Z/2 over Z/4 is not incorrectly accepted on Tor grounds merely for
  having constructible degree-zero cohomology: tests run over every module, and its
  unbounded Tor fails the finite-Tor condition on a nonempty point site.
- A sum of infinitely many nonzero shifts on a point is allowed as M but fails the local
  Tor condition; boundedness is a conclusion, not a binder or a silent restriction.
- The separate universe v permits coefficients larger than the scheme universe; no
  equality of site-object and original site-morphism universes is imposed.

Searches for an existing exact statement:

- `msearch.py ... leanfinder`: "A constructible proetale complex locally of finite Tor
  dimension is the inverse image of a bounded constructible etale complex of finite Tor
  amplitude". Eight hits concerned scheme/ring etaleness (`IsEtale.of_comp`,
  `RingHom.Etale.propertyIsLocal`, `Algebra.Etale.comp`, etc.); none was the criterion.
- `msearch.py ... loogle`: `"TorAmplitude", "Constructible"`. Zero hits.
- `msearch.py ... grep`: `torAmplitude|finiteTorDimension|constructible.*complex`.
  Four hits in `Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean` concern
  constructible sets and polynomial complexity, not derived complexes.
- `msearch.py ... leansearch`: "A constructible proetale derived complex has locally
  finite Tor dimension if and only if it is the inverse image of a bounded constructible
  etale complex with finite Tor amplitude". Eight hits included
  `DerivedCategory.isLE_Q_obj_iff`, scheme etaleness, and degree-zero Ext size; none
  expressed this theorem.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  the item id, the prospective declaration name, comparison-derived names and local
  Tor/etale-origin phrases. No exact existing criterion. Read the nearby upstream
  `FiniteCoefficient/Derived/EtaleOriginHomology.lean`: its bounded-origin lemmas start
  with already bounded or already origin-defined predicates, and do not give this
  local-Tor criterion on arbitrary unbounded M. Reused the existing coefficient-model
  comparison and Tor declarations instead of duplicating any notions.

Validation: the initial statement compiled cleanly through `scompile.py`, both as a
sandbox file and under its actual library module name. Final wrapper checks follow below.
No `STATEMENT-DISPUTED` or source-statement fault was found.

## Repair of returned delivery

The maintainer returned immutable head `637a5d5f856b` for H13: the packet unnecessarily
rebound `def-weil-derived-cohomology-sheaves` from the live N5 record to Mathlib's general
homology functor. Removed that dependency node file from this delivery. The existing
`coefficientModelCohomology` in `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`
already provides precisely the cohomology used by the item, so no dependency repair is
needed. The N5 binding and its twelve declarations remain owned by their existing node.
There are no dependency modules in this repaired packet.

The item module and item node are byte-identical to the retained returned packet.
The module SHA256 is
`207b7bb891df34f798b2bb32e4637bba58582166775a90d531cf9ef6c55138b7`.
Compared the item's node with the current read clone: only `lean` differs. The theorem
signature is verbatim in `lean.statement`; every universe and variable is explicitly
bound, and the only postponed proof is the one named theorem's whole-proof `sorry`.

## Second reading by Q11

The maintainer's independent reading of immutable head `637a5d5f856b`, reproduced in
the repair brief, accepted the item's mathematical statement: qcqs X, Noetherian A in
the coefficient-sized convention, constructible H^q and exactly the local Tor condition
of `hasFiniteCoefficientProEtaleTorAmplitude_iff_locally`, equivalent to a bounded
constructible etale C with `HasCoefficientModelTorAmplitude`, and the canonical
termwise pullback isomorphic to M via a representative P. It also accepted the edge
cases, proof docstring, verbatim signature and sorry-only proof. The sole identified
fault was the unnecessary dependency rebind; the repair removes its node file and
retains the independently accepted item unchanged. The repair self-check reread the
item signature and the landed definition of `coefficientModelCohomology`: the latter
is directly `DerivedCategory.homologyFunctor` at `HasDerivedCategory.standard`.

Validation of the repaired packet is recorded by the fresh server compile and delivery
dry run; the initial retained packet's dry run also passed, confirming that H13 was
an independent-review finding rather than a compiler or preflight error.
