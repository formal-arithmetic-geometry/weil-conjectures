## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleTorIntervalTriangle` states
`AlgebraicGeometry.Scheme.coefficientProEtale_tor_interval_triangle`, with `sorry`.
Its two helpers have real data: `coefficientProEtaleTorModulesAbelian` explicitly
specializes Mathlib's canonical abelian instance, and `coefficientProEtaleTorTensor`
partially applies the published derived tensor to the given test module in degree zero.
There is no newly chosen tensor product, resolution, map, or cohomology theory.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`lemma-cone-tor-amplitude`, Tag 08G2(2), including its proof hint;
`definition-tor-amplitude`, Tag 08FZ. The unequal-interval assertion follows by
widening to the minimum lower and maximum upper endpoint. The same-interval
assertion is vanishing in that interval, with no endpoint optimality claim.
The item's statement, statement dependencies and proof are unchanged.
No mathematical statement correction is needed; the H13 record repair is detailed below.

Clause-by-clause correspondence:

- An arbitrary scheme is `Y : Scheme.{u}`. An arbitrary commutative coefficient
  ring is `A : Type (max v (u + 1))` with `[CommRing A]`. The two universes remain
  independent. This is precisely the size convention of the recorded Tor predicate:
  any smaller ring can be represented by its universe lift, rather than imposing
  a size equality on the scheme and its coefficients.
- The site is `coefficientProEtaleModelTopology.{u,v} Y`, the existing AsSmall
  model of the small pro-etale site. Its objects and morphisms both have size
  `max v (u+1)`, and the published site equivalence preserves the topology. Its
  constant ordinary ring sheaf is `ConstantCompletion.constant ... A`.
- The unbounded derived category is exactly `ConstantCompletion.D` of that ring
  sheaf, using Mathlib's module sheaves and `HasDerivedCategory.standard`.
  `coefficientProEtaleTorModulesAbelian` is the existing
  `SheafOfModules.instAbelian` with the published `coefficientModelAdditiveSheafify`
  passed explicitly. It resolves an inference ambiguity through old successor-size
  sheafification instances; it supplies no hypothesis and changes no category.
- The triangle is `T : Triangle (...)`, and `hT : T ∈ distTriang (...)` is exactly
  its distinguishedness. The vertices U,V,W are `T.obj₁`, `T.obj₂`, `T.obj₃`;
  the first two given arrows are `T.mor₁`, `T.mor₂`.
- Every degree-zero ordinary module sheaf is quantified as `N : ConstantCompletion.Mod
  (...)`. The helper uses `DerivedCategory.singleFunctor ... 0`, with no flatness,
  finite presentation or constructibility condition on N.
- Its tensor image on objects AND maps is the flip of the curry of
  `SheafOfModules.siteDerivedTensorIndependentCoefficients`, evaluated at N[0].
  This is the published K-flat total tensor of the intrinsic module-sheaf category.
- `∀ N (i : ℤ), ∃ h, (ShortComplex.mk ... ... h).Exact` is the exact cohomology
  segment. Both maps are obtained by composing that actual tensor functor with
  `coefficientModelCohomology ... i` and applying to the given triangle arrows.
  This cohomology abbreviation unfolds to `DerivedCategory.homologyFunctor` on
  the standard localization. The existential `h` is only the zero-composite proof
  required to form a short complex, not a freely chosen replacement arrow.
  `ShortComplex.Exact` is Mathlib's categorical exactness, equivalently equality
  of the image and kernel in this abelian sheaf category.
- The second conjunct quantifies `aU bU aW bW : ℤ`, then exactly the two order
  conditions and the Tor-amplitude hypotheses for the two outside vertices.
  Its conclusion is the recorded `HasCoefficientProEtaleTorAmplitude` for the
  middle vertex in `(min aU aW, max bU bW)`.
- The third conjunct explicitly states the common-interval specialization for
  every `a b : ℤ` with `a ≤ b`, with the same recorded predicates on all three
  vertices. The conjunction ensures the exact segment is unconditional on the
  Tor bounds. There is no boundedness, constructibility, Noetherian, nonzero-ring,
  field, finite-type, or finiteness assumption.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`:
  `AlgebraicGeometry.Scheme.HasCoefficientProEtaleTorAmplitude`,
  `CategoryTheory.HasCoefficientModelTorAmplitude`,
  `CategoryTheory.coefficientModelCohomology`,
  `AlgebraicGeometry.Scheme.coefficientModelAdditiveSheafify`.
  Its retained original `HasProEtaleTorAmplitude` was also read; its ULift
  same-size presentation is unnecessary for this coefficient-sized consumer.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.siteDerivedTensorIndependentCoefficients`, whose source
  constructs the functor through resolving-class localization with its natural
  representative comparison. Its existing owning nodes and the live derived-tensor
  record are preserved; no dependency repair is needed for this consumer.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, `homologyFunctorFactors`, and the proof leaf
  `DerivedCategory.HomologySequence.exact₂`. The specialized sfModelCohomology
  signature and docstring were read; its specialized declaration and all twelve
  owned declarations remain recorded unchanged. This item uses the general
  coefficientModelCohomology already provided by the Tor-amplitude module.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`:
  `CategoryTheory.Pretriangulated`, `Triangle`, `distTriang`, the mathlib_match
  of `def-weil-triangulated-category`.
- The stated proof dependencies are imported without `public`:
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
  (`CochainComplex.exists_isKFlatResolutionIndependentCoefficients`),
  `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`
  (`SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated`), and
  `Sheaf.Algebra.Homology.DerivedTensorResolutionIndependent`
  (`AlgebraicGeometry.Scheme.derivedTensor_resolution_independent`).
  The complete four-step proof plan is in the theorem docstring.

Edge cases checked before stating:

- N=0, a zero triangle, the zero coefficient ring, and the empty scheme are allowed;
  tensor/cohomology vanish and no nonemptiness condition occurs.
- A split triangle with outside amplitudes [0,0] and [2,2] gives [0,2], rather than
  an incorrect intersection or a shifted middle interval.
- Negative endpoints and one-point intervals are included by integer binders.
- Equal intervals give the third conjunct; arbitrary wider intervals are not
  claimed minimal. The order conditions agree with the recorded predicate.
- Non-flat N, for example Z/2 over Z/4, is included: the tensor is derived and
  no ordinary exactness or flatness assumption was substituted.
- Unbounded vertices and unrelated scheme/coefficient universes remain allowed.

Searches (2026-10-21):

- `msearch.py ... leanfinder` query: "Tensor a distinguished triangle with any
  degree zero module sheaf: exact cohomology segment and Tor amplitude of the
  middle term in the minimum lower and maximum upper interval". Eight hits:
  DerivedCategory.TStructure.t, IsGE, IsLE, the two Ext homology-sequence
  applications, and representative-support lemmas. None states all clauses.
- `msearch.py ... loogle '"TorAmplitude"'`: zero hits.
- `msearch.py ... grep 'TorAmplitude|torAmplitudeIn|tor_amplitude' Algebra/Homology`:
  zero Mathlib hits.
- `msearch.py ... leansearch` query: "Tor amplitude of the middle term of a
  distinguished triangle of sheaves of modules, and exactness of cohomology
  after derived tensor with any module". Eight hits, including
  Functor.homologySequence_exact₂, Functor.map_distinguished_exact and
  Module.Flat.rTensor_shortComplex_exact; general homological-functor or flat
  ordinary-module results only, not the Tor predicate and quantitative conclusion.
- `rg` over `lean/WeilConjectures/CategoryTheory/DerivedCategory` and the project's
  homological-algebra and algebraic-geometry modules found the existing
  torAmplitudeIn and the two recorded pro-etale Tor predicates. The upstream
  TorAmplitude module gives a general monoidal-category predicate and widening
  lemmas, not this combined theorem for the recorded ringed-site predicate.
- `rg` of the node id over `lean/WeilConjectures` and `lean/Sheaf` found no module
  for this item. Searching all three new full-name suffixes in Mathlib and both
  project roots found no collisions.

Validation: the final module passed `scompile.py Q34
lem-weil-proetale-tor-interval-triangle <file>` in both sandbox and library modes,
with no errors or warnings (21.8 s / 20.5 s). All universes and variables are
explicit. The only postponed proof is the named item theorem.
No statement dispute or mathematical correction was necessary.

## Returned-delivery repair (H13)

1. `def-weil-derived-cohomology-sheaves`: restored its complete node file
   byte-identically from current live. In particular, N5's existing:false
   `Sheaf.Paper.SfCommonStageWeilCohomology` record, its twelve declarations,
   ownership, and stage-3 work remain intact. The item already imports
   `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude` and uses its
   `CategoryTheory.coefficientModelCohomology`, which is the standard
   `DerivedCategory.homologyFunctor`. No rebind is necessary.
2. `def-weil-derived-tensor`: restored its complete node file byte-identically
   from current live. NE's existing:true
   `AlgebraicGeometry.ProEtale.derivedTensor` record remains intact. The item
   uses the already published intrinsic
   `SheafOfModules.siteDerivedTensorIndependentCoefficients`, owned by
   `lem-weil-pbc-site-derived-tensor-descent` and
   `def-sfb-derived-tensor-sheaves`, for the coefficient-sized site. No ownership
   transfer or new construction is necessary.

The item's `lean.note` now explains both existing-interface uses. There are no
changed dependency nodes or dependency modules in the repaired delivery. The
Lean module is unchanged from the mathematically accepted returned packet.
The advisory about the public Abelian specialization was considered: it supplies
only the canonical Mathlib structure; the stage-2 convention explicitly prohibits
file-local instances, so the accepted declaration is retained.

## Second reading by Q34

A second pass compared the node text, the full final signature and both
restored live dependency records. This pass was performed by the same worker because
the dispatcher brief forbids starting other agents; the maintainer's independent
review is still required. In particular, the exact-segment clause quantifies over
all N independently of the conditional interval assertions, applies the two
composites to the actual given arrows, and uses genuine categorical exactness.
The min/max and common-interval clauses use the recorded Tor predicate verbatim.
No stronger hypotheses or missing clauses were found. The implementation repair
was to fix the canonical abelian-instance universe arguments and to package the
segment as `∃ h, (ShortComplex.mk ... ... h).Exact`, avoiding expensive inference
of an auxiliary kernel limit. This changes neither maps nor exactness. No source
statement correction or new independent notion was needed.

Repair self-check: reopened the item, its module, the four statement-dependency
records, the coefficient-sized Tor/cohomology interface, the existing intrinsic
tensor definition, both retained specialized declarations, and Stacks Tag 08G2(2).
Every hypothesis and clause still matches the correspondence above. Compared
with current live, every item field outside `lean` is identical. Compared with
the returned packet, the Lean file and its recorded signature are unchanged;
the two dependency files now exactly equal live. Both numbered H13 points are
resolved by preserving their ownership rather than rebinding them. The initial
saved-packet dry run passed, but that mechanical result did not resolve H13;
the repaired packet is compiled and checked again before delivery.

Repaired-packet validation (2026-10-21): the unchanged delivered module passed
`scompile.py Q34 lem-weil-proetale-tor-interval-triangle <file>` in sandbox and
library modes (21.8 s / 20.5 s), with no compiler diagnostics. The explicit
byte comparisons and signature self-check above passed.
