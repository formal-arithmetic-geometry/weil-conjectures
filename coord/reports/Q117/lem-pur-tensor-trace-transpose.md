## Worker report

`lean/Sheaf/Paper/TensorTraceTranspose.lean` states
`AlgebraicGeometry.ProEtale.tensorTraceTranspose`, with its sole proof `sorry`.
Its real auxiliary constructions name the canonical Koszul symmetry, inverse
projection/trace composite, the existing exceptional tensor mate with the source
symmetry, its integration transpose, the canonical coefficient realization, and
the two-component projection-isomorphism domain. All belong to this node and are
listed in `lean.declarations`; none introduces an independent mathematical notion.
No node statement, dependency list, proof plan, or dependency binding is changed.

The saved packet was inspected first and subjected to `deliver2.py --no-push`.
Its first diagnostic was that the Probe modules belonged to no delivered node.
Those files are preserved under `scratchpad/`, outside the delivered Lean tree.
The intended saved module then timed out at 60 seconds, confirmed by the wrapper.
Self-review also found that its theorem omitted the bounded constructible and
finite-Tor conditions, omitted the k-scheme hypotheses, imposed separate ambient
adjunction/boundedness/braiding assumptions, and put theta before 1 tensor P.
The repaired statement removes those defects and states naturality explicitly.

Hypothesis and clause correspondence:

- The finite field, algebraic closure k, prime ell distinct from the characteristic,
  finite coefficient extension inside the fixed closure, quotient ring, and n >= 1
  are exactly `P : PurityFiniteSetting`, with `P.field`, `P.coefficients`,
  `P.extension`, `P.level`, and `P.level_pos`. The intrinsic coefficients are
  `P.Ring`; the standard fixed-scalar size lift is `P.Coefficient`. Finiteness is
  supplied by the existing quotient-finiteness theorem, not a new assumption.
- The schemes V and S have their `Over (Spec (.of P.field.k))` structures, and their
  structure morphisms have `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`.
  The named morphism f is a morphism over k with the same three properties.
  These express all of the node's separated finite-type k-scheme setting.
- `c : Compactification f` specifies coordinates for compact supports. This is a
  choice of the existing compactification, not an additional existence condition:
  the finite-type field setting admits one by Nagata (also the construction used
  in the recorded `P.comparedCompactification`). The identity is stated for every
  such choice. `c.hasCompactification` is installed by an instance binder.
- `L : Scheme.proEtaleDerivedCategory V P.Ring` is the original arbitrary intrinsic
  pro-etale object. `_hL` is the published
  `Scheme.intrinsicFiniteTorsionConstructible ... V L`, precisely D^b_c, without
  finite Tor amplitude imposed on L.
- `K : Scheme.proEtaleDerivedCategory S P.Ring` is the original arbitrary intrinsic
  pro-etale object. `_hK` uses the dependency's exact
  `WeilConjectures.finiteTorConstructible ... S K`, precisely D^b_ctf.
- `L₀`, `K₀`, `_eL`, and `_eK` retain arbitrary etale representatives of these SAME
  objects. `tensorTraceRealization` is literally the derived equivalence of the
  published `finiteCoefficientIntrinsicRealization`, with the existing finite
  coefficient theorem supplying its instance. Thus the witnesses do not replace
  L or K by a smaller domain or specify an arbitrary operation. Bounded
  constructible pro-etale objects have such representatives by etale origin.
- `_hPF : tensorTraceProjectionDomain P f c L K` is exactly the conjunction of
  invertibility of the canonical pro-etale `projectionMap` at (L,K) and
  (omega_f,K), in the fixed-scalar presentation obtained by the inverse of that
  canonical coefficient equivalence. Its omega is the recorded
  `comparedDualizing P f`, namely comparison pullback of etale f^! of the unit.
  This is the unit-normalized model of the recorded exceptional inverse image.
- The universal `t` is an arbitrary trace in these comparison coordinates,
  `Etale.rightDerivedLowerShriek ... f |>.obj L₀ ⟶ 𝟙_ _`. Compact-support
  comparison, the coefficient unit comparison, `_eL`, and full faithfulness on
  bounded-below representatives identify this Hom set with the original
  Hom(Rf_! L,A_S). Hence all original traces are included. P is its uniquely
  determined exceptional transpose, written explicitly as
  `(Etale.rightDerivedUpperShriekAdjunction ... f).homEquiv L₀ (𝟙_ _) t`.
  The letter P in the Lean binder names the coefficient setting, not this map.
- `Etale.tensorTraceProjection` implements the node's Pi followed by integration:
  apply Rf_! to the canonical symmetry f^*K tensor L -> L tensor f^*K,
  invert the existing projection component, insert the symmetry
  Rf_!L tensor K -> K tensor Rf_!L, apply 1 tensor t, and apply the right unitor.
  These are the specified canonical maps, without an arbitrary endpoint arrow.
- `Etale.tensorTraceTheta` uses the existing
  `Etale.dualizingComplexTensorMap` after the canonical source symmetry. The
  existing map is the exceptional transpose of inverse projection followed by
  counit tensor 1 and the left unitor; the two target symmetries in the node
  cancel by unitor naturality. Its source is exactly f^*K tensor omega_f.
- The first conclusion is `(1 tensor transpose(t))` FOLLOWED BY theta equals
  `tensorTraceIntegrated`, the exceptional transpose of that inverse
  projection/trace composite. Both sides are mapped through comparison inverse
  image followed by the canonical coefficient realization, so this is an
  equality in the intrinsic pro-etale category, expressed in the retained
  representative coordinates. Canonical pullback/tensor comparisons and `_eL`,
  `_eK` identify its source with f^*K tensor L and its target with Rf^!K.
- The second conclusion states naturality: for every representative K₁ whose
  intrinsic realization is D^b_ctf and satisfies the same projection assumptions,
  and every arrow a : K₀ -> K₁, the integrated transpose followed by f^!(a)
  equals (f^*(a) tensor 1_L) followed by the integrated transpose at K₁.
  These are the naturality square's two paths, again mapped to the intrinsic
  pro-etale category. Combined with the first equality, this is naturality of
  the asserted equality on exactly the stated domain.
- There is no smoothness, invertibility of the trace transpose, orientation of
  omega_f, or finite-Tor condition on omega_f. There is no ambient pro-etale
  exceptional adjunction hypothesis. All operations use the constructible
  comparison adjunction of the recorded cohomological-smoothness interface.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, its
  `Ring`, `Coefficient`, and field/extension/positive-level data; imported through
  the recorded `Sheaf.Paper.CohomologicalSmoothnessComparison`.
- `Sheaf.Paper.CohomologicalSmoothnessComparison`: `comparedDualizing`, and the
  canonical etale `dualizingComplexTensorMap` consumed by `comparedTensorClause`.
  This is the current recorded def-pur-co-smoothness interface.
- `Sheaf.Paper.ExchangeProjection` (source inspected): the exact `projectionMap` and
  `projectionMapOfCompactification` that its `finiteExchangeProjection` uses.
  The defining smaller `WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekProjection`
  is imported and its projection component used directly, with no dummy Cartesian square.
- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`;
  `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` (transitively imported):
  `Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`:
  `finiteCoefficientIntrinsicRealization` and its recorded exact equivalence.
  Deriving this exact equivalence is the same canonical coefficient realization
  used by `sfIntrinsicDerivedEquivalence` in the exceptional dependency.
- Finite derived tensor/pullback and compact supports are the existing
  `Etale.derivedTensor`, `Etale.upperStar.leftDerivedFunctor`,
  `Etale.rightDerivedLowerShriek` in the canonical comparison coordinates; the
  exceptional Hom bijection is `Etale.rightDerivedUpperShriekAdjunction.homEquiv`.
  These are the defining constituents of the recorded
  `sfFiniteExceptionalFixed` = Rnu_* then etale f^! then nu^*. No private version
  of the exceptional functor, tensor, pullback or compact-support functor is made.
  The smaller constituent imports are used because importing the full exceptional
  dependency beside ExchangeProjection duplicates `upperStarIsoLowerStarInv`
  between the finite and legacy Iso modules; importing finite projection beside
  the recorded cohomological-smoothness module duplicates `laxMonoidal_Q`.
  The wrapper confirmed both diagnostics. The retained import set uses one
  published version of each construction and the recorded comparison interface.
- `Etale.derivedBraidedCategory` supplies the specified Koszul symmetry without
  assuming an arbitrary braiding or choosing a mere Nonempty endpoint iso;
  `Etale.derivedTensorRightUnitor` supplies the existing tensor-unit constraint.
  Generic typing of the symmetry retains the coefficient-category object
  universe independently of the small-site universe.
- Scheme properties are Mathlib `Scheme.Over`, `Scheme.Hom.IsOver`,
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` as prescribed by the
  convention-only def-weil-scheme-morphism-properties node.

Edge cases checked: n = 1 is included by the positive-level setting; no divisibility
of the level by a ramification index is imposed. Zero L, zero K, identity f, empty
V, empty S, and noninvertible or zero trace transposes are admitted. Only K has
finite Tor amplitude. Independent coefficient-category object universes are
bound explicitly, and Scheme.{u} retains its small-site universe convention.
Every helper has real data, every theorem has `sorry`, and the sole theorem's
docstring contains all four proof steps. No mathematical node fault was found.

Searches (repeated during repair):

- `msearch.py leanfinder`, query "Tensoring the adjoint transpose of a trace with a
  pullback and applying the exceptional tensor map equals the adjoint transpose
  of coefficient integration": 8 results, concerning linear-map trace/contraction,
  tensor-product Hilbert adjoints, and character modules; none is this statement.
- `msearch.py loogle`, query
  `CategoryTheory.Adjunction.projectionTensorMap, CategoryTheory.Adjunction.homEquiv`:
  0 results; projectionTensorMap is not indexed by that Mathlib service. Its
  published project source was opened separately and is used through the
  canonical tensor map, not restated as a theorem.
- `msearch.py grep`, query `projectionTensorMap|tensorTrace|trace.*[Tt]ranspose`
  in Mathlib CategoryTheory: 0 hits.
- `rg` in the upstream WeilConjectures and current `lean/Sheaf` for tensorTrace,
  trace/transpose combinations, and all proposed full declaration names:
  no existing statement of this node and no name collisions. The existing
  TraceTransposeBaseChange treats a different identity. `dag/lean_names_upstream.json`
  has no binding for this item. The original node already records related
  LeanFinder, Loogle and grep searches with no exact match.

Validation is through the prescribed scompile.py and deliver2.py wrappers only;
no global build, direct git mutation, or write to either source repository was used.

Final per-file wrapper validation: sandbox compile passed in 21.3 seconds and
library confirmation passed in 20.3 seconds, with no warnings. The local packet
self-check confirms one owned Lean module, six real auxiliary definitions and one
postponed theorem, all seven names recorded, a verbatim theorem signature, no
line above 100 characters, and only the item's `lean` field changed.

## Second reading by Q117

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
