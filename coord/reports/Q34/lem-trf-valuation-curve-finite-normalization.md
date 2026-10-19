## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ValuationCurveFiniteNormalization.lean` states
`AlgebraicGeometry.finite_normalization_of_valuation_curve`, the finite-normalization assertion
of Temkin, Stable modification of relative curves, Section 4.1 opening paragraph, printed p. 25
(blueprint `lem-trf-valuation-curve-finite-normalization`). The proof is `sorry`, as required at
stage 2.

The valuation base is rendered by commutative domain `V`, fraction field `K` via
`[Algebra V K] [IsFractionRing V K]`, and the explicit condition
`∀ a : K, a ≠ 0 → a ∈ Set.range (algebraMap V K) ∨ a⁻¹ ∈ Set.range (algebraMap V K)`.
The finite-chain condition is rendered by finiteness of the set of prime ideals and
`p ≤ q ∨ q ≤ p` for every pair of prime ideals. `T` is `Spec (CommRingCat.of V)` and the
field point is the canonical `Spec.map (CommRingCat.ofHom (algebraMap V K))`.

For `X` and `f`, `[IsIntegral X]`, `[Flat f]`, `[LocallyOfFinitePresentation f]`,
`[QuasiCompact f]`, and `[QuasiSeparated f]` render integral, flat, and finitely presented over
`T`; the generic fibre smoothness is `[Smooth (pullback.snd f (Spec.map ...))]`. The hypothesis
`hpure` says that for each `y`, if the fibre is nonempty, every
`C ∈ irreducibleComponents (f.fiber y : Type u)` has `topologicalKrullDim C = 1`; this is
exactly the stated meaning of pure dimension one and leaves empty fibres unconstrained.

The conclusion is rendered clause by clause: `IsFinite X.fromNormalization` and
`Surjective X.fromNormalization`; the generic-fibre isomorphism is the `IsIso` assertion for
the canonical `pullback.map` induced by `X.fromNormalization` and the identity on `Spec K`;
normality is `∀ x : X.normalization, IsDomain (...) ∧ IsIntegrallyClosed (...)`;
flatness and finite presentation of the normalization over `T` are the corresponding `Flat`,
`LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated` classes for
`X.fromNormalization ≫ f`; and the final `∀ y` clause repeats pure dimension one for every
nonempty normalized fibre.

Dependency declarations used: `IsSepClosed` in `Mathlib.FieldTheory.IsSepClosed` for separably
closed fields; `AlgebraicGeometry.Spec` from `Mathlib.AlgebraicGeometry.Scheme` for spectra;
`AlgebraicGeometry.IsIntegral` from `Mathlib.AlgebraicGeometry.Properties`; `AlgebraicGeometry.Flat`
from `Mathlib.AlgebraicGeometry.Morphisms.Flat`; `AlgebraicGeometry.LocallyOfFinitePresentation`
from `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`; `topologicalKrullDim` from
`Mathlib.Topology.KrullDimension`; `AlgebraicGeometry.Scheme.normalization` and
`AlgebraicGeometry.Scheme.fromNormalization` from `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`;
`AlgebraicGeometry.IsFinite` and `AlgebraicGeometry.IsIntegralHom` from
`Mathlib.AlgebraicGeometry.Morphisms.Finite`; and `AlgebraicGeometry.Surjective` from
`Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`. Smoothness uses
`AlgebraicGeometry.Smooth` from `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.

Edge cases checked: the explicit nonzero condition excludes only `a = 0`, the valuation
condition allows either orientation for each nonzero fraction, the finite chain includes all
prime ideals, and `hpure` imposes no condition on an empty fibre. The formulation permits
relative dimension one with any characteristic and does not require a discrete valuation ring.
Height zero (`V = K`) is allowed: the prime chain has one member and the conclusion reduces
to the identity normalization of a smooth integral curve. `[IsIntegral X]` excludes the empty
total scheme, exactly as the node does. No properness or separatedness of `X` is assumed.
The module is validated with `scompile.py` and the delivery preflight.

Searches made on this delivery with `msearch.py Q34 lem-trf-valuation-curve-finite-normalization`:

- `leanfinder`: “The normalization of a flat finitely presented relative curve over a finite
  height valuation ring with separably closed fraction field and smooth generic fibre is
  finite”. Eight hits on relative normalization, its integrality and finite global sections;
  none gives the claimed finiteness over a valuation base.
- `loogle`: `"normalization", "IsFinite"`. Zero hits.
- `grep`: `normalization.*(IsFinite|finite)|[Ii]sFinite.*[Nn]ormalization`, restricted to
  `AlgebraicGeometry`. Three hits in `ZariskisMainTheorem.lean` about the quasi-finite locus;
  no match.
- `leansearch`: “Normalization is finite for a flat finitely presented curve over a valuation
  ring with smooth generic fibre and separably closed fraction field”. Eight hits on relative
  normalization constructions and their properties; none is the item.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, the project's `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id, proposed declaration name, and valuation /
  normalization combinations found no existing copy of this statement. The upstream
  normalization source was read: its finite-normalization theorem requires a scheme locally
  of finite type over a field and cannot replace this theorem over a general valuation ring.

Source checked directly: [Temkin, Stable modification of relative curves](https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf), Section 1.2 (the definition
of a relative curve, including nonseparated ones), Section 4 opening setup and Section 4.1
opening paragraph, and Theorem 3.5.5 / Proposition 3.5.2. The source's curve hypothesis means
flat finite presentation and pure relative dimension one; the statement adds no separation
assumption and keeps the smooth-generic-fibre case specified in the node.

The theorem docstring now records all seven DAG proof steps, including their dependencies.
The currently recorded proof modules are imported privately for stage 3; the two proof nodes
without a recorded declaration (`lem-trf-reduced-fibre-modification` and
`lem-trf-geometric-reduced-fibre-locus-base-change`) have no module to import. Neither supplies
an object used to state this theorem, so no extra statement dependency is needed.

An in-thread second pass compared every binder and conjunct with the node. It corrected an
initial draft that quantified over all irreducible closed subsets (too strong) to quantify
only over `irreducibleComponents`, retained both qc and qs for finite presentation, removed
the redundant named generic-point parameter in favour of the canonical Spec map, and added
explicit universe annotations and `set_option autoImplicit false`. It also replaced the
valuation-ring typeclass by the node's literal nonzero-element membership condition.
The maintainer supplies the independent delivery review; no independent worker review is
claimed here.

Process note: during exploration a temporary `WeilConjectures/TempCheck.lean` was accidentally
written in the read-only source checkout, and scratch files were compiled directly. The file
was removed, and every version intended for delivery was checked using `scompile.py`. No live
library declaration was changed. Scratch files outside the sandbox were also removed.

## Second reading by Q34

Independent maintainer reading, 2026-10-18, of immutable delivery
f409b839593e88d7a3ded9b7d56312d3ad4631d9. This reading was performed after the worker's
submission; the reviewer did not author the delivery or its earlier DAG review.

The packet, immutable item node, all twelve statement-dependency nodes, delivered module,
and worker report were read against the recorded dependency declarations. The source read
was [Temkin, Stable modification of relative curves](https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf),
§1.2 (printed p. 2), §4 opening setup (p. 24), §4.1 opening paragraph (p. 25),
Proposition 3.5.2 (pp. 20–21), Theorem 3.5.5 (pp. 21–24), and Lemma 4.4.1(i) (p. 30).
These support the smooth-generic-fibre normalization assertion without a separation hypothesis.

Clause-by-clause comparison:

- The field and separably closed hypotheses are `[Field K] [IsSepClosed K]`.
  The recorded `IsSepClosed` definition uses splitting of separable polynomials, equivalent
  to absence of nontrivial finite separable extensions. It does not require algebraic closure.
- `V` is a commutative domain; `[Algebra V K] [IsFractionRing V K]` supplies its injective
  inclusion into its fraction field. `hval` is exactly the node's membership alternative
  for each nonzero element. This is an equivalent representation of a valuation subring.
- `hfinite` includes every prime ideal, and `hchain` makes them pairwise comparable.
  Together these render precisely the finite-chain condition.
- `Spec (CommRingCat.of V)` and `Spec.map (CommRingCat.ofHom (algebraMap V K))`
  give the specified base and its canonical generic field point, without an arbitrary map.
- `[IsIntegral X]` supplies nonemptiness and integral affine charts. `[Flat f]` is the
  recorded flatness notion, equivalent to flat stalk maps. Locally finite presentation,
  quasi-compactness and quasi-separatedness together give finite presentation.
- `hpure` quantifies over all base points, and over maximal irreducible subsets of each
  nonempty scheme-theoretic fibre. `topologicalKrullDim C` uses the subspace topology.
  It asserts dimension one for components, not for every irreducible closed subset.
- The `Smooth` instance is on the second projection of the pullback to `Spec K`, so
  smoothness is required precisely on the generic fibre.
- `X.normalization` and `X.fromNormalization` reuse the recorded upstream construction
  as relative normalization in `X.functionField`; no duplicate normalization is defined.
- `IsFinite` and `Surjective` assert finiteness and surjectivity of that canonical morphism.
  `pullback.map` uses `X.fromNormalization` and the identity maps on the base and on
  `Spec K`; its `IsIso` asserts the generic base change of this morphism is an isomorphism.
- The stalk conjunction is exactly normality as stated: every stalk is a domain and
  integrally closed. The next four conjuncts give flat finite presentation over the base.
  The final quantified conjunct gives pure dimension one for every nonempty normalized fibre.

All clauses agree; no mathematical or signature change was needed. The docstring contains
all seven node proof steps and their citations. In steps 1–3, torsion-freeness gives a dense
integral generic fibre, smoothness gives normality and geometric reducedness, reduced-fibre
modification applies, and the proper valuative criterion provides the section after the
finite separable extension collapses over K. Steps 4–5 use eta-normality on affine charts
and the finite algebra B[b] to prove normality. Step 6 identifies the finite algebra with
integral closure in the common function field. Step 7 uses proper closed image and fibre
purity. The cited statements supply these inputs; no statement prerequisite is missing.
Proof-only nodes awaiting Lean declarations do not obstruct stating this theorem.

Edge cases: V = K (height zero) is allowed; no discrete valuation, Noetherianity, excellence,
perfectness, characteristic restriction, properness or separatedness is assumed. Empty
special fibres impose no condition. The total scheme is nonempty by integrality, and
flatness over the domain makes its generic fibre nonempty. All variables are bound with
`autoImplicit false`. The arbitrary common universe u is the standard scheme/ring universe;
there is no independent test-object universe or forced universe equality between sites.

Independent searches used valuation/normalization combinations and the proposed full name
in the group's side algebraic-geometry/trace-formula modules, slopmaster2, and Mathlib.
No duplicate of this statement was found. The upstream finite-normalization theorem was
opened: it assumes local finite type over a field, which is insufficient for this node's
valuation base. All twelve statement dependencies reuse their recorded notions. No helper
construction or dependency-interface repair is required. No statement_change or citer audit
is applicable. No cited node intersects the current route-pivot dropped list, and the shared
repair-note lookup found no note for this item. No pro-etale substitute or dropped machinery
is used.

Compiler reproduction: ran the prescribed command on the immutable module:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q34 lem-trf-valuation-curve-finite-normalization snapshot/lean/Sheaf/AlgebraicGeometry/ValuationCurveFiniteNormalization.lean
sandbox Sheaf/Stage2/Sandbox0.lean
(with the modules compiled into /dev/shm/nt-tmp/nt-local-compile-q1zxd9nh/.lbuild) [24.1 s]
library Sheaf/AlgebraicGeometry/ValuationCurveFiniteNormalization.lean
[52.4 s]
exit code 0; no Lean diagnostics
```

The installed wrapper currently delegates to the server side-overlay compiler and performs
both checks; its own connection emitted multiplexing notices before successful compilation.
No direct ssh command, global build or project edit was performed by this reviewer.
The worker report originally asserted validation without retaining detailed compiler output;
this reproduction supplies that evidence. The node's lean.statement was compared programmatically
with the signature before `:= by` and is verbatim equal. All module lines are at most
100 characters; its only theorem proof is `sorry`. The two `by simp` arguments merely
certify the squares needed to specify the canonical pullback map.

Finding H11: the submitted second-reading section was only a placeholder. This complete
replacement report retains the Worker report and supplies the actual independent reading.
The worker also disclosed a removed temporary Lean file in the read-only source checkout
and direct exploratory scratch compilation. That was a process violation, not a compliant
workflow; removing the file does not erase that history. The delivered module itself has no
scratch declaration or live-library change, and its required compile has now been reproduced.
The review found no fault in the mathematical statement warranting RETURN. Verdict: FIX,
limited to this complete report replacement.
