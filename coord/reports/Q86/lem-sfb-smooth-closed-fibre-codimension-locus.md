## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothClosedFibreCodimensionLocus` gives the
literal set introduced as G_c in the node and states the complete node as
`AlgebraicGeometry.smooth_closed_fibre_codimension_locus`. Its only theorem proof
is `sorry`; nothing is proved in this delivery. The auxiliary definition
`AlgebraicGeometry.Scheme.Hom.fibreCodimensionLocus` has real data: the displayed
universal local-ring inequality. This is a helper for the very set introduced in
the item's statement, allowed in the owning module by the missing-helpers rule;
it is recorded in `lean.declarations`. No separate independent notion is added.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes and the named morphism are `{X S : Scheme.{u}}` and `(f : X ⟶ S)`.
- Noetherian S is `[IsLocallyNoetherian S] [CompactSpace S]`, precisely the two
  properties specified by the node, without a separation assumption.
- Smoothness is `[Smooth f]`. The remaining finite-presentation conditions are
  `[QuasiCompact f] [QuasiSeparated f]`. Mathlib's Smooth instance already gives
  `LocallyOfFinitePresentation f`; an extra hypothesis for that consequence is
  unnecessary. No finite type, properness, separatedness, relative dimension,
  nonemptiness, or surjectivity hypothesis is added.
- The closed subset is `(Z : Set X) (hZ : IsClosed Z)`. It is not replaced by
  extra closed-subscheme data in the statement.
- The nonnegative integer c is `(c : ℕ)`, including zero, cast into `WithBot ℕ∞`
  for comparison with `ringKrullDim`.
- The fibre X_s is `f.fiber s`, Mathlib's pullback along
  `S.fromSpecResidueField s`. The inverse image Z_s is membership
  `f.fiberι s z ∈ Z`, equivalently `(f.fiberι s) ⁻¹' Z`.
- G_c is `f.fibreCodimensionLocus Z c`. Its defining predicate quantifies over
  every `z : f.fiber s` in Z_s and requires
  `(c : WithBot ℕ∞) ≤ ringKrullDim ((f.fiber s).presheaf.stalk z)`.
  This is dimension of the local ring, not local topological dimension.
- Constructibility is the first conjunct
  `Topology.IsConstructible (f.fibreCodimensionLocus Z c)`.
- The second conjunct quantifies over every `s`, field `K`, and
  `[Algebra (S.residueField s) K]`. The morphism is exactly
  `Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K))`.
  The extended fibre is its pullback with `f.fiberToSpecResidueField s`.
  Membership of its points in the closed subset is tested by the first pullback
  projection followed by `f.fiberι s`. The right-hand bound uses stalks of this
  extended fibre. The equivalence preserves AND reflects the all-points bound;
  it does not assert pointwise equality of stalk dimensions.
- The third conjunct quantifies over every `S' : Scheme.{u}` and `v : S' ⟶ S`.
  The new structure morphism is `pullback.snd f v`, the inverse-image subset is
  `(pullback.fst f v) ⁻¹' Z`, and its locus equals
  `v ⁻¹' f.fibreCodimensionLocus Z c`. There is no hypothesis at all on S'.
- The fourth conjunct independently uses bound 1 and is the equivalence with
  `∀ W ∈ irreducibleComponents (f.fiber s), ¬ W ⊆ (f.fiberι s) ⁻¹' Z`.
  Thus the criterion concerns containment of an entire component, not merely
  meeting every component or equality to a component.
- The last two conjuncts say explicitly that `IsEmpty (f.fiber s)` or the equality
  `(f.fiberι s) ⁻¹' Z = ∅` puts s in G_c, for every c. These are the node's two
  empty cases.

All objects live in one arbitrary ambient scheme universe u, as in Mathlib's
Scheme pullbacks and fibre API. The field K also has `Type u`, so the family of
field extensions is not quantified in an independent, potentially smaller test
universe. Enlarging the ambient universe covers any given schemes and field
extensions. All variables/universes are bound; autoImplicit and
relaxedAutoImplicit are explicitly disabled.

Dependency declarations read and used (some are re-exported by the public imports):

| Node | Module | Declaration |
| --- | --- | --- |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme, Scheme.Hom |
| pqf-def-locnoeth | Mathlib.AlgebraicGeometry.Noetherian | AlgebraicGeometry.IsLocallyNoetherian |
| def-weil-pbc-quasi-compact-scheme | Mathlib.Topology.Defs.Filter | CompactSpace |
| def-sbc-smooth-morphisms | Mathlib.AlgebraicGeometry.Morphisms.Smooth | AlgebraicGeometry.Smooth |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback | CategoryTheory.Limits.pullback, pullback.fst, pullback.snd |
| def-weil-residue-field | Mathlib.AlgebraicGeometry.ResidueField | AlgebraicGeometry.Scheme.residueField |
| def-weil-affine-spectrum | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Spec, Spec.map |
| def-weil-pbc-krull-dimension-ring | Mathlib.RingTheory.KrullDimension.Basic | ringKrullDim |
| def-weil-constructible-subset | Mathlib.Topology.Constructible | Topology.IsConstructible |
| def-pc-field-extension | Mathlib.Algebra.Algebra.Defs | Algebra, algebraMap |
| def-weil-irreducible-components | Mathlib.Topology.Irreducible | irreducibleComponents |

`Mathlib.AlgebraicGeometry.Fiber` supplies the existing fibre construction and its
canonical projections, also the recorded proof dependency def-pc-scheme-fibre.
Plain proof imports retain the already stated smooth dimension, dimension formula,
closed irreducible dimension/trdeg, fibre base-change and dimension-supremum
interfaces. Relevant Mathlib proof interfaces come from the imported/re-exported
Noetherian, ideal subscheme, closed immersion, finite presentation, quasi-separated,
Noetherian topology and scheme properties modules. The proof-only node
lem-sfb-finite-presentation-fibre-dimension-levels has no recorded Lean declaration
at inspection time, so no nonexistent module for it is imported. The theorem
proof docstring gives all nine steps of the node's proof, including that input.

Sources opened: the full node and every statement-dependency node; the signatures
and docstrings of their recorded declarations in Mathlib; Stacks
more-morphisms.tex, `lemma-dimension-fibres-constructible` (05F9), beginning at line
8454; and the current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`.
No statement correction or dependency repair was needed.

Edge cases checked before drafting and again on the completed signature:

- X empty, S empty, a single empty fibre, Z empty, and empty Z_s: the quantifiers
  are vacuous, and both empty-case conjuncts remain present.
- c = 0: no points are excluded, because a scheme stalk is a nonzero local ring;
  the cast is zero, with no positive-bound hypothesis.
- c greater than every fibre dimension: the locus still includes every empty
  Z_s and excludes any nonempty Z_s with an insufficient local dimension.
- Z = X: every nonempty smooth fibre contains generic points of dimension-zero
  local rings, so G_1 is exactly the empty-fibre locus. This agrees with the
  component criterion, including when the fibre is empty.
- A closed point of a smooth curve, and a whole component of a reducible smooth
  fibre: the former has local dimension one and the latter contains a generic
  point of local dimension zero. The criterion distinguishes these correctly.
- The identity extension and transcendental field extensions: the quantifier
  includes both. A lifted closed point can have a different local ring dimension;
  the theorem only preserves the all-points minimum bound on the closed subset.
- Identity base change and arbitrary non-Noetherian S': neither is excluded.
  The locus helper is defined without Noetherian or smoothness assumptions.

Searches (through the prescribed msearch.py wrapper, Q86/item, 2026-10-24):

- LeanFinder: "In a smooth finitely presented family over a Noetherian scheme,
  the locus where a closed subset has fibre codimension at least c is
  constructible and commutes with base change". Eight hits: constructible-image
  and preimage theorems, Chevalley and constructible-set data. Their returned
  types do not express this fibre-local-ring bound or its other clauses.
- LeanSearch: "The fibre codimension bound for a closed subset of a smooth
  scheme over a Noetherian base defines a constructible locus". Eight hits:
  constructible image/preimage, locally constructible sets, a specialization
  criterion, constructible-set data and Scheme.Hom.fiber. No exact statement.
- Loogle: `"ringKrullDim", "IsConstructible"`. No hits.
- Mathlib grep: `codimension|codim|dimension.*constructible|constructible.*dimension`
  in AlgebraicGeometry. Three hits in OrderOfVanishing and AlgebraicCycle.Basic;
  none is the locus or this theorem.
- Direct rg over lean/WeilConjectures and lean/Sheaf for codimension/constructible
  dimension terminology, followed by exact proposed-name searches in both trees
  and dag/lean_names_upstream.json: existing divisor, regular immersion and
  resolution-strata definitions, but no fibre-codimension locus or this theorem.
- Direct rg of the item's id in lean/WeilConjectures: no hit.

Validation: scompile.py compiled both its sandbox probe and the library-path
module cleanly (10.2 s and 6.3 s). The initial compile exposed a binder elaboration
issue: a bare `pullback` was inferred in Type when used as a point's binder.
Writing the explicit scheme-carrier coercion `↥(pullback ...)` fixed it without
changing any mathematical object or hypothesis. No other compiler warning was left.

## Second reading by Q86

I reopened the original node and reread the complete final module after compilation.
This is the dispatcher's worker's own second pass; no second agent was started,
in accordance with the explicit brief. The maintainer supplies the independent
review of the delivery.

The Noetherian hypothesis is exactly local Noetherianity plus quasi-compactness;
smoothness supplies the lfp part and the signature retains the qc and qs parts.
The closed set is a set with IsClosed, and c includes zero. The locus uses stalks
of `f.fiber s`, not of X and not topological dimension at a point. I checked all
three field-extension projections in the signature: the point type, the test
for lying over Z, and the stalk dimension belong to the same extended fibre.
The equivalence is on all-points bounds in both directions. The base-change
formula uses the second projection as the structure map, the first to pull back
Z, and v to pull back the locus. It requires no new-base hypotheses. The bound-one
criterion says no component is contained in Z_s. Both empty cases remain explicit.
The helper is real data and works over any base, and only the theorem has sorry.
No mathematical mismatch, missing clause or node correction was found. The sole
change from the first draft was the explicit point-carrier coercion required by
the compiler. The theorem's nine-step proof docstring follows the node's proof.
