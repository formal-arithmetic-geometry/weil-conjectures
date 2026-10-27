## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeDifferentialSheafBaseChange` states
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialSheaf_baseChange`. Its only
postponed proof is that theorem, with the six steps of the node's proof in its
docstring. The helper `relativeDifferentialsBaseChangeOpen` is a real abbreviation
for the intersection of inverse images of two opens; it introduces no new notion.
The node changes only in its `lean` field. There are no new nodes, dependency
repairs, statement corrections, or disputed statements.

Hypothesis and clause correspondence:

* Arbitrary scheme morphisms are `{X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)`.
  The universe `u` is arbitrary. `T` denotes the node's `S'`.
* The fibre product `X'` is `pullback f g`, with `p = pullback.fst f g` and
  `f' = pullback.snd f g`. No extra cartesianness assumption is supplied.
* The two differential sheaves are `f.relativeDifferentials` and
  `(pullback.snd f g).relativeDifferentials`; both quasi-coherence assertions are
  the first two conjuncts, using `SheafOfModules.IsQuasicoherent`.
* Ordinary module pullback is the recorded explicit `Modules.tensorPullback`.
  The existential `c` is a morphism of sheaves of modules from its value on the
  first differential sheaf to the second differential sheaf. This gives precisely
  the required linearity.
* The first conjunct after `∃ c` is the formula on every open `U` and every
  section `a` of its structure sheaf. `Modules.tensorPullbackSection` is the actual
  section `1 ⊗ da`, and the right side is the target universal derivation applied
  to `(pullback.fst f g).app U a`. The next conjunct says any map with this formula
  equals `c`; thus this is the characterized canonical map, not an arbitrary
  isomorphism. `IsIso c` is its isomorphism assertion.
* Affine triples are `U : X.affineOpens`, `V : S.affineOpens` and
  `V' : T.affineOpens`. `hU` and `hV'` are exactly the two image-inclusion
  conditions. Their open fibre product is
  `relativeDifferentialsBaseChangeOpen f g U.1 V'.1` (called `W` below).
  Its affineness is explicit in `IsAffineOpen W`.
* `A = Γ(X,U)`, `R = Γ(S,V)`, `R' = Γ(T,V')`, and the intrinsic model for
  `A' = R' ⊗[R] A` is `Γ(pullback f g,W)`. The `IsPushout` clause, with the two
  restricted projection ring maps, canonically identifies this intrinsic ring
  with that tensor product, including its two structural maps. This avoids
  noncanonical replacement of an arbitrary affine triple by chosen ring models.
* `α` identifies `A' ⊗[A] Ω[A/R]` with the sections of the restricted pullback
  sheaf. `ModuleCat.extendScalars` forms this tensor product with the specified
  ring map; the `α` formula fixes its normalization on `1 ⊗ da` as restriction of
  the actual tensor-pullback section.
* `δ` identifies `Ω[A'/R']` with sections of the second differential sheaf on W,
  preserving the universal derivation on every `z : A'`.
* `β` is the `A'`-linear equivalence between those ring modules, with its formula
  on every `b ⊗ da` given explicitly. Under the pushout identification the
  restricted projection sends `a` to `1 ⊗ a`, so its right side is precisely
  `b d(1 ⊗ a)`.
* The last affine equation `c.app W (α x) = δ (β x)` for every tensor `x`
  identifies the actual restriction of `c` with `β`, not just unrelated
  isomorphic modules. All triples use the same global sheaf morphism `c`.
  Therefore their identifications agree on every overlap by the defining
  naturality of `c`, and the normalized α and δ comparisons identify the same
  pulled-back differentials there. No assumption that intersections of affines
  are affine is used.
* The final implication assumes exactly `LocallyOfFiniteType f` and concludes
  `IsFiniteType` for both sheaves. The quasi-coherence and isomorphism assertions
  precede this implication, so they do not acquire a finite-type hypothesis.
  There is no flatness, quasi-compactness, finite-presentation, nonempty-scheme,
  characteristic, or nonzero-ring assumption.

Statement dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; `Mathlib.AlgebraicGeometry.Pullbacks` supplies
  their scheme instances and the ring-pushout affine model.
* `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsDerivation`, and its
  affine/restriction comparisons. The universal derivation is used directly.
* `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullbackSection` and the publicly imported upstream
  `Scheme.Modules.tensorPullback`. The former has actual tensor/sheafification
  data, so the formula does not depend on an arbitrary adjunction choice.
* `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes the recorded
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType` predicates.
  Its conjunction `Scheme.Modules.IsQuasiCoherentFiniteType` is unnecessary here
  because quasi-coherence is unconditional and finite type is conditional.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.

Every recorded proof dependency's module is imported as a plain import when it
is not already a public statement import: the open restriction comparison,
associated module pullback, ring Kähler base change, tilde adjunction/sections,
module gluing, local isomorphism criterion, affine differential sections,
quasi-coherent finite-type criterion, and finite-type preservation by pullback.
`Mathlib.AlgebraicGeometry.Pullbacks` covers the two Mathlib affine-fibre-product
proof dependencies. No dependency interface needed repair.

Edge cases checked before and during drafting: empty X or T, empty affine opens
and zero section rings, identity base change, f the identity (zero differential
sheaf), arbitrary nonflat g, and finite type with zero algebra generators. All
remain in the quantified statement. The pushout and linear-equivalence forms
apply to zero rings and zero modules. No independent small universe of test
objects makes any quantifier vacuous.

Sources read: local `literature/stacks-project/morphisms.tex`,
`lemma-differentials-affine` (01UT), `lemma-functoriality-differentials` (01UV),
`lemma-base-change-differentials` (01V0), and `lemma-finite-type-differentials`
(01V2). These give exactly the derivation normalization, base-change isomorphism,
and finite-generation conclusion of the node.

Searches made:

* `msearch.py ... leanfinder`: “Relative differential sheaves commute with arbitrary
  scheme base change and are quasi coherent and finite type for locally finite
  type morphisms”. Eight hits: generic presheaf relative differentials,
  `KaehlerDifferential.isBaseChange`, and `KaehlerDifferential.finite`, among others;
  no scheme-sheaf theorem with all the node's clauses.
* `msearch.py ... loogle`: `"KaehlerDifferential", "tensorKaehlerEquiv"`.
  Eleven hits including `tensorKaehlerEquiv`, `tensorKaehlerEquivBase`, and their
  generator formulas. These are the ring theorem already recorded as a proof
  dependency, not the global sheaf statement. Their source signatures were read.
* `msearch.py ... grep`: `relativeDifferentials|differential.*baseChange`,
  subdirectory `AlgebraicGeometry`: zero Mathlib hits.
* `rg` in both project roots for `relativeDifferentials` and differential
  base-change names found the upstream differential sheaf, affine comparisons,
  and the same-base `RelativeDifferentialsPullbackMap`. That map targets
  `(h ≫ g).relativeDifferentials` over the unchanged base, so does not state this
  cartesian base-change theorem. Its full source was read; no second definition
  of that map was introduced. Searching the exact node id in `WeilConjectures`
  found no existing declaration. Searching the new declaration names in both
  project roots, Mathlib, and `dag/lean_names_upstream.json` found no collision.

Validation: scompile.py compiled the sandbox and its actual library module with
no warnings or errors (the only postponed theorem has the permitted sorry proof).
The first compile identified a noncomputable abbreviation and an untyped numeral
in the restricted-scalar tensor; both were corrected, and the repeat passed.

## Second reading by Q04

This section records the worker's own rereading, not an independent agent review;
the dispatcher forbids starting other agents and the maintainer independently
reviews the delivery. I reread the node and the complete Lean signature together.
The affine comparison includes the open's affineness and the ring pushout, both
projection ring maps, normalized source and target identifications, the full
`b ⊗ da` formula, and an equation with the actual `c.app`. This checks the affine
clause without replacing it by a bare existence of isomorphisms. Quasi-coherence
is unconditional; finite type occurs only under its stated implication. The
canonical map's uniqueness is separated from its isomorphism property, so its
normalization cannot be absorbed into an arbitrary chosen equivalence. No node
statement changed. The first drafting omission found in this rereading was the
explicit affineness conjunct for W; it was added before the clean compile.
