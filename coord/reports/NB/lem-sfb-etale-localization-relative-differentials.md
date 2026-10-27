## Worker report

Item: lem-sfb-etale-localization-relative-differentials. The module
`Sheaf.AlgebraicGeometry.EtaleLocalizationRelativeDifferentials` states
`AlgebraicGeometry.Scheme.Hom.etale_localization_relativeDifferentials`, with
`sorry` as its entire proof. No definitions, auxiliary axioms, new nodes, dependency
repairs, or statement corrections are introduced. The node changes only in `lean`.

Source read: `literature/stacks-project/more-morphisms.tex`,
`lemma-sheaf-differentials-etale-localization` (Tag 04BX), statement and proof.
The source permits an arbitrary commutative square, not just a Cartesian one.
The additional generator and restriction clauses in the node describe the canonical
functoriality map of Morphisms, Tag 01UV.

Hypotheses and objects, clause by clause:

- The four arbitrary schemes are `{X₁ X₂ S₁ S₂ : Scheme.{u}}`, for explicitly
  bound arbitrary universe `u`; the four arrows are `a`, `b`, `f₁`, `f₂`, with
  exactly the types and directions of the node's square.
- Both horizontal arrows are étale: `[Etale a] [Etale b]`. No assumption is made
  on the vertical arrows. Commutativity is `h : a ≫ f₁ = f₂ ≫ b`.
- The existing sheaves are `f₁.relativeDifferentials` and
  `f₂.relativeDifferentials`; their derivations are the corresponding
  `relativeDifferentialsDerivation`. Nothing is replaced by an arbitrary module.
- Ordinary module pullback is `(Modules.tensorPullback a).obj
  f₁.relativeDifferentials`, the recorded sheafified tensor construction.
- The comparison is the quantified module-sheaf morphism `c` from that actual
  tensor pullback to `f₂.relativeDifferentials`. Its canonical nature is fixed
  by the next formula, not by merely postulating an isomorphism between objects.
- `IsIso c` is exactly the isomorphism conclusion.
- For every source open `W : X₁.Opens` and section `r : Γ(X₁, W)`, the first
  universal quantifier says that `c.app (a ⁻¹ᵁ W)` sends the actual tensor-unit
  section `tensorPullbackSection a ... W (f₁.relativeDifferentialsDerivation.d r)`
  to `f₂.relativeDifferentialsDerivation.d (a.app W r)`. This renders both
  `1 tensor dr ↦ d(a-sharp r)` and compatibility with universal derivations.
  Differential symbols generate the differential sheaf locally, and their tensor
  units generate the pullback locally. Consequently there is at most one map with
  this formula: the existentially specified arrow is precisely the canonical map.
- The final quantifier ranges over every source open `O : X₂.Opens`. Its `e`
  identifies restriction of the actual pullback with pullback along `O.ι ≫ a`.
  The formula for every section `m : Γ(f₁.relativeDifferentials, W)` fixes `e`
  on actual tensor units, hence fixes the canonical identification. The displayed
  presheaf map is the usual restriction from `a ⁻¹ᵁ W` to the image of its
  preimage under `O.ι`; it is essential to make the section types correct.
- `cO` is the comparison for the restricted vertical arrow `O.ι ≫ f₂`, again
  fixed by the same formula for every `W` and `r`. The final equation is the
  actual commuting diagram: restricting `c` and then applying the existing
  `relativeDifferentialsRestrictIso` equals `e.hom ≫ cO`. It states compatibility
  of maps, not just existence of isomorphic sheaves. Together with the existing
  target/base open differential identifications `relativeDifferentialsRestrictIso`
  and `relativeDifferentialsCompIso`, the same local formula also identifies the
  comparison when the other schemes in the square are restricted to compatible
  opens; no choice of affine chart or open cover is a hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom` (locally ringed spaces and their morphisms).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale` (the
  affine-local étale ring-map condition).
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`,
  `relativeDifferentialsDerivation`, `relativeDifferentialsHomEquiv`,
  `relativeDifferentialsRestrictIso`, and `relativeDifferentialsCompIso`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSection`, with its actual
  sheafified tensor formula, and the public upstream tensor pullback functor
  `tensorPullback` from `WeilConjectures.AlgebraicGeometry.TensorPullback`.
  The normalized adjunction is the recorded dependency's own interface.
- Proof imports are `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`
  (`AlgebraicGeometry.smooth_and_fibre_dimension_zero_of_etale`) and
  `Sheaf.AlgebraicGeometry.RelativeDifferentialsTransitivityExact`
  (`AlgebraicGeometry.Scheme.Hom.relativeDifferentials_transitivity_exact`).
  The recorded rank theorem `isFiniteLocallyFreeOfRank_relativeDifferentials`
  is already in the publicly imported differential module. The rank predicate
  `SheafOfModules.IsFiniteLocallyFreeOfRank` is publicly available there from
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`.
  The Kähler differential module and universal derivation in Mathlib are also
  imported there. The smooth short-exact-sequence proof dependency has no Lean
  record yet; it is named in the proof docstring but is not needed for the type
  of this statement and is not restated in this delivery.

Edge cases checked before writing: empty schemes and empty opens are included;
restriction to `O = ⊥` uses precisely the same comparison diagram. Identity
horizontal maps recover the identity comparison, while open immersions recover
ordinary restriction. No nonemptiness, smoothness of a vertical arrow, dimension,
characteristic, flatness of a vertical arrow, finite type, or Cartesian condition
was added. All schemes are in one arbitrary universe, as in the existing scheme
and differential APIs; there is no independently smaller universe of test objects.
The theorem does not assert equality of derivations with different codomains:
it states their correctly typed comparison formula on local sections.

Searches made (2026-10-24):

- `msearch.py ... leanfinder "Kahler differential sheaves are invariant under
  etale localization in a commutative square of schemes"`: eight hits, including
  `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` and
  `KaehlerDifferential.isBaseChange_of_formallyEtale`. These are ring-level
  statements, not the square of scheme module sheaves; no exact match.
- `msearch.py ... loogle '"KaehlerDifferential", "FormallyEtale"'`: five hits,
  comprising the ring tensor equivalence and its formulas and the vanishing
  instance. No scheme-level arbitrary-square comparison.
- `msearch.py ... grep
  'relativeDifferentials|etale.*differential|differential.*etale'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` of the upstream differential module and of
  `lean/WeilConjectures` for relative-differential/étale comparison patterns:
  no theorem matching the item. The upstream module constructs the differential
  sheaf, derivation, affine and open comparisons, and rank results, not Tag 04BX.
- `rg` of `lean/Sheaf/AlgebraicGeometry` for differential/étale and
  `relativeDifferentialsPullbackMap` patterns: the existing
  `RelativeDifferentialsPullbackMap` handles a fixed base, while
  `EtaleDifferentialPullbackPresentation` concerns the small étale/logarithmic
  site, not this Zariski square. The transitivity sequence is used as a proof
  dependency. None is a duplicate of this item.
- Exact proposed declaration-name searches in Mathlib, `WeilConjectures`, and
  `Sheaf` found no collision. The item id likewise has no upstream occurrence.

Validation: the prescribed `scompile.py NB
lem-sfb-etale-localization-relative-differentials <module file>` compiled both
its sandbox and library module forms successfully, in 6.1 s and 3.1 s, with no
compiler messages. All universes and variables are explicitly bound. Every line
is at most 100 characters. The natural-language proof follows all four DAG steps
and names their dependencies. No statement fault or dispute was found.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
