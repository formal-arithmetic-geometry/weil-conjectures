## Worker report

The delivery states `AlgebraicGeometry.IsAffineRegularImmersion.comp` in
`Sheaf.AlgebraicGeometry.AffineRegularImmersionComposition`. Its proof is `sorry`;
its docstring contains all five accepted DAG proof steps and their dependencies.
The item statement and accepted proof are unchanged. Its statement dependencies
only gain the new definition node described below. No dependency record is repaired.

Hypothesis and clause correspondence:

- Schemes and morphisms `i : Z → Y`, `j : Y → X` are the explicit binders
  `{Z Y X : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)`.
- The two regular-immersion assumptions are
  `(hi : IsAffineRegularImmersion i) (hj : IsAffineRegularImmersion j)`.
- In the definition, the immersion requirement is `IsImmersion a`.
  Mathlib's `IsImmersion.isImmersion_iff_exists` identifies this with the node's
  closed-immersion/open-immersion factorization.
- Every source point and its open neighbourhood are
  `∀ t : T, ∃ V : T.Opens, t ∈ V ∧ ...`.
- The affine ambient ring and finite sequence are
  `∃ (A : CommRingCat.{u}) (r : List A), RingTheory.Sequence.IsRegular A r ∧ ...`.
  The ideal is exactly `Ideal.ofList r`; choosing this ideal is equivalent to
  choosing an ideal and a generating finite sequence, as in the item.
- The affine open inclusion in the target is
  `∃ (e : Spec A ⟶ W), IsOpenImmersion e ∧ ...`.
- The identification of the source open with the quotient spectrum is the actual
  isomorphism `q : V.toScheme ≅ Spec (CommRingCat.of (A ⧸ Ideal.ofList r))`.
- The prescribed quotient map and factorization, with their order fixed, are
  `V.ι ≫ a = q.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ e`.
  Thus the closed arrow is the canonical quotient-spectrum arrow, not an arbitrary map.
- The conclusion is `IsAffineRegularImmersion (i ≫ j)`, where `i ≫ j` is `j ∘ i`.
- There is no Noetherian, field, nonempty-source, dimension, or fixed-length assumption.
  The universe `u` is explicit, and chart rings are in the scheme universe.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
  Their recorded dependency interfaces are used through the public immersion import.
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `IsImmersion` and
  `IsImmersion.isImmersion_iff_exists`; this is the immersion clause already carried
  by `def-weil-closed-immersion`, not a new notion.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`.
  Its inherited prefix-quotient injectivity and `top_ne_smul` are exactly the
  regular-sequence definition in `def-weil-pbc-regular-sequence`.
- The proof-only imports expose the Mathlib matches of the proof dependencies:
  `IsImmersion.comp` (permanence); `exists_basicOpen_le_affine_inter` (common affine
  principal neighbourhood); `Scheme.evaluation_eq_zero_iff_notMem_basicOpen`,
  `IsAffineOpen.fromSpec_preimage_basicOpen`, `IsAffineOpen.fromSpec_primeIdealOf`,
  `PrimeSpectrum.mem_basicOpen`, `IsAffineOpen.basicOpen`, and
  `IsAffineOpen.isLocalization_basicOpen` (principal-open comparison);
  `RingTheory.Sequence.IsWeaklyRegular.of_isLocalization` (localization);
  `Scheme.Hom.app_surjective`, `IsAffineOpen.preimage`,
  `HasAffineProperty.iff_of_iSup_eq_top`, `IsClosedImmersion.hasAffineProperty`
  (closed affine charts). Proof-only modules are plain imports.

Sources read: `divisors.tex`, labels `lemma-regular-ideal-sheaf-scheme` (063G),
`definition-regular-immersion` (063J), and `lemma-composition-regular-immersion`
(067Q), including assertion (1) and its algebraic concatenation reference.
No statement correction or STATEMENT-DISPUTED issue was found.

Edge cases checked before writing: an empty source makes only the chart quantifier
vacuous, while the immersion condition remains; `r = []` is allowed, with regularity
requiring a nonzero ambient ring at a source point; open immersions admit the empty
sequence locally. The empty scheme therefore causes no false nontriviality assumption.
The proof plan covers either or both concatenated blocks empty and obtains the
nonzero final quotient from the fixed source point. Lengths can vary between charts
and components. General locally closed immersions are allowed; no closed immersion
of the entire source into the entire target is required. No characteristic is excluded.

Searches performed (all service searches actually executed through `msearch.py`):

- LeanFinder: “Composition of regular immersions of arbitrary schemes is a regular
  immersion without Noetherian hypotheses”: ordinary immersion/preimmersion
  composition results, no exact regular-immersion statement.
- LeanSearch and LeanFinder: “A regular immersion of arbitrary schemes is an
  immersion locally cut out by a finite regular sequence”: ordinary `IsImmersion`,
  closed immersions, and smoothness results, no matching regular-immersion predicate.
- Loogle: `"IsRegularImmersion"`: zero hits.
- Mathlib grep: `IsRegularImmersion|regular.*immersion` in `AlgebraicGeometry`:
  zero hits.
- Project grep: `IsRegularImmersion|[Rr]egular[Ii]mmersion|regular.*immersion` in
  both `lean/WeilConjectures` and `lean/Sheaf`; opened the relevant definitions and
  composition declaration. The upstream
  `WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion` defines
  `IsRegularImmersion (c : ℕ) (i : Z ⟶ X)` as a closed immersion with prescribed
  common length at every target point; its `IsRegularImmersion.comp` is not this
  item, which permits nonclosed immersions and varying local lengths.
- Read `Sheaf.AlgebraicGeometry.RegularClosedImmersionCodimension`:
  `IsRegularClosedImmersionWithCodimension` likewise imposes global closedness and
  a specified codimension function, so is not the general notion.
- Read the Koszul-near and Koszul-closed-chart nodes and their interfaces; these use
  Koszul regularity, a weaker condition without Noetherian hypotheses.
- `rg` and the requested recursive grep for this item's id in `lean/WeilConjectures`:
  no attachment. Exact-name searches for the new declarations found no collision.
- DAG definition search for “regular immersion” and
  `tools/blueprint_refs.py search 'regular immersion'`: only the more specialized
  closed, purity, and Koszul notions; no exact general definition.
  `tools/blueprint_refs.py ancestor lem-sfb-regular-immersion-composition` returned
  `None`, matching the item's inherited null ancestor and retained via chain.

Validation: both delivered files passed `scompile.py` separately, in dependency
order, against the live published library, with no errors or unexpected warnings.

## New nodes

`def-sfb-affine-regular-immersion`, module
`Sheaf.AlgebraicGeometry.AffineRegularImmersion`, defines the exact affine-chart
regular-immersion notion spelled out in the item's statement, using only existing
Mathlib scheme, immersion, spectrum, quotient, and regular-sequence constructions.
The definition has real data and no `sorry`. Its source is Stacks 063G and 063J.
The searches above and its recorded actual search responses distinguish it from the
fixed-codimension closed predicate, the varying-codimension closed predicate, the
stalk-only predicate, and the Koszul predicate. The new node is in the item's chapter
and is added to the item's statement dependencies; no other item field is changed.

## Second reading by Q82

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
