## Worker report

The new module `Sheaf.AlgebraicGeometry.FiniteFunctionNormNonvanishing` states
`AlgebraicGeometry.finite_function_norm_nonvanishing`, with its sole proof `sorry`.
It gives the fibrewise nonvanishing equivalence and the prescribed open neighborhood,
including both inverse identities. No definitions, new nodes, dependency repairs, or
statement corrections are needed. Only the item's `lean` field changes.

I read the item, its three statement dependencies and their full recorded source
signatures/docstrings, and both proof-dependency Mathlib matches. I checked the
source in `literature/stacks-project/divisors.tex`, Section 0BCX, the neighborhood-unit
observation and Tags 0BCY/0BCZ. The statement isolates exactly the general multiplicative
map argument; the additional degree condition from the full Stacks norm definition
is deliberately absent, as the node requires.

Hypothesis and clause correspondence:

- Schemes and finite morphism: `{Y Z : Scheme.{u}} (p : Y ⟶ Z) [IsFinite p]`.
  The explicit universe covers arbitrary schemes in the common scheme category.
- A map on sections for every open: `ν : ∀ V : Z.Opens,
  Γ(Y, p ⁻¹ᵁ V) →* Γ(Z, V)`. A `MonoidHom` preserves multiplication and one;
  it imposes neither additivity nor preservation of zero.
- Commutation with restriction: `hν_restrict` quantifies over every `W ≤ V` and
  every section. The upstairs restriction is
  `Y.presheaf.map (homOfLE (p.preimage_mono h)).op`, and the downstairs
  restriction is `Z.presheaf.map (homOfLE h).op`.
- Residue-field vanishing implication: `hν_vanish` quantifies over all opens,
  sections, points `y`, and membership witnesses `hy`. Both sides use
  `Scheme.evaluation`, the germ followed by the quotient to the residue field.
  In the second evaluation `hy` also proves `p y ∈ V` by the definition of preimage.
- Fixing arbitrary `V`, `b`, and `z ∈ V`: the final four binders are
  `(V : Z.Opens) (b : Γ(Y, p ⁻¹ᵁ V)) (z : Z) (hz : z ∈ V)`.
- The node's `D(b)` is exactly `Y.basicOpen b`. The recorded proof dependency
  `Scheme.evaluation_ne_zero_iff_mem_basicOpen` identifies its membership with
  nonzero residue-field evaluation, and `Scheme.basicOpen_le` places it in
  `p ⁻¹ᵁ V`. No replacement nonvanishing definition is introduced.
- The equivalence is the first conjunct:
  `Z.evaluation V z hz (ν V b) ≠ 0 ↔ p ⁻¹' {z} ⊆ (Y.basicOpen b : Set Y)`.
- The additional conclusion is the second conjunct, conditional on that same
  fibre inclusion. `∃ (W : Z.Opens)` means the set is open in the entire base.
  Its set equality prescribes exactly `V` minus the image of
  `(p ⁻¹ᵁ V : Set Y)` minus `Y.basicOpen b`, rather than merely an arbitrary
  smaller neighborhood. The witness `hWV : W ≤ V` supplies the inclusion
  needed to type the restriction; it follows from the displayed set equality
  and introduces no extra hypothesis or stronger mathematical conclusion.
- `z ∈ W` makes it a neighborhood of `z`, and
  `(p ⁻¹ᵁ W : Set Y) ⊆ Y.basicOpen b` is the stated preimage inclusion.
- `∃ c : Γ(Y, p ⁻¹ᵁ W)` introduces the requested inverse section. The final
  two equalities are respectively the restriction of `b` times `c` equals one,
  and `ν W` of that restriction times `ν W c` equals one. Both use the actual
  sheaf restriction and the originally supplied family `ν`.
- No flatness, surjectivity, degree, scalar power identity, integrality of either
  scheme, affine-open restriction, or reducedness is assumed.

Dependency declarations used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-finite-integral-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.
  The integral alternative of the dependency is not needed by this item.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField` and `Scheme.evaluation`.
  I also read the recorded `Scheme.Hom.residueFieldMap`; no comparison of
  residue-field elements from different points is needed here.
- `lem-weil-pbc-basic-open-function`: Mathlib matches `Scheme.basicOpen`,
  `Scheme.mem_basicOpen`, `Scheme.evaluation_ne_zero_iff_mem_basicOpen`,
  `Scheme.basicOpen_le`, and `RingedSpace.isUnit_res_basicOpen`. Their modules
  are available through the public Scheme/ResidueField imports.
- `lem-weil-pbc-finite-closed-map-finite-fibres`: proof imports
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` give the finite-to-proper
  instance, `Scheme.Hom.isClosedMap`, and `Scheme.Hom.finite_preimage_singleton`.
  These are plain imports, since they belong to the proof plan.

Edge cases checked before drafting:

- Empty `V` has no point `z ∈ V`, so the pointwise assertion has no instance.
- An empty fibre is allowed. Closed-image shrinking gives an open `W` with
  empty upstairs preimage. Its section ring is the zero ring, and preservation
  of one still yields the stated norm inverse identity. No zero-preserving
  condition on `ν` is used or inferred.
- Empty source schemes and nonsurjective finite morphisms remain covered.
  When `b = 0` and a fibre is nonempty, the vanishing hypothesis forces the
  norm evaluation to vanish, as the equivalence requires.
- For the identity morphism and identity family, the specified `W` is `D(b)`.
  For a disjoint union of sheets with product norm, the criterion is exactly
  that each sheet value is nonzero.
- Nonreduced schemes are included: `D(b)` uses residue-field nonvanishing,
  not nonzero elements of the stalk ring, so a nilpotent is never incorrectly
  treated as nonvanishing.
- The relative zero locus need not be closed in all of `Y`. The proof docstring
  keeps the step `C = F ∩ p⁻¹V`, so `W = V` minus `p(F)` is open in the base.

Searches for an existing statement (all run with the prescribed `msearch.py`):

- LeanFinder: "For a finite morphism of schemes a restriction compatible
  multiplicative map preserving one and vanishing has nonzero value exactly
  when the section is nonzero on the whole fibre". Eight hits include
  `Scheme.evaluation_ne_zero_iff_mem_basicOpen` and locally ringed space
  versions, section localization, and basic-open vanishing lemmas. They give
  individual prerequisites, not the theorem for an arbitrary family `ν`.
- Loogle: `"norm", "basicOpen"`. Successful query, zero hits.
- Mathlib grep: `norm.*(nonvanish|vanish|fibre|fiber)` in `AlgebraicGeometry`.
  Three hits in `Normalization.lean` are about normalization diagram maps,
  not norms or the requested criterion.
- LeanSearch: "A multiplicative restriction compatible map of structure
  sheaves for a finite morphism is nonzero at a point if and only if the
  section is nonzero everywhere in its fibre". Eight hits on structure-sheaf
  restrictions and tilde modules, none on this criterion.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `norm.*(nonvanish|vanish|fibre|fiber)|finite_function_norm|functionNorm`:
  I read the relevant hits. `WeilConjectures.AlgebraicGeometry.BaseChangeNorm`
  defines `Scheme.Hom.normAt` and proves `mem_basicOpen_normAt` only for a
  base change to a finite field extension, on affine opens, for the specific
  algebra norm. It cannot represent this arbitrary multiplicative family on
  every open. `Sheaf.AlgebraicGeometry.FiniteNormInvertibleSections` uses the
  same `∀ V, ... →* ...` family with additional surjectivity and power conditions
  and has a different conclusion about norm line bundles; it supplies no
  existing theorem with this statement. No new norm notion is needed.
- The required recursive grep of this node id in `lean/WeilConjectures` had
  no hits. A search of the proposed full declaration name in Mathlib,
  both project roots and `dag/lean_names_upstream.json` had no hits.

There is no statement dispute or node fault. The theorem docstring contains
all four proof steps with the original dependency ids. All variables and the
universe are explicitly bound, `autoImplicit` is false, and the file has no
lines over 100 columns. Compilation and delivery validation use only the
prescribed server wrappers.

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
