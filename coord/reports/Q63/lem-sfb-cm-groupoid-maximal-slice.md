## Worker report

The module `Sheaf.AlgebraicGeometry.CohenMacaulayGroupoidMaximalSlice` states
`AlgebraicGeometry.exists_cm_groupoid_maximal_slice`, with one whole-proof `sorry`.
There are no new definitions, auxiliary theorems, dependency repairs or statement
corrections. Its docstring carries all eleven proof steps, with their dependency
identifiers, from the node. The source was read in
`literature/stacks-project/more-groupoids.tex`, Tags 04MZ and 04MY.

Hypothesis and clause correspondence:

- Schemes S, U and R: `{S U R : Scheme.{u}}`, with explicit universe `u` and
  `set_option autoImplicit false`. The size-convention node is metatheoretic.
- Groupoid data: the binders `s t e i c` and `hG : IsGroupoidScheme s t e i c`.
  The structure morphisms are `p : U ⟶ S`, `q : R ⟶ S`, with
  `hs : s ≫ p = q`, `ht : t ≫ p = q`. These imply that e, i and c are over S:
  use the identity, inverse and composition source laws, respectively. No
  additional structure-map compatibility is omitted.
- Cohen-Macaulay source and target: `[Flat s] [Flat t]`, and `hcm` for each
  `f = s ∨ f = t`, each base point `v : U` and every `r : f.fiber v`.
  The latter is exactly `IsNoetherianRing` of that fibre stalk and equality
  between `IsLocalRing.depth` of its self-module and `ringKrullDim`, with the
  inclusion from ℕ∞ into `WithBot ℕ∞`. No Noetherian assumption on U or S.
- Locally finitely presented source and target: the two
  `[LocallyOfFinitePresentation ...]` binders.
- Finite type point: `u : U`, with `LocallyOfFiniteType` and `QuasiCompact` of
  `U.fromSpecResidueField u`, the two recorded conditions for finite type.
- Affine slice, immersion and its finite presentation: existential `B g b`
  with `IsAffine B ∧ IsImmersion g ∧ LocallyOfFinitePresentation g`.
  This is an immersion, as the node requires, and need not be globally closed.
- b lies over u and the induced residue-field map is an isomorphism:
  `g b = u ∧ IsIso (g.residueFieldMap b)`. Its domain is κ(g b), identified
  with κ(u) by the preceding equality.
- Saturation is exactly `pullback g t`, with map `pullback.snd g t ≫ s`.
  Its flatness, local finite presentation and every fibre's Noetherian
  depth-equals-dimension condition are all explicit conjuncts.
- Identity point in h⁻¹(u): `x : (pullback.snd g t ≫ s).fiber u`, with its
  image under `fiberι` projecting to b and e(u). Thus it is the stated
  x = (b,e(u)), not an unspecified point chosen to satisfy a dimension bound.
  The projection to R is an immersion because g is; hence x is unique.
- Dimension equality: `topologicalKrullDimAt x = topologicalKrullDim ...`.
  The right-hand scheme is the pullback of
  `pullback.lift s t (hs.trans ht.symm) : R ⟶ U ×_S U` along
  `pullback.lift (U.fromSpecResidueField u) (U.fromSpecResidueField u) rfl`.
  This is canonically G_u by associativity of pullbacks: the stabilizer
  first imposes s=t and its fibre then fixes that common endpoint to u.
  It has one κ(u) factor; it is not the relation with independent endpoint
  residue-field factors. `topologicalKrullDim` is the supremum of lengths
  of chains of irreducible closed subsets, as in the statement.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.GroupoidScheme`: `IsGroupoidScheme`, including
  the full signature, docstring and all the laws.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift` (available via the public imports).
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`;
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.fromSpecResidueField`, `Scheme.Hom.residueFieldMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `IsImmersion`, the immersion
  clause of the closed-immersion dependency's recorded Mathlib match.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `WeilConjectures.RingTheory.Depth`: `IsLocalRing.depth`;
  `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`;
  `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`;
  `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.

The module also imports stated proof dependencies: the hypersurface slice,
Cohen-Macaulay field extension, representable algebraic spaces, the local-dimension
supremum theorem, and the Mathlib permanence, étale and finite-stability interfaces.
The proof-only groupoid-locus descent, double restriction, finite-type-point criterion,
affine fibre dimension and constant local dimension nodes have no recorded usable
statement in the read clone, so no module for them is invented or imported.

Edge cases checked: an empty U has no u and hence no input; an input u guarantees
nonempty R by e and nonempty stabilizer fibre by its identity. Zero-dimensional
stabilizer and source fibres are included (the induction equality case). No positive
dimension hypothesis, characteristic restriction, global Noetherian assumption,
quasi-compactness assumption on s or t, or bound on the dimension is imposed.
Arbitrary base S is permitted. B cannot be empty since b is supplied. Infinite
dimensions are represented by the extended dimension type, without assuming them
finite in the signature; finiteness needed for induction is part of the proof.

Searches (all before writing the declaration):

- `msearch.py ... leanfinder` with query “A Cohen Macaulay locally finitely
  presented scheme groupoid has an affine immersed slice with source fibre
  dimension equal to stabilizer dimension”: eight hits, including affine
  neighbourhood, preimmersion and reduction-to-affine lemmas; no matching theorem.
- `msearch.py ... loogle '"Scheme", "IsGroupoidScheme"'`: zero hits.
- `msearch.py ... grep 'max.slice|slice.*groupoid|Cohen.?Macaulay'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` for groupoid slice/maximal slice/CohenMacaulay slice in both project roots:
  the existing hypersurface slice and unrelated closed-point slicing results;
  no maximal-slice theorem. Searching the item id in WeilConjectures gave no hit.
- `rg 'exists_cm_groupoid_maximal_slice'` in `dag/lean_names_upstream.json`,
  WeilConjectures and Sheaf gave no name collision.

No statement fault or disputed mathematical claim was found.

## Second reading by Q63

The delivered section disclaimed an independent reading (dispatcher policy). This
section records the maintainer reviewer's clause-by-clause second reading of commit
e4ab90ec, against the node, Stacks 04MY/04MZ (more-groupoids.tex) and the recorded
declarations of every stmt_dep.

- S, U, R schemes (def-pc-scheme, size convention): `{S U R : Scheme.{u}}`, one
  universe, no restriction. Holds.
- Groupoid over S (def-a1-groupoid-scheme): `IsGroupoidScheme s t e i c` (landed Q05
  structure, `c : pullback s t ⟶ R`, `s(a)=t(b)`), with `hs : s ≫ p = q`,
  `ht : t ≫ p = q`. e, i, c over S follow from identity_source, inverse_source,
  composition_source. Holds.
- G = U ×_{Δ_{U/S}, U×_SU, (s,t)} R and G_u = G ×_U Spec κ(u): rendered as
  `pullback (pullback.lift s t _) (pullback.lift (fromSpecResidueField u) (fromSpecResidueField u) rfl)`,
  i.e. R ×_{U×_SU} Spec κ(u) along Δ ∘ (Spec κ(u) → U); by pasting of pullbacks this is
  G ×_U Spec κ(u). Holds (one κ(u) factor).
- Cohen–Macaulay (flat + every fibre stalk Noetherian with depth = Krull dim): `[Flat s]
  [Flat t]` and `hcm` over `f = s ∨ f = t`, all `v : U`, all `r : f.fiber v`, using
  `Scheme.Hom.fiber` (def-pc-scheme-fibre), `IsNoetherianRing`, `IsLocalRing.depth`
  (WeilConjectures.RingTheory.Depth, depth w.r.t. the maximal ideal of R over itself)
  and `ringKrullDim`, compared in `WithBot ℕ∞`. Holds, no stronger.
- s, t locally of finite presentation: two `LocallyOfFinitePresentation` instances. Holds.
- u a finite type point: `LocallyOfFiniteType` + `QuasiCompact` of
  `U.fromSpecResidueField u` = the recorded finite-type pair. Holds.
- Conclusion: `∃ B g b`, `IsAffine B`, `IsImmersion g` (the immersion clause of the
  def-weil-closed-immersion Mathlib match), `LocallyOfFinitePresentation g`, `g b = u`,
  `IsIso (g.residueFieldMap b)`; h = `pullback.snd g t ≫ s` on `pullback g t`
  (= B ×_{g,U,t} R, s ∘ pr_R) flat, LFP, and the fibre-stalk CM condition for all
  `v`, `y`. Holds, every clause, not weaker.
- x = (b, e(u)) ∈ h^{-1}(u): `∃ x : (h).fiber u` with both projections of `fiberι u x`
  equal to b and e u; since κ(b) = κ(u) = κ(e u), the point is unique. Holds.
- dim_x h^{-1}(u) = dim G_u: `topologicalKrullDimAt x` (def-kun-topological-dimension-at-point,
  infimum over open neighbourhoods) `= topologicalKrullDim G_u` (supremum of chains of
  irreducible closed subsets). Holds.

Edge cases: d = 0 / zero-dimensional stabilizer included; empty U gives no u; no
Noetherian, quasi-compactness or characteristic assumption; infinite dimensions allowed
in `WithBot ℕ∞`. Source (5) is not part of the node (place note lists (1)–(4), (6)).

Searches: rg for maximal slice / exists_cm_groupoid / IsGroupoidScheme in the live
lean/Sheaf and WeilConjectures trees: only the hypersurface-slice module; no duplicate.
No mismatch found; the Lean statement and records are unchanged.
