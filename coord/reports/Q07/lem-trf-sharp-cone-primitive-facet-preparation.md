## Worker report

The new module `Sheaf.RingTheory.SharpConePrimitiveFacetPreparation` states
`ToricMonoid.sharp_cone_primitive_facet_preparation`, with its whole proof `sorry`.
It introduces no definitions, axioms, extra nodes or dependency repairs. The item's
JSON differs only in `lean`. No statement correction or disputed statement is needed.

Source read: ILO, Travaux de Gabber, PDF page 76 / printed page 70, Exposé VI 1.6(i)--(ii),
using pdftotext on the project's PDF. This supplies the sharp fs monoid setting, not
this auxiliary theorem. Its proof is the node's agent-formulated eleven-step argument,
which is reproduced step by step in the declaration docstring. Kato (1994) is unread
and no proof is attributed to it. The current blueprint's
`sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md` was read for
the recorded ancestry; it contains no assertion of this cone theorem.

Hypotheses and objects, matched against the node:

- `P : Type u` and `[AddCommMonoid P]` give the additive commutative monoid, in any
  universe. `hfs : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative P)` is
  exactly finite generation, injectivity into the canonical group completion, and
  saturation; the multiplicative type tag changes notation only.
- `hsharp : ∀ p : P, IsAddUnit p → p = 0` says zero is the only invertible element.
- `Lattice P`, `RationalSpace P`, `latticePoint`, `rationalPoint`, and `cone P` are
  the dependency's canonical G, Q tensor G, and their point maps and rational cone.
  Tensor symmetry identifies its Q tensor G convention with G tensor Q in the node.
- `Facet P`, `IsFacet`, `IsPrimitiveNormal`, and `IsRationalExtension` are the exact
  recorded definitions, without a private replacement.

Conclusions, in the order in which the Lean states them:

- `∃ r, Nonempty (Module.Basis (Fin r) ℤ (Lattice P))` is finite free abelian G;
  `Function.Injective (fun g ↦ (1 : ℚ) ⊗ₜ[ℤ] g)` is the lattice embedding.
- `x ∈ cone P → -x ∈ cone P → x = 0` is pointedness. The difference presentation
  `∀ x, ∃ a ∈ cone P, ∃ b ∈ cone P, x = a - b` says the cone spans V. For a
  rational cone this is equivalent to linear spanning, including V = 0.
- `∀ g, 1 ⊗ g ∈ cone P ↔ ∃ p, latticePoint p = g` is P = sigma intersect G.
- `Set.Finite {F | IsFacet P F}` states finiteness of the full set of facets.
- Existential families `ν` and `h` provide each primitive integral normal and its
  rational extension. `IsPrimitiveNormal F (ν F)` includes surjectivity,
  nonnegativity on P, and the facet zero locus. The following universal equality
  `∀ μ, IsPrimitiveNormal F μ → μ = ν F` is uniqueness. `IsRationalExtension` and
  the displayed zero-locus equality tie the chosen extension to the same normal.
- `(cone P : Set _) = {v | ∀ F, 0 ≤ h F v}` is the complete facet half-space formula.
- `∀ F, ∃ f : P, rationalPoint f ∈ F.val ∧ ∀ H, H ≠ F → 0 < ν H (latticePoint f)`
  is the required integral witness on each facet with strict positivity on all others.
- Under `∀ g : Lattice P, g = 0`, the theorem gives `∀ p, p = 0`, `∀ v, v = 0`,
  `cone P = {0}` as sets, and `IsEmpty (Facet P)`: precisely the G = 0 clause.
- `∃ v : RationalSpace P, v ≠ 0` is positive dimension. The earlier finite-basis
  conclusion ensures finite dimensionality, so this condition is equivalent to
  positive finrank, without assuming finite dimensionality as a new hypothesis.
- In this case `s m : ℕ`, `I : Fin s → V →ₗ[ℚ] ℚ`, `a : Fin m → P`, `x₀`, `e`,
  and `x` encode all simultaneous finite families. `0 < s` makes the form-index
  set nonempty and `∀ i, I i ≠ 0` excludes zero forms.
- The equality with `{v | ∀ i, 0 ≤ I i v}` gives the inequalities. For every i,
  the existence of v satisfying all other inequalities and violating i expresses
  exactly irredundancy (the deleted inequality strictly enlarges the locus).
- Equality with `ConvexCone.hull ℚ (Set.range (fun j ↦ rationalPoint (a j)))` says
  the finitely many a_j in P generate sigma. The next equality defines x₀ as
  their sum, and `∀ i, 0 < I i x₀` states its strict interior property.
- `e : Fin s ≃ Facet P` is the claimed bijection, and its zero-locus equality
  identifies its value with sigma intersect ker h_i, rather than an arbitrary facet.
- `x i ∈ cone P`, `I i (x i) = 0`, and strict inequalities for `j ≠ i` describe
  x_i. `Submodule.span ℚ ((e i).val) = LinearMap.ker (I i)` is the span equality.
- `∃ c : ℚ, 0 < c ∧ h (e i) = c • I i` makes each normal's rational extension a
  positive rational multiple of the corresponding form.
- Finally `∃ (n : ℕ) (f : P), 0 < n` with facet membership, strict values at all
  other facets and `rationalPoint f = n • x i` asserts that the required lattice
  witnesses can be obtained as positive integral multiples of these same x_i.
  The ν and h families scope over this clause as well as the earlier clauses.

Recorded dependency declarations read and used:

- `Sheaf.RingTheory.CompleteToricModel`: `ToricMonoid.Lattice`, `latticePoint`,
  `RationalSpace`, `rationalPoint`, `cone`, `IsFacet`, `Facet`, `IsRationalExtension`,
  `IsPrimitiveNormal`; all signatures and docstrings were read in full.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`, public dependency import:
  the fs monoid predicate is publicly reexported from
  `Sheaf.AlgebraicGeometry.LogRegularPair`, `AlgebraicGeometry.IsFineSaturatedMonoid`.
  Its full defining formula was read: finite monoid generation, injective group
  completion map, and the saturation implication for every positive integer.
- Plain proof import `Sheaf.GroupTheory.SharpConeLatticeIntersection`:
  `AlgebraicGeometry.sharp_fs_monoid_cone_lattice_intersection`; signature and
  complete proof docstring read. Its PointedCone hull contains zero; the canonical
  ConvexCone hull used here contains zero since rationalPoint 0 is a generator.
- Plain proof import `Sheaf.TraceFormula.RationalConeDualFinite`:
  `Weil.rationalConeDualFinite`; signature and full proof docstring read.

Edge cases checked mathematically before finalizing: P = {0} yields G = V = sigma = 0,
no facets, empty ν/h families, and no obligation to produce a positive-dimensional
family. For P = N there is one facet {0}, so x_i = f_i = 0 is allowed and the other
facet inequalities are vacuous. For P = N², coordinate normals and the opposite-axis
witnesses satisfy every clause. For the nonsmooth saturated cone generated by (1,0)
and (1,2) in Z², the primitive normals are y and 2x-y; witnesses (1,0) and (1,2)
meet the respective faces. The statement does not assume a free monoid or a smooth cone.
Empty finite generator lists are not excluded a priori; they cannot generate a cone
of positive dimension, as is already forced by the stated equalities.

Searches (all through the prescribed tools or read-only source searches):

- msearch leanfinder: "A sharp finitely generated saturated monoid has finitely many
  facets with unique primitive integral normals and interior lattice witnesses".
  Eight hits: IsProperLinearSet, ZLattice.FG / Zlattice.FG, IsAffineMonoid.toFG,
  ZSpan.setFinite_inter, and number-field lattice/fundamental-cone declarations;
  no match for the theorem.
- msearch loogle: "ToricMonoid.IsPrimitiveNormal, ToricMonoid.IsFacet, ConvexCone".
  Zero hits, unknown project identifier. Retried with Mathlib names
  "ConvexCone, LinearMap.ker": zero hits.
- msearch grep: "primitive.*(normal|facet)|irredundant|IsFacet" in Geometry/Convex:
  zero hits.
- rg over lean/WeilConjectures and lean/Sheaf for primitive facet/normal,
  IsPrimitiveNormal, sharp facet, and irredundant. The complete-model and
  SharpMonoidFacetForms definitions already used here appeared. The parent theorem
  CompleteToricFacetValuations includes some clauses but assumes a complete model
  and does not state this preparation result. FacetLatticeSupportedCoordinateCover
  cites the present node in its proof; it is a different conclusion. No duplicate.
- rg of the exact item id in lean/WeilConjectures and of sharp/primitive facets or
  normals in dag/lean_names_upstream.json returned no declaration match.
- No coord/repair-notes/<item>.json exists. The withdrawn CompactObject example and
  its updated upstream lean record were read; module/public import/public section
  conventions were followed.

Validation: scompile.py Q07 <item> <module> compiled the sandbox probe and the library
module cleanly, with no diagnostic. The theorem's only postponed proof is its single
whole `sorry`; every variable and universe is explicit.

## Second reading by Q07

Author's separate second pass, as a dispatcher-started worker with no subagents;
independent review is supplied by the maintainer after delivery. Reopened the node
and Lean module and checked each hypothesis and clause using the mapping above.
The positive-dimension condition uses nonzero V, equivalent here to positive
finite dimension. The same ν/h choices scope over the positive-scaling and integer
witness clauses. The primitive extension equality is an equality of linear maps,
not merely equality on selected generators. Irredundancy explicitly includes a
violating vector for each deleted inequality. The rank-zero implication asserts
all four requested degeneracies, and rank-one witnesses may be zero. No final
mismatch, hidden hypothesis, extra declaration, or node fault was found.
