## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SL2OpenCellSheafExtension` states
`AlgebraicGeometry.existsUnique_sl2_openCell_extension`. Its only proof is `sorry`;
no theorem is proved and no definition is introduced. The item's node changes only
in `lean`. No statement correction, new node, dependency-module repair, or disputed
statement is needed.

Clause-by-clause correspondence:

- The arbitrary base scheme is `(S : Scheme.{u})`. Every test scheme is an object
  `T : Over S`; all morphisms of S-schemes are quantified as `f : U ⟶ T`.
- The specified topology is `Scheme.fppfTopology.over S`. Its Mathlib precoverage
  consists of jointly surjective flat locally finitely presented families. The
  slice is the big fppf site of S, not its small site or a site of affine schemes.
- The arbitrary group sheaf is `H : Sheaf (Scheme.fppfTopology.over S) GrpCat.{v}`.
  Its values are groups, restriction maps are group homomorphisms, and its sheaf
  property supplies unique gluing. The section universe `v` is independent of `u`.
  There is no representability, separatedness, commutativity, flatness or finiteness
  hypothesis on H or S.
- The source sections G(T) are exactly
  `Matrix.SpecialLinearGroup (Fin 2) Γ(T.left, ⊤)`, Mathlib's 2-by-2 matrices with
  determinant 1 over the actual global functions of T. Its existing group instance
  uses matrix multiplication, identity, and adjugate inverse. Restriction is
  `Matrix.SpecialLinearGroup.map f.left.appTop.hom`, applying the canonical global
  section pullback entrywise.
- Omega(T) is expressed directly by `IsUnit (g 1 1)`. Fin indices are zero-based,
  so `(1,1)` is the bottom-right entry. A family on a subtype is equivalently a
  family taking a section `g` and a proof `hg : IsUnit (g 1 1)`; proof irrelevance
  makes this independent of the proof. This is the precise open subfunctor in the
  node, without a second definition of the matrix group or an arbitrary open set.
- The natural transformation sigma is the family `σ` together with `hσ_natural`.
  Its right-hand side uses the canonical matrix pullback; `hg.map` witnesses that
  pullback preserves the unit condition. Naturality is required for every S-map.
- The identity condition is `hσ_one : ∀ T, σ T 1 isUnit_one = 1`. The bottom-right
  entry of the identity is 1, so the supplied existing unit proof has the exact type.
- The partial multiplication condition is `hσ_mul`: arbitrary matrices `a,b` and
  proofs `ha,hb,hab` require a, b, and ab to lie in Omega, and its equation is
  exactly `σ T a ha * σ T b hb = σ T (a * b) hab`. There is no requirement that
  Omega be a subgroup and no multiplication assumption outside these triples.
- The conclusion `∃! τ : ∀ T, ... →* H.obj.obj (op T), ...` supplies unique
  componentwise group homomorphisms. The first conjunct is naturality for every
  S-map and every determinant-one matrix. The second conjunct is the restriction
  equation for every `g` with `IsUnit (g 1 1)`. Uniqueness is among families satisfying
  both conjuncts; together these say exactly a unique group-sheaf homomorphism.
- The node's opening discussion of group schemes, separatedness and central exact
  sequences fixes terminology for its surrounding splitting application; none is
  an object or hypothesis of this extension assertion. In particular the theorem
  does not assume a central extension, nor that H is a scheme. The prescribed
  closed-immersion dependency module is imported, but its class supplies no binder.
- The formulas for Ga, Gm, x(u), y(v) and h(t) describe the chosen matrix cell and
  are not extra hypotheses or conclusions. They are consistent with the direct
  membership condition: x(u)h(t)y(v) has entries
  `(t + u*t⁻¹*v, u*t⁻¹; t⁻¹*v, t⁻¹)`. Conversely, for a determinant-one matrix
  `(a,b;c,d)` with d a unit, take `t=d⁻¹`, `u=b/d`, `v=c/d`; the determinant
  identity gives `a=d⁻¹+bc/d`. Thus the Lean domain is exactly that parameterized
  cell over every ring, including nonreduced and zero rings. No coordinate chart
  construction or representability theorem is substituted for the node's assertion.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; the structure and full locally affine condition
  were read, as was `Scheme.Hom` as a locally ringed-space morphism.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; the class extends
  `SurjectiveOnStalks` and has an `IsClosedEmbedding` field. This is contextual
  terminology only, as explained above; its recorded module is publicly imported.
- Existing Mathlib interfaces used directly: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology` in `Mathlib.AlgebraicGeometry.Sites.Fpqc`;
  `GrothendieckTopology.over` in `Mathlib.CategoryTheory.Sites.Over`;
  `Sheaf` in `Mathlib.CategoryTheory.Sites.Sheaf`;
  `GrpCat` in `Mathlib.Algebra.Category.Grp.Basic`;
  `Matrix.SpecialLinearGroup` and its `map` in
  `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup`; `Scheme.Hom.appTop`
  in `Mathlib.AlgebraicGeometry.Scheme`. Their source declarations were read.
- The proof dependency `lem-sfb-unimodular-linear-forms-fppf-cover` has no recorded
  Lean module in the assigned read clone, so there is no proof-only import to add.
  Its role, and all four original proof steps, are preserved in the docstring.

Edge cases checked: empty base and empty test scheme are allowed (the global
section ring may be the zero ring); no nontriviality condition is imposed.
Characteristic 2 and finite residue fields are allowed. The proof needs an fppf
cover rather than a point in the original ring simultaneously avoiding all forms.
Nonaffine tests and nonreduced tests are retained. For the identity, d=1 and the
cell is inhabited; for products leaving the cell there is no imposed equation.
The trivial target group and noncommutative targets are allowed. Empty comparison
words are handled by the identity hypothesis, as the proof docstring explains.
The ring-level chart calculation above also works when 0=1. No universe equality
or smallness assumption is imposed on the target sheaf.

Searches made (2026-10-24):

- `msearch.py ... leanfinder`: "A partially multiplicative natural map from the
  open cell of SL2 extends uniquely to an arbitrary fppf group sheaf". Eight hits,
  including ordinary gluing, `Presieve.IsSheafFor.unique_extend` and nonabelian
  cochain constructions. None extends a partial map from this non-covering cell.
- `msearch.py ... leansearch`: "A partially multiplicative map from the big open
  cell of SL2 to an fppf sheaf of groups extends uniquely to a natural group
  homomorphism". Eight hits, including `Matrix.SpecialLinearGroup.map` (used),
  `SpecialLinearGroup.toLinearEquiv`, and free-group uniqueness; no matching theorem.
- `msearch.py ... loogle "SpecialLinearGroup, Sheaf, fppfTopology"`: no hits;
  the service reported that the unqualified identifier `Sheaf` was unknown.
- `msearch.py ... grep "open.?cell|specialLinear|fppf" AlgebraicGeometry`:
  seven hits, identifying the actual Mathlib fppf precoverage/topology (used).
- `rg -l "specialLinear|SL2|sl2|openCell|open.cell" lean/Sheaf lean/WeilConjectures`
  and focused `rg -n "open.?cell|partial.*multiplic|extend.*SL|SL.*extend"`:
  existing field-based linear group schemes, rank-one root interfaces, and
  unrelated open-cell geometry. Read `LinearGroupSchemes.lean` and the SL2Hom
  interface; they are over fields with representable targets, not this arbitrary
  base/arbitrary group-sheaf extension. No duplicate declaration was found.
- `grep -rn "lem-sfb-sl2-open-cell-sheaf-extension" lean/WeilConjectures` and
  the proposed declaration-name search in `dag/lean_names_upstream.json`,
  `lean/WeilConjectures` and `lean/Sheaf`: no matches.

Source checked directly online: Brian Conrad, Reductive group schemes,
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, printed pp.130–131,
(4.3.2), including the explicit passage to an arbitrary group sheaf. It proves
extension by comparing finite cell-words after an fppf-local common translate.
The latest blueprint unit `sk-thm-sf-ctf-stability/_section.md` was also read; this
is a subordinate structural input and no unit statement changes.

Validation: the prescribed `scompile.py N8 lem-sfb-sl2-open-cell-sheaf-extension`
compiled both its sandbox and library module forms cleanly (1.6 seconds each),
with no diagnostics. All variables and universes are bound explicitly; there is
one public theorem with its whole proof `sorry`, and no helpers or diagnostic commands.

## Second reading by N8

This is the author's self-check; the maintainer's independent reading follows
separately. Re-read the node and the compiled theorem together. The two substantive
hypotheses on sigma are the unit equation and exactly the multiplication triples
in Omega; naturality is present on all S-maps. The source is the full determinant-one
matrix group of global functions, not just affine points or field points. H is a
bundled fppf group sheaf and carries no geometric hypotheses. The conclusion combines
natural group homomorphisms with the restriction equation inside one unique-existence
quantifier. The contextual central-extension terminology adds no extra hypotheses.
No node correction or change to the accepted split was necessary.
