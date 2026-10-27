## Worker report

The module `Sheaf.AlgebraicGeometry.AffinePolynomialEmbeddingPseudoCoherence` states
`AlgebraicGeometry.Scheme.isMPseudoCoherent_affine_polynomial_embedding_iff`.
Its only theorem proof is `sorry`, as required for stage 2. It adds no definitions.
The node is changed only in `lean`; the informal statement and dependency lists are unchanged.

Source checked: `literature/stacks-project/more-morphisms.tex`, Tag 09VC,
`lemma-relatively-pseudo-coherent`, including its full proof. This is precisely the
pairwise comparison used to establish the source's some-embedding/all-embeddings equivalence.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Affine schemes X and S | `{X S : Scheme.{u}} [IsAffine X] [IsAffine S]` |
| A finite type morphism f : X → S | `(f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]` |
| E in the full D(O_X) | `(E : schemeDerivedCategory X)` |
| An arbitrary integer m | `(m : ℤ)` |
| Arbitrary n,r ≥ 0 | `(n r : ℕ)` |
| The relative affine spaces | `AffineSpace (ULift.{u} (Fin n)) S` and its r version |
| Closed immersion i into the first affine space | `(i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S) [IsClosedImmersion i]` |
| Closed immersion j into the second affine space | The corresponding j binder with `[IsClosedImmersion j]` |
| Both embeddings are over the fixed S-morphism f | `hi : i ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = f` and `hj` |
| Ri_*E is m-pseudo-coherent on the first affine space | `IsMPseudoCoherent (AffineSpace (ULift.{u} (Fin n)) S) m ((schemeDerivedDirectImage i).obj E)` |
| If and only if Rj_*E is m-pseudo-coherent on the second | `↔` followed by the same predicate with r and j |
| No quasi-coherence of the cohomology of E assumed | No `schemeDerivedQCohProperty`, boundedness, flatness or Noetherian binder occurs |

The `HasDerivedCategory` instances specify the localizations used by the dependency
interfaces. Their universes `wX`, `wN`, `wR` are independent. For each target the
open-subscheme localizations use that target's universe, exactly as required by
`Scheme.IsMPseudoCoherent`. They impose no mathematical condition on E or the schemes.
`ULift.{u} (Fin n)` is the library's finite affine-space index at scheme universe u;
it does not impose u = 0.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
  These are publicly available through the affine-space import; no duplicate Scheme import.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine`, also exposed
  by the affine-space import.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`,
  exposed by FiniteType. These are the dependency's recorded finite-type conjunction.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, on the shared `SheafOfModules` carrier.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace` and its
  canonical structure map `AffineSpace.over`. The latter is the first projection.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage`.
- `Sheaf.AlgebraicGeometry.MPseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsMPseudoCoherent`. Its full definition was read: local
  strictly perfect approximations on open subschemes with isomorphisms above m and
  epimorphism in degree m. Its use retains the same m on both sides.

All recorded proof-dependency modules that exist are plain imports: polynomial rings
(`Mathlib.Algebra.MvPolynomial.Basic`), regular sequences and Koszul complexes
(`WeilConjectures.RingTheory.RegularSequenceKoszulRegular`,
`WeilConjectures.AlgebraicGeometry.KoszulComplex`), tilde/free and tilde/pushforward
(`Mathlib.AlgebraicGeometry.Modules.Tilde`), the affine pseudo-coherence criterion
(`WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentCriterion`), and derived direct
image composition (`WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition`).
The proof dependency `lem-sfb-closed-pushforward-pseudocoherence` has no Lean record
or Mathlib match in the checked DAG and is therefore not imported. It is used only
in the proof plan, not needed to state this theorem. No proof import cycle is introduced.
The theorem docstring includes all five proof steps and names their dependencies.

Edge cases checked before writing:

- n = 0 or r = 0: `Fin 0` is empty, so both canonical zero-dimensional affine charts
  remain allowed. The graph resolution is then the degree-zero identity resolution.
- n = r and i = j: the statement becomes reflexivity of the predicate, even if the
  two derived-category presentations have different permitted morphism universes.
- Empty X or S and zero coefficient rings: no point, nonempty, domain or characteristic
  hypothesis is imposed; the monic-polynomial proof works over the zero ring too.
- E zero, unbounded, or without quasi-coherent cohomology: all are allowed.
- Negative, zero and positive m: the binder is ℤ, and both predicates use exactly m.
- No shift by either affine-space dimension occurs.

Searches for an existing statement (msearch wrapper, Q58 / this item):

- LeanFinder: `For two closed embeddings of a finite type affine scheme into affine
  spaces over the same affine base, the derived pushforwards of any complex are m
  pseudo coherent simultaneously` — eight hits about ordinary finite-type morphisms,
  affine descent and module pushforward; none states the comparison.
- LeanSearch: `Independence of finite degree pseudo coherence under two closed
  embeddings into relative affine spaces` — eight hits about affine independence,
  finite morphisms and closed immersions; no derived pseudo-coherence result.
- Loogle: `"PseudoCoherent", "pushforward"` — zero hits.
- Mathlib grep: `pseudo.?coher|IsMPseudoCoherent` — zero hits.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `IsMPseudoCoherent|polynomial.*[Ii]nvar|embedding.*[Pp]seudo|affine_polynomial`:
  found the shared scheme definition, its relative version and ring-level results.
  `Sheaf.RingTheory.PolynomialPresentationPseudoCoherence` states the all-degrees
  ring restriction-of-scalars theorem, not this fixed-degree scheme theorem for arbitrary
  sheaf complexes, so it cannot replace the present declaration.
- `grep -rn` for the item id in `lean/WeilConjectures` — no hits.
- `rg` for `embedding.*pseudo|affine_polynomial_embedding|polynomial_embedding` in
  `dag/lean_names_upstream.json`, `lean/WeilConjectures`, `lean/Sheaf` — no hits.

No statement fault or disputed mathematical clause was found. No new node or dependency
interface repair was required.

## Second reading by Q58

A separate second pass by the same worker reread the node, the source proof and the
complete Lean signature; the dispatch instruction prohibits starting another agent.
This is a self-review, not an independent worker review. The maintainer's independent
delivery review remains required.

The second pass checked each correspondence in the table: both schemes are affine;
finite type has both recorded components; E is in D(O_X), not a QCoh subcategory;
n and r include zero; both maps are closed immersions; hi and hj assert compatibility
with the same f; both sides use the recorded derived direct image and the identical
integer m; the result is an equivalence. It checked the affine-space structure map
against `AffineSpace.over`, and the dependent open-localization instances against the
full definition of `IsMPseudoCoherent`. No mismatch or correction was found.

Validation uses only the prescribed `scompile.py` and `deliver2.py` wrappers. The delivered
file contains no diagnostic commands, local notation, private helpers or auto-bound variables.
