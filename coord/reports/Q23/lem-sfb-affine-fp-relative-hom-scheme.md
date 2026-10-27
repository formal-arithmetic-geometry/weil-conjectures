## Worker report

The module `Sheaf.AlgebraicGeometry.AffineFpRelativeHomScheme` states
`AlgebraicGeometry.Scheme.exists_affine_fp_relativeHomScheme` with its sole theorem
proof `sorry`. It introduces no definitions. The item is changed only in `lean`;
its natural-language statement, statement dependencies and accepted split are unchanged.

Source checked: `literature/stacks-project/more-morphisms.tex`, the full statements
and coefficient-construction proofs of Tags 05Y6 and 0BL3, lines 20100–20193.
The finite-presentation refinement is obtained by taking finitely many generators
and relations in the displayed construction. The recorded Conrad reference remains
WANTED; no unexamined Conrad result is used to alter the statement. The current
blueprint was searched under `literature/blueprint/latest/`; no replacement statement
for this prerequisite appeared. The declaration docstring carries all ten steps of
the accepted proof and their named prerequisites.

Hypothesis and conclusion correspondence:

| Node text | Lean rendering |
| --- | --- |
| Schemes S, X, Y and structural morphisms | `{S X Y : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)` |
| X finite locally free over S | `[p.IsFiniteLocallyFree]`, the recorded upstream class extending `IsFinite p`, `Flat p`, and `LocallyOfFinitePresentation p` |
| Y affine over S | `[IsAffineHom q]` |
| Y of finite presentation | `[LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]`, exactly the convention in the item |
| Affine representing S-scheme H | `∃ H : Over S, IsAffineHom H.hom ∧ …` |
| H of finite presentation | `LocallyOfFinitePresentation H.hom ∧ QuasiCompact H.hom ∧ QuasiSeparated H.hom` |
| Every S-scheme T | `∀ T : Over S`; there is no affine, nonempty or finite-type restriction on tests |
| Hom over S from T to H | `(T ⟶ H)` in `Over S` |
| Hom over T between X times T and Y times T | The morphisms between `(Over.pullback T.hom).obj (Over.mk p)` and `(Over.pullback T.hom).obj (Over.mk q)` in `Over T.left` |
| Natural bijections | `∃ e : ∀ T, … ≃ …`, together with the equation for every `T T'`, `a : T' ⟶ T`, and `g : T ⟶ H` |
| Restriction by base change | `pullback.map p T'.hom p T.hom (𝟙 X) a.left (𝟙 S)` is the canonical source restriction; the equation compares the two Y-coordinates |
| Every affine open U of S | `∀ (U : S.Opens) (hU : IsAffineOpen U), …` |
| Finite polynomial presentation over A | `n m : ℕ`, `r : Fin m → MvPolynomial (Fin n) Γ(S,U)`, and the ring `MvPolynomial (Fin n) Γ(S,U) ⧸ Ideal.span (Set.range r)` |
| Isomorphism over U to Spec P | `Nonempty (Over.mk (pullback.snd H.hom U.ι) ≅ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap …)) ≫ hU.isoSpec.inv))` |
| No group structure; zero and varying rank allowed | No group, rank, positivity or constant-degree binder occurs |

The naturality equation is exactly base-change naturality, not an unspecified
naturality condition. The left side is the Y-coordinate of the relative map
associated with `a ≫ g`. The right side first applies the canonical map
`X ×_S T' → X ×_S T` and then the Y-coordinate of the relative map associated
with g. Both maps into `Y ×_S T'` have the same T'-coordinate because the
codomain of each equivalence is a Hom in `Over T'`. Thus equality of the
Y-coordinates is equivalent, by pullback uniqueness, to equality with the
base-changed morphism. This quantifies over all morphisms a, including identities.
No auxiliary functor or duplicate relative-Hom definition is required.

For the last clause, it is equivalent to choose P to be the displayed quotient
itself: any algebra isomorphism from an arbitrary presented P induces the same
spectrum isomorphism over U. `hU.isoSpec.inv` identifies `Spec Γ(S,U)` with U.
Using an isomorphism in `Over U.toScheme` includes the structural-map equality;
it does not merely identify the underlying schemes. `Fin 0` allows both empty
families. The statement only asserts existence, and defines no chosen algebra
or representing scheme using a postponed existence proof.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-pc-finite-locally-free`:
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`, declaration
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` (full class read at lines 893–900).
- `pqf-def-affine-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
  declaration `AlgebraicGeometry.IsAffineHom`.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, declaration
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-pbc-scheme-conventions` is a convention record, with no owning
  declaration. Its prescribed finite-presentation conjunction uses the preceding
  class and `AlgebraicGeometry.QuasiCompact`, `AlgebraicGeometry.QuasiSeparated`
  from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and `…QuasiSeparated`.
  Their full definitions were read, including quasi-compactness of the diagonal.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, declarations
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.map`.
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies pullbacks of schemes.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Spec` and `Spec.map`.
- The existing Mathlib interfaces `CategoryTheory.Over`, `Over.mk`, `Over.w`,
  `Over.pullback`, `AlgebraicGeometry.IsAffineOpen.isoSpec`, `MvPolynomial`,
  `Ideal.span` and `Ideal.Quotient` supply the rest of the statement. Their
  definitions are read in `Comma/Over/Basic`, `Comma/Over/Pullback`,
  `AlgebraicGeometry/AffineScheme`, and the polynomial and quotient modules.

The available proof-dependency modules are imported plainly, including the
recorded upstream finite-pushforward theorem and
`Sheaf.AlgebraicGeometry.ExistsSchemeOfZariskiCocycle`. Mathlib-match proof
prerequisites are imported through AffineScheme, Finite, Proper, Restrict,
MvPolynomial.Basic, TensorProduct.Maps, Pullbacks, Gluing, Yoneda, Affine,
FinitePresentation and Separated. The proof-only prerequisite
`lem-sfb-finite-free-algebra-map-coordinates` currently has neither a Lean record
nor a Mathlib match, so there is no module of that node to import yet. Its full
mathematical role is retained in step 4 of the docstring.

Edge cases checked mathematically before drafting:

- Rank zero: X is empty over that base chart, so every test has exactly one
  relative morphism; H is the base chart, with zero variables and relations.
- Varying rank: finite local freeness imposes no global constant rank; the
  representing scheme is glued from the local coefficient schemes.
- X = S: the relative Hom functor is represented by Y, consistent with every clause.
- Empty base and empty test schemes: all Hom-over-base and pullback expressions
  remain meaningful and the required singleton/empty cases are not excluded.
- Empty target: maps exist precisely on the rank-zero locus of X, a clopen
  base locus, consistent with an affine finitely presented representing scheme.
- The empty affine open has zero section ring, and its spectrum quotient is empty.
- Zero generators or relations are admitted, and no Noetherian, characteristic,
  field or separated-base condition is present.
- All schemes and tests use the same arbitrary universe u; the tests do not
  quantify over an independently smaller universe.

Searches (exact external-search records are also in sandbox `searches.jsonl`):

- LeanFinder via `msearch.py`: “The relative Hom functor from a finite locally
  free scheme to an affine finitely presented scheme is represented by an affine
  finitely presented scheme”. Eight hits, including affine-space finite
  presentation and finitePresentation_appLE; none states this theorem.
- Loogle via `msearch.py`: `AlgebraicGeometry.Scheme, CategoryTheory.Over.pullback`.
  Five hits, concerning monoid pullback and flat-descent faithfulness; no relative
  Hom representability theorem.
- Mathlib grep via `msearch.py`: `relativeHom|homScheme|WeilRestriction|weilRestriction`
  in `AlgebraicGeometry`: zero hits.
- LeanSearch via `msearch.py`: “finite locally free source affine target relative
  Hom scheme representable finite presentation”. Eight hits, including
  `Scheme.LocalRepresentability.isRepresentable` and the finite-presentation
  predicates. The local-representability theorem is a general gluing criterion,
  not the claimed relative-Hom representability statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, using the same relative-Hom
  pattern and the item id: only unrelated derived relative-Hom/constant Weil
  restriction declarations; no duplicate construction or theorem.
- `rg` for `exists_affine_fp_relativeHomScheme` in both library roots and
  `dag/lean_names_upstream.json`: no existing declaration of that name.
- `rg` in `literature/blueprint/latest/` for relative Hom, 05Y6 and 0BL3:
  unrelated derived-Hom text only, consistent with the recorded null unit ancestor.

No statement correction, disputed statement, new definition node, or dependency
repair is needed. The current compiler result and dry-run result are recorded below.

Validation: `scompile.py Q23 lem-sfb-affine-fp-relative-hom-scheme` compiled the
module in sandbox and library modes with no errors or warnings after replacing
the unnecessary `simpa` in a pullback compatibility proof argument.
`deliver2.py Q23 lem-sfb-affine-fp-relative-hom-scheme --no-push` printed
`OK (dry run): commit 4af2ce4321b passes the preflight and compiles; nothing pushed`.
The report is now updated with that validation before the final delivery.

## Second reading by Q23

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
