## Worker report

The module `Sheaf.AlgebraicGeometry.BertiniPrescribedPointDimensionCut` states
`AlgebraicGeometry.exists_integral_closedSubscheme_dimension_cut_through_finite_closedPoints`.
Its only proof is `sorry`; it introduces no definitions or extra nodes. The node is
unchanged except for `lean`. The source read is Charles–Poonen,
`literature/charles-poonen-bertini-irreducibility.pdf`, Theorem 1.8 and its proof on
printed p. 4. This is the codimension-one result itself, rather than Corollary 1.9.
The source's reduction by Nagata and Chow confirms that quasi-projectivity and
properness are not input hypotheses. The supplied node has already specialized to
algebraically closed fields and reduced induced structures.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]` |
| Scheme X over k | `(X : Scheme.{u}) [X.Over (Spec (.of k))]` |
| X integral, including nonemptiness | `[IsIntegral X]` |
| X separated over k | `[IsSeparated (X ↘ Spec (.of k))]` |
| X finite type over k | `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and `[QuasiCompact (X ↘ Spec (.of k))]` |
| Integer dimension m at least two | `(m : ℕ) (hm : 2 ≤ m)`; these are precisely the integers at least two |
| Topological Krull dimension X = m | `(hX : topologicalKrullDim X = (m : WithBot ℕ∞))` |
| Finite subset of the underlying space | `(F : Set X) (hF : F.Finite)` |
| Each prescribed point closed | `(hclosed : ∀ x ∈ F, IsClosed ({x} : Set X))` |
| Existence of Y and a morphism i to X | `∃ (Y : Scheme.{u}) (i : Y ⟶ X), ...` |
| Y integral | `IsIntegral Y` |
| Y a separated k-scheme | `IsSeparated (i ≫ (X ↘ Spec (.of k)))` |
| Y finite type over k | `LocallyOfFiniteType (i ≫ (X ↘ Spec (.of k)))` and `QuasiCompact (i ≫ (X ↘ Spec (.of k)))` |
| Dimension Y = m - 1 | `topologicalKrullDim Y = ((m - 1 : ℕ) : WithBot ℕ∞)` |
| i a closed immersion | `IsClosedImmersion i` |
| F contained in the image | `F ⊆ Set.range i` |

The k-structure on Y is exactly the composite `i ≫ (X ↘ Spec (.of k))`.
Consequently i is over k by construction; there is no arbitrary second structure
map or missing compatibility hypothesis. Both dimensions are finite natural-number
values in Mathlib's extended dimension type. Natural subtraction agrees with integer
subtraction here because `2 ≤ m`. The common scheme/field universe is the project's
standard universe convention and leaves every field and finite-type variety covered.

Statement dependencies read and used (the full signatures and adjacent docstrings
were read in the pinned Mathlib source):

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, line 180.
- `def-weil-algebraic-closure`: the recorded match explicitly identifies the
  algebraically closed predicate with `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, line 62. No algebraic extension of another
  base field is part of this specialization, so no `AlgebraicClosure` is chosen.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms,
  `Mathlib.AlgebraicGeometry.Scheme`, line 42 and namespace `Scheme`.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties`, line 240. It includes nonemptiness and
  integral sections on nonempty opens.
- `def-weil-proper-morphism`: its separatedness declaration is
  `AlgebraicGeometry.IsSeparated`, `Mathlib.AlgebraicGeometry.Morphisms.Separated`,
  line 44, available through the recorded `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
  The stronger `IsProper` predicate is not used in the signature.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, line 43, together with
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  line 43, exactly as the node's record prescribes for finite type.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  `Mathlib.Topology.KrullDimension`, line 39, the dimension of irreducible closed chains.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, line 45.

All recorded proof-dependency modules are imported without `public`, including
Mathlib leaves (`Noetherian`, `AlgClosed.Basic` and finite-type/proper APIs), the
recorded upstream dimension-of-opens and proper-map lemmas, and the project's
Bertini, reduced-induced-structure, pure-dimension and closed-point modules.
The Chow-envelope and immersive-finite-base nodes have no recorded Lean statement
or Mathlib match at the time of reading, so there is no module to import for them.
They are proof dependencies only; no notion required by this signature is missing.
The theorem's docstring includes all seven supplied proof steps and identifies
these future proof inputs. No proof dependency was replaced or silently discarded.

Edge cases checked before writing:

- `F = ∅` is allowed: finiteness holds and the pointwise closedness condition is
  vacuous. No nonemptiness assumption was introduced. The proof adds an extra point
  over the birational isomorphism open; `IsIntegral Y` still requires nonempty Y.
- `m = 2` gives an integral curve with dimension one. Zero and one are excluded
  exactly by the supplied lower bound; infinite dimension is excluded exactly by
  the supplied equality. No issue with truncated subtraction occurs for `m ≥ 2`.
- Singular, nonproper and non-quasi-projective X are allowed. No smoothness,
  properness, projectivity, quasi-projectivity or characteristic assumption appears.
- Nonclosed prescribed points cannot silently enter: closed singletons are an
  explicit hypothesis for every member. A set encoding makes repeated markings
  irrelevant, just as in the node.
- Empty X is already excluded by integrality; no extra nonempty-X binder is needed.

Searches actually run on 2026-10-24:

1. `msearch.py ... leanfinder` with query
   `An integral separated finite type scheme over an algebraically closed field contains an integral closed subscheme of dimension one less through any finite set of closed points`.
   Eight results: integral schemes, proper/universally-closed global-section facts,
   and Jacobson fibres. None states existence of the required subvariety.
2. `msearch.py ... loogle` with query
   `AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.IsIntegral`.
   Successful search, zero hits.
3. `msearch.py ... grep` with query
   `Bertini|bertini|prescribed.point|dimension.cut`, subdirectory `AlgebraicGeometry`.
   Successful search, zero Mathlib hits.
4. `rg -n 'bertini|Bertini|prescribed.point|dimension.cut'` on both
   `lean/WeilConjectures` and `lean/Sheaf`. Found Bertini–Noether specialization,
   existing linear-system Bertini smooth/irreducible-member statements, and unrelated
   ring-theoretic dimension cuts, but no prescribed-point integral dimension cut.
5. `grep -rn 'lem-sfb-bertini-prescribed-point-dimension-cut' lean/WeilConjectures`:
   no upstream declaration tagged for the item.
6. Exact-name/concept check using `rg -n` for
   `exists_integral_closedSubscheme_dimension_cut_through_finite_closedPoints|dimension_cut_through|prescribed.*closed.*point`
   on both Lean library trees: only two unrelated prescribed-point docstrings.

Validation: `scompile.py Q03 lem-sfb-bertini-prescribed-point-dimension-cut <module>`
compiled both the wrapper's sandbox and library-module forms successfully (1.7 s and
1.8 s). There were no errors or unexpected warnings. The file sets `autoImplicit false`
and declares its universe and every variable explicitly. Its line widths are at most
100 characters. There are no statement disputes or corrections.

## Second reading by Q03

This is the dispatcher's requested single-worker task; no other agents were started.
I reread the node alongside the final signature as a separate self-review pass;
this section does not claim an independent worker review. The maintainer's independent
review is still required by the dispatch brief.

The rereading checked the field and algebraic closedness, all three properties of X
(integral, separated, finite type), the lower bound and dimension equation, finiteness
and closed singletons of F, and every existential clause for Y and i against the table
above. In particular, the composite k-structure on Y makes i a k-morphism and prevents
an unrelated k-structure from satisfying the conclusion. The finite-type conclusion
has both locally finite type and quasi-compactness. The image containment uses the
underlying continuous map of i, and the dimension subtraction is taken in naturals
before coercion, so it gives precisely the required finite dimension m - 1.

No mismatch or added geometric assumption was found; no change was needed after this
pass. The proof docstring was also reread against all seven node proof steps,
including the extra point for empty F, proper image, and the final dimension argument.
