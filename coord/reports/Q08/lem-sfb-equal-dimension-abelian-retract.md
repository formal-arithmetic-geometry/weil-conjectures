## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.EqualDimensionAbelianRetract`
states `AlgebraicGeometry.IsAbelianVariety.exists_iso_of_retraction_equal_dim` with
proof `sorry`.  No definition is introduced and no node statement is corrected.
The conclusion is an existential isomorphism `e : A ≅ B` with `e.hom = s` and
`e.inv = r`, which renders exactly that `s` is an isomorphism and that `r` is its
inverse.

Hypothesis and clause correspondence:

- The base field is `{k : Type u} [Field k] [IsAlgClosed k]`; `Field` is the
  Mathlib commutative field notion and `IsAlgClosed` is the algebraically closed
  field notion.
- The abelian varieties are `{A B : Over (Spec (.of k))}` with
  `[GrpObj A] [GrpObj B] [IsAbelianVariety A] [IsAbelianVariety B]`.  `Over`
  supplies the k-scheme structure, `GrpObj` supplies group operations, and
  `IsAbelianVariety` supplies properness, smoothness and connectedness.
- Equal dimension is `(hdim : A.left.dim = B.left.dim)`, using the recorded
  `AlgebraicGeometry.Scheme.dim` from `def-pc-dimension`.
- The homomorphisms are `(s : A ⟶ B) [IsMonHom s]` and
  `(r : B ⟶ A) [IsMonHom r]`.
- The one-sided inverse hypothesis is `(hsr : s ≫ r = 𝟙 A)`.  Since Lean's
  categorical composition `f ≫ g` means first `f`, this is exactly
  (r\circ s=\mathrm{id}_A) from the node.
- The conclusion is `∃ e : A ≅ B, e.hom = s ∧ e.inv = r`, retaining both maps
  and both inverse identities through the bundled isomorphism.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`, declaration
  `AlgebraicGeometry.IsAbelianVariety`, including its full class signature and
  docstring.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, Mathlib declarations
  `CategoryTheory.GrpObj`, `CategoryTheory.IsMonHom`, and the kernel/group-scheme
  interfaces documented there.
- `WeilConjectures.AlgebraicGeometry.Dimension`, declaration
  `AlgebraicGeometry.Scheme.dim`.
- The proof docstring records the proof-only declarations and their sources:
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny` provides
  `AlgebraicGeometry.IsIsogeny.finrank_eq`, `IsIsogeny.isFinite`, and
  `IsIsogeny.flat`; `Mathlib.AlgebraicGeometry.Morphisms.FlatRank` provides
  `Scheme.Hom.isIso_iff_finrank_eq`.  The finite-kernel equal-dimension lemma is
  a proof dependency with no Lean record yet, so it is named in the docstring
  but not imported or restated.

The proof docstring follows the four node proof clauses.  It computes the
scheme-theoretic kernel from the retraction and the fibre-product universal
property, applies the finite-kernel equal-dimension criterion, identifies the
finite-flat rank with the kernel order (one), applies the rank-one isomorphism
criterion, and finally proves that the given retraction equals the inverse.

Edge cases checked: dimension zero (the trivial abelian variety), the identity
map, multiplication-by-(n) maps (which have nontrivial kernels for (n>1) and
therefore do not satisfy the retraction hypothesis), inseparable/Frobenius
kernels in positive characteristic, and nonreduced finite kernels.  The
statement has no separability or positive-dimension assumption and the kernel
argument is scheme-theoretic, so these cases are retained.  The universes of
`k`, `A`, and `B` are shared as in the dependency declarations.

Searches for an existing declaration or duplicate:

- `msearch.py ... leanfinder "A split monomorphism between abelian varieties of equal dimension is an isomorphism"` returned eight categorical split-mono/isomorphism hits (such as `CategoryTheory.IsIso.of_mono_retraction`) but no abelian-variety theorem.
- `msearch.py ... loogle "IsAbelianVariety, IsIso"` returned zero hits (`IsAbelianVariety` is unknown to the standalone Loogle environment).
- `msearch.py ... grep "AbelianVariety|equal.*dim.*[Rr]etract|[Rr]etract.*dim"` returned only generic Mathlib retract lemmas; no matching geometric statement.
- Direct `rg` searches over `lean/WeilConjectures`, `lean/Sheaf`, `dag/lean_names_upstream.json`, and the item id found no existing declaration or duplicate.  The related landed
  `Sheaf.AlgebraicGeometry.AbelianVariety.MultipleRetraction` theorem concerns a
  different positive-integer retraction and does not state this item.

Validation: `scompile.py Q08 lem-sfb-equal-dimension-abelian-retract` compiled the
sandbox and library module separately against the live published build, with no
errors or warnings beyond the permitted `sorry` declaration warning.  The file
uses `set_option autoImplicit false`, and all variables and universes are explicit.
No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by Q08

I reread the node and the final Lean signature side by side.  The field,
abelian-variety, equal-dimension, two homomorphism, and one-sided inverse
hypotheses all occur exactly once.  The categorical order `s ≫ r` was checked
against the node's (r\circ s), and the existential bundled isomorphism was
checked to preserve the specified `s` and `r`.  No hypothesis or conclusion was
added, dropped, weakened, or strengthened.
