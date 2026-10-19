## Worker report

Existing-declaration delivery for `lem-sfb-smul-id-in-w`. No Lean library module is added.
The two existing lemmas in
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization` together say
exactly what the node says. The inherited attachment already names both, but lacks a
module, primary declaration, signature, and existing-declaration metadata. Only the
node's `lean` field is completed. The old audit's module path omits `Complete`; the
actual declaration file and the dependency's landed record use `Complete.Rationalization`.

The node and its source were read in
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`
`sk-def-sfb-rationalization/lem-sfb-smul-id-in-w.md`; their statements agree verbatim.
The dependency node `def-sfb-rationalization-morphisms`, its `lean` record, and the full
upstream definition and docstring of `CategoryTheory.Rationalization.W` were read.
The setting is inherited from `lem-sfb-torsion-triangulated`, also read with its record.

Hypothesis and conclusion correspondence:

- The commutative coefficient ring is `{R : Type w} [CommRing R]`, and the submonoid is
  `(M : Submonoid R)`.
- The category is `(C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]`, with
  `[HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]`,
  `[∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C]`. These are exactly the
  dependency's pretriangulated linear setting, without an added octahedral-axiom
  hypothesis or any domain/nonzero assumption on the coefficient ring.
- `m ∈ M` is `{m : R} (hm : m ∈ M)` in `W_smul_id`; the object is `(X : C)`.
- Every cone is represented by the arbitrary binders `{X Z : C} (m : R)` and
  `(g : X ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)` and the witness
  `(hT : Triangle.mk (m • 𝟙 X) g h ∈ distTriang C)` in `smul_id_cone_eq_zero`.
  Its conclusion is `(m * m) • 𝟙 Z = 0`, exactly annihilation by m squared.
  No particular chosen cone is substituted for this universal clause. This lemma
  holds for arbitrary m, so its application to the node's m in M requires no further
  hypothesis.
- The final clause is `W M C (m • 𝟙 X)`, the conclusion of `W_smul_id`.
  The recorded dependency declaration `CategoryTheory.Rationalization.W` is used
  literally by this lemma. Its definition `(torsion M C).trW` unfolds through
  `CategoryTheory.ObjectProperty.trW` to the existence of a distinguished triangle
  on this very morphism with torsion third object. `torsion M C Z` means
  `∃ m ∈ M, m • 𝟙 Z = 0`; the proof uses `M.mul_mem hm hm` for the witness m squared.

Exact source signatures, with their section variables as listed above:

```lean
lemma smul_id_cone_eq_zero {X Z : C} (m : R) (g : X ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (m • 𝟙 X) g h ∈ distTriang C) : (m * m) • 𝟙 Z = 0 :=
lemma W_smul_id {m : R} (hm : m ∈ M) (X : C) : W M C (m • 𝟙 X) :=
```

Dependency declarations used:

- `WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization`:
  `CategoryTheory.Rationalization.W` (recorded statement dependency), and its actual
  object predicate `CategoryTheory.Rationalization.torsion`.
- `Mathlib.CategoryTheory.Triangulated.Subcategory`:
  `CategoryTheory.ObjectProperty.trW`, whose full definition and docstring were read.
- The same upstream rationalization module supplies the two existing lemmas and the
  inherited setting of `CategoryTheory.Rationalization.instIsTriangulatedTorsion`.

The upstream proof was read: distinguished-triangle exactness factors m times the
identity of Z through h; shift linearity gives m times h equal to zero, so m squared
annihilates Z. A distinguished cocone exists for m times the identity, and its torsion
witness m squared lies in M. This is the node's proof, with Lean composition order.

Edge cases checked: m = 0 when 0 belongs to M makes both annihilation and membership
valid; m = 1 gives a zero cone; M containing only 1 is allowed; the zero object is
allowed; the zero ring and rings with zero divisors are allowed. Universes w, u, v
are independent, with no universe equality or smallness restriction. An empty M is
not a submonoid (1 belongs to every submonoid). No source or statement correction is
needed, and there is no disputed statement.

Searches made:

- `msearch.py`, LeanFinder: "In a linear triangulated category the cone of multiplication
  by m is annihilated by m squared and the scalar identity has torsion cone".
  Eight hits included `ObjectProperty.smul_mem_trW_iff`,
  `Triangulated.Subcategory.smul_mem_W_iff`, and triangle exactness; none gives this
  precise pair of clauses for a commutative-ring submonoid.
- `msearch.py`, Loogle:
  `CategoryTheory.Rationalization.W_smul_id, CategoryTheory.Rationalization.smul_id_cone_eq_zero`.
  No hits; Loogle reports the upstream name unknown to its Mathlib index.
- `msearch.py`, Mathlib grep in CategoryTheory:
  `smul_id_cone_eq_zero|W_smul_id|smul.*cone`. No hits.
- `rg` of the source `WeilConjectures` tree with that same expression found the exact
  two declarations at lines 119 and 145 of `CategoryTheory/DerivedCategory/Complete/`
  `Rationalization.lean`, and their uses and explanatory module docstring.
- `rg` of the source tree for the blueprint id found no textual tag. `rg` of
  `dag/lean_names_upstream.json` for the two names found no entries; these indexes
  predate the upstream attachment.
- `rg` of `lean/Sheaf` with the same expression found only an unrelated integer-scalar
  computation in `PreorderBarTotalCone.lean`, and no duplicate statement.

Validation: `scompile.py Q71 lem-sfb-smul-id-in-w` passed cleanly on the sandbox
scratch probe importing the actual upstream module and checking both fully explicit
signatures. Each lemma uses only propext, Classical.choice, and Quot.sound; neither
uses sorry. The delivery dry run also generates and compiles its own existing-declaration
probes. No library source is edited and no theorem is reproved.

## Second reading by Q71

I independently read the node statement, its blueprint source and proof, the copied
dependency node `def-sfb-rationalization-morphisms`, and the complete upstream source
`WeilConjectures/CategoryTheory/DerivedCategory/Complete/Rationalization.lean`.

The statement's objects and hypotheses render as follows. The coefficient ring is
`{R : Type w} [CommRing R]`, the submonoid is `(M : Submonoid R)`, and the category is
`(C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]`. The required categorical
structure is `[HasZeroObject C] [HasShift C ℤ]`, additive and `R`-linear shift functors,
and `[Pretriangulated C]`. These are exactly the inherited setting; there is no extra
`IsTriangulated`, field, nonzero, finiteness, or universe-equality assumption.

The first conclusion clause, “every cone of `m • id X` is killed by `m²`”, is rendered
by `CategoryTheory.Rationalization.smul_id_cone_eq_zero`: arbitrary `{X Z : C}`, arbitrary
`m : R`, maps `g : X ⟶ Z` and `h : Z ⟶ X⟦(1 : ℤ)⟧`, and an arbitrary distinguished-triangle
witness for `Triangle.mk (m • 𝟙 X) g h`, concluding `(m * m) • 𝟙 Z = 0`. Thus it does not
silently choose a cone or weaken the universal quantifier. The “in particular” clause is
rendered by `CategoryTheory.Rationalization.W_smul_id`, with `{m : R}`, `hm : m ∈ M`, and
`X : C`, concluding exactly `W M C (m • 𝟙 X)`. The latter uses the recorded dependency
`CategoryTheory.Rationalization.W`, whose `trW` definition is the existence of precisely
such a distinguished cone with an `M`-torsion third object.

Edge cases remain covered: `m = 0` when `0 ∈ M`, `m = 1`, submonoids consisting only of
units (including `{1}`), the zero object, zero rings and rings with zero divisors, arbitrary
characteristic, and independent universes `w`, `u`, and `v`. A submonoid is nonempty by
`1 ∈ M`, so the source does not require an additional nonemptiness hypothesis.

I repeated the existing-notion searches with LeanFinder, Loogle, `rg` over Mathlib,
`WeilConjectures/`, and this repository's `lean/Sheaf`, and checked the upstream-name
index. Only the two exact upstream declarations were found; no duplicate project or
Mathlib statement exists. The source signatures and `#print axioms` output were checked
through the required `scompile.py` wrapper and are sorry-free.

The only mismatch was inherited metadata: the old audit mentioned the stale module path
`...DerivedCategory.Rationalization` and did not provide a primary declaration/signature.
The node copy now records module
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization`, primary
declaration `CategoryTheory.Rationalization.W_smul_id`, both declarations, the verbatim
signature, `existing: true`, and Q71/date metadata. No Lean source, statement, dependency,
or mathematical clause required repair.
