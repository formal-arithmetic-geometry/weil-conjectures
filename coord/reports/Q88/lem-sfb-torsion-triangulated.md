## Worker report

No Lean module is added. The node is already represented by the exact upstream declarations
`CategoryTheory.Rationalization.instIsTriangulatedTorsion` and
`CategoryTheory.Rationalization.smul_id_obj₂_eq_zero` in
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization`.
The node had previously been attached to these declarations; this delivery records the
required stage-2 `existing: true` record and the source signature
`instance instIsTriangulatedTorsion : (torsion M C).IsTriangulated where`.

The hypotheses are rendered by the upstream enclosing binders: `{R : Type w}` with
`[CommRing R]`, `(M : Submonoid R)`, `(C : Type u)` with `[Category.{v} C]`,
`[Preadditive C]`, `[Linear R C]`, and the pretriangulated-section assumptions
`[HasZeroObject C]`, `[HasShift C ℤ]`, `[∀ n : ℤ, (shiftFunctor C n).Additive]`,
`[∀ n : ℤ, (shiftFunctor C n).Linear R]`, and `[Pretriangulated C]`.
The instance type `(torsion M C).IsTriangulated` renders the three triangulated-subcategory
clauses: it contains zero, is stable under integer shifts, and is closed under distinguished
triangles. The companion lemma has the exact middle-object clause: for
`T : Triangle C`, `hT : T ∈ distTriang C`, and witnesses
`h₁ : m₁ • 𝟙 T.obj₁ = 0` and `h₃ : m₃ • 𝟙 T.obj₃ = 0`, it concludes
`(m₁ * m₃) • 𝟙 T.obj₂ = 0`. The source instance constructs the product witness using
`M.mul_mem`, so the conclusion keeps the required `m₁m₃ ∈ M` clause from the node.

I read the dependency node `def-sfb-torsion-objects`. Its recorded declaration
`CategoryTheory.Rationalization.torsion` in the same upstream module is the exact predicate
`∃ m ∈ M, m • 𝟙 X = 0`; no private definition is introduced. The source docstrings and full
signatures were read for both the dependency and the two declarations above.

Edge cases checked: `M` always contains `1`; when `0 ∈ M` every object is torsion; for the
trivial submonoid `{1}`, torsion means a zero identity; the zero object is included; no
nonzero-ring, characteristic, abelian, or nonempty-category assumption is added; and the
universes `w`, `u`, and `v` remain independent.

Searches made:

- `msearch.py Q88 lem-sfb-torsion-triangulated grep
  "instIsTriangulatedTorsion|smul_id_obj₂_eq_zero" WeilConjectures/CategoryTheory`: no hits
  through the wrapper's subdirectory query (the direct source search below found the declarations).
- `msearch.py Q88 lem-sfb-torsion-triangulated leanfinder
  "torsion objects form a triangulated subcategory"`: returned generic
  `CategoryTheory.ObjectProperty.IsTriangulated` and closure declarations, with no exact
  torsion declaration.
- `msearch.py Q88 lem-sfb-torsion-triangulated loogle
  "ObjectProperty.IsTriangulated, torsion"`: zero hits; Loogle reported the project identifier
  as unknown.
- `msearch.py Q88 lem-sfb-torsion-triangulated grep
  "instIsTriangulatedTorsion|smul_id_obj₂_eq_zero"
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures`: four hits in
  `CategoryTheory/DerivedCategory/Complete/Rationalization.lean`.
- Direct `rg` over the upstream source and the DAG found no competing project declaration.

No new node, dependency module, statement correction, or `STATEMENT-DISPUTED` issue applies.

## Second reading by Q88

I read the node statement, its blueprint source place, the dependency
`def-sfb-torsion-objects`, and the upstream source declaration. The item-by-item
match is as follows:

- The category `\mathcal T` is the upstream `C : Type u` with
  `[Category.{v} C]` and `[Preadditive C]`; this is the same preadditive category.
- Linearity over the commutative ring `R` is `[CommRing R]` and `[Linear R C]`,
  with `R : Type w`; no extra ring or universe restriction is present.
- The submonoid `M \subseteq R` is exactly `(M : Submonoid R)`.
- “Pretriangulated” is `[HasZeroObject C]`, `[HasShift C ℤ]`, additive and
  `R`-linear shift functors, and `[Pretriangulated C]`, exactly the assumptions
  enclosing `instIsTriangulatedTorsion`.
- “Contain `0`” and “stable under shifts” are the `ContainsZero` and
  `IsStableUnderShift ℤ` fields of `(torsion M C).IsTriangulated`.
- For a distinguished triangle, the upstream `IsTriangulatedClosed₂` field
  uses `T : Triangle C`, `hT : T ∈ distTriang C`, and torsion witnesses
  `m₁ ∈ M`, `m₃ ∈ M` with `m₁ • 𝟙 T.obj₁ = 0` and
  `m₃ • 𝟙 T.obj₃ = 0`; it returns the witness
  `m₁ * m₃ ∈ M` and `(m₁ * m₃) • 𝟙 T.obj₂ = 0`. This is exactly the final
  clause of the node, with the dependency's torsion predicate unfolded.

The recorded Lean declaration is
`CategoryTheory.Rationalization.instIsTriangulatedTorsion` with the verbatim
signature `instance instIsTriangulatedTorsion : (torsion M C).IsTriangulated where`;
the companion declaration `CategoryTheory.Rationalization.smul_id_obj₂_eq_zero`
supplies the stated middle-object annihilation. I found no mismatch and made no
statement change. The dependency declaration
`CategoryTheory.Rationalization.torsion` is the exact predicate
`∃ m ∈ M, m • 𝟙 X = 0`.

Edge cases checked: the empty category is covered by the universal class
assumptions; the zero object is included by `ContainsZero`; `M = ⊥` (the trivial
submonoid) and `0 ∈ M` are allowed; `n = 0` is included among all integer shifts;
and the independent universes `w`, `u`, and `v` introduce no restriction. No
characteristic, nonzero-ring, abelian, or nonempty-category assumption is added.

I repeated the existing-definition searches. The `msearch.py` grep wrapper query
returned no hit in its relative subdirectory mode, while direct `rg` found both
declarations in `WeilConjectures/CategoryTheory/DerivedCategory/Complete/Rationalization.lean`.
LeanFinder returned only generic `ObjectProperty.IsTriangulated` declarations,
and Loogle returned no result (its project identifier was unknown). Searches of
Mathlib, `WeilConjectures/`, and the repository's `lean/Sheaf/` found no competing
declaration. Therefore no module is added; the node's `lean` record is repaired
to the exact upstream existing declaration and its companion.
