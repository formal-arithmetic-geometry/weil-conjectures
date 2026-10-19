## Worker report

This delivery records an exact existing match, without adding a Lean module or a duplicate
statement. The source is `WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows`, lines
170–182, confirmed against the current source returned by `scompile.py --source`.
The declarations are `HomologicalComplex₂.singleRow₀ObjTotal` and
`HomologicalComplex₂.singleRow₀ObjTotal_hom_naturality`. Only the item's `lean` record changes.
There is no repair note for this item.

Hypothesis and clause correspondence:

- The category `C` is an arbitrary `Type u` with `Category.{v} C`, `Preadditive C`,
  and `HasZeroObject C`. The source's `Type*` and category instance elaborate with independent
  object and morphism universes, as confirmed by the compiled fully explicit `#check`.
- Every integer cochain complex is the binder `(L : CochainComplex C ℤ)`. This is Mathlib's
  `HomologicalComplex C (ComplexShape.up ℤ)`: differentials have degree +1 and their successive
  composites vanish. No boundedness, abelian-category, or derived-category hypothesis is added.
- The row bicomplex is `(HomologicalComplex₂.singleRow C (up ℤ) (up ℤ) 0).obj L`.
  The source defines `singleRow` by applying the single-complex functor in the second
  coordinate to the first-coordinate complex. `singleRowXXIso` identifies its row-zero terms
  with `L.X i`, `isZero_singleRow_X_X` makes every other row zero, and
  `singleRow_obj_d_f` identifies the row-zero differential with that of `L`.
- Diagonal coproduct totalization is `.total (up ℤ)`, the existing Mathlib total complex.
  Its `HasTotal` condition is the existence of the coproduct over pairs with `x + y = n`.
  The upstream instance in this same module constructs that coproduct from
  `cofanSingleRowObjTotal` and `isColimitCofanSingleRowObjTotal`. Thus a general countable
  coproduct assumption is unnecessary: only `(n, 0)` can have a nonzero summand.
- The canonical isomorphism is precisely the return type of `singleRow₀ObjTotal`:
  `((singleRow C (up ℤ) (up ℤ) 0).obj L).total (up ℤ) ≅ L`.
  Its actual construction specializes `singleRowObjTotal` to row and shift zero and composes
  with `shiftFunctorZero`. It uses the diagonal coproduct isomorphisms, not an arbitrary
  isomorphism chosen from a nonemptiness hypothesis.
- Naturality for every cochain map is the second recorded declaration, with binders
  `{K L : CochainComplex C ℤ} (φ : K ⟶ L)` and equation
  `total.map ((singleRow C (up ℤ) (up ℤ) 0).map φ) (up ℤ) ≫
  (singleRow₀ObjTotal L).hom = (singleRow₀ObjTotal K).hom ≫ φ`.
  This supplies the whole naturality clause, which the primary definition's type alone
  would not record.

Dependency declarations read:

- `def-weil-preadditive-category` is the Mathlib leaf `CategoryTheory.Preadditive` in
  `Mathlib.CategoryTheory.Preadditive.Basic`, lines 60–71. Its class has additive commutative
  Hom groups and the two bilinearity axioms, exactly as its node states.
- `def-weil-abstract-derived-category` records `DerivedCategory` and `HasDerivedCategory`
  in `Mathlib.Algebra.Homology.DerivedCategory.Basic`, lines 70–95. Their full signatures
  and docstrings were read. The item's explicit qualifier uses only the underlying
  cochain-complex notion from this dependency, with terms in `C`; it does not ask for
  the derived category of this merely preadditive `C`. That notion is Mathlib's
  `CochainComplex`, read in `Mathlib.Algebra.Homology.HomologicalComplex`, lines 153–158,
  together with `HomologicalComplex` and its differential-square-zero field.
  The dependency's current blueprint update makes the same distinction; it is not changed.
- `HomologicalComplex₂.HasTotal` and `HomologicalComplex₂.total` in
  `Mathlib.Algebra.Homology.TotalComplex` supply the canonical diagonal-coproduct total.

The upstream module's source header says it was migrated from Joël Riou's bicomplex-rows
module and adapted to Mathlib v4.33.1. The two recorded declarations do not have individual
docstrings in that existing file; their types, actual constructions, and naturality proof
were read rather than inferred from their names. No new source or docstring is delivered.
The node has no postponed proof steps (`proof` and `proof_deps` are empty).

Edge cases checked by reading the constructions and the unrestricted types: zero complex;
complexes supported in one degree; unbounded complexes; negative as well as zero and positive
degrees; zero cochain maps and identity maps; categories without general countable coproducts;
and independent object/morphism universes. Every degree has the diagonal pair `(n, 0)`,
so no empty-diagonal assumption arises. Off-row zero terms are handled by the universal
property of zero objects, including when the distinguished summand is itself zero.
There is no false or disputed statement and no correction or additional node is needed.

Searches for existing declarations (all through the prescribed search wrapper unless stated):

- LeanFinder: `Total of a single row integer cochain complex is naturally isomorphic to the
  cochain complex` returned eight hits on single-degree complexes and Hom-complex equivalences;
  none is the row-total statement.
- Loogle: `HomologicalComplex₂.total, CochainComplex` returned eleven total-shift compatibility
  hits; none replaces the existing upstream row-zero identification.
- Mathlib grep: `singleRow|single.*[Tt]otal` in `Algebra/Homology` returned zero hits.
- LeanSearch: `single row total complex natural isomorphism` returned eight hits, including
  `total.mapIso`, `hasTotal_of_iso`, and unrelated single-complex homology/naturality results;
  no exact Mathlib match.
- Direct `rg` of `singleRow₀ObjTotal|singleRowObjTotal|singleRow₀` in `WeilConjectures`
  found the exact declarations in `FromJoel/Algebra/Homology/BicomplexRows.lean` and their
  uses in `LeftResolution/CochainComplexMinus.lean`, lines 220 and 248. The parallel search
  in the side project's `lean/Sheaf` found no competing declaration.
- Direct `rg` of the item id in `WeilConjectures` found no blueprint-id annotation;
  the name/signature match above is the evidence. Searching `dag/lean_names_upstream.json`
  for `singleRow₀ObjTotal` returned no hit; the current upstream source and compiled checks
  supply the authoritative declaration.

Validation: `scompile.py Q04 lem-sfb-left-resolution-single-row-total scratch/Check.lean`
compiled a sandbox-only probe cleanly (no warnings), checking both full declaration types
and their applications under arbitrary explicit universes `u v`. `#print axioms` on each
recorded declaration returned exactly `propext`, `Classical.choice`, and `Quot.sound`;
neither depends on `sorryAx`. The probe is outside `lean/` and is not delivered.
The prescribed delivery dry run additionally checks both recorded declarations.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
