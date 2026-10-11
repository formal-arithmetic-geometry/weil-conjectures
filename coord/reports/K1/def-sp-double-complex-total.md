## Worker report

Repair of R-dct0742, head e65502c4d. The module is
`lean/Sheaf/CategoryTheory/DoubleComplexTotal.lean`. It defines only
`HomologicalComplex₂.firstFiltration` and `HomologicalComplex₂.secondFiltration`.
All other declarations are named theorems with `sorry`; there is no wrapper
structure, redefinition of the total, redefinition of its inclusion, or
redefinition of the graded projection. The node statement is unchanged.

Hypothesis and clause correspondence:

- Abelian category: explicitly bound universes `v u`, `{C : Type u}`,
  `[Category.{v} C] [Abelian C]`, using the declaration of `def-sp-abelian`
  from `Mathlib.CategoryTheory.Abelian.Basic` (its class signature and
  docstring were read). No coproduct axiom is added.
- Integer double complex: `K : HomologicalComplex₂ C (ComplexShape.up ℤ)
  (ComplexShape.up ℤ)`, reused from `Mathlib.Algebra.Homology.HomologicalBicomplex`.
  The object is `(K.X p).X q`; the horizontal differential is
  `(K.d p (p+1)).f q` and the vertical differential is `(K.X p).d q (q+1)`.
  Its complex-of-complexes laws give both square-zero identities and commuting
  squares (the horizontal maps are complex morphisms).
- First quadrant: the Prop hypothesis
  `∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((K.X p).X q)`.
  It is not a new structure, and it supplies no construction data.
  The integer form retains exactly the node's indices and negative-degree
  clauses. The source's natural-indexed form restricts to the nonnegative
  quadrant; conversely it extends by zero. Its `hasTotal_up_nat` and
  `HomologicalComplex₂.exists_spectralSequence`, in
  `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`, were read; the citer
  `thm-sp-double-complex-spectral-sequences` uses that natural-indexed form.
  This repair does not replace or modify that citer.
- Columns are `K.X p`; rows are `K.flip.X q`. Their cohomology uses
  `HomologicalComplex.homology`. Horizontal cohomology maps use
  `HomologicalComplex.homologyMap` on `K.d p (p+1)`; the complex of column
  cohomology is
  `((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).
  mapHomologicalComplex (ComplexShape.up ℤ)).obj K`. Its degree-p homology
  is the stated iterated cohomology. Apply the same declarations to `K.flip`
  for the reversed order. The homology definitions and functor signature
  were read in `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`,
  and `Functor.mapHomologicalComplex` in `Mathlib.Algebra.Homology.Additive`.
  These existing notions are recorded, not redefined.
- Total: exactly `K.total (ComplexShape.up ℤ)`, with its diagonal inclusions
  `K.ιTotal` and `K.ιTotalOrZero`. Their complete definitions were read in
  `Mathlib.Algebra.Homology.TotalComplex`. The construction uses a
  `[K.HasTotal ...]` witness, whose existence follows from the named theorem
  `hasTotal_of_firstQuadrant`; thus users need no additional mathematical
  hypothesis. In each diagonal only [0,n] contributes. The theorem
  `total_isZero_of_neg` states the negative-degree vanishing.
- Total differential: Mathlib's `TotalComplexShape` (the actual class name
  is global) and `ComplexShape.ε₂` are recorded in `lean.declarations`.
  Reading `ComplexShapeSigns.lean:156-159,182-192` gives ε₁=1 and
  ε₂(p,q)=p.negOnePow, precisely (-1)^p. Mathlib's `total` adds the two
  signed contributions, and its complex laws give d²=0. The two cross
  terms cancel by the sign change and commuting squares. This agrees with
  [Stacks 012Z](https://stacks.math.columbia.edu/tag/012Z).
- Filtrations: `firstFiltration K n` has step p equal to
  `(Finset.Icc p n).sup (fun i ↦ imageSubobject
  (K.ιTotalOrZero (ComplexShape.up ℤ) i (n-i) n))`. For the second filtration
  swap the two indices. For a first-quadrant K the omitted terms i>n have
  negative complementary index and are zero, so this is exactly the
  node's indicated sum. `firstFiltration_antitone` and
  `secondFiltration_antitone` supply the proofs needed by the real
  `DecreasingFiltration` definitions, without sorry in definition data.
  The dependency `CategoryTheory.DecreasingFiltration` and its
  `gradedPiece` declaration in `Sheaf.CategoryTheory.Filtration` were read
  in full and are used directly.
- Subcomplexes: `firstFiltration_subcomplex` and
  `secondFiltration_subcomplex` assert existence of the restriction f and
  its commutative inclusion equation with the total differential. They
  are conclusions, not fields demanded from a user.
- Bounds: `firstFiltration_zero`, `secondFiltration_zero` give step 0=top;
  `firstFiltration_finite`, `secondFiltration_finite` give step (n+1)=bottom.
  These are theorem statements under first-quadrant vanishing.
- Graded pieces and their canonical identifications:
  `firstFiltration_graded` and `secondFiltration_graded` let F denote the
  actual constructed filtrations and π the existing `cokernel.π` of
  `Subobject.ofLE`, exactly the quotient defining `F.gradedPiece`.
  Each asserts existence of families a, f, δ. The first equation fixes
  `a n` as the lift of the ORIGINAL total inclusion through `F^p`.
  Since the step arrow is mono this lift is unique, including zero cases.
  The next equation states `IsIso (a n ≫ π n)`: hence the isomorphism is
  precisely the canonical D→F→gr map, not an arbitrary chosen iso.
  The equations for f fix it as the restriction of the total differential;
  π≫δ=f≫π fixes δ as its quotient differential (π is epi).
  The final equations identify this differential via the canonical maps
  with `(-1 : ℤ)^p.natAbs • (K.X p).d (n-p) ((n+1)-p)` for the first,
  and `(K.d (n-p) ((n+1)-p)).f p` for the second, and assert δ²=0.
  Integer p and |p| have the same parity, so the first sign is exactly
  (-1)^p even for negative p. The families of degree-n terms, adjacent δ,
  and δ²=0 state the graded cochain complexes (off-adjacent maps are zero).

Edge cases checked before writing: zero bicomplex; n=0 (one possible
nonzero diagonal term); n<0 (all terms zero); n=-1 (step 0 is simultaneously
top and bottom on a zero object); p>n (empty interval); negative p (only
zero additional summands); negative complementary index in the canonical
graded map (both source and quotient zero). No characteristic restriction
or countable-coproduct assumption is present, and universes are explicit.

Searches actually run during this repair:

- `msearch.py leanfinder`, query “first and second filtrations on the total
  complex of a first quadrant double complex”: eight hits including
  `HomologicalComplex₂`, `HasTotal`, `total`, `ιTotalOrZero`, and
  `TotalComplexShape`; none define these two filtrations.
- `msearch.py loogle`, query `HomologicalComplex₂.total`: twelve hits
  including total, inclusions, totalDesc and functoriality; reused those
  existing constructions instead of adding names for them.
- `msearch.py grep`, query `firstFiltration|secondFiltration|firstQuadrant`
  in `Algebra/Homology`: nine hits about first-quadrant spectral objects,
  none defining these filtration constructions on a bicomplex.
- `msearch.py leansearch`, query “first and second filtrations of the total
  complex of a first quadrant bicomplex”: HTTP Internal Server Error;
  recorded as unavailable, not as no match.
- Direct `rg` in the source `WeilConjectures` homology directory and project
  `lean/Sheaf/CategoryTheory` for double complexes and both filtration names:
  source natural-indexed total and spectral-sequence infrastructure only;
  no existing filtration construction. Direct `rg` for the item id in
  `WeilConjectures` gave no hits. Earlier delivery searches remain in
  `searches.jsonl`, but this report does not rely on its stale claimed fields.

The blueprint literature file is not present on this machine; the node's
full blueprint text was read, and its external reference was opened at
[Stacks 12.18](https://stacks.math.columbia.edu/tag/0FNB), especially 012Z.
Finite diagonals and the signed total agree with that source. The two
filtration and graded-piece formulas are the node's explicit clauses.
No new notion or dependency module was needed, no statement was changed,
and no STATEMENT-DISPUTED issue was found.

## Repair checklist

1. H4: recorded existing bicomplex, total, inclusions, signs, rows/columns
   and homology in `lean.declarations` with module/sign details in `lean.note`.
   Removed firstQuadrantTotal, firstQuadrantTotalInclusion,
   firstQuadrantGradedProjection and FirstQuadrantDoubleComplex.
2. H3/H5: the two filtrations are finite supremum constructions on K;
   antitonicity is a named theorem. There is no wrapper or supplied data.
3. Subcomplex, bounds, canonical quotient isomorphisms and their induced
   signed differentials are theorem statements with sorry and full proof
   docstrings; none is hidden in a field or arbitrary iso.
4. H11: replaced the entire stale report; no second reading is claimed by
   this worker. The second reader must read this repaired version.

Validation: server single-file compile succeeded cleanly (1.7 seconds).
The repaired 208-line file also compiled cleanly after parenthesizing the
let-expression signatures. `deliver2.py K1 def-sp-double-complex-total
--no-push` printed OK: compile and preflight passed except for the independent
second reading, which the second reader writes. Nothing was pushed. The
current preflight supports recording existing names alongside new declarations.

## Second reading by K1

I independently compared the node statement with `DoubleComplexTotal.lean` and its
recorded dependencies. The abelian-category hypothesis is rendered by
`[Category.{v} C] [Abelian C]`; the double complex is Mathlib's
`HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)`, whose two
component complexes and commuting differentials supply the column and row
complexes. The first-quadrant clause is exactly the explicit hypothesis
`∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((K.X p).X q)`. Total, its diagonal
inclusions, and the signed differential are the existing
`HomologicalComplex₂.total`, `ιTotalOrZero`, and `ComplexShape.ε₂` constructions.

The two new constructions are `firstFiltration` and `secondFiltration`, each a
`DecreasingFiltration` whose step is the finite supremum of the relevant
`ιTotalOrZero` images over `Finset.Icc p n`; under first-quadrant vanishing this
is exactly the node's sums over indices at least the filtration index. The
antitone theorems provide the structure field. `total_isZero_of_neg` gives the
negative-degree clause, the two `*_subcomplex` theorems give restriction maps
and their inclusion equations, and `*_zero`/`*_finite` give the degreewise
bounds. The `*_graded` theorems quantify canonical lifts, quotient projections,
restricted differentials, induced quotient differentials, the signed (first)
or horizontal (second) differential formula, and square-zero laws. Their lift
 equations use the original diagonal inclusions, so the asserted `IsIso` is the
canonical graded-piece identification rather than an arbitrary isomorphism.

I checked edge cases n < 0, n = 0, p > n (empty interval), negative indices,
zero bicomplexes, and zero complementary summands. The interval supremum is
bottom when empty, and first-quadrant zero hypotheses make omitted indices
zero. No characteristic, finiteness, countable-coproduct, or extra universe
restriction is introduced. The dependency declarations
`CategoryTheory.Abelian` (Mathlib) and `CategoryTheory.DecreasingFiltration`
(`Sheaf.CategoryTheory.Filtration`) were opened; they match the notions used.

Searches were rerun with `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf`,
plus the recorded LeanFinder/Loogle/LeanSearch queries. They found only the
generic Mathlib bicomplex/total infrastructure and no existing first/second
filtration or graded-piece construction. No mismatch was found, so no source
or node change was required.
