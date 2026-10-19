## Worker report

This delivery records existing declarations; it adds no Lean module, definition, or proof.
The node already had an upstream attachment naming these two theorems, but lacked the
module, primary declaration, signature, author, date, and existing flag required by stage 2.
Only its `lean` field is changed; in particular its inherited `status` is preserved.

The exact match is in the current published module
`WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap`, read through
`scompile.py --source`. The older local checkout keeps equivalent declarations under
`DerivedCategory.Complete.RationalizationMap`; the record uses the live path to avoid
importing duplicate definitions. The source node's old line reference describes the
same two statements. No statement correction or dependency repair is necessary.

Hypotheses and conclusions, clause by clause:

- The commutative ring is `{R : Type w} [CommRing R]`.
- The category is `{C : Type u₁} [Category.{v₁} C]`; its R-linear structure is
  `[Preadditive C] [Linear R C]`. The hom modules and bilinear composition are exactly
  Mathlib's `CategoryTheory.Linear` (dependency `def-weil-linear-category`).
- Triangulation is `[HasZeroObject C] [HasShift C ℤ]`,
  `[∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]`,
  exactly the interface of `def-weil-triangulated-category`: TR1–TR3 and TR4, with the
  zero object and additive integer shifts. These encode the node's triangulated category,
  rather than additional mathematical restrictions.
- R-linearity of every integer shift is the explicit binder
  `[∀ n : ℤ, (shiftFunctor C n).Linear R]`.
- The arbitrary submonoid is `{M : Submonoid R}` in both theorem signatures after the
  source's `variable {M}`. There is no nonzero, nontriviality, domain, or powers-only condition.
- The rationalization and its functor are `CategoryTheory.Rationalization M C` and
  `CategoryTheory.Rationalization.Q M C`, from the recorded dependency
  `sk-def-sfb-rationalization`. In its live module
  `WeilConjectures.CategoryTheory.DerivedCategory.Rationalization`,
  `Rationalization := (Rationalization.W M C).Localization`,
  `W := (torsion M C).trW`, `torsion X := ∃ m ∈ M, m • 𝟙 X = 0`, and
  `Q := (W M C).Q`. Thus this is the prescribed Verdier rationalization with its
  canonical R-linear structure, not an arbitrary localization map or scalar action.
- The node's arbitrary K,L are the implicit objects `{X Y : C}` in both theorems.
  Clause 1 is exactly `CategoryTheory.Rationalization.exists_smul_eq_map`:
  `lemma exists_smul_eq_map {X Y : C} (φ : (Q M C).obj X ⟶ (Q M C).obj Y) :
  ∃ m ∈ M, ∃ f : X ⟶ Y, m • φ = (Q M C).map f`.
  Its arbitrary `φ` is the node's α; the existential membership, numerator, and equality
  render every part of clause 1.
- Clause 2 is exactly `CategoryTheory.Rationalization.map_eq_map_iff`:
  `lemma map_eq_map_iff {X Y : C} (f g : X ⟶ Y) :
  (Q M C).map f = (Q M C).map g ↔ ∃ m ∈ M, m • f = m • g`.
  It quantifies over both arbitrary original morphisms, asserts both directions, and
  uses the same scalar on f and g. The extra D/F variables later in the module do not
  occur in or constrain either theorem.

The dependency signatures and their full docstrings were read: `CategoryTheory.Linear`
from `Mathlib.CategoryTheory.Linear.Basic`; `CategoryTheory.Pretriangulated` from
`Mathlib.CategoryTheory.Triangulated.Pretriangulated`; `CategoryTheory.IsTriangulated`
from `Mathlib.CategoryTheory.Triangulated.Triangulated`; `CategoryTheory.HasShift` from
`Mathlib.CategoryTheory.Shift.Basic`; and the recorded rationalization declarations from
its live source. The upstream theorem docstrings and complete proof bodies were also read.
The blueprint source is the Morphisms of the rationalization paragraph in
`main-20261015/blueprint/sec-proetale-coefficients/sk-thm-sfb-rationalization-comparison/`
`thm-sfb-extend-scalars-localization.proof.md`; its ℓ-power argument is generalized to
an arbitrary submonoid by the cited upstream source, as the node explicitly specifies.

Edge cases checked by reading the quantified statements and constructions:
`M = {1}` gives ordinary morphisms and equality, with m = 1;
`0 ∈ M` kills every object, and m = 0 witnesses scalar equality (the numerator can be 0);
the zero ring is allowed and falls in that case; zero objects and zero morphisms are
included; rings with zero divisors are allowed. The universes w, u₁, v₁ are independent,
so the statement imposes no equality between ring, object, and morphism universes.
The specializations `M = Submonoid.powers ℓ`, including ℓ = 0 or 1, are covered.

Searches made with `msearch.py NA lem-sfb-rationalization-scalar-fractions`:

- LeanFinder: “Morphisms in the Verdier rationalization of an R-linear triangulated
  category are scalar fractions, and equality is detected after multiplication by a
  submonoid element” returned eight generic triangulated-subcategory/fraction results,
  including `ObjectProperty.smul_mem_trW_iff` and left-fraction equality, no exact match.
- Loogle: `"map_eq", "Localization"` returned twelve ring/monoid/module-localization
  results, no exact triangulated rationalization statement.
- LeanSearch: “Rationalization of a linear triangulated category scalar fractions equality
  after scalar multiplication” returned eight rational-scalar and triangle-scalar results,
  no exact match.
- Mathlib grep: `exists_smul_eq_map|map_eq_map_iff|rationalization`, restricted to
  CategoryTheory, returned zero hits.
- `rg` with `exists_smul_eq_map|map_eq_map_iff` in the source `WeilConjectures` tree found
  the two exact declarations in `DerivedCategory/Complete/RationalizationMap.lean`,
  their subsequent uses, and a descriptive reference in `SixFunctors/ClosedImmersionStages`.
  The same search in project `lean/Sheaf` found no declaration.
- `rg` for the item id in the source tree found no blueprint-id annotation;
  searching `dag/lean_names_upstream.json` for both full names returned no hit.
  The item's own `lean_candidates` and closed audit independently name these two results.
- `scompile.py --source` for both live Rationalization and RationalizationMap modules
  confirmed the moved import paths and the full signatures, docstrings, and constructions.

Validation: the prescribed delivery dry run performs real #check probes for BOTH existing
fully qualified declarations through scompile.py, then the server preflight. No Lean file
is delivered and no duplicate theorem is restated. There are no disputed statements,
new nodes, or dependency modules. The independent second reading is left to the next worker.


## Second reading by NA

I independently read the item node, its three statement-dependency nodes, the
blueprint proof at the node's source place, and both live upstream modules via
`scompile.py --source`. There is no repair note for this item. The sandbox differs
from the base node only in `lean`; there is no `statement_change`, new definition
node, dependency module, or delivered Lean file to review.

The source is the “Morphisms of the rationalization” paragraph of
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`
`sk-thm-sfb-rationalization-comparison/thm-sfb-extend-scalars-localization.proof.md`.
That paragraph treats powers of ell. The node explicitly also cites the general
submonoid statement and proof in the upstream RationalizationMap module. Reading
that general source confirms that no constructibility, scheme, coefficient-field,
or boundedness hypotheses from the surrounding blueprint application enter this
abstract result. I also read Stacks `dga.tex`, section Linear categories,
`definition-linear-category` (09MJ): Hom modules and bilinear composition are the
notion used here, without an additivity assumption on a merely linear category.
The item itself assumes triangulation, which supplies the additive structure.

Here is the node's complete object/hypothesis/conclusion list, matched to Lean.
All names below are in `CategoryTheory`, and the two theorem names are in
`CategoryTheory.Rationalization`.

1. Commutative ring R: `{R : Type w} [CommRing R]`. Verdict: exact; neither a
   field, domain, nontrivial ring, nor characteristic restriction is assumed.
2. R-linear category T: `{C : Type u₁} [Category.{v₁} C] [Preadditive C]
   [Linear R C]`. I opened `Mathlib.CategoryTheory.Linear.Basic` and read
   `Linear.homModule`, `smul_comp`, and `comp_smul`. These are the module structures
   and bilinear composition of `def-weil-linear-category`, whose record is a
   Mathlib match. Verdict: exact; no private substitute.
3. Triangulated structure: `[HasZeroObject C] [HasShift C ℤ]
   [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
   [IsTriangulated C]`. I opened both Mathlib triangulated-class definitions:
   `Pretriangulated` gives TR1–TR3 and `IsTriangulated` gives the octahedral axiom.
   These are exactly the interfaces named by `def-weil-triangulated-category`'s
   `mathlib_match.how`. The zero object and additive shifts are part of the
   triangulated structure, and binary biproducts follow in Mathlib. Verdict: exact.
4. R-linear integer shifts: `[∀ n : ℤ, (shiftFunctor C n).Linear R]`.
   Verdict: exact, for every integer, including zero and negative integers.
5. Submonoid M of R: `(M : Submonoid R)` in the section and `variable {M}`
   immediately before these lemmas. Verdict: arbitrary submonoid, with no extra
   nonvanishing assumption or restriction to powers of one scalar.
6. Rationalization and Q: `Rationalization M C` and `Q M C`. The dependency
   `sk-def-sfb-rationalization` records the live module
   `WeilConjectures.CategoryTheory.DerivedCategory.Rationalization`. I read its
   actual construction: `torsion M C X := ∃ m ∈ M, m • 𝟙 X = 0`,
   `W M C := (torsion M C).trW`,
   `Rationalization M C := (W M C).Localization`, and `Q M C := (W M C).Q`.
   It uses the canonical localized preadditive and R-linear structures and
   triangulated localization, and inverts scalar identities for every m in M.
   Verdict: precisely the node's Verdier quotient and scalar action, with real
   data and no hollow definition or arbitrary choice of a map.
7. Arbitrary K,L and clause 1: `{X Y : C}` and
   `lemma exists_smul_eq_map {X Y : C} (φ : (Q M C).obj X ⟶ (Q M C).obj Y) :
       ∃ m ∈ M, ∃ f : X ⟶ Y, m • φ = (Q M C).map f`.
   Verdict: exact. Phi is universally quantified before m and f; m lies in M;
   the numerator is a morphism of C with the same endpoints. The recorded
   `lean.statement` is verbatim this source signature, including its line break.
8. Arbitrary original morphisms and clause 2:
   `lemma map_eq_map_iff {X Y : C} (f g : X ⟶ Y) :
       (Q M C).map f = (Q M C).map g ↔ ∃ m ∈ M, m • f = m • g`.
   Verdict: exact, with both directions and one common scalar. This second
   declaration is present in `lean.declarations`; the primary declaration alone
   would not cover the whole node. D and its structures in the module's section
   are absent from both actual theorem types; F is introduced later.

Edge cases: M cannot be empty because a submonoid contains 1; no index set is
quantified here. M = {1} gives the ordinary Hom representation and equality.
If 0 belongs to M, all quotient objects are zero; m = 0 and numerator 0 satisfy
clause 1, and m = 0 satisfies clause 2. This includes the zero ring. Zero objects,
zero morphisms, rings with zero divisors, and every characteristic are included.
Powers of ell include ell = 0, ell = 1, and exponent zero. The independent
universes w, u₁, v₁ impose no equality between the ring, objects, and Hom types;
the quotient's larger Hom universe is handled by `W.Localization`, without a
smallness hypothesis. An empty category has no triangulated zero-object structure;
this is intrinsic to the node. No scheme, degree, or finite index family occurs.

Independent searches, using different wording from the first reader:

- LeanSearch through `msearch.py NA lem-sfb-rationalization-scalar-fractions`:
  “Clearing denominators for hom sets of a triangulated category localized at
  torsion cones” returned eight generic fraction/localization results, including
  `MorphismProperty.LeftFraction.Localization.Hom.mk` and
  `ObjectProperty.instHasRightCalculusOfFractionsTrWOfIsTriangulatedOfIsTriangulated`.
  None is the specific scalar-denominator representation and equality criterion.
- Loogle through the same wrapper: `"exists_smul", "map"` returned only
  `NumberField.InfinitePlace.exists_smul_eq_of_comap_eq`, unrelated to this item.
- Grep for `denominator|clearing|torsion.*cone|scalar fraction` in Mathlib
  CategoryTheory, upstream CategoryTheory, and project `lean/Sheaf/CategoryTheory`
  found general fraction and derived-functor interfaces, not a competing scalar
  rationalization interface. A subsequent exact-name grep across the entire
  upstream `WeilConjectures` and project `lean/Sheaf` trees found precisely the
  two upstream declarations in the older `Complete/RationalizationMap.lean`,
  together with their uses, and no project duplicate. Both names have no entry
  in `dag/lean_names_upstream.json`. The live source wrapper confirms the current
  path without `Complete`, as already recorded by the first reader.

I read the theorem proof bodies as well as their signatures. The source proves
scalar domination of a torsion-cone denominator using the exact Hom sequence of
a distinguished triangle. It represents a quotient morphism by a left fraction
and clears its denominator for clause 1. For clause 2, localized equality gives
postcomposition by a torsion-cone denominator, which scalar domination clears;
the reverse direction cancels the inverted scalar identity. This is the general
form of the blueprint paragraph's argument. The node's `proof` is empty, so no
recorded proof step is omitted. H8's new-module docstrings and H6's sorry-only
proof requirement require no edits to these pre-existing proved declarations.
No theorem or definition is added in this delivery.

Mismatches and changes: none found in the statement, dependency interfaces,
universes, or primary signature. I preserved the correct node record and worker
report and appended this independent reading. Validation uses the prescribed
`deliver2.py --no-push` existing-declaration probes for both full names, followed
by server preflight; no duplicate statement module is introduced.
