## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedQCohCompactGeneration` states
`AlgebraicGeometry.schemeDerivedQCoh_compactlyGenerated`. Its sole proof is `sorry`.
No definition is introduced, and the item's mathematical statement is unchanged.
The already-landed definition node `def-pc-compactly-generated` is added to stmt_deps
because the conclusion uses its recorded declaration directly.

Hypothesis and clause correspondence:

- “For every scheme X” is `(X : Scheme.{u})`, the recorded Mathlib scheme carrier.
- “quasi-compact” is `[CompactSpace X]`: compactness of the whole underlying space,
  without a Hausdorff or separated hypothesis.
- “quasi-separated” is `[QuasiSeparatedSpace X]`: intersections of compact opens
  are compact. No Noetherian, affine, separated, field or finiteness hypothesis is added.
- `D_QCoh(O_X)` is exactly the dependency's `schemeDerivedQCohCategory X`, namely
  the full subcategory of `schemeDerivedCategory X` whose every cohomology module
  sheaf is `SheafOfModules.IsQuasicoherent`. This is not D(QCoh(X)).
- The binder `[HasDerivedCategory.{w} (SheafOfModules.{u}
  (moduleRings X.toRingedSpace))]` is the shared dependency's localization carrier
  convention, using Mathlib's abelian instance. It does not postulate compact generation,
  coproducts, quasi-coherent closure, or a second derived category.
- “is compactly generated” is `IsCompactlyGeneratedTriangulated.{u}
  (schemeDerivedQCohCategory X)`. By the recorded definition, this means a family
  indexed by `I : Type u` of compact objects whose coproduct is a weak generator.
  Compactness tests all coproducts indexed by `Type u`; the generating family may
  be empty. The coproduct generator detects all integer shifts of every nonzero object.
- The existential `htri : (schemeDerivedQCohProperty X).IsTriangulated` asserts the
  closure needed for Mathlib's inherited full-subcategory structure. Its `letI` makes
  that canonical structure available; no arbitrary replacement shift or triangulation
  is chosen. The existential `hsums : HasCoproducts.{u} ...` asserts arbitrary
  set-indexed sums. These are parts of the conclusion, not extra assumptions. The
  `letI` binders only register these witnesses for elaborating the shared predicate.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (and its morphism
  carrier `Scheme.Hom`, read along with the scheme docstring).
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`, all under
  `AlgebraicGeometry`; all three signatures and docstrings read.
- `Sheaf.CategoryTheory.CompactlyGenerated`:
  `CategoryTheory.IsCompactlyGeneratedTriangulated` (`def-pc-compactly-generated`);
  full section parameters and definition read.
- Its dependency modules `Sheaf.CategoryTheory.CompactObject` and
  `Sheaf.CategoryTheory.WeakTriangulatedGenerator`: `IsCompactObject`,
  `IsWeakTriangulatedGenerator`, `IsTriangulatedGeneratingFamily`; all read.
- `Mathlib.CategoryTheory.Triangulated.Subcategory`: `ObjectProperty.IsTriangulated`
  (contains zero, stable under shifts, extension closure up to isomorphism) and
  the inherited `Pretriangulated` and `IsTriangulated` full-subcategory instances read.
- `Mathlib.Topology.QuasiSeparated`: `QuasiSeparatedSpace`, definition read;
  `CompactSpace` read in `Mathlib.Topology.Defs.Filter`.

Edge cases checked before writing: the empty scheme is allowed and its zero category
has a vacuous weak-generator test; an empty generating index is allowed precisely
when its zero coproduct generates; zero objects are excluded only in the generator's
nonzero-object test. Integers, including zero and negative degrees, are used for shifts
and cohomology. There is no characteristic restriction. The scheme and coproduct index
universe are both u, so the result applies at every chosen ambient small universe.
The morphism universe w of the localization is explicitly bound and not tied to a
second abelian/category instance.

Source verification: the local Stacks source checkout is absent on this machine.
Read the primary online source https://stacks.math.columbia.edu/tag/09IS (Theorem
36.15.3, the theorem named perfect-theorem-bondal-van-den-Bergh) and
https://stacks.math.columbia.edu/tag/09SQ (Definition 13.37.5). The former proves a
single perfect generator for every qcqs scheme; the node uses its compact-generation
consequence, with compactness and a set of representatives supplied by its proof nodes.
The latter is exactly the landed compact-generation definition. No statement correction
or disputed statement is needed. The theorem docstring carries all three DAG proof
steps, including the orthogonal-class argument and the cited triangle exactness.

Searches for an existing statement (msearch queries are also recorded by the launcher):

- `msearch.py ... leanfinder`: “derived category of quasi-coherent sheaves on a
  quasi-compact quasi-separated scheme is compactly generated” returned eight
  derived-category/T-structure hits, none a compact-generation theorem.
- `msearch.py ... loogle`: `CategoryTheory.IsCompactlyGeneratedTriangulated,
  DerivedCategory` returned zero hits, unknown identifier for the project's predicate.
- `msearch.py ... leansearch`: “compactly generated derived category quasi-coherent
  sheaves” was unavailable (Internal Server Error); no negative verdict inferred.
- `msearch.py ... grep`: `CompactlyGenerated|compactly generated` in CategoryTheory
  returned zero hits.
- `rg` of Mathlib CategoryTheory for `ObjectProperty.IsTriangulated` identified the
  inherited full-subcategory structures, not the item theorem.
- `rg` of project `lean/Sheaf` for `CompactlyGenerated|compactlyGenerated|DQCoh|
  derivedQCoh`, followed by `schemeDerivedQCoh`, found only the shared definitions
  and an abstract Brown-representability input, no theorem for schemes.
- `rg` of the source WeilConjectures for the item id, the shared predicate name,
  and “compactly generated” found only an unrelated subrepresentation-lattice comment.
- `tools/lean_names_upstream.py show lem-pc-derived-qcoh-compact-generation` and
  `rg` of `dag/lean_names_upstream.json` found no upstream declaration for the item.
- `rg` in Mathlib, source WeilConjectures and project Sheaf for the chosen name
  `schemeDerivedQCoh_compactlyGenerated` found no collision.

Validation: `scompile.py C1 lem-pc-derived-qcoh-compact-generation
<module path>` returned exit code 0, compiled in 1.9 seconds, with no warnings.


## Second reading by C1

Independent second reader: opened the sandbox node and Lean, the three statement
dependency nodes and their recorded modules, and the definitions of compact objects
and weak generators used by the compact-generation predicate. No mathematical mismatch
was found; the Lean and node signatures are unchanged. This delivery has no new nodes,
no dependency modules, and no statement correction.

The node's complete object/hypothesis/conclusion list and its Lean correspondence:

1. An arbitrary scheme X: `(X : Scheme.{u})`. The recorded `def-pc-scheme` declaration
   is Mathlib's `Scheme`, extending a locally ringed space with locally affine charts
   over commutative rings. Verdict: the same object; no base field or affine restriction.
2. X is quasi-compact: `[CompactSpace X]`. Read `Topology.Defs.Filter`: its only field
   is compactness of the whole space, without Hausdorffness. Verdict: exact hypothesis.
3. X is quasi-separated: `[QuasiSeparatedSpace X]`. Read `Topology.QuasiSeparated`:
   intersections of any two compact opens are compact. Verdict: exact scheme hypothesis;
   no separatedness, Noetherianity or finite-type assumption.
4. The category is D_QCoh(O_X): `schemeDerivedQCohCategory X`, the full subcategory
   given by `schemeDerivedQCohProperty X` of `schemeDerivedCategory X`. Opened all
   three declarations in `Sheaf.AlgebraicGeometry.DerivedCategory`: this is the derived
   category of `SheafOfModules (moduleRings X.toRingedSpace)`, restricted by
   `∀ n : ℤ, (homologyFunctor ... n).obj K |>.IsQuasicoherent`. Also opened `moduleRings`:
   it is the structure sheaf composed with the forgetful functor to rings. Verdict:
   the dependency's category, not the derived category of the abelian QCoh category.
5. That category is compactly generated: the conclusion first supplies
   `htri : (schemeDerivedQCohProperty X).IsTriangulated`, then
   `hsums : HasCoproducts.{u} (schemeDerivedQCohCategory X)`, then the recorded
   `IsCompactlyGeneratedTriangulated.{u}`. Opened Mathlib's subcategory instances:
   they use precisely the ambient distinguished triangles and inherited shifts.
   Opened `CompactlyGenerated`, `CompactObject`, and `WeakTriangulatedGenerator`:
   the predicate asserts `∃ (I : Type u) (E : I → C)`, compactness of every E i,
   and that their coproduct receives a nonzero map into a shift of every nonzero K.
   Compactness uses the canonical direct-sum-of-Hom map for every small family.
   Verdict: all clauses of the shared definition, in the correct quantifier order;
   closure and coproduct existence are conclusions, not extra hypotheses.
6. Encoding binder `[HasDerivedCategory.{w} (SheafOfModules.{u} ...)]`: opened
   Mathlib `DerivedCategory.Basic`. It chooses a localization at quasi-isomorphisms
   with Hom universe w; `HasDerivedCategory.standard` supplies the usual construction.
   Verdict: required by the recorded category carrier, without a second Abelian instance
   or any compact-generation assumption. The statement is uniform in that choice.

Source checked independently: the local Stacks checkout is absent. Read Tag 09IS
(https://stacks.math.columbia.edu/tag/09IS) and the actual upstream TeX
`perfect.tex`, label `theorem-bondal-van-den-Bergh`, including the chapter conventions
and the introduction to the generating-derived-categories section. The DAG's
`derived-categories-of-schemes.tex` names that chapter; its upstream filename is
`perfect.tex`. There is no standing base/Noetherian/separation hypothesis beyond qcqs.
The source's single perfect generator implies the node's compact-generation consequence
using the node's perfect-compactness and coproduct prerequisites. Read Tag 09SQ
(https://stacks.math.columbia.edu/tag/09SQ) and upstream `derived.tex`, label
`definition-compactly-generated`, against the landed predicate. No source correction needed.

Edge cases: X may be empty; no `Nonempty X` is imposed. The zero derived category is
allowed. The generating family may have empty index type; its zero coproduct can
weakly generate the zero category. The nonzero-object condition is confined to the
weak-generator definition, not a restriction on the objects of the category. All integer
cohomological degrees and shifts, including zero and negative integers, are retained.
No characteristic is specified. Universes u and w are explicitly bound; the scheme and
coproduct index share u, and w only specifies the localization Hom size. No unbound
variable or accidental independent test-index universe occurs. The `letI` witnesses
are proof-valued structural instances needed to elaborate the inherited predicate.

Independent duplicate searches, using different wording from the first reader:

- LeanFinder via msearch: “existence of a compact generator for complexes with
  quasicoherent cohomology on qcqs schemes”: eight results on quasicoherent data,
  affine restriction of sections and T-structures; no statement of this theorem.
- Loogle via msearch: `AlgebraicGeometry.Scheme, DerivedCategory`: zero results.
  An earlier query with `CategoryTheory.DerivedCategory` had an unknown identifier;
  it was corrected, and is not negative evidence.
- LeanSearch via msearch: “A quasi compact quasi separated scheme has a perfect
  generator of its derived category”: service returned Internal Server Error;
  recorded as unavailable, without a negative verdict.
- `rg` for `compact.*generat|generat.*compact|Bondal|van.den.Bergh|DQCoh|
  schemeDerivedQCoh` across Mathlib AlgebraicGeometry/CategoryTheory, source
  WeilConjectures and project Sheaf, and for compact/perfect generators in Mathlib's
  derived-category directory. Only abstract generators, the shared definitions and
  unrelated finite generation results occurred; no scheme compact-generation theorem.
- `rg` for the item id and chosen declaration in `dag/lean_names_upstream.json` and
  source WeilConjectures: no hits. No usable existing declaration was found.

H5/H6/H8/H9: there is no new definition, no hollow data and no proved auxiliary theorem.
The sole theorem ends in `by sorry`. Its source/blueprint docstrings are present;
its three proof steps match the node, including the orthogonal-class cone argument
using triangle exactness (ii) and the direct-sum existence prerequisite. Imports are
used for the category carrier, generation predicate, inherited triangulation and
quasi-separatedness; topic and namespace conventions and 100-character lines pass.
Checked by exact string equality that `lean.statement` is the file's full signature.

Validation: independent `scompile.py C1 lem-pc-derived-qcoh-compact-generation`
with the delivered module returned exit code 0, compiled in 1.9 seconds, with no
warnings or errors. Changes by this reader: appended this independent review only;
no Lean or node repair was necessary.
