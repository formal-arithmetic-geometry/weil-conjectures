## Worker report

The module `Sheaf.Algebra.Homology.FilteredBoundedLocalizationComparison` states
`CategoryTheory.uniformFiltered_bounded_localization_comparison`, with `sorry` as its
entire proof. It also constructs the actual filtered good truncations and their
canonical comparison maps. The helper definition module
`Sheaf.Algebra.Homology.UniformFiniteFilteredLocalization` supplies the generic
uniformly finite localization that the statement needs. No theorem is proved in
this delivery. There is exactly one postponed theorem, matching the item node;
its docstring records all eleven steps of the existing proof plan.

The item's mathematical statement and proof plan are unchanged. The only changes
to its node are `lean` and addition of the new definition node to `stmt_deps`.

Hypothesis and clause correspondence:

1. An arbitrary abelian category is `(C : Type u) [Category.{v} C] [Abelian C]`.
   Both universes are explicit and independent. There are no assumptions about
   injectives, projectives, smallness, a ring, a scheme, or degree boundedness of
   the ambient category.
2. Cochains are `CochainComplex C ℤ`. The filtration is exactly the recorded
   `CategoryTheory.DecreasingFiltration`, on the whole complex in its abelian
   category. `FilteredObject (CochainComplex C ℤ)` and its existing morphism
   category give subcomplexes and filtration-preserving chain maps. Thus the
   subobjects are not unrelated degreewise choices.
3. `uniformFilteredProperty B P` requires `K.filtration.IsFinite`, the existing
   finite-filtration predicate. Its two bounds are bounds of subcomplexes, hence
   independent of cochain degree. Its formulation with two arbitrary endpoints
   is equivalent to the node's `a ≤ b`, `Fᵃ = K`, `Fᵇ⁺¹ = 0`: given endpoints
   `n,m`, take `a = min n (m-1)` and `b = m-1`. Antitonicity supplies `Fᵃ = K`.
4. Grades are the existing `DecreasingFiltration.gr`, cokernels of successive
   subcomplex inclusions. The canonical chain map on each grade is the existing
   `FilteredObject.gradedMapSteps`; `uniformFilteredQuasiIso` says `∀ p, QuasiIso`
   of this map. `UniformFilteredDerived` is Mathlib's constructed formal category
   localization of precisely this chain-map category and this class of maps.
5. `P = fun _ ↦ True` gives `DF(A)`, `CochainComplex.plus C` gives `D⁺F(A)`,
   `CochainComplex.minus C` gives `D⁻F(A)`, and `uniformCochainBounded` gives `DᵇF(A)`.
   These conditions are cochain-term bounds, not just cohomological bounds.
   `uniformFilteredComparison` localizes the actual inclusion; it is not a
   freely chosen functor or an extra equivalence assumption.
6. The first three `Nonempty (...FullyFaithful)` conjuncts assert full faithfulness
   of bounded, below, and above into unbounded. `FullyFaithful` is Mathlib's
   structure containing inverse Hom functions and their two equations;
   `Nonempty` expresses its existence as a proposition.
7. The next two such conjuncts assert `DᵇF → D⁺F` and `DᵇF → D⁻F` fully faithful,
   using the projections of the conjunction defining bounded term support.
8. The next three conjuncts quantify over **all objects** of the unbounded
   localization. Their left sides are the corresponding functor's `essImage`.
   Their right sides are respectively `∃ c d, c ≤ d ∧` graded support in
   `Set.Icc c d`, support in `Set.Ici c`, and support in `Set.Iic d`.
   `uniformGradedSupport S K` spells out `∀ p n, n ∉ S → IsZero` of
   `(K.filtration.gr p).homology n`. The same bound therefore applies to every
   grade. `uniformLocalizedSupport` expresses this on a representative isomorphic
   to the localized object. This is a definition of cohomological support on the
   localization: every object has a representative and graded cohomology
   factors through localization, so it does not depend on choosing a special
   representative or on a hypothetical bounded representative.
9. The final two conjuncts quantify over every uniformly finite `K` and cutoff
   `c` or `d`. Vanishing below `c`/above `d` is the corresponding
   `uniformGradedSupport` premise. Their conclusions assert, on **every grade**,
   `QuasiIso (FilteredObject.gradedMapSteps (uniformFilteredTruncGEπ ...) p)`
   and the analogous `uniformFilteredTruncLEι` assertion. The directions are
   `K → τ≥c K` and `τ≤d K → K` exactly as in the node.
10. The truncation definitions use the existing good complexes `truncGE` and
    `truncLE`, not an arbitrary bounded replacement. The former's filtration is
    `K.filtration.image (K.obj.πTruncGE c)`, the canonical quotient filtration;
    the latter is the pullback of each step along `K.obj.ιTruncLE d`, hence the
    induced subobject filtration. This has the node's cokernel and kernel
    cutoff terms, since these are precisely Mathlib's good truncations.
    The respective map components are isomorphisms above/below the cutoff,
    asserted by the last clauses. The removed terms are `IsZero`, explicitly
    asserted in the preceding clauses. The definitions transport the original
    filtration along those same component isomorphisms, so its steps outside
    the cutoff are unchanged under these canonical identifications.
11. `B : Option (ℤ × ℤ)` quantifies the complete assertion over both `none`
    (all uniformly finite filtrations, with different objects allowed different
    bounds) and `some (a,b)` (fixed `Fᵃ = K`, `Fᵇ⁺¹ = 0`). Thus all five
    embeddings and all three essential-image descriptions hold for the
    fixed-interval localizations themselves. Each truncation conclusion includes
    `uniformFilteredProperty B ...` for its resulting complex, retaining those
    exact bounds. Taking `B = some (a,b)` proves nonenlargement for any interval
    in which the input lies. No inclusion of fixed-interval localizations is
    assumed fully faithful as a shortcut.

Dependencies used and read:

- `def-sp-abelian`: `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`; its preadditive, kernel and cokernel
  structures also give the abelian category of cochain complexes.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `HasDerivedCategory`, publicly imported by the helper; ordinary complex
  quasi-isomorphisms are Mathlib's `QuasiIso`. The filtered localization itself
  uses `MorphismProperty.Localization`, without an artificial abelian structure
  on finite filtered objects.
- `def-sp-filtration`:
  `WeilConjectures.CategoryTheory.Abelian.Filtration`,
  `CategoryTheory.DecreasingFiltration`, fields `F`, `F_succ_le`, and `gr`.
  I read the current source using `scompile.py --source` and the shared published
  source, since the older slopmaster2 checkout lacks that module. The existing
  `Sheaf.CategoryTheory.Filtration` compatibility layer and
  `WeilConjectures.CategoryTheory.Filtration` supply `FilteredObject`, its
  category, and `DecreasingFiltration.IsFinite` without redefining a notion.
- `def-kun-truncations`:
  `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits` is publicly imported.
  Its documentation records its existing component declarations
  `CochainComplex.truncLE`, `truncGE`, `ιTruncLE`, `πTruncGE`, with their cutoff
  kernels/cokernels, and it publicly imports their Mathlib module. The separate
  homotopy-colimit predicate recorded as that composite node's main declaration
  is not confused with its good-truncation components.
- `lem-sp-finite-filtration-induction`:
  `Sheaf.CategoryTheory.FiniteFiltrationInduction`,
  `CategoryTheory.FilteredObject.gradedMapSteps`, reused for actual canonical
  graded maps in both modules.
- Proof-only imports are
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
  `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`,
  `Mathlib.CategoryTheory.Triangulated.Subcategory`, and
  `Mathlib.CategoryTheory.Localization.CalculusOfFractions`. They provide the
  recorded long exact sequence, cone criterion, cone-system fraction calculi,
  and left/right roof representation and equality declarations. The two
  remaining proof dependencies, `lem-trf-finite-filtered-graded-exactness` and
  `lem-coef-dg-abc-homotopy-category-triangulated`, have no Lean records or
  Mathlib match on the read base, so there is no stated module to import for
  either. They are named in the eleven-step proof docstring, not assumed as
  extra hypotheses. There are no omitted imports to avoid cycles.

Edge cases checked before writing:

- The zero complex, including the wholly graded-acyclic case: no nonzero object,
  nonempty support, or nonvanishing cohomology is required. Acyclic objects can
  use any nonempty interval `c ≤ d` in the bounded support description.
- A single filtration grade `a=b` is allowed, as are any signed integer cutoffs
  and filtration endpoints; there is no normalization `F⁰=K`.
- `B=none` allows different uniformly finite bounds for different complexes but
  forbids merely degreewise finite filtrations with no common interval.
- Fixed interval includes its zero object. If `a>b`, the conditions force the
  zero object; the uniform parameterization still gives the harmless degenerate
  case in addition to every requested `a≤b` case.
- Below and above have different cochain quantifiers; a complex unbounded on
  the opposite side is admitted. Neither boundedness predicate is imposed on
  the unbounded localization.
- Canonical truncations retain cutoff cohomology, and change a kernel/cokernel
  term at the cutoff, rather than using stupid truncation.
- Arbitrary independent object and morphism universes compile. No size equality
  or enough-injective hypothesis is needed for the formal localization.

Searches made:

- `msearch.py leanfinder`: “Finite filtered cochain complexes bounded localization
  fully faithful good truncations”; ordinary derived-category bounded
  representatives and homological localization results, no filtered match.
- `msearch.py loogle`: `CategoryTheory.Functor.FullyFaithful, Localization`;
  zero hits. `"Filtered", "Complex"` gives filtered colimits of complexes and
  simplicial-set subcomplexes, not filtered derived categories.
- `msearch.py grep`: `FilteredComplex|FilteredDerived|filtered.*trunc` and
  `FilteredDerived|UniformFiltered|filtered.*quasi` in Mathlib Algebra/Homology;
  zero hits.
- `msearch.py leansearch`: both “Uniform finite decreasing filtered complexes
  localization at graded quasi-isomorphisms and bounded support subcategories”
  and the generic uniformly finite localization query recorded in the new node;
  hits are ordinary `DerivedCategory`, `HasDerivedCategory`, and its localization
  API, without filtered-complex localizations.
- A separate `msearch.py leanfinder` search for the uniformly finite localization
  returns ordinary derived-category cohomological bounds, fractions, and CM5b,
  no matching generic filtered construction. The four fresh raw search records
  are preserved verbatim in the new node's `mathlib_searches`.
- `rg` in Mathlib, `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`,
  for filtered/localization/complex/bounded notions and the new declaration
  names. No existing theorem states the item; the item id has no source match.
- DAG search and `tools/blueprint_refs.py search` for uniformly finite filtered
  and filtered derived notions; I read the candidate definitions and modules
  listed in the New nodes section below.

No STATEMENT-DISPUTED flag, source correction, dependency-record repair, or
mathematical node fault is needed. The first complete compile of both modules
passed with no errors and no warnings. All final delivered files are checked
again by `scompile.py` and the required `deliver2.py --no-push` dry run.

## New nodes

`def-trf-uniform-finite-filtered-localization` defines the generic uniformly finite
filtered cochain category, its arbitrary cochain support restriction, graded
quasi-isomorphisms, formal localization, canonical comparison for weakened cochain
support, and graded support predicates. The module uses real Mathlib category and
localization constructions throughout; no choice of an unspecified comparison map,
new axiom, postponed instance, or hollow data is introduced. Its source is Stacks
05S2/05S4/05S5/05S6, restricted to the uniformly finite convention explicitly
required by the item. It cites the existing abelian, cochain, filtration and
canonical graded-map nodes. Search evidence is in its `mathlib_searches`.

This generic interface was missing. `def-trf-finite-filtered-localization` and
`Sheaf.Algebra.Homology.FiniteFilteredLocalization` permit filtration bounds to
vary with cochain degree when their optional interval is absent, and construct
only a bounded-below filtered-homotopy localization; using them here would change
both the ambient category and the uniformly finite condition.
`def-trf-bounded-filtered-derived-category` specializes to pro-etale coefficient
module sheaves and to ordinary abelian groups; it has no generic arbitrary-abelian
Lean declaration. `CochainComplex.FiniteFilteredModuleHomotopy` concerns ordinary
modules and the homotopy quotient, and `TwoStepModuleDerived` only two-step module
filtrations. None supplies the arbitrary-abelian, chain-map, four-cochain-bound
localization required here. The new generic node does not restate their
specializations, filtered-homotopy quotient, or filtered-injective construction.

## Second reading by Q49

I read the item node, its source at Stacks Tags 05S4, 05S5 and 05S6, and the
source declarations of all four recorded statement dependencies. The Lean
rendering matches the node item by item:

1. The arbitrary abelian category is `(C : Type u) [Category.{v} C] [Abelian C]`,
   with independent object and morphism universes; no ring, scheme, injective,
   projective, Noetherian, or degree-bound hypothesis is added.
2. A complex is `CochainComplex C ℤ` and a filtration is the recorded
   `DecreasingFiltration` on that whole complex. `FilteredObject` and its
   morphisms give filtered subcomplexes and filtered chain maps.
3. `uniformFilteredProperty` uses the recorded `DecreasingFiltration.IsFinite`
   predicate, so the filtration bounds are uniform in cochain degree. The
   optional `B : Option (ℤ × ℤ)` adds exactly the fixed endpoint equations
   `F a = ⊤` and `F (b + 1) = ⊥`; the apparent absence of `a ≤ b` is harmless,
   since decreasingness makes the reversed case the zero object and permits
   equal endpoints.
4. `uniformFilteredQuasiIso` is `∀ p, QuasiIso (FilteredObject.gradedMapSteps f p)`;
   `UniformFilteredDerived` is the formal localization at precisely these maps.
5. The unrestricted, bounded-below, bounded-above, and bounded conditions are
   respectively `fun _ ↦ True`, `CochainComplex.plus C`,
   `CochainComplex.minus C`, and their conjunction. The five comparison functors
   in the theorem are exactly the three embeddings into the unrestricted
   localization and the two bounded intermediate embeddings.
6. The three essential-image clauses quantify over every unrestricted localized
   object and use `uniformLocalizedSupport` with `Set.Icc`, `Set.Ici`, and
   `Set.Iic`; `uniformGradedSupport` quantifies over every grade and cochain
   degree, with `IsZero` outside the stated set. This is the node's common
   graded cohomology support condition.
7. The lower truncation clause uses `uniformFilteredTruncGE`, its canonical
   projection `uniformFilteredTruncGEπ`, the induced quotient/image filtration,
   zero terms below `c`, and isomorphism components above `c`. The upper clause
   dually uses `uniformFilteredTruncLE`, `uniformFilteredTruncLEι`, the induced
   pullback/subobject filtration, zero terms above `d`, and isomorphism
   components below `d`. Both clauses retain `uniformFilteredProperty B`, hence
   the same fixed interval.

Edge cases checked were the zero and graded-acyclic complexes, a single grade
`a = b`, signed cutoffs and `n = 0`, `B = none`, a fixed interval with reversed
endpoints (which forces the zero object), and complexes bounded on only one
cochain side. No case covered by the node is excluded, and no characteristic,
field, or size restriction appears.

For duplicate searches I ran `msearch.py` with LeanFinder, Loogle, and grep
queries for uniformly finite filtered localizations, bounded filtered derived
categories, and the declaration names; I also ran `tools/blueprint_refs.py
search 'uniform finite filtered'`. I searched Mathlib, the slopmaster2
`WeilConjectures` tree, this project's `lean/Sheaf`, and DAG records. The only
nearby matches are ordinary derived-category bounds and module-specific finite
filtered homotopy localizations; no exact declaration exists. The worker's new
definition node `def-trf-uniform-finite-filtered-localization` is therefore
necessary, and its module uses real localization, filtration, support, and
truncation constructions without hollow data. Its dependency record and the
item's added `stmt_deps` entry are consistent.

No mismatch was found. I changed no Lean declaration or node statement. Both
modules were compiled with the required `scompile.py` wrapper, with no errors
or warnings beyond the intentional theorem `sorry`; the theorem docstring
contains the node's eleven proof steps and every declaration has its source and
`(blueprint: lem-trf-filtered-bounded-localization-comparison)` documentation.

## Maintainer review fix (2026-10-17)

The reviewer of the delivery at 39f066cbcf02 replaced the private definition
`CategoryTheory.uniformCochainMinus` (`fun K ↦ ∃ d, K.IsStrictlyLE d`) by the
identical existing upstream predicate `CochainComplex.minus C` of
`WeilConjectures.FromJoel.Algebra.Homology.CochainComplexMinus` (one definition per
notion, delivery-errors H4). `uniformCochainBounded` is now
`CochainComplex.plus C K ∧ CochainComplex.minus C K`, and the item's statement uses
`CochainComplex.minus C` for the bounded-above localizations; its mathematical
content is unchanged. The item module also imports
`Sheaf.Paper.FiniteFilteredGradedExactness`, the module of the proof dependency
`lem-trf-finite-filtered-graded-exactness`, which has been stated since the
delivery's base. Both modules compile clean with `tools/nt_compile.py`.
