## Worker report

The delivery states `CochainComplex.exists_filteredProjectiveModel` in
`Sheaf.Algebra.Homology.FilteredProjectiveModel`. Its proof is `sorry`; no result is
proved. The item statement, proof, and proof dependencies are unchanged from the
current ND-reviewed stage-1 repair. The only node changes are its `lean` record and
the addition of the missing two-step localization definition to `stmt_deps`.

The source read was Stacks `trace.tex`, the definition preceding 03TB, the
projective comparison in 03TB, and 03TJ's filtered perfect category and full
faithfulness paragraph. I also read current blueprint main-20261015
`sec-trace-formula/sk-p-trace/prop-trf-trace-formal-laws.proof.md`, clause (2),
including its warning about arbitrary triangle endomorphisms and Ferrand's
example. The current item's six-step proof is reproduced step by step in the
main theorem's docstring. `lem-trf-filtered-projective-comparison` is still
unstated, so it is documented but cannot yet be imported; the ordinary comparison
leaf `lem-pc-ring-derived-map-representative` is imported from Mathlib.

Hypotheses and clauses, matched to Lean:

- A commutative ring is `{A : Type u} [CommRing A]`. The ring and modules have the
  usual common coefficient universe `u`. Ordinary derived localization has an
  independent universe `w` and `[HasDerivedCategory.{w} (ModuleCat.{u} A)]`.
  No equality of localization and coefficient universes is imposed.
- The node's ordinary perfectness is precisely the dependency predicate
  `DerivedCategory.IsPerfectRingComplex`. Its full definition was read: existence
  of an integer bounded complex with every term `Module.Projective` and
  `Module.Finite`, and an isomorphism to its ordinary derived image.
- `P : TwoStepModuleDerived A` is an arbitrary object in the unbounded two-step
  localization defined in the new node. Objects before localization are
  monomorphisms `K' → K`, not arbitrary triangles or an independently specified
  pair of graded objects. Chain maps are commuting squares, so their total map
  preserves the given subcomplex.
- `hP : ∀ c : Bool, IsPerfectRingComplex ((twoStepGraded A c).obj P)` is perfectness
  of exactly both graded objects: `true` means the subcomplex, `false` means the
  cokernel quotient. The functors are canonical localization lifts of those
  operations. The property is imposed after localization, as the node says.
- `uP : P ⟶ P` is any localized endomorphism; there is no chain-map-origin
  assumption on it and no bound on an initial representative.
- `∃ M : TwoStepModuleComplex A` supplies the inclusion `M.obj.hom` from
  `M.obj.left` to `M.obj.right`. Its cokernel is literally the chosen quotient
  complex, so there is no unrelated candidate for `M''`.
- `∃ a b : ℤ` with `IsStrictlyGE a` and `IsStrictlyLE b` on the total and on both
  graded complexes is termwise boundedness of all three complexes. A common
  interval is equivalent to separate bounds for this finite list of complexes.
- `∀ n`, the total and both graded modules are `Module.Finite A` and
  `Module.Projective A`: all three complexes consist of finitely generated
  projectives, not merely perfect derived objects.
- The `ShortExact` conjunct is the canonical sequence with first map
  `M.obj.hom` and second map `cokernel.π M.obj.hom`. It gives the exact sequence
  of complexes and therefore its exactness in every cochain degree.
- For every `n`, `∃ s`, `s ≫ (cokernel.π M.obj.hom).f n = 𝟙 _` explicitly supplies
  a section in that degree. No chain splitting is requested or asserted.
- `j : (twoStepModuleQ A).obj M ≅ P` is the required filtered derived
  isomorphism. `ū : M ⟶ M` is an actual commuting square of chain maps and hence
  a filtration-preserving total endomorphism with its restricted endomorphism.
- `(twoStepModuleQ A).map ū ≫ j.hom = j.hom ≫ uP` says its localized image is
  the given endomorphism under this isomorphism, with the correct direction.
- For each `c`, the final equality intertwines the ordinary derived image of the
  canonical restricted or quotient chain map with `(twoStepGraded A c).map uP`
  under the image of `j`. These are the two required graded representation
  assertions. The normalization is definitional from the quotient and
  localization lift constructions, which is why the displayed maps typecheck
  without inserting unspecified comparisons.
- There is no image-intersection strictness predicate; the preservation is
  exactly the commutative square. In particular the total map can kill the
  subcomplex or have image intersecting it more than its restricted image.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, with the full localization signature
  and independent localization universe.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, read in full.
- `WeilConjectures.CategoryTheory.PBCFiltration`:
  `CategoryTheory.PBCDecreasingFiltration`, read through `scompile.py --source`:
  its fields are `step` and `antitone_step`. This is the recorded general
  filtration interface. A two-step filtration is represented directly by its
  subcomplex inclusion; no general-filtration definition is duplicated.
- `Sheaf.Algebra.Homology.FilteredComplexSubquotients`:
  `CategoryTheory.DecreasingFiltration.complexStep`, `complexQuotient`,
  `complexQuotientπ`, `complexCycles`, and `complexBoundaries`, full source read.
  Its quotient construction is the cokernel of the inclusion, the construction
  used here directly for the two-step quotient. Both recorded filtration
  dependency modules are public imports of the new definition module.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.Algebra.Module.Projective`: `Module.Projective`.
- `Mathlib.Algebra.Homology.DerivedCategory.KProjective`:
  `CochainComplex.IsKProjective.Qh_map_bijective`, read in full with its
  unrestricted-target signature; its bounded-above hypothesis is supplied by
  `CochainComplex.isKProjective_of_projective` in the corresponding homotopy
  category module. This is a proof dependency, imported non-publicly.

I also read `def-kun-finite-filtered-module-homotopy` and its published module in
full. It is the globally finite filtered homotopy category, with arbitrary
filtration bounds; it does not define the localization restricted throughout to
pairs. Using its globally filtered localization in place of DF₂ would silently
use the later two-step comparison theorem. The new construction therefore uses
Mathlib's full subcategory of monomorphisms, quotient category, and localization
construction for the specified pairs themselves.

Edge cases checked mathematically against the signature: the zero ring and zero
complex are included; `K'=0` and `K'=K` are allowed monomorphisms; zero quotient
and zero subcomplex are valid perfect objects. There is no nonzero or nonempty
hypothesis, no fixed degree-zero bound, no noetherian or field hypothesis, no
finite-generation condition on the original representative, and no restriction
on the initial localized endomorphism. Degenerate intervals and complexes
supported in a single integer degree remain included. Nonzero off-diagonal
maps and Ferrand's example are permitted; arbitrary endomorphisms of an ordinary
triangle are deliberately not substituted for a filtered localized morphism.

Searches made through `msearch.py`:

- LeanFinder: `two step filtered complex with perfect graded pieces bounded finite
  projective model endomorphism`: 8 ordinary derived/projective-resolution hits,
  including `CochainComplex.isKProjective_of_projective`, `IsKProjective`,
  `DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective`, and
  `ProjectiveResolution.ofComplex`; no filtered model statement.
- Loogle: `"Filtered", "Projective"`: 0 hits.
- Mathlib grep: `FilteredComplex|filtered.*projective|projective.*filtered`,
  under `Algebra/Homology`: 0 hits.
- LeanSearch and a second LeanFinder query for the new two-step localization are
  recorded with the returned names in the new node's `mathlib_searches`.
- `rg` over the source `WeilConjectures`, the group's `lean/WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` for the item id and proposed
  declaration names found no existing declaration. DAG concept searches and
  `tools/blueprint_refs.py search 'two-step filtered'` found no definition node
  for DF₂; the latter returned 0 matches. The broader searches found the
  globally finite homotopy definition just discussed and sheaf-coefficient
  filtered derived nodes, which do not supply this two-step module category.

No statement dispute or statement correction is needed. The earlier dispatch
failure referred to ND's concurrent stage-1 split/review. This packet starts from
that current reviewed split and keeps it intact.

## New nodes

`def-trf-two-step-filtered-module-derived` defines the exact two-step filtered
homotopy category and its unbounded localization, together with their canonical
quotient/localization functors and the canonical subcomplex/quotient graded
functors into ordinary D(R). Its source is the first paragraph of current
blueprint trace formal laws, clause (2), with filtered homotopies and localization
as in Stacks 03TB/03TJ. It uses Mathlib `Arrow`, the full subcategory of monic
arrows, `Homotopy`, `CategoryTheory.Quotient`, `coker`, and
`MorphismProperty.Localization`; all definitions have real data. Two named
well-definedness theorems have `sorry`, `twoStepGraded_homotopy` and
`twoStepGraded_inverts`, each matching the corresponding assertion in this
node's statement and carrying its complete natural-language proof. They only
postpone proofs needed by the constructions; they do not choose objects or
maps from existence assertions. The three kinds of search and DAG search are
recorded in the node. The already defined general finite filtered homotopy
category is not redefined: this node fixes two-step objects throughout, as the
item requires.

Validation: both files compiled separately in dependency order through
`scompile.py`, with no errors or non-sorry warnings. All universes and variables
are bound explicitly under `set_option autoImplicit false`. The required dry run is `deliver2.py Q110 lem-trf-filtered-projective-model --no-push`;
the final worker status is READY only after it prints OK.

## Second reading by Q110

I independently opened the current node, both delivered Lean modules, the new
definition node, every statement-dependency record and its actual declaration,
and the source passages. There is no repair note for this item. The sandbox
item differs from the current shared node only in `lean` and the added
`def-trf-two-step-filtered-module-derived` statement dependency; its statement
and all six proof steps agree with the current reviewed node. There is no
`statement_change`, so no correction or citer audit is called for.

Here is my object/hypothesis/conclusion inventory and independent matching:

1. The coefficient is an arbitrary commutative ring: `{A : Type u} [CommRing A]`.
   Verdict: exact; no field, characteristic, nonzero, or Noetherian assumption.
2. Ordinary `D(A)` and perfectness mean bounded finite-projective models:
   `[HasDerivedCategory.{w} (ModuleCat.{u} A)]` and
   `DerivedCategory.IsPerfectRingComplex`. I read `Basic.lean` and
   `PerfectRingComplexGeneral.lean`: the latter explicitly asks for an integer
   bounded complex, `Module.Projective` and `Module.Finite` in each degree, and
   an isomorphism to its derived image. Verdict: the recorded dependency, with
   an independent localization universe, exactly supplies the node's predicate.
3. The filtered category is the unbounded localization of pairs, not the
   category of triangles: `P : TwoStepModuleDerived A`. Its underlying objects
   are `TwoStepModuleComplex A`, the full subcategory of monic arrows of integer
   cochain complexes. Arrow morphisms are commuting squares. Verdict: the mono
   is a subcomplex inclusion up to its canonical image identification; it
   encodes precisely a two-step filtration and its preserving chain maps.
4. Homotopies have degree minus one and preserve that subcomplex:
   `twoStepModuleHomotopyRel` asks for `Homotopy f.hom.right g.hom.right` and
   factors each component through the target inclusion after precomposing the
   source inclusion. I read Mathlib's `Homotopy`: its `zero` field forces
   components off degree minus one to vanish, and `comm` is `f-g=dh+hd`.
   Requiring factorization also at the zero off-diagonal components adds no
   condition (use the zero lift). Monicity makes the restrictions unique.
   Verdict: exact. The relation is an equivalence stable under composition,
   so Mathlib's category quotient by its generated congruence is the usual
   homotopy quotient, not an additional identification.
5. The inverted maps are exactly graded quasi-isomorphisms:
   `twoStepModuleQuasiIso` requires a representative with `QuasiIso` on each
   `twoStepGradedComplex A c`; `TwoStepModuleDerived` is its constructed
   localization. Verdict: exact, with no initial termwise degree bound.
6. Both graded objects must be perfect:
   `hP : ∀ c : Bool, IsPerfectRingComplex ((twoStepGraded A c).obj P)`.
   `true` is `Arrow.leftFunc` (the subcomplex); `false` is Mathlib's `coker`
   (the quotient). I read `coker` and its map formula: it uses the total map
   followed by the quotient projection, so the map is canonical.
   `twoStepGraded` is the lift of these operations followed by ordinary `Q`.
   Verdict: exactly two perfect graded pieces, imposed after localization.
7. The input endomorphism is arbitrary in that localization: `(uP : P ⟶ P)`.
   Verdict: no chain representative or triangle-lifting hypothesis is added.
8. The output is a pair `∃ M : TwoStepModuleComplex A`: its domain is `M'`,
   its target is `M`, and `cokernel M.obj.hom` is `M''=M/M'`.
   Verdict: the quotient is constructed from this inclusion, not supplied
   independently or replaced by an unrelated isomorphic object.
9. All three complexes are bounded: the existential `a b : ℤ` bounds the
   total and both graded complexes by `IsStrictlyGE` and `IsStrictlyLE`.
   I read their Mathlib definitions and zero-outside-interval characterizations.
   Verdict: termwise boundedness, not merely bounded cohomology. A common
   interval is equivalent to three intervals by taking their minimum/maximum.
10. Every term of all three complexes is finitely generated projective:
    the `∀ n : ℤ` conjunct uses `Module.Finite A` and `Module.Projective A`
    on the total and both graded terms. I checked these dependency signatures
    in `Finiteness/Defs.lean` and `Module/Projective.lean`.
    Verdict: exact; these are not finiteness of the underlying sets.
11. The required exact sequence is the canonical one:
    `(ShortComplex.mk M.obj.hom (cokernel.π M.obj.hom)
    (cokernel.condition M.obj.hom)).ShortExact`. The next conjunct gives,
    for every integer `n`, a section `s` of that degree's quotient projection.
    Verdict: exact and degreewise split; no chain-complex splitting is asserted.
12. The filtered derived identification and representative are
    `∃ j : (twoStepModuleQ A).obj M ≅ P, ∃ ū : M ⟶ M` followed by
    `(twoStepModuleQ A).map ū ≫ j.hom = j.hom ≫ uP`.
    Verdict: correct conjugacy direction and quantifier order. The model,
    isomorphism, and representative can depend on the supplied endomorphism.
13. The last `∀ c : Bool` identity conjugates the ordinary derived image of
    each restricted/quotient chain map by `(twoStepGraded A c).map j.hom`
    to `(twoStepGraded A c).map uP`. Verdict: both graded representation
    clauses are present. The chosen quotient and localization constructions
    make the chain-map normalization definitional; no arbitrary comparison
    or arbitrary map is substituted.
14. The last sentence excludes image-intersection strictness. In Lean, `ū`
    is just a commuting square. Verdict: this is exactly preservation of the
    inclusion, with no stronger strictness predicate.

I read Stacks `trace.tex`, lines 618–677 (the filtered-category definition and
03TB), and lines 884–927 (03TJ and additivity), as well as clause (2) of the
current `main-20261015` trace-formal-laws proof. The Stacks comparison assumes
enough projectives; module categories have them over every ring, so no extra
coefficient hypothesis is missing here. The finite-projective replacement
claim is in the blueprint, while 03TJ supplies full faithfulness; the source
record and docstring correctly distinguish those roles. The blueprint's
block-triangular meaning of a preserving map is retained, including its warning
about arbitrary triangle endomorphisms. I matched the main theorem docstring's
six numbered paragraphs to the node's good truncation, projective replacement,
ordinary representative/homotopy, block-model construction, filtered Hom
bijection, and graded descent steps. They preserve the proof route.

I also reviewed the new definition node as a new stage-1 notion. Its statement
is self-contained and its three cited notion dependencies are exactly its
`stmt_deps`; its empty proof fields, source, ancestry, creation, chapter/unit,
searches, and lean audit fields meet brief §5. The module defines its category,
quotient, inverted maps and localization using actual Mathlib constructions.
The two named postponed well-definedness assertions occur explicitly in the
node's statement and have source/proof docstrings. Restricting a preserving
homotopy and passing it through cokernels gives ordinary homotopies; a
representative graded quasi-isomorphism becomes an isomorphism under `Q`.
Thus these theorems only supply proofs needed by canonical lifts. They do not
choose data from an undetermined existence assertion. No dependency repair
module is part of this delivery.

For the filtration dependencies I read both
`FilteredComplexSubquotients.lean` and the current published
`WeilConjectures.CategoryTheory.PBCFiltration` through `scompile.py --source`.
The latter has `step` and `antitone_step`; the former takes cokernels of
subcomplex inclusions. The delivered pair model uses that same categorical
notion of inclusion/quotient and does not redefine general decreasing
filtrations. Both dependency modules are imported. I read the already landed
`FiniteFilteredModuleHomotopy.lean` and its DAG node: they allow arbitrary
finite filtration lengths and do not construct the localization restricted
throughout to two-step pairs. Using it as DF₂ would require the comparison
assertion of the separate projective-comparison node. Hence the new specialized
category is needed, rather than an exact existing declaration.

Independent searches (fresh wording):

- LeanFinder via `msearch.py`: `monomorphism of cochain complexes localization
  homotopy finite projective graded pieces`. Eight hits, namely ordinary
  `cm5b` factorization/monomorphism declarations, `IsKProjective`,
  `isKProjective_of_projective`, `IsKInjective`, and related orthogonality/null
  homotopy facts. None states the filtered model theorem or defines DF₂.
- Loogle via `msearch.py`: `"Homotopy", "filtered"`: zero hits.
- Mathlib grep via `msearch.py`: `graded.*projective|projective.*graded`:
  five unrelated projective-spectrum hits.
- Direct `rg` in Mathlib's homology directory, the supplied upstream
  `WeilConjectures`, and shared `lean/Sheaf` for filtered homotopy/projectivity,
  `TwoStepModule`, `twoStepModule`, and subcomplex/localization combinations.
  No exact construction or theorem. I opened the nearby
  `FilteredFreeKProjective.lean`: it proves ordinary K-projectivity from an
  exhaustive semi-free filtration, not two-step localization or simultaneous
  filtered endomorphism representation. The filtered spectral-sequence result
  likewise concerns homotopy invariance, not this model theorem.
- DAG search for two-step filtered categories, `DF_2`, and homotopy found the
  current item and projective-comparison statement, but no existing definition
  node for this localization. I checked the worker's recorded LeanSearch,
  LeanFinder, Loogle and grep results for the new node as well.

Edge cases: the zero ring, zero complexes, `K'=0`, and the identity inclusion
`K'=K` all remain allowed. Their zero graded pieces are legitimate perfect
objects. There is no indexed nonempty family here (`Bool` selects exactly the
two pieces), and no scheme or geometric-point assumption. The splitting is
quantified over every integer, including degree zero; any single-degree or
zero-support complex satisfies suitable bounds. All characteristics are
covered. Both modules use `autoImplicit false`; every variable and universe is
explicitly bound. The coefficient universe is polymorphic and the ordinary
derived morphism universe `w` is independent; the two-step category uses the
unrestricted constructed localization, imposing no small-Hom assumption.

Mismatches found: none. I retained the Lean and node records unchanged and
added this independent reading. The exact main signature matches
`lean.statement` verbatim. Module and declaration docstrings identify the
owning blueprint nodes and source places; theorem bodies are only `sorry`;
definitions have actual data. Both delivered files compiled separately in
dependency order through the required `scompile.py` wrapper, with no errors or
non-sorry warnings. Delivery preflight and push results are recorded below.

The prescribed `deliver2.py Q110 lem-trf-filtered-projective-model --no-push`
printed `OK (dry run): commit e1583bea64 passes the preflight and compiles;
nothing pushed`. The final delivery uses the same reviewed source files.
