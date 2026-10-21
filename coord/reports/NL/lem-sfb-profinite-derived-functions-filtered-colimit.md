## Worker report

This stage-2 delivery states `lem-sfb-profinite-derived-functions-filtered-colimit` in
`Sheaf.Paper.ProfiniteDerivedFunctionsFilteredColimit`. Its main declaration is
`CategoryTheory.ProfiniteDerivedFunctions.comparison_isIso`; the three other theorems
state the coprojection normalization and the two naturality clauses of the same node.
All four theorem proofs are `sorry`. The four helper definitions have actual bodies.
No proof, new independent definition node, dependency repair, or statement correction is delivered.

The previous attempt's stale-dispatch diagnosis confused a reviewed stage-1 split with a
stage-2 Lean binding. The live node has `status: split` and no `lean` record. Its reviewed
five-step proof is retained verbatim; only `lean` and the added landed definition
dependency change. Q07's stage-1 work is used, not replaced. No repair note for this
item exists in `coord/repair-notes`.

### Exact correspondence of hypotheses and clauses

The statement is rendered using compatible resolutions, as its complex-colimit clause
explicitly permits. Resolution data are universally quantified, rather than selected from
an unnormalized existence theorem. The resolution hypotheses specify what it means to
compute the displayed derived functors; they do not restrict the coefficient diagram.
Nonnegative injective resolutions are available in this Grothendieck module category.
The construction and the invertibility assertion allow every such compatible resolution
and every chain lift preserving the original module coprojections.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Arbitrary commutative condensed ring R | `R : CondensedBar.Ring.{u}`, the existing `CommMon (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})`. Its underlying monoid is `R.toMon : Profinite.CondensedRing`; commutativity is bundled, with no topological presentation or nontriviality hypothesis. |
| Small coherent profinite site, finite jointly surjective coverings | The existing `coherentTopology Profinite.{u}` in `Ring` and `Modules`; no alternate topology is introduced. |
| Compatible universe convention | Explicit `universe u`, `Profinite.{u}`, coefficients `AddCommGrpCat.{u+1}`, `I : Type (u+1)` and `[SmallCategory I]`; the index lives in the coefficient/module universe. All variables are explicitly bound and `autoImplicit` is false. |
| Ordinary internal R-modules | Existing `CondensedBar.Modules R`, transparently `Mod (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u+1}) R.toMon.X`. No action or equivariance is assumed. |
| Ordinary unbounded derived category | The target and source of `comparison` use Mathlib `DerivedCategory.Q` from the category of cochain complexes indexed by all integers. |
| Arbitrary profinite parameter P | `P : Profinite.{u}`; no nonemptiness, finiteness, projectivity or dimension bound. |
| Free internal R-module R[P] | Existing `CondensedBar.freeParameter R P`. Its body is free-abelian-sheafification followed by `Mod.free`, applied to the actual `uliftYoneda` representable of P. The free functor is the explicit `Sheaf.composeAndSheafify ... AddCommGrpCat.free ⋙ Mod.free R.toMon.X` composite defining `freeParameter`. |
| Internal module Hom, right adjoint to relative tensor | `ihom (freeParameter R P)`, with the existing closed relative monoidal structure on `Mod`. `onComplexes` applies this very functor termwise. |
| Small filtered category, including nonemptiness | `[SmallCategory I] [IsFiltered I]`; Mathlib `IsFiltered` includes nonemptiness, common targets, and equalization of parallel arrows, equivalently cocones for every finite diagram. |
| Diagram of modules M | `M : I ⥤ Modules R`. |
| Place each M_i in degree zero | `M ⋙ HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0`. |
| Compatible nonnegative injective resolutions M_i[0] -> K_i | `K : I ⥤ CochainComplex (Modules R) ℤ`, natural augmentation `s`, `hs : ∀ i, QuasiIso (s.app i)`, `hI : ∀ i n, Injective ((K.obj i).X n)`, and `hneg : ∀ i n, n < 0 → IsZero ((K.obj i).X n)`. Thus Q of `onComplexes R P` applied to K_i computes RH_P(M_i[0]). |
| Resolve (colim M)[0] by a nonnegative injective complex | `c.pt`, augmentation `sLimit`, quasi-isomorphism `hsLimit`, termwise injectivity `hILimit`, and negative-term vanishing `hnegLimit`. Thus the target of `comparison` computes RH_P((colim M)[0]). |
| Maps induced by the original coprojections | `hcompat` is the equality `s.app i ≫ c.ι.app i = single.map (colimit.ι M i) ≫ sLimit` for every i. It rules out an arbitrary cocone unrelated to the coefficient maps. |
| Exact filtered colimit of a compatible diagram of complexes | The domain is `DerivedCategory.Q.obj (colimit (K ⋙ onComplexes R P))`. Mathlib's complex colimits are degreewise colimits in the module category. Exactness of filtered colimits makes this the exact/derived filtered-colimit construction specified by the node. No categorical filtered colimit in the ordinary derived category is substituted. |
| The actual canonical comparison | `comparison` is `Q.map (colimit.desc ... ((onComplexes R P).mapCocone c))`. `comparison_coprojection` states its defining equation after every coprojection. |
| It is an isomorphism in D(Mod_R) | Conclusion `IsIso (comparison R P c)` of `comparison_isIso`. |
| Natural in diagrams and supplied module morphisms | `comparison_naturality` states the square for every map `f : K ⟶ L` and vertex map `g` commuting with the cocone legs. For lifts of a module-diagram map, augmentation compatibility makes these precisely the corresponding derived coefficient maps. It also applies to changes of resolution and lift. |
| Natural in continuous profinite parameter maps | `freeParameterMap` linearizes `f : P' ⟶ P` by the actual free functor and Yoneda map; `parameterRestriction` is internal-Hom precomposition. `comparison_parameterNaturality` states the square with the colimit of these maps and the same map on the target resolution. |
| No finite cohomological-dimension hypothesis | None occurs in any binder; the parameter is arbitrary. |
| No unbounded-product interchange | Only termwise Hom from a module and filtered colimits of complexes are used; there is no product over cohomological degrees. |

The main declaration's proof docstring reproduces the five-step proof plan of the node:
internal-to-sectionwise module transport, coherent-site cohomological continuity, derived
presheaf inclusion degree by degree, the free-representable derived-functions model,
and normalization/naturality of the actual comparison. Each remaining theorem's docstring
explains the corresponding coprojection/universal-property argument. The source is
`literature/stacks-project/sites-cohomology.tex`, Tag 0GN3 (`lemma-colim-global`), whose
hypotheses and conclusion were read directly, together with the reviewed Q07 split report.

### Dependency declarations used

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, publicly available
  through the bar-data module. Its full abbreviation and docstring were read.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, and the category
  of linear morphisms. These are the recorded internal module objects, with their actual
  unital and associative action laws.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded total
  right-derivation interface and its `rightDerivedFunctorOfQuasiIsoResolutionsObjIso`.
  Its full signature, universal-pair normalization and docstrings were read. The present
  theorem is given on the nonnegative injective models explicitly stipulated by its node;
  such models are K-injective and compute that total derived functor.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`: the recorded derived
  tensor/Hom convention, exposing the general closed structure and internal Hom API.
  Its primary declaration is the scheme specialization; the present profinite-site
  statement uses the existing general `ihom` on the specified internal module category,
  not that scheme specialization and not an arbitrary replacement Hom functor.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `colimit`, `colimit.ι`,
  `colimit.desc`, and `colimMap`; `CategoryTheory.IsFiltered` is the recorded filteredness.
  The definitions/docstrings were inspected in their actual Mathlib sources.
- `Sheaf.CategoryTheory.CondensedEquivariantBarData`: existing `CondensedBar.Ring`,
  `Modules`, `ringComm`, and `freeParameter`. This landed node
  `def-sfb-condensed-equivariant-bar-data` is added to `stmt_deps` to name their owner;
  none of its group-action, bar or computation data are assumed here.
- `Sheaf.composeAndSheafify`, `AddCommGrpCat.free`, and `Mod.free`: the explicit
  composite in the body of the landed `CondensedBar.freeParameter`, also used on
  morphisms by `freeParameterMap`. No internal-bar theorem is a statement dependency.
- `Mathlib.Algebra.Homology.HomologicalComplexLimits`: the actual termwise colimits;
  `Functor.mapHomologicalComplex` and `NatTrans.mapHomologicalComplex` give the termwise
  functor and parameter maps. The canonical `DerivedCategory.Q` is Mathlib localization.

The modules of already stated proof dependencies are imported without `public`:
module-sheaf colimits/forgetting, exact filtered colimits of abelian sheaves, the internal
section-tensor comparison, sheaf-module tensor closedness, colimits of sites and their
cohomology, site-covering axioms, and exact sheafification. Other proof dependencies are
already public transitively. The proof-only node
`lem-sfb-free-representable-derived-functions-model` has no recorded declaration yet;
there is no module to import for it. It is not needed to type this statement and remains
an existing proof prerequisite, not a missing statement notion.

### Edge cases

- Empty P is allowed. Its representable and free internal module are initial; internal
  functions are zero, giving the zero-to-zero comparison. The definition never picks a
  point of P.
- Terminal P reduces to Hom from the regular module, hence the identity comparison on
  the derived module. Finite P gives the corresponding finite power comparison.
- The zero ring and zero coefficient diagram are allowed. No nontriviality binder occurs.
  Arbitrary nonnegative injective resolutions of zero are still allowed, not just the
  identically zero complex.
- A singleton filtered category reduces to a quasi-isomorphism of resolutions of the
  same module. A general filtered category with parallel arrows is permitted; no poset
  or directed-order structure is imposed.
- An empty index category is correctly excluded by `IsFiltered`, as the statement says.
- Negative cohomological degrees vanish on the given models; degree zero is included,
  and there is no upper bound on degrees or injective dimension.
- The constant, identity, and arbitrary continuous parameter maps are all included.
  Naturality for zero maps, identities, and module-diagram morphisms uses the same
  comparison, not an independently chosen abstract isomorphism.

### Searches made

All four prescribed searches were actually run through `msearch.py`; the compact original
results are retained in sandbox `searches.jsonl`.

- LeanFinder: `Derived internal Hom from a free condensed module on a profinite set
  commutes with filtered colimits of modules in degree zero`. Eight hits, principally
  `LightCondensed.ihomPoints`, its naturality formulas, and free internal projectivity.
  They concern light condensed modules over a constant ring or underived Hom and do not
  give the derived assertion for an arbitrary commutative condensed ring.
- Loogle: `"Condensed", "colimit"`. Twelve hits, including
  `Condensed.hasExactColimitsOfShape`, colimit existence, and locally constant sheaf
  presentations. None states this derived profinite-function comparison. An initial
  unquoted-name query returned unknown identifier `colimit`; the quoted query repaired it.
- Mathlib grep: `(derived|Ext|cohomolog).*(filtered|colimit)|(filtered|colimit).*(derived|Ext|cohomolog)`
  in `Condensed`. Seven hits in AB, discrete colimits, and light sequences, no match.
- LeanSearch: `Cohomology on coherent sites commutes with filtered colimits of sheaves of
  modules`. Eight hits on exactness/existence of colimits and colimit/limit interchange,
  no derived internal-function assertion.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for profinite/filtered colimits,
  derived functions, free parameters, and internal Hom. The existing
  `ProfiniteConstantDerivedFunctions` module was read: its `freeParameter` and `functions`
  are the related free object and right-derived Hom, but its theorem is a scheme-specific
  comparison for constant finite-dimensional coefficient models, not this colimit theorem.
  The smaller original bar-data/free modules supply the actual constructors used here.
- Exact blueprint-ID search in `lean/WeilConjectures` returned no declaration of this item.
  Exact new namespace/module-name searches in Mathlib/upstream/project names returned no
  conflict before writing the module.

No `STATEMENT-DISPUTED` flag or mathematical node fault was found. The source and reviewed
split agree with the stated canonical comparison. The metatheoretic size convention is
implemented by universe polymorphism, not an additional mathematical object.

### Validation

The delivered module compiled cleanly through `scompile.py` against the live server in
both sandbox and library module modes (17.7 s and 23.8 s). There were no errors or
unexpected warnings. A module-mode probe also checked the existing free constructor,
abelian structure, derived-category instance, additivity of internal Hom, and canonical
colimit/map signatures. All delivered lines are at most 100 characters. Every introduced
declaration is recorded under this node and carries its source/blueprint docstring.


## Repair of returned head c55170c5ab82

The saved packet passed the initial required dry run (commit e7347bddb01). The repair
changes `freeParameterMap` from `InternalBar.free` to the explicit composite
`Sheaf.composeAndSheafify (coherentTopology Profinite.{u}) AddCommGrpCat.free.{u + 1} ⋙
Mod.free R.toMon.X`, and removes `lem-sfb-condensed-internal-bar-resolution` from
`stmt_deps`. I read both definitions: the old free functor and the composite have
identical bodies, and `CondensedBar.freeParameter` is the object application of exactly
this composite. Thus the parameter map is definitionally unchanged. The retained
`def-sfb-condensed-equivariant-bar-data` dependency owns the free parameter construction.
No dependency node or theorem signature changed. Compared with the current read clone,
the item differs only in `lean` and the addition of that definition dependency.

The advisory on proof-only imports was checked against stages/2-statements.md §3(7):
these imports are the recorded proof plan and are required even with `sorry` proofs.
They are retained as non-public imports.

## Second reading by NL

Repair self-check (no other agent was started, as the dispatcher requires): I reopened
the node and the full Lean module. `Ring`, `Modules` and `freeParameter` retain the
arbitrary commutative condensed coefficients and ordinary module category. The main
signature still quantifies over every filtered diagram and all compatible nonnegative
injective resolutions; `hcompat` still uses the actual `colimit.ι M i`. The comparison
remains `Q.map (colimit.desc ...)`, with its coprojection normalization, coefficient
naturality and parameter naturality. In the last clause only the body of its parameter
map changes syntactically; unfolding the former `InternalBar.free` gives exactly the
replacement. Empty profinite parameters, the zero ring and module, singleton filtered
categories, and identity or arbitrary continuous parameter maps remain covered. The
sole mismatch found in the returned packet was the theorem-owned free helper in
`stmt_deps`; the explicit composite and removal above repair it without changing any
mathematical clause. The maintainer's independent review remains the external second
reading of this delivery.
