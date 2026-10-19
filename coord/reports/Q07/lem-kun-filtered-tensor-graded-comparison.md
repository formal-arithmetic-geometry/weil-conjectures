## Worker report

Item: `lem-kun-filtered-tensor-graded-comparison`.
Module: `Sheaf.Algebra.Homology.FilteredTensorGradedComparison`.
Main declaration: `CochainComplex.filteredTensor_graded_comparison`.

The module constructs the actual convolution filtration and states the complete complex and
derived comparison, simultaneous naturality, and preservation of filtered quasi-isomorphisms.
It proves nothing. The two postponed theorems are `kunnethConvolution_decreasing` (the decreasing
filtration assertion of the node, proof step 2) and `filteredTensor_graded_comparison` (the
remaining assertions). Both have source and proof docstrings and belong to this DAG node.
Every definition contains real data; only the proof of monotonicity used by the filtration
constructor is postponed as its own named theorem.

Read the item's statement, source, all seven proof steps, statement dependencies and their
records. Read the full signatures and docstrings of the recorded filtration, subquotient,
K-flat, total tensor and derived tensor declarations. The current upstream filtration module,
missing from the older source checkout, was also read with `scompile.py --source
WeilConjectures.CategoryTheory.Abelian.Filtration`; it agrees with the side source. Read the
source paragraphs in `more-algebra.tex`, lines 15425–15520 and 15755–15800: the image-of-sum
convolution formula, diagonal quotient comparison, K-flat interpretation, and Tag 0H7Y.
No source-based correction of the item is necessary.

Hypothesis and conclusion correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Commutative ring R | `{R : Type u} [CommRing R]` |
| Integer cochain complexes of R-modules | `CochainComplex (ModuleCat.{u} R) ℤ` |
| Decreasing filtrations by subcomplexes | `FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)` using the recorded `DecreasingFiltration` |
| Finite filtrations with arbitrary integer endpoints | `P.filtration.IsFinite`, the first conjunct of `HasKunnethFiltration`; this is existence of a full step and a zero step, without fixing step zero |
| Every P^n and Q^n flat | `∀ n, ObjectProperty.flat (P.obj.X n)` and the same predicate for Q |
| Every step term flat | `∀ i n, ObjectProperty.flat ((P.filtration.step i : CochainComplex … ℤ).X n)` and the Q version |
| Every graded term flat | `∀ i n, ObjectProperty.flat ((P.filtration.gradedPiece i).X n)` and the Q version |
| P and Q K-flat | `(HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat P.obj`, and Q |
| Every step complex K-flat | The sixth conjunct of `HasKunnethFiltration`, universally over integers |
| Every graded complex K-flat | The seventh conjunct, universally over integers |
| Graded means successive quotient | Existing `DecreasingFiltration.gradedPiece`, definitionally the cokernel of the next-step inclusion; `kunnethGradedProjection` calls the existing `complexQuotientπ` |
| All these hypotheses for both variables and every primed object | `KunnethFilteredComplex R` is the existing full-subcategory construction on precisely the seven conjuncts; its morphisms retain all filtration-preserving maps |
| Total tensor, including unbounded direct-sum totalization and signs | The upstream `⊗` of cochain complexes is `CochainComplex.mapBifunctor` of the module tensor, with differential `d ⊗ 1 + (-1)^p 1 ⊗ d` |
| G^a is the sum of images over i+j=a | `kunnethConvolutionArrow P Q a` is `Sigma.desc` of tensor inclusions; `kunnethConvolution.F a` is its `imageSubobject` |
| The diagonal indexing | `i : ℤ` indexes the pair `(i, a-i)`; this is a bijective reindexing of all pairs of integers with sum a |
| G is decreasing | `kunnethConvolution_decreasing`, used by the constructor's `F_succ_le` field |
| G is finite, all underlying/step/graded terms flat, and all underlying/step/graded complexes K-flat | First conjunct of the main conclusion: `HasKunnethFiltration (kunnethConvolutionObject P.obj Q.obj)` |
| Canonical complex isomorphism from the diagonal sum to gr_G | Family `e P Q a : (∐ kunnethTensorGraded … a) ≅ (kunnethConvolution …).gradedPiece a` |
| Induced by tensoring representatives and taking the quotient class | The `l` inclusion equation fixes the map from each step tensor into G^a. The next equation equates tensor of the two quotient projections followed by the summand inclusion and `e.hom` with `l` followed by the G quotient projection |
| Naturality for both filtration-preserving chain maps simultaneously | `m … f g` is a filtered map, its underlying map is `f.hom.hom ⊗ₘ g.hom.hom`, and the square involving the sum of `gradedMapSteps f ⊗ₘ gradedMapSteps g` and `e` commutes |
| Identities and composition | Explicit identity and simultaneous composition laws for `m`; induced graded maps, tensor, coproduct maps and localization are functorial, so the natural comparison squares also apply to identities and composites |
| T represents the derived tensor | `c P Q` is an isomorphism from `Q(P) ⊗ Q(Q)` to `Q(P ⊗ Q)`, with hom exactly `Functor.LaxMonoidal.μ DerivedCategory.Q …` |
| Each graded ordinary tensor represents the derived tensor | `cgr P Q a i` and its equation fix it to the same canonical localization tensor comparison on the graded factors |
| Natural derived comparison gr_G T ≅ sum of derived graded tensors | The displayed `Cofan.mk` has point `DerivedCategory.Q.obj (∐ kunnethTensorGraded … a)`, legs `cgr.hom ≫ Q.map (Sigma.ι …)`, and satisfies `Nonempty (IsColimit …)`. Thus this concrete localized complex sum IS the coproduct of the derived tensors. The required comparison is exactly `(DerivedCategory.Q.mapIso (e P Q a)).symm`; the following equation states its naturality |
| Filtered quasi-isomorphisms mean quasi-isomorphisms on every graded complex | Last clause assumes `∀ i, QuasiIso (gradedMapSteps f.hom i)` and the analogous condition for g, and concludes it for every graded map of `m … f g` |
| No spectral sequence, truncation or Tor-of-cohomology formula | None occurs in any conclusion or helper |

`ObjectProperty.flat` is the upstream predicate that tensor on each side is exact (preserves
finite limits and finite colimits). For modules over a commutative ring this is precisely the
node's exact-sequence definition. It is not an automatic predicate for arbitrary modules.
K-flatness is the dependency's existing predicate, without a duplicate acyclic-tensor definition.
The derived-category size parameter `w` is explicitly bound and remains arbitrary; the statement
does not add a coproduct-existence assumption. Its universal-property encoding supplies the
derived direct sum even when typeclass search has no selected coproduct for that localization.
This is not a `Nonempty` choice of an unspecified comparison: the underlying sum and all its
coprojections are explicitly constructed, `e` is fixed on representatives, and `c`/`cgr` are
fixed to the canonical localization maps. Only the universal-property proof is in `Nonempty`.

Dependencies used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, `Functor.mapIso`.
- `WeilConjectures.CategoryTheory.Abelian.Filtration`: `CategoryTheory.DecreasingFiltration`,
  its step family and successive quotient `gr`; `Sheaf.CategoryTheory.Filtration` supplies the
  existing accessors, arbitrary-bound `IsFinite`, and category of filtration-preserving maps.
- `Sheaf.Algebra.Homology.FilteredComplexSubquotients`:
  `CategoryTheory.DecreasingFiltration.complexQuotientπ`; its other recorded declarations
  were read, but cycles and boundaries are not needed for this item.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`:
  `CategoryTheory.MorphismProperty.kFlat`, specialized exactly as in the dependency record;
  the abelian flat/K-flat API is imported by the upstream derived tensor module.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, through the
  upstream cochain monoidal instance, not a private tensor complex.
- `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`:
  `DerivedCategory.exists_derivedTensor_second_factor_functor`, imported as both the
  recorded derived tensor interface and the planned proof tool. The canonical derived
  tensor is the existing monoidal tensor from
  `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`; the module
  docstring explains the fixed-second-factor interpretation with A=R.
- `Sheaf.CategoryTheory.FiniteFiltrationInduction`:
  `CategoryTheory.FilteredObject.gradedMapSteps` and the underlying `restrictionSteps` API.
  Its already-recorded node `lem-sp-finite-filtration-induction` is added to `stmt_deps`;
  no dependency node or module is rewritten.
- Proof-only Mathlib modules `Mathlib.RingTheory.Flat.Equalizer` and
  `Mathlib.Algebra.Homology.HomologySequence` give the two other recorded proof dependencies:
  `LinearMap.lTensor_injective_of_exact_of_flat` and
  `CategoryTheory.ShortComplex.ShortExact.homology_exact₂` (together with the connecting
  maps and the neighboring exactness statements).

Edge cases checked before drafting: the zero complex and zero ring; zero-length/empty
nonzero layer ranges; a single graded layer; gaps between nonzero layers; filtration bounds
strictly negative or shifted arbitrarily; a grading index outside the finite nonzero range;
and unbounded complexes in cochain degree. None is excluded. Lower bounds A,B give the full
convolution step at A+B; upper zero bounds C,D give zero at C+D-1. The infinite integer
indexing includes zero summands and imposes no spurious nonemptiness or `F^0 = top` condition.
For the degenerate diagonal all coproduct objects and comparisons are the corresponding zero
objects. Naturality quantifies over every filtered map, not only strict maps, injective maps,
or maps already assumed to be quasi-isomorphisms. The final assertion alone adds the two
specified graded quasi-isomorphism hypotheses.

Searches (2026-10-16):

- `msearch.py … leansearch` query: “The associated graded of the convolution tensor of flat
  filtered cochain complexes is the sum of the tensors of associated graded complexes”.
  Eight hits: coalgebra convolution and `GradedTensorProduct`, graded multiplication and
  algebra grading declarations. These concern algebra multiplication or convolution of
  linear maps, not the filtration subquotient comparison. No exact match.
- `msearch.py … leanfinder` query: “associated graded convolution tensor product finite
  filtered cochain complexes K-flat”. Eight hits: `HomologicalComplex.HasGoodTensor₁₂`,
  `HasGoodTensor₂₃`, their instances, tensor existence/unit instances, and `Tor'`. Read the
  returned total tensor APIs: they define the existing total tensor but give no convolution
  filtration, quotient comparison, or filtered quasi-isomorphism assertion.
- `msearch.py … loogle '"associatedGraded"'`: zero hits.
- `msearch.py … grep 'convolution|associatedGraded.*tensor|tensor.*associatedGraded'
  Algebra/Homology`: zero hits.
- `rg` over the source `WeilConjectures` and shared `lean/Sheaf` for the item identifier,
  convolution tensors and filtered tensor names found only the downstream
  `BoundedTensorTorSpectralSequence` proof-docstring use, with no comparison declaration.
- `rg` over `dag/lean_names_upstream.json`, Mathlib and project sources found no declaration
  with any of the newly used helper or theorem names. Read
  `Mathlib.Algebra.Homology.Monoidal`, `Mathlib.CategoryTheory.GradedObject.Monoidal`,
  and `Mathlib.LinearAlgebra.TensorProduct.Graded.Internal`: tensor products of complexes
  and already graded objects/algebras are not this quotient comparison.

No `STATEMENT-DISPUTED` issue, no changed mathematical statement, no independent new
notion/node, and no dependency repair. The auxiliary definitions only package this item's
hypotheses and explicitly displayed constructions, as permitted for helpers in its module.

Compilation is through the prescribed `scompile.py` wrapper, one file at a time, with its
unchanged 60-second limit. The required `deliver2.py --no-push` result is recorded after
validation; the independent second reader supplies its own section and performs delivery.


## Second reading by Q07

Independent second reader, 2026-10-16. I opened the node and its seven proof steps,
the complete sandbox module, and the actual Stacks cache
`/home/ubuntu/c1-stacks-review/more-algebra.tex`, lines 15425–15520 and
15755–15810. The source starts with a ring, decreasing filtered complexes, the image
of the diagonal sum of step tensors, all six families of flat modules, and then all
six families of K-flat complexes. The node deliberately states the commutative-ring,
finite-filtration specialization and the elementary consequences proved in its steps.
No additional boundedness in cochain degree or assumption from the later convergence
lemma is required here.

My object/hypothesis/conclusion checklist, in statement order:

| Node item | Lean rendering and verdict |
| --- | --- |
| Commutative ring R | `{R : Type u} [CommRing R]`; exact, no field or nonzero assumption. |
| Integer cochain complexes of modules | `FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)`; exact. I read `DerivedCategory.Basic`: its localization and its cochain complexes have the required meaning. |
| Decreasing filtrations by subcomplexes | The recorded `DecreasingFiltration` on the complex object; its `F_succ_le` is the next-step containment. Exact. |
| Finite filtrations | First conjunct of `HasKunnethFiltration`, using the existing `IsFinite`. I opened `lean/WeilConjectures/CategoryTheory/Filtration.lean`: the definition is `∃ n m : ℤ, F.F n = ⊤ ∧ F.F m = ⊥`, with arbitrary endpoints. Exact. |
| Flat underlying modules, both variables | Second conjunct, `∀ n, ObjectProperty.flat (P.obj.X n)`, and the Q instance of the same predicate; exact. |
| Flat step modules, both variables | Fourth conjunct quantifies over every `i n : ℤ`; exact. |
| Flat graded modules, both variables | Fifth conjunct quantifies over every `i n : ℤ`; exact. |
| K-flat underlying complexes | Third conjunct uses the recorded quasi-isomorphism morphism property's `kFlat`; exact. |
| K-flat step and graded complexes | Sixth and seventh conjuncts quantify over every integer step; exact. |
| Graded complexes are successive quotients | Existing `gradedPiece = gr`; I read the current upstream `gr` using `scompile.py --source WeilConjectures.CategoryTheory.Abelian.Filtration`: it is the cokernel of the next-step inclusion. `kunnethGradedProjection` uses the recorded `complexQuotientπ`, whose signature and body I opened. Exact. |
| Total tensor T | Existing monoidal `P.obj ⊗ Q.obj`, not a replacement complex. `HomologicalComplex.tensorObj` is the existing `mapBifunctor` on module tensor, with diagonal direct-sum totalization and Koszul signs. Exact. |
| G^a is the sum of images for i+j=a | `kunnethConvolutionArrow` is `Sigma.desc` of tensor inclusions; `kunnethConvolution.F a` is its `imageSubobject`. Index `i : ℤ` parametrizes `(i,a-i)` bijectively. Exact. |
| G is decreasing | Named `kunnethConvolution_decreasing` supplies just the containment proof needed by the actual filtration constructor. Exact. |
| G finite and every underlying/step/graded term flat and complex K-flat | First main conjunct applies the same seven-part `HasKunnethFiltration` to the convolution object; none of these conclusions is omitted. Exact. |
| Canonical graded isomorphism | The jointly quantified family `e P Q a` has source `∐ kunnethTensorGraded ... a` and target the convolution's `gradedPiece a`. Exact. |
| Comparison sends tensors of residue classes to tensor representatives modulo G^(a+1) | The `l` equation fixes the step map by its monic inclusion into T; the following equation fixes `e.hom` after the two quotient projections and each coprojection. These projections are epi, so this characterizes the comparison, rather than an arbitrary isomorphism. Exact. |
| Simultaneous naturality for all filtration-preserving chain maps | Full-subcategory arrows impose only the existing `HomPreservingSteps`. The `m.hom` equation is the ordinary tensor map; the `Sigma.map` square states naturality for arbitrary `f` and `g`. Exact. |
| Underlying T represents the derived tensor | `c` is an isomorphism whose hom is exactly `Functor.LaxMonoidal.μ DerivedCategory.Q`. I read the upstream derived monoidal module and the recorded fixed-second-factor derived tensor module: this is the ordinary K-flat derived tensor with identical coefficient rings. Exact. |
| Each graded tensor has its derived interpretation | `cgr` is fixed to the same localization comparison on the two graded factors. Exact. |
| Natural derived graded comparison with the direct sum | The displayed `Cofan.mk` has the concrete localized complex sum as vertex and the specified `cgr.hom ≫ Q.map (Sigma.ι ...)` as legs. `Nonempty (IsColimit ...)` asserts its universal property; it does not choose arbitrary object data. The inverse of `Q.mapIso (e P Q a)` gives precisely the stated derived comparison. Its square is explicit; naturality of the legs also follows from that of μ and coprojections. Exact. |
| Filtered quasi-isomorphisms between objects with the same hypotheses | The final clause assumes `∀ i, QuasiIso (gradedMapSteps f.hom i)` and the analogous condition for `g`, and concludes the same for each graded map of `m`. All four objects belong to `KunnethFilteredComplex R`. Exact. |
| Identity and composition compatibility | Explicit laws for `m`; `e`'s naturality and its representative characterization, canonical μ, and localization functoriality give the same laws for every displayed comparison. Exact. |
| No spectral sequence, truncation or Tor-of-cohomology assertion | No such conclusion occurs. Exact. |

I also opened the signatures and bodies of `restrictionSteps`,
`exists_gradedMap_steps`, and `gradedMapSteps` in `FiniteFiltrationInduction`:
restrictions are uniquely determined by the monic step arrows and the graded maps
by the cokernel projections. Thus these are the induced maps of the node, including
for non-strict morphisms. I read `MorphismProperty.kFlat`: it is preservation of
quasi-isomorphisms under tensor on both sides, the recorded equivalent module notion.
I read `ObjectProperty.flat` in the upstream abelian flat API: both tensor functors
are exact, so it is precisely module flatness, not an automatic typeclass predicate.
The proof-only imports cover the two Mathlib exactness dependencies named by the node.
There are no new nodes, dependency modules, private notions or statement corrections.
The added dependency on the already recorded finite-filtration node supplies its
canonical induced-map API; it imposes no further hypothesis.

Edge cases: the zero ring and zero complex are allowed; there is no `Nontrivial`,
characteristic or field restriction. Filtration degree zero is an ordinary integer,
not a normalization. Lower endpoints can be negative or positive; a one-layer
filtration, gaps, and no nonzero graded layers are all included. The integer diagonal
is never artificially truncated: a diagonal with no nonzero summands has the zero
coproduct. Finite filtration endpoints are uniform in cochain degree, as in the
node, but cochain degrees themselves remain unbounded in both directions. There is
no scheme or empty-scheme object in this module. Universes `u w` are bound explicitly:
`u` is the ambient module/ring universe and `w` the chosen derived morphism universe.
There is no extra equality between them or selected-derived-coproduct hypothesis;
`HasDerivedCategory.{w}` is the dependency's size convention, with its standard
localization always available at the standard size. All primed objects and maps are
quantified jointly before the naturality and quasi-isomorphism conclusions.

Independent searches, using different wording from the author's:

- `msearch.py Q07 lem-kun-filtered-tensor-graded-comparison leanfinder
  "The quotient for the product filtration of two complexes with flat associated
  quotients is the diagonal direct sum of their graded tensors"`: eight hits,
  all tensor/direct-limit lemmas (`Submodule.FG.lTensor.directLimit_apply`, its
  variants and `TensorProduct.toDirectLimit` / `fromDirectLimit`). I opened the
  introduction and declarations in `RingTheory/TensorProduct/DirectLimitFG.lean`:
  they concern directed unions of finitely generated submodules, not filtered
  successive quotients of tensor complexes. No match.
- `msearch.py ... loogle '"tensor", "gradedPiece"'`: zero hits.
- `msearch.py ... grep 'gradedPiece|productFiltration|tensorFiltration'
  Algebra/Homology`: zero hits.
- Independent `rg` over upstream `WeilConjectures`, project `lean/Sheaf`, and
  Mathlib `Algebra/Homology` and `LinearAlgebra/TensorProduct`, for convolution,
  filtered tensor, tensor/gradedPiece and product-filtration names: only unrelated
  Fourier/kernel or algebra convolutions, and the downstream bounded tensor
  spectral-sequence proof docstring. No implementation of this comparison.
  I opened the existing Mathlib `HomologicalComplex.tensorObj` / `tensorHom`
  declarations: these supply the total tensor used here and do not duplicate
  the filtration or comparison being stated.

No mismatch found; I left the correct Lean and mathematical node text unchanged.
The only authored change in this second reading is this independent review section.
The main `lean.statement` was mechanically checked verbatim against the signature
in the file; all lines are at most 100 characters. Both postponed theorem proofs
are exactly `sorry`; definition data are real constructions, and the sole postponed
constructor proof is the separately named monotonicity theorem. All declarations
carry source and blueprint docstrings; the main docstring follows all seven node
proof steps. The prescribed `scompile.py` compiled the sole delivered module cleanly
(sandbox 12.7 seconds, library 23.6 seconds), with no errors or warnings.

Delivery dry run: `deliver2.py Q07 lem-kun-filtered-tensor-graded-comparison --no-push`
printed `OK (dry run): commit f689a4ce6d passes the preflight and compiles; nothing pushed`.
