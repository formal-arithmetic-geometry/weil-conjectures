## Worker report

Repaired the returned stage-2 delivery of
`lem-coef-bifibrant-comparison-common-replacement` by writing
`Sheaf.CategoryTheory.BifibrantComparisonCommonReplacement`.
Its theorem `CategoryTheory.bifibrant_comparison_common_replacement` states both
conclusions with one `sorry`. Its only helper,
`CategoryTheory.BifibrantCommonReplacement.fullNerveInclusion`, constructs the
actual full enriched inclusion on coherent nerves, with identity maps on enriched
Hom objects, then lifts it degreewise. This definition contains real data and no
postponed theorem. No new node or dependency module is needed.

The supplied sandbox contained only dispatcher brief-marker files, without a
module, node copy or report to preserve. The current shared node has the reviewed
NQ six-step split described in the return. This repair copies that current node
and changes only `lean`: it does not repeat the returned stage-1 summary edit.
The delivery wrapper rebases the packet onto the current server newtargets-dag.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean rendering |
| --- | --- |
| Nested universes containing all categories | Independent `universe u v t`, `D : Type u`, `Category.{v} D`, and common simplicial-set universe `max u v t`; arbitrary enlargement is allowed through `t`. |
| One underlying simplicially enriched category D | One `D`, one `[Category.{v} D]`, and one `[SimplicialCategory D]` throughout; neither category nor enrichment is replaced for q. |
| Two simplicial model structures p and q | `[p : ModelCategory D] (q : ModelCategory D)`. The p and q factorization hypotheses supply the two functorial weak factorization systems for each structure; `[HasLimits D] [HasColimits D]` supply completeness and cocompleteness. `_tensor : SimplicialTensorCotensor D`, `_hpSM7 : SatisfiesSM7 D`, and `_hqSM7 : @SatisfiesSM7 D _ q _` supply the common enrichment's tensor/cotensor data and each structure's actual SM7 axiom. The structures need not have equal fibrations or cofibrations. |
| Common weak equivalences W | `weakEquivalences D` denotes p's W and `_hW` identifies it with `q.categoryWithWeakEquivalences.weakEquivalences`. |
| P and Q are the full subcategories of bifibrant objects | The recorded `Bif D` and `@Bif D _ q`, not arbitrary categories, use precisely cofibrancy and fibrancy for p and q respectively. Their inherited simplicial enrichments come from the same enrichment on D. |
| Full simplicial E containing both | `E : ObjectProperty D`; its actual full subcategory is `E.FullSubcategory`. `hPE` and `hQE` assert containment on all bifibrant objects. They impose no repleteness and no quasicategory condition on its coherent nerve. |
| Ordinary R from Q_0 to P_0 | `R : @Bif D _ q ⥤ Bif D`. This is an ordinary functor with no enriched-functor structure. |
| Ordinary natural transformation c in E_0 | `c : R ⋙ ObjectProperty.ιOfLE (...) ⟶ ObjectProperty.ιOfLE (...)`, with the two inclusions obtained from `hPE` and `hQE`. |
| Every c_G belongs to W | `_hc : ∀ X, weakEquivalences D (E.ι.map (c.app X))` checks the actual components after inclusion into D. |
| T a quasicategory | `T : SSet.{max u v t}` and `[SSet.Quasicategory T]`. |
| e is a simplicial map out of the coherent nerve of E | `e : SSet.uliftFunctor.{t}.obj (SimplicialNerve E.FullSubcategory) ⟶ T`. |
| e inverts exactly the W edges from E_0 | `_he : Inverts ((weakEquivalences D).inverseImage E.ι) (aE ≫ e)`. The predicate tests every ordinary W arrow, not all enriched edges. |
| Canonical passage from ordinary nerves | `aP`, `aQ`, and `aE` have the recorded `IsOrdinaryNerveMap` predicate. This characterizes every simplex: objects are those of the ordinary string and each mapping-poset nerve maps constantly to the corresponding composite. They are thus the specified canonical maps, not arbitrary choices of a map or extra enriched structure on R. |
| Common infinity localization L | `L`, `loc`, and `_hloc : IsLocalization (weakEquivalences D) loc`. The existing predicate includes quasicategorical L and the universal property for the entire coherent functor category. No choice from an unproved mere existence theorem is made. |
| Inclusion-normalized comparisons psi_p and psi_q | Maps `ψp`, `ψq`; `_hψp` and `_hψqNorm` are coherent natural equivalences between their ordinary restrictions and the actual inclusion-then-`loc` maps. `_hψq` is `IsFunctorEquivalence ψq`. The chosen p inverse is specified explicitly by `ψpInv`, `_hψpInv₁`, `_hψpInv₂`, exactly unpacking `IsFunctorEquivalence ψp` without a duplicate premise. These are the comparisons of the recorded model-nerve-localization interface. |
| Phi = psi_p inverse psi_q | `ψq ≫ ψpInv`, in Lean's left-to-right composition convention. Any coherent quasi-inverse with the two inverse witnesses is allowed. |
| Restrictions e_p, e_q of the same e | `fullNerveInclusion hPE ≫ e` and `fullNerveInclusion hQE ≫ e`; the helper acts by postcomposition of each enriched simplex with the full inclusion. |
| First conclusion e_q naturally equivalent to e_p Phi | First conjunct `AreNaturallyEquivalent (fullNerveInclusion hQE ≫ e) ((ψq ≫ ψpInv) ≫ fullNerveInclusion hPE ≫ e)`. It uses the recorded coherent functor-space equivalence edge and both inverse-triangle witnesses. |
| Second conclusion e_p equivalence implies e_q equivalence | Second conjunct `IsFunctorEquivalence (fullNerveInclusion hPE ≫ e) → IsFunctorEquivalence (fullNerveInclusion hQE ≫ e)`. The first conclusion does not assume e_p is an equivalence. |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`:
  `CategoryTheory.SimplicialModelLocalization.Bif`, `SatisfiesSM7`,
  `IsOrdinaryNerveMap`, and the statement of
  `CategoryTheory.simplicial_model_nerve_localization`. The theorem's proof plan
  applies that theorem twice; none of its conclusions is substituted as a
  stronger model-structure hypothesis.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.AreNaturallyEquivalent`, `IsFunctorEquivalence`, and the
  equivalence-edge convention used by `Inverts`.
- `Sheaf.CategoryTheory.FiniteReedyLocalization` (publicly imported through the
  model-nerve module): `HomotopicalAlgebra.FiniteReedy.largeNerve`, `Inverts`,
  `IsLocalization`, recorded by `def-coef-coherent-localization-interface`.
- `Sheaf.CategoryTheory.SimplicialTensorCotensor` (also publicly imported):
  `CategoryTheory.SimplicialTensorCotensor`.
- `Sheaf.CategoryTheory.PointwiseEquivalences` (proof-only import):
  `SSet.Enhanced.pointwise_equivalences`, corresponding to
  `lem-coef-infinity-pointwise-equivalences`.
- Mathlib: `SimplicialNerve`, `ModelCategory`, full-subcategory enrichment,
  `ObjectProperty.ιOfLE`, `EnrichedFunctor.comp`, `SSet.uliftFunctor`,
  and `MorphismProperty.HasFunctorialFactorization`.

Edge cases checked before writing:

- Equal model structures, R the identity and c the identity: the statement
  reduces to coherence of the two inclusion-normalized comparisons. It does not
  require them or their chosen inverses to be strictly equal.
- Empty bifibrant categories: no nonemptiness premise is added. The existence of
  the stipulated model structure/replacement controls which such data exist;
  all containment and component clauses retain their usual vacuous meanings.
- T terminal: both restrictions agree, while the implication still correctly
  requires e_p to be an equivalence before claiming e_q is one.
- E may contain nonbifibrant objects and its coherent nerve need not be a
  quasicategory. Only the actual target T is assumed quasicategorical.
- R is allowed to be nonenriched. No coherent nerve of R occurs in the signature.
- Object and morphism universes are independent. All coherent nerves and
  ordinary nerves are explicitly lifted to their arbitrary common enlargement;
  the target can be enlarged by choosing t appropriately.
- q's model instance is passed explicitly in `@Bif` and `@SatisfiesSM7`.
  The normalization's `@IsCofibrant`/`@IsFibrant` also use q's actual classes.
  Choices of initial/terminal-object existence proofs are propositionally
  irrelevant; no equality of cofibration/fibration classes is imposed.

Searches performed afresh for this stage-2 repair:

- `msearch.py ... leanfinder "Two simplicial model structures sharing weak equivalences yield naturally equivalent comparison functors via ordinary bifibrant replacements"`:
  eight hits, headed by `BifibrantObject.weakEquivalence_homMk_iff`, ordinary
  bifibrant inclusion and cofibrant homotopy-category replacements. These
  concern membership in W or ordinary homotopy categories, not the stated
  coherent natural comparison.
- `msearch.py ... leansearch "Ordinary functorial bifibrant replacements for two simplicial model structures with the same weak equivalences give naturally equivalent coherent comparison functors"`:
  eight hits on ordinary cofibrant replacements, bifibrant W membership and
  ordinary derived-functor comparison; no exact coherent statement.
- `msearch.py ... loogle "CategoryTheory.Localization.functorEquivalence"`:
  one hit. Read its signature and docstring in Mathlib's
  `CategoryTheory/Localization/Predicate.lean`: it compares ordinary functor
  categories, not quasicategories. Also read `Localization/Equivalence.lean`.
- `msearch.py ... grep "SimplicialNerve|bifibrant|comparison" CategoryTheory/Localization`:
  five hits, all ordinary `rightDerivedFunctorComparison`; no match.
- `rg -n "bifibrant.*comparison|common.*replacement|BifibrantComparison"`
  in `lean/Sheaf` and the upstream `WeilConjectures` source: related mapping
  presentations and Bergner comparisons, but no statement for these two model
  structures, ordinary R and ordinary c. Opened the related coherent-nerve and
  model-comparison modules; the bundled small-SCat nerve action does not give
  the independent-universe full-subcategory inclusion used here.
- `grep -rn "lem-coef-bifibrant-comparison-common-replacement"` in upstream
  `WeilConjectures`: no hits.
- Exact declaration-name searches in project, upstream and Mathlib found no
  existing `bifibrant_comparison_common_replacement` or `fullNerveInclusion`.

Source locations checked in the independent maintainer reading:
[Higher Algebra](https://www.math.harvard.edu/~lurie/papers/HA.pdf),
Definition 1.3.4.1 (the entire functor-category localization property),
Remark 1.3.4.16, Construction 1.3.4.18, Theorem 1.3.4.20 and its proof,
and the replacement argument in Lemma 1.3.4.21. These support the recorded
common-localization argument. HTT Remark 4.2.4.5 and Proposition A.3.3.2
provide its diagram-model context; the general supporting lemma is the
agent formulation recorded in the node. No statement correction or disputed
statement is needed.

Return repair inventory:

- H1: added the actual .lean module and both report sections.
- H2: added a complete `lean` record with a verbatim multiline signature and
  both declarations. The node is copied from current main; only `lean` changes.
- A6: this is substantive new stage-2 content: a compiled theorem statement and
  real canonical-inclusion definition, replacing the empty stage-2 packet.
- H4: carried out and recorded fresh LeanFinder, LeanSearch, Loogle, Mathlib grep,
  upstream grep and project rg searches; used the recorded notions directly.

Validation: `scompile.py Q110 lem-coef-bifibrant-comparison-common-replacement`
compiled the complete module through the server wrapper cleanly (sandbox 2.0 s,
library 2.3 s). All variables and universes are explicitly bound under
`set_option autoImplicit false`; every Lean line is at most 100 characters.
The node's only postponed theorem is the main theorem and its docstring records
all six proof steps and their DAG dependencies. Dry-run and push results are
recorded by the delivery tool.

## Second reading by Q110

The current direct-delivery brief prohibits starting other agents and assigns
independent review to the maintainer. This section records a second self-reading
with the node and final file open; it does not claim an independent worker read.

Checked again that D and its enrichment occur only once; p and q are actual
model structures with the source's completeness, functorial factorizations and
SM7 conventions; W is the same; P and Q are the actual full bifibrant categories;
E is full and contains both; R and c are ordinary; every c component lies in W;
T is quasicategorical; e is precisely one simplicial map inverting the stipulated
ordinary W edges; and the comparisons carry their ordinary inclusion
normalizations. Canonical aP/aQ/aE are constrained on all simplices, so no
arbitrary replacement map or arbitrary unrelated comparison was introduced.
The p quasi-inverse is supplied together with its two coherent inverse equations,
and Phi has the correct orientation `ψq ≫ ψpInv`.

Read both conjuncts against the final two sentences: the first is the coherent
natural equivalence e_q equivalent to e_p Phi; the second is the conditional
transfer of functor equivalence. Neither conclusion was dropped or moved into a
hypothesis. Checked the nonenriched R case, possibly nonquasicategorical E, equal
structures, and independent universes again. Found no mismatch requiring a
statement correction. The helper contains only the canonical full inclusion,
not a private copy of any recorded equivalence/localization notion. The report's
hypothesis table matches every binder and both clauses of the node.

Independent maintainer reading of immutable head
`6b6206ebee4114c77b76e0e8ca661391b362fc15` (2026-10-17): checked the
hypothesis table against the exact theorem and opened the dependency definitions
and statements. Both conclusions, the ordinary (possibly nonenriched) R and c,
the actual full inclusion, the W-edge condition, and both comparison
normalizations agree. Completeness, cocompleteness and both functorial
factorizations are already part of the dependency node's model-category
convention. No added equality of object and morphism universes, no
quasicategory assumption on E, and no missing helper were found. The single
postponed theorem has all six proof steps in its docstring. The node's
lean.statement is verbatim equal to the file signature. The immutable file
recompiled through scompile.py with exit code 0: sandbox 1.6 s, library 1.6 s,
no diagnostics. The installed wrapper used the server side overlay. Only this
report's corrupted source-reference paragraph was corrected; the Lean and
node are unchanged. Full independent findings are in the maintainer review.md.
