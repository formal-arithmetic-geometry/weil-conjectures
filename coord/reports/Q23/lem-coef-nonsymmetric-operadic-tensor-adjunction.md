## Worker report

The module `Sheaf.CategoryTheory.NonsymmetricOperadicTensorAdjunction` states
`SSet.Enhanced.OperadicTensor.nonsymmetric_operadic_tensor_adjunction`, with one postponed
proof. All supporting definitions and the two statement records have real data; there
are no axioms, opaque objects, local notation, local instances or extra postponed lemmas.
The natural-language statement and its eight-step proof are unchanged. The resolved
stage-1 repair note was read: its request to keep the statement and the split proof route
is respected. No stage-2 maintenance repair was present.

The theorem existentially supplies normalized presentations in universes `u` and
`max u v`, together with their canonical enlargement. These existential witnesses are
the asserted tensor/algebra functors and their properties, not extra hypotheses. Nothing
is assumed about presentability of an input category or operad, the coefficient monoidal
category, nonemptiness, or an indexing category. Presentability supplies colimits in the
proof, rather than restricting the theorem to a smaller class of inputs.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Fix a small and a containing universe | `u`, `v`, `max u v` for simplices; categories of all such objects lie in `u + 1` and `max u v + 1`. No universe equality is imposed. |
| The ordinary small nonsymmetric infinity operads of the dependency | `NonsymmetricOperad.Object` and the exact recorded `NonsymmetricOperad.category`, with no replacement operad definition. `operadObject` merely reads the object of a vertex. |
| A small quasicategory C | `CoherentNerve.QCats`; `categories K` is the recorded coherent nerve from the normalized marked point model. `categoryObject` reads its vertex. |
| For every C and O the categorical-pattern tensor exists | `Presentation.tensor` is a coherent bifunctor on the product of the actual Cat infinity and operad infinity category. |
| Its marked-product construction | `input C O` is the existing `Marked.Over.productLeft O.obj` applied to `Marked.natural C`. The harmless order is `O × C`; the projection is to O and then to the simplex base. |
| Marked exactly for an equivalence in C and an inert edge in O | Existing `Marked.product` marks a pair iff both factors are marked. `Marked.natural` is exactly equivalences by the dependency's `natural_marking`; the operad object's marking is exactly inert cocartesian edges by `NonsymmetricOperad.IsObject`. Explicit degenerate markings add no edges in these fibrant inputs. |
| Operadic fibrant replacement and weak-equivalence map | `replacement` is an ordinary functor from all pairs of quasicategories and operads into `NonsymmetricOperad.Object`, and `replacementMap` maps the displayed input into that fibrant operad. `replacement_weak` is the actual sharp-mapping restriction test against every fibrant operad. All marked pattern objects are cofibrant; this is the model's weak-equivalence test, not an arbitrary underlying equivalence. |
| The construction is coherent, not just an object assignment | `replacement_natural` fixes the entire marked-product action on all simplices and ordinary maps; `tensor_comparison` identifies its localization with `tensor` by an equivalence of whole coherent functors. `operadLocalization_is` and `categoryLocalization_is` are localization universal properties on full functor infinity categories. |
| Alg_O(Q) is the full infinity category over the base preserving inert edges | `algebraIso` identifies the ordinary algebra functor `B` with the already defined `InertOperad.algebras`, which uses the dependency's full `Algebroid.overFunctors` subcomplex. It keeps every transformation over the fixed base. No core or discrete functor set replaces this category. |
| Its actual variance in O and Q | `algebra_maps` fixes maps by pre- and postcomposition through `InertOperad.algebraInclusion`, on the entire simplicial functor object. `opposite_formula` specifies reversal of every ordinary nerve simplex. `algebra_comparison` then fixes the coherent functor `algebra` on `Op.op × Op`. |
| The displayed equivalence of mapping spaces | `mapping_equivalence : MappingAdjunction tensor algebra`. The left pulled-back twisted-arrow coupling has fiber Map(T(C,O),Q). The right has fiber Map(C,Alg_O(Q)). |
| Coherent naturality in all three variables | `MappingAdjunction` supplies an equivalence over the whole base `(Cat × Op).op × Op`. The base maps are respectively `(T.op,id)` and `(C.op,Alg(O.op,Q))`. Thus its fiberwise equivalences come from one natural equivalence of space-valued diagrams. This is stronger information than a bijection on components, and is exactly the requested coherent natural equivalence. |
| Separate preservation of small colimits in C and O | `preserves_first` and `preserves_second` use `PreservesSmallColimits`. This is a thin specialization of `Presentability.PreservesColimitsIn` to `Presentability.IsSmall`, and tests the actual image of every colimiting cocone. |
| Fibrant replacement means the stated model structure, with mono cofibrations | Fibrancy uses precisely the dependency's ordinary operad objects with inert marking. Weak equivalences use the canonical sharp restriction test. The imported `MarkedOperadic.Model`, `cofibrations`, `fibrant`, and marked enriched model theorem provide the stipulated model conventions; no alternative model structure is introduced. |
| Different weak-equivalence replacements give equivalent operads | `replacement_independent` quantifies over every other fibrant target Y and every weak-equivalence map from the same marked product. It gives an equivalence edge from the tensor vertex to Y in the actual operad category. |
| Universe inclusion is the genuine inclusion of smaller operads | `Enlargement.operads`, `markedIso`, `over_base`, and `operad_maps` fix the enlarged marked object, its base projection and all its maps. `enlargedBase` is the canonical resize between the two `AsSmall` simplex nerves. `inclusion_normalized` identifies the resulting ordinary functor with the coherent `inclusion` via localization. |
| Inclusion preserves colimits indexed by simplicial sets small in the first universe | `Enlargement.preserves_colimits : PreservesSmallColimits.{u} inclusion` explicitly tests the original small universe `u`, on the actual included coherent diagrams and cocones. |
| C and Q may be in the containing universe | The theorem supplies a whole `Q : Presentation L` in `max u v`; its `tensor`, `algebra`, `mapping_equivalence`, `preserves_first`, and `preserves_second` apply to all categories and operads there, including larger C and Q with the smaller O included by `inclusion`. All these mapping objects are formed in that containing universe. |
| Agreement for smaller inputs | `Enlargement.tensor_comparison` is a coherent natural equivalence between the included smaller tensor and the containing-universe tensor of the included two inputs. `categoryFunctor`, `categoryIso`, `category_maps`, and `category_normalized` fix the genuine category inclusion as well. |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CompleteAlgebroid`: the complete-algebroid and monoidal universe
  conventions; `Algebroid.overFunctors` is reused through the recorded algebra definition.
- `Sheaf.CategoryTheory.PresentableInfinityCategory`: `IsSmall`, `IsPresentable`,
  `PreservesColimitsIn`; its coherent colimit convention is used without a new definition.
- `Sheaf.CategoryTheory.NonsymmetricOperadsPresentability`: `Object`, `OverBase`,
  `IsObject`, `category`, `category_quasicategory`, `presentable` and the exact normalized
  relative enrichment used to define that coherent nerve.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`: `CartesianModelStatement`,
  `quasicategoryNerve`, `natural`, `product`, `enlarge`, `enlargeMap`,
  `marked_point_cartesian_model`; its normalization fields specify cores of full functor
  categories as the mapping spaces of Cat infinity.
- `Sheaf.CategoryTheory.MarkedOperadicModelStructures`: `Model`, `FullAlgebraHom`,
  `marked_operadic_model_structures`; these supply the common marked enrichment, exact
  ordinary operad fibrancy, full algebra Hom and its simplex normalization.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `IsEquivalenceEdge`,
  `IsFunctorEquivalence`, `AreNaturallyEquivalent` and the full subcategory convention.
- `Sheaf.CategoryTheory.InertOperadColorReconstruction`: `algebras`, `algebraInclusion`,
  which retain the whole fixed-base coherent transformation simplex.
- `Sheaf.CategoryTheory.CoherentNerveInfrastructure`: `QCats`, `qcatEquivalences`.
- `Sheaf.CategoryTheory.FiniteReedyLocalization`: `largeNerve`, `IsLocalization`, `object`.
- `Sheaf.CategoryTheory.CosimplicialFrameMapping`: `frameLargeNerveMap`, with all source,
  hom, ambient, target-object and target-hom universes specified at its uses.
- `Sheaf.CategoryTheory.TwistedArrowLeftFibration`: `twistedArrow`, `twistedProjection`.
  Their canonical left-fibration coupling is the natural Hom functor.

The last six existing landed nodes are added to `stmt_deps` because their notions occur
in the statement signature or its defining records. They are not new nodes. All original
statement dependencies remain. No dependency node is rewritten. Existing proof-dependency
modules are imported (privately when used only in the proof plan):
`SimplicialModelNerveLocalization`, `ModelInfinityDerivedAdjunction`,
`SimplicialModelCoherentDiagrams`, `InfinityYonedaPresheafLimits`, and
`MarkedEnrichedColimitUniverse`. The other already stated proof dependencies are public
statement imports. Five proof prerequisites had no recorded Lean module when checked:
`lem-coef-categorical-pattern-model-calculus`, `def-coef-categorical-pattern-fibrancy`,
`lem-coef-finite-pattern-universe-comparison`,
`lem-coef-projective-diagram-universe-cofibrancy`, and
`lem-coef-coherent-diagram-universe-naturality`; no invented import is used for them.
They are proof prerequisites, not missing notions required to type this statement.

Edge cases checked before writing:

- Empty indexing simplicial sets are allowed by `IsSmall`; neither preservation field
  assumes nonemptiness or even a quasicategory indexing shape.
- C may be empty; the construction is still its empty marked product followed by
  fibrant replacement. It does not assert that the literal empty product is already
  an operad.
- O and Q range over every ordinary operad, including the arity-zero/terminal-fiber
  conditions and empty mapping product in the recorded operad definition.
- Algebra categories can be empty. The full subcomplex and its coherent nerve retain
  this case, and no vertex in an algebra category is required as a hypothesis.
- The inclusion of a universe into itself (`v = 0`) remains included. The normalized
  lifts have their usual canonical equivalences; no strictly larger universe or
  nontrivial lift is assumed.
- A containing-universe C or Q need not be small in `u`. The second presentation has
  universe `max u v`, while the operad inclusion's colimit test still has smallness `u`.
- No presentability hypothesis on the individual C, O or Q, or a monoidal coefficient
  hypothesis, was added. Those would incorrectly restrict this general foundation.

Searches for an existing declaration (all through the authorized search wrapper or
read-only repository/source searches):

- LeanFinder, query `Tensor and algebra adjunction for nonsymmetric infinity operads`:
  8 hits, all simplex-category concatenation or tensor algebra; none is the statement.
- Loogle, query `Operad, Adjunction`: 0 hits; `Operad` is not a known Mathlib identifier.
- Mathlib grep, query `operadicTensor|operadic_tensor|NonsymmetricOperad` in
  `CategoryTheory`: 0 hits.
- LeanSearch, query `Nonsymmetric infinity operads tensor algebra adjunction marked
  product`: 8 hits, ordinary tensor-Hom adjunctions/types and algebra tensor products;
  none treats nonsymmetric infinity operads.
- Read-only `rg` over upstream `WeilConjectures` and side `lean/Sheaf` for
  `nonsymmetric-operadic-tensor-adjunction|operadicTensor|operadic_tensor`: only this
  node's citation in `OperadicAlgebraPresentability` and an unrelated action tensor in
  `ModuleOperadicColimitDetection`; neither states the theorem.
- Read the dependency source declarations, full signatures and docstrings; the
  operadic marked Hom exists and is reused, while the tensor/algebra adjunction with
  separate colimits and universe enlargement was not already stated.

Source checked directly: the named Rochester PDF, printed pp.608--610 and 619--620,
particularly Remark 3.2.12, the product left-Quillen bifunctor in the proof of
Lemma 3.6.8, and Definition 3.6.12. The universe argument follows the unchanged expanded
DAG proof. WANTED: retain the full Gepner--Haugseng source archive in the shared
`literature/` collection; this worker cannot write to that read-only collection.

Validation: `scompile.py` compiled the sandbox and library-relative module cleanly,
with no errors or warnings. Earlier compile diagnostics were repaired by selecting the
exact dependency enrichment when reading nerve vertices and spelling out the independent
source/target lift universes. No mathematical statement was changed for those repairs.
The final delivery dry run and compile are run after this report is completed.

No STATEMENT-DISPUTED flag, new nodes, dependency module repair or statement correction.

## Second reading by Q23

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
