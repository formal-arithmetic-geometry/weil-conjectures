## Worker report

The delivery states `SSet.Enhanced.SpaceBimoduleCollage.space_bimodule_collage` in
`Sheaf.CategoryTheory.SpaceBimoduleCollage`. Its conclusion is `Nonempty
(Presentation C D H)`. The record spells out the collage, its complete Segal string
presentation and its universal crossing-label description. No object is extracted
from this existence theorem. All definitions have real data; the only postponed
proofs are the main theorem and the two named well-definedness lemmas
`diagramFunctor_endpoints` and `couplingMap_comm`. Their docstrings contain the
natural-language proofs. The helper declarations are parts of this one collage
notion, not new independent notions or private replacement definitions.

I read HTT Definition the project server and Remark the project server on printed pp. 96–97 (PDF pages
114–115 of the 2017 Harvard file). The text defines correspondences over Δ[1] and
identifies them with coherent functors C-op × D → spaces. The explicit Segal
strings and parameter description are the DAG's refinement, as its source record
already says. I also read the current blueprint ancestor
`prop-coef-integral-exceptional-adjoint.proof.md`, paragraph 2. No statement
correction is needed.

The hypotheses and clauses are rendered as follows:

| Node text | Lean rendering |
| --- | --- |
| Fixed nested universes; small C,D and small-space-valued H | Explicit `universe u`; `C D : SSet.{u}`; `Parameters C D = ulift(C.op ⊗ D)` in u+1; `H : Parameters C D ⟶ Spaces.infinityCategory.{u}`. The lift has an explicit coordinatewise product comparison `splitLift`. |
| C,D are infinity categories | The two `[Quasicategory C]`, `[Quasicategory D]` binders. H is a simplicial map to the recorded coherent nerve of Kan complexes, not an ordinary set-valued functor. |
| Small collage over [1] | `Presentation.category : SSet.{u}`, `quasicategory`, `projection : category ⟶ Δ[1]`. |
| Full endpoint fibers C,D | `source`, `target` identify C,D with the actual fibers. `source_full`, `target_full` use the recorded right-pinched `IsFullyFaithful`. Choosing an endpoint-fixed representative is permitted: transfer the coherent-nerve model along the endpoint equivalences and take a relative inner-fibrant replacement fixing the endpoints. |
| Objects are disjoint endpoint objects | `objects` is bijectivity of the sum of the two actual endpoint inclusion maps on vertices; no extra objects occur. |
| Mixed mapping spaces equal H as spaces | `mixedComparison`, `mixed_weak`, with the existing realization-based weak homotopy equivalence predicate. `value` decodes H's actual small Kan value. |
| Mixed actions, units and all higher compatibilities equal H's | `mixed : AreNaturallyEquivalent H (mixedHom i j)` compares entire coherent functors. `mixedHom` is the existing singular-rigidification Hom pairing restricted along the two inclusions. The further `mixedModel` classifies the actual twisted-arrow coupling, with `mixedModel_diagram = H`. These are not unrelated objectwise mapping identifications. |
| No reverse arrows | `reverse_empty` quantifies over every simplicial degree of the recorded mapping space from a target vertex to a source vertex. |
| Complete Segal presentation with coherent object spaces | `complete` uses the recorded `SegalSpace.IsComplete` on `Classification.diagram category`, whose nth space is the core of Fun(Δ[n],category). `strings_segal` uses its actual consecutive-edge Segal map, so its strict products compute the homotopy products by Reedy fibrancy. |
| Nondecreasing labels; exactly one change in a mixed string | `labels_unique` says every vertical simplex has a unique label α : Δ[n] → Δ[1]. Such an ordinal map is nondecreasing. If nonconstant it has exactly one change 0→1; no reverse change is possible. `strings` retains the entire space over that label. |
| Pure strings have the endpoint data | `sourceStrings`, `targetStrings` are isomorphisms from the endpoint classification spaces. Their `_map` equations require the maps to be the actual endpoint inclusion maps, in every n. |
| Faces and degeneracies use the endpoint composition and mixed actions | `stringRestriction` and `stringRestriction_map` specify restriction along every ordinal map β as the actual restriction of the classification diagram. Thus they include both all faces and all degeneracies, not chosen maps between equivalent spaces. The coherent `mixed` identification fixes the cross-change actions; the pure-string identifications fix the other faces and units. |
| Prescribed endpoint diagrams; compatible crossing labels | `diagrams i j F G` is the actual endpoint restriction fiber on cores of functor categories. For these disjoint full inclusions, restriction is a Kan fibration, so the strict fiber computes the homotopy fiber. `labels H F G` is the entire mapping space from H to the restricted target Hom functor in Fun(C-op × D,Spc), including all action compatibilities. |
| Giving those diagrams means giving those labels | `crossingLabels` is an equivalence of these whole spaces. `crossingLabels_restriction` normalizes it by `AdjunctTransport`: it must classify the map on actual twisted arrows induced by `diagramFunctor` of the supplied diagram. `couplingMap` is constructed by the pullback universal property from `twistedArrowMap f`. The comparison cannot be an arbitrary equivalence between spaces. `targetModel_diagram` fixes the target Hom functor to `mixedHom F G`. |
| Coherence in H, endpoint functors, and additional small simplicial parameters | `crossingLabels_fibers` asserts contractible spaces of realizations of prescribed labels. Applying this to another collage and precomposing its endpoint inclusions with endpoint functors produces the compatible map of collages; natural transformations of bimodules supply precisely its label. Contractibility supplies compatible compositions and higher choices. `crossingLabels_parameters` states equivalence after the actual internal-Hom functor for every `A : SSet.{u+1}`, including non-quasicategories and the empty parameter. It is the same simplicial comparison, not a separate set of bijections on vertices. |

Dependency interfaces read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `core`, `diagramVertex`,
  `mappingSpace`, `IsWeakHomotopyEquivalence`, `IsFullyFaithful`,
  `AreNaturallyEquivalent`, `IsFunctorEquivalence`, `homotopyFiber`, `IsContractible`.
- `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`:
  `CategoryTheory.Spaces.infinityCategory` and its Kan-complex value convention.
- `Sheaf.CategoryTheory.CompleteSegalQuasicategoryComparison`:
  `complete_segal_quasicategory_comparison`, reexported `Classification.diagram`,
  `Classification.map`, `Classification.vertex`, and `SegalSpace.IsComplete`/
  `segalMap`. The full comparison theorem signature and proof docstring were read.
- `Sheaf.CategoryTheory.InfinityPresheafYoneda`:
  `CategoryTheory.Spaces.yonedaPairing`, including the reflected first-variable
  subset paths and ordinary second-variable paths in its definition.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`: the recorded
  interface reexports `SSet.Enhanced.fiber` from `InfinityFibrations`; its point
  factor comes first, so `pullback.snd` is always the inclusion used here.
- `Sheaf.CategoryTheory.InfinityAdjunctionMappingEquivalence`:
  `adjunctCoupling`, `AdjunctBifunctorModel`, `AdjunctTransport`. Their full
  signatures/docstrings were read: classification is over the entire two-variable
  base, and the transport cylinder has the specified classifying endpoint maps.
- `Sheaf.CategoryTheory.InfinityYonedaEvaluation`: `SSet.Enhanced.Yoneda.point`,
  the explicit one-point Kan complex, not a chosen point of some arbitrary space.
- The recorded proof-only modules `CoherentNerveComparison` and
  `TriangularCofibrantResolution` are imported without `public`. The proof-only
  `lem-coef-strict-bimodule-rectification` has no recorded module in this snapshot;
  its use is preserved in the main proof docstring and the existing DAG proof.

The four already-landed owning nodes for the added statement interfaces are added
to `stmt_deps`: `def-coef-infinity-presheaf-yoneda`,
`def-coef-infinity-fibrations`,
`lem-coef-infinity-adjunction-mapping-equivalence`,
`lem-coef-infinity-yoneda-evaluation`. Read-only traversal of their statement and
proof prerequisite closures found no path back to the item. No dependency node,
source module or shared repository file was changed.

Edge cases checked before and during formulation: empty C, empty D, both empty;
point endpoints with empty H (the disjoint union), terminal H (the join), and an
arbitrary Kan space H (the two-object space of arrows); nontrivial endpoint cores;
empty reverse and mixed mapping spaces; n=0 and n=1, where no n≥2 Segal condition
is imposed; all face/degeneracy operators, including maps collapsing the crossing;
empty and non-quasicategorical extra parameters. There is no nonemptiness, local
Kan structure on a strict endpoint model, or choice of strict composition added
as a hypothesis on the given quasicategories. No node fault or disputed statement
was found.

Searches for an existing statement/definition:

- `msearch.py ... leansearch "Collage of a space valued coherent bimodule between
  infinity categories"`: 8 unrelated hits, principally ordinary monoidal `Bimod`;
  no infinity-categorical collage.
- `msearch.py ... leanfinder "Any coherent functor C opposite times D to spaces is
  the mixed mapping bimodule of a collage infinity category"`: 8 unrelated hits
  on realization, graded functors, monoidal Bimod and ordinary Grothendieck
  constructions; no matching statement.
- `msearch.py ... loogle "CategoryTheory.Profunctor, CategoryTheory.Join"`:
  0 hits.
- `msearch.py ... grep "collage|Collage|bimodule" CategoryTheory/Enriched`:
  0 hits.
- `rg` on Mathlib's ordinary Profunctor directory, upstream WeilConjectures, the
  upstream name index and the item id: no coherent collage declaration. The
  ordinary set-valued profunctor/join APIs do not retain the required spaces.
- `rg` on `lean/Sheaf`: unrelated operadic collages, triangular cofibrant
  resolutions and attachment lemmas; no space-valued collage theorem. The search
  did locate the existing Hom pairing, twisted-arrow classification and Segal
  interfaces used above, which are reused instead of copied.

## Second reading by Q32

Author's separate second reading with the original node and the entire final
module open; the maintainer's independent delivery review remains separate.
I checked each row of the clause table against the record fields and the actual
helper bodies. I corrected the initially implicit vertex binders in `objects`,
qualified `SSet.stdSimplex.map` to avoid the topological simplex namespace, and
made the pullback projection type explicit when decoding a diagram. I also
replaced a merely unnormalized universal space equivalence by the full
`AdjunctTransport` restriction condition on actual induced mixed coupling maps.
The lifted product comparison now has explicit degreewise data matching the
published classifier's universe convention. The endpoint string isomorphisms
and every string restriction carry their inclusion equations. All variables and
universes are explicitly bound, declarations are public in the upstream-style
namespace, and no line exceeds 100 characters. The original node statement,
source and proof were not changed.

Validation: the required `scompile.py Q32 lem-coef-space-bimodule-collage` run
completed with exit 0 and no diagnostics for both the sandbox compile and the
canonical module-path confirmation. The final-path invocation reported 47.1 s;
the wrapper retained the prescribed 60 s per-file limit. The node JSON was
checked against the shared source: only `lean` and the four landed additions to
`stmt_deps` differ, and `lean.statement` is the exact final source signature.
