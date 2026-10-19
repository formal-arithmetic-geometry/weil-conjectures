## Worker report

The module `Sheaf.CategoryTheory.SimplicialMappingLocalization` defines the canonical enriched corner map `simplicialCornerMap`, the data of a simplicial model category (`SimplicialModelCategoryData`), the ordinary bifibrant localization/saturation package assumed from the dependency (`SimplicialBifibrantLocalizationData`), and the result package (`SimplicialMappingLocalization`). The theorem `CategoryTheory.simplicial_mapping_localization` states that these hypotheses provide a mapping-localization comparison.

The theorem's explicit hypotheses are `(S : SimplicialModelCategoryData M)` and `(L : SimplicialBifibrantLocalizationData M)`. The conclusion is `Nonempty (SimplicialMappingLocalization M)`. In the result package, `equiv` renders, for every `P` and `Y` with explicit proofs `IsCofibrant P` and `IsFibrant Y`, the bijection
`SSet.π₀ (sHom P Y) ≃ ((weakEquivalences M).Q.obj P ⟶ (weakEquivalences M).Q.obj Y)`.
The `vertex` clause says the image of the vertex represented by `f : P ⟶ Y` is `(weakEquivalences M).Q.map f`, so the comparison is induced by the actual localization functor. The `natural` clause renders precomposition by every actual `a : P' ⟶ P` between cofibrant sources and postcomposition by every actual `d : Y ⟶ Y'` between fibrant targets. The `identity` clause sends the identity vertex to the localization identity. The `composition` clause renders composition for `P,Y` cofibrant and `Y,Z` fibrant, with `Y` carrying both hypotheses. The corner-map definition uses the enriched precomposition and postcomposition maps and the naturality equality of `sHomFunctor`; `corner_fibration` and `corner_trivial` render the Kan-fibration and triviality clauses, with `SSet.modelCategoryQuillen.J.rlp` and `SSet.modelCategoryQuillen.I.rlp`.

Dependency declarations used: `Sheaf.AlgebraicTopology.SimplicialBoundaryCollapseTest` (`CategoryTheory.simplicial_boundary_collapse_test`), `Sheaf.CategoryTheory.SimplicialTensorCotensor` (`CategoryTheory.SimplicialTensorCotensor`, including its tensor/cotensor declarations), `Sheaf.AlgebraicTopology.KanQuillenRightProper` (`SSet.KanQuillen.right_proper_kan_quillen`), and `Sheaf.CategoryTheory.SimplicialBifibrantLocalization` (`CategoryTheory.simplicial_bifibrant_localization` and its component-category helpers). The module imports the last two dependency modules publicly; the first two arrive through the bifibrant-localization import.

Edge cases checked: `P` and `Y` may already be bifibrant; the statement allows empty mapping-component sets and empty localized Hom sets; the initial and terminal objects are independent; identity and composition are included explicitly; the naturality maps have no weak-equivalence restriction. The corner map has the correct pullback orientation and its square commutes by enriched functoriality.

Searches for existing declarations: `msearch.py leanfinder "simplicial mapping pi zero localization cofibrant fibrant"` returned only ordinary model-homotopy and bifibrant-object results, with no simplicial mapping-space localization theorem; `msearch.py loogle "SimplicialCategory, sHom, Localization, IsCofibrant, IsFibrant"` returned no hits; `msearch.py grep "simplicial.*mapping|π₀.*Localization" AlgebraicTopology/ModelCategory` returned no hits. Additional `rg` over `lean/Sheaf` and the source checkout found no declaration with this statement. Mathlib's `FundamentalLemma` and related homotopy-class declarations do not identify the specified `SSet.π₀` mapping components with the formal localization, so no existing match was used.

## Second reading by NH

Independent maintainer reading of immutable delivery ea5a8795b090b00e35b0f750528e8ea5f0077606,
performed with the packet, all five snapshot node records, the delivered module, the exact
imported dependency modules, and the source open. The original worker report above describes
the delivered version; the corrections below supersede its description of the corner-map fields.

The source is literature/blueprint/main-20261015/blueprint/sec-six-functors/
sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md, paragraph 2,
the coefficient-adjunction computation. It motivates this agent-written ordinary prerequisite;
it does not itself state a model-category theorem or a Stacks tag. I read all six proof steps
of the item and each of its four statement dependencies.

Hypotheses and conclusions:

- Objects and size: `{M : Type u} [Category.{v} M]` with independent universes. Mathlib's
  `SimplicialCategory` is `EnrichedOrdinaryCategory SSet.{v} M`, and `homEquiv'` identifies
  actual arrows with vertices. The localization is exactly Mathlib's path-quiver quotient
  by identity, composition, and the two inverse relations, not a coherent localization.
- Model category: `ModelCategory M` gives the two weak factorization systems, retract
  stability and two-out-of-three. It supplies only finite (co)limits and nonfunctorial
  factorizations. The corrected signature explicitly adds `[HasLimits M] [HasColimits M]`
  and both `HasFunctorialFactorization` instances required by the node's opening convention.
  These restore node hypotheses; they do not add assumptions beyond the node.
- Tensors/cotensors: `S.tensorCotensor` uses the dependency's real universal-element
  construction, with enriched representing isomorphisms in both variables.
- SM7: corrected `S.sm7` uses the existing
  `SimplicialModelLocalization.SatisfiesSM7`. Its canonical `cornerMap` has exactly the
  pullback orientation in the node, with precomposition and postcomposition as projections.
  `J.rlp` means Kan fibration. The weak-equivalence clause, together with this fibration
  clause, is equivalent to the original `I.rlp` clause by `right_proper_kan_quillen`.
- Assumed ordinary bifibrant conclusions: `L.hom` and `L.hom_vertex` express the Hom-set
  bijections induced by the dependency's equivalence and actual localization functor.
  `L.saturated` and `L.represented` express its saturation and representation conclusions.
  `BifibrantObject` is the existing notion; the dependency's `SimplicialBifibrantComponent`
  is a type synonym for precisely these objects. The package extracts the assumed
  consequences, without assuming the desired comparison for arbitrary cofibrant/fibrant pairs.
- For each cofibrant `P` and fibrant `Y`, result field `equiv` is the required bijection.
  `vertex` pins it to `q(f)` for every actual arrow, so the `Nonempty` conclusion is not
  an arbitrary map or hollow choice. No definition chooses an object from this theorem.
- `natural` quantifies over every actual `a : P' ⟶ P` and `d : Y ⟶ Y'`, with no weakness
  condition. Vertex surjectivity of `SSet.π₀.mk` extends the displayed equation to every
  component. `composition` has precisely cofibrancy of `P,Y` and fibrancy of `Y,Z`;
  `identity` requires the single object to be bifibrant. These formulas also extend to all
  components and agree with the dependency's quotient composition.

Proof audit: step 1 uses the two lifting systems to construct bifibrant replacements;
step 2 uses the enriched tensor/cotensor isomorphisms to identify terminal mapping sets;
step 3 applies SM7 and the Kan dependency to get two component bijections; step 4 uses
only the assumed bifibrant Hom comparison and localization of the replacement arrows;
step 5 uses two fillers to obtain the strict equality `i ≫ h ≫ p = f`, which proves the
actual-vertex normalization; step 6 uses vertex representatives and functoriality for
naturality, identities and composition. No properness or infinity-localization result is used.
The repaired theorem docstring now carries all six steps and their dependencies.

Searches and exact declarations: I searched the read-only group `lean/Sheaf`, upstream
`WeilConjectures`, Mathlib's ModelCategory, Enriched and SimplicialCategory directories for
simplicial model, corner-map, SM7 and mapping-component/localization names. Mathlib
`BifibrantObjectHomotopy.lean:41,65,148` uses ordinary `RightHomotopyRel` and does not
supply this enriched comparison. The worker records LeanFinder, Loogle and grep searches;
my LeanSearch query for the cofibrant/fibrant mapping-component localization theorem returned
HTTP 403 (unavailable, not no match). My Loogle query `"SSet.π₀", "IsCofibrant"` returned
zero hits. Importantly, the project search DID find an existing canonical corner map and
SM7 predicate in `SimplicialModelNerveLocalization.lean:53,63`; the replacement reuses these
through an alias and a field, instead of constructing duplicate notions. This import uses
only those definitions, not that module's localization theorem. Its recorded dependency
closure has no path back to this item. No new DAG node or dependency-module repair is needed.

Findings fixed: H3 (omitted completeness/functorial-factorization conventions), H4 (duplicate
corner-map/SM7 constructions), H6 (a local proof inside the corner-map definition), H8
(missing six-step proof docstring), and H1/H11 (placeholder second reading). The theorem
remains a single `sorry`; the corner alias and structures contain real data and no proofs.
No TeX statement or source correction was necessary. The lean record is a complete
replacement with its signature whitespace-normalized verbatim from the corrected module.

Edge cases: empty mapping sets remain empty component sets and may correspond to empty
localized Hom sets; every component, when present, has a vertex. Already bifibrant objects,
identity maps, initial/terminal objects and the degenerate initial=terminal case are covered.
No nonemptiness, properness, characteristic, finiteness, or equality of `u` and `v` is imposed.
There is no index restriction or positive-degree restriction; boundary lifting includes degree
zero through the Kan dependency. There is no pro-etale object or substitute in this delivery.

Compilation: reproduced the original snapshot file through `scompile.py NH
lem-coef-simplicial-mapping-localization <snapshot file>`: exit 0, sandbox 1.7 s,
library 1.9 s, no diagnostics. Reproduced the complete corrected file through the same wrapper:
exit 0, sandbox 1.8 s, library 1.9 s, no diagnostics. The installed wrapper identifies itself
as server-side persistent-overlay compilation and reported private `/dev/shm/nt-tmp/`
artifacts; I used the prescribed wrapper, without invoking SSH directly or changing it.
Each reported Lean invocation has a 60-second limit. No global build, delivery, merge,
preflight command, Git mutation, project-clone edit or live Lean write was performed.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
