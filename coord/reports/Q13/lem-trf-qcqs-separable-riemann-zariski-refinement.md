## Worker report

The module `Sheaf.AlgebraicGeometry.QcqsSeparableRiemannZariskiRefinement` states
`AlgebraicGeometry.RiemannZariski.qcqs_separable_refinement`, with proof `sorry`.
Its only helper, `separableGenericMap`, is the explicit composite of `Spec.map`
of the algebra map with `S.fromSpecStalk (genericPoint S)`. It contains real data.
The theorem docstring reproduces all fourteen proof steps of this node, including
qcqs permanence, the valuation-pair inverse constructions, both topology
comparisons, and the relative-cover argument.

The natural statement is unchanged. The only added statement dependency is the
already landed `lem-trf-riemann-zariski-finite-refinement`: its module owns the
unrestricted definitions of `GenericScheme`, `Model`, `QuasiModel`, `ModelHom`,
`Point`, `pointTopologicalSpace`, `GenericScheme.fieldEmbedding`,
`GenericScheme.IsFiniteSeparableOver`, `ValuationPoint`, `Corresponds`,
`ValuationPoint.LiftsTo`, and `ValuationPoint.push`. The old theorem in that module
requires finite type over Z and asserts a height bound; it is not the present
statement. No theorem of that module is used to strengthen the hypotheses here.
No new node and no dependency repair is needed.

The correspondence of every hypothesis and clause is as follows.

| Node text | Lean rendering |
| --- | --- |
| Integral scheme S | `(S : Scheme.{u}) [IsIntegral S]` |
| Quasi-compact, quasi-separated S | `[CompactSpace S] [QuasiSeparatedSpace S]`; for schemes, this is equivalent to a finite affine cover with quasi-compact pairwise intersections |
| F = k(S) and specified separable closure L/F | `S.functionField`, `(L : Type u) [Field L] [Algebra S.functionField L] [IsSepClosure S.functionField L]` |
| Spec L mapping to the specified generic point of S | `separableGenericMap S L`, explicitly induced by the given algebra map |
| Integral proper L-model with generic factorization | `Model S L (separableGenericMap S L)`; its fields are integral `X`, proper `map`, `generic`, `generic_point`, and `fac` |
| Separated finite-type L-quasi-model | `QuasiModel S L ...`; its fields supply `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` of the structure morphism |
| Model morphisms over S commuting with Spec L | Existing `ModelHom.over` and `.generic`, used in the compatibility condition defining `Point` |
| All model and quasi-model function fields finite separable inside L/F | First conjunct, `∀ U, U.toGenericScheme.IsFiniteSeparableOver (algebraMap S.functionField L)`; models are included via `Model.toQuasiModel` |
| RZ inverse limit and its coarsest topology | Existing `Point` is the subtype of point families compatible with every `ModelHom`; `pointTopologicalSpace` is the infimum of the induced projection topologies |
| RZ is quasi-compact | `CompactSpace (Point S L ...)` |
| Its points are exactly centred valuation subrings V of L | `∃ e : Point ... ≃ ValuationPoint ...`, with `∀ x, Corresponds x (e x)` |
| Full morphism c: Spec V to S extending the generic map | `ValuationPoint.centre` and `.fac`; `Corresponds` characterizes every coordinate by a proper lift of this same centre morphism, preserving more than the underlying centre point |
| Valuation condition and fraction field L, without a height bound | `ValuationSubring L` is the existing subring with `x ∈ V ∨ x⁻¹ ∈ V`, and has its natural fraction-field structure on L; no height or rank assumption or conclusion occurs |
| For each U, composition gives an open injection RZ(U) to RZ(S) | Existential `eU` and `j`, with `Corresponds x (eU U x)`, `IsOpenEmbedding (j U)`, and `e (j U x) = ValuationPoint.push U (eU U x)` |
| Image consists exactly of pairs lifting to U | `x ∈ Set.range (j U) ↔ (e x).LiftsTo U` |
| Natural identification RZ(T) = RZ(S) for a model | For every `M : Model ...`, a homeomorphism `h : Point M.X L M.generic ≃ₜ Point S L ...` whose function is `j M.toQuasiModel` |
| Every finite family U_i | `∀ (I : Type w) [Finite I] (U : I → QuasiModel ...)` |
| One common L-model T | Existential `M : Model ...`, chosen once for all the subsequent clauses |
| Quasi-compact open subschemes W_i in T | Existential `W : I → QuasiModel S L ...`, maps `a i : (W i).X ⟶ M.X`, and `IsOpenImmersion (a i) ∧ CompactSpace (W i).X`; each W is identified with its open image, so this represents exactly an open subscheme |
| Proper dominant maps W_i to U_i | `q i : (W i).X ⟶ (U i).X` with `IsProper (q i) ∧ IsDominant (q i)` |
| Maps are over S | `a i ≫ M.map = (W i).map` and `q i ≫ (U i).map = (W i).map` |
| All specified generic maps agree | `(W i).generic ≫ a i = M.generic` and `(W i).generic ≫ q i = (U i).generic` |
| RZ(W_i) = RZ(U_i) inside RZ(S), using the natural model identification | `Set.range (j (W i)) = Set.range (j (U i))`; j is already characterized by composition of valuation centres, and the homeomorphism for M supplies precisely the identification with RZ(M) |
| If RZ(U_i) cover RZ(S), W_i cover T | `(∀ x, ∃ i, x ∈ Set.range (j (U i))) → ∀ y : M.X, ∃ i, y ∈ Set.range (a i)` |
| Any selected subfamily over any open S0 | `∀ (J : Set I) (S₀ : S.Opens)` with no compactness or nonemptiness condition on S0 |
| Selected U_i factor through S0 | `∀ i, i ∈ J → ∃ g : (U i).X ⟶ S₀.toScheme, g ≫ S₀.ι = (U i).map` |
| Selected RZ(U_i) cover RZ(S0) | Every `v : ValuationPoint S L ...` whose `v.centre` factors through `S₀.ι` lifts to a selected `U i`; by the preceding correspondence and image equivalence this is exactly the cover of the relative valuation subspace, including when S0 is empty |
| Corresponding W_i cover T ×_S S0 | `∀ y : M.X, (∃ i, i ∈ J ∧ y ∈ Set.range (a i)) ↔ M.map y ∈ S₀`; the right side is the underlying open of the base change. The reverse inclusion is the stated cover, and the forward inclusion follows from the required factorizations and over-S equalities |

The W_i are stored as quasi-models over S solely to use the existing j maps on
those actual schemes. This adds no mathematical restriction: a quasi-compact
open in a proper integral model, containing the specified generic point, is
integral and separated of finite type over S. Conversely the open immersions
in the conclusion identify these schemes with exactly the opens the node asks
for. No canonical construction has been replaced by an arbitrary unrelated map:
the e/eU correspondences and the push equation characterize j by composition.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` and `IsSepClosure`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  the separated and universally closed definitions are the inherited Mathlib
  `IsSeparated` and `UniversallyClosed`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType` and `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map`.
- `Sheaf.AlgebraicGeometry.RiemannZariskiFiniteRefinement`: all the unrestricted
  Riemann--Zariski interfaces listed above, read with their full definitions
  and docstrings, not the more specialized theorem as a replacement.

The statement interfaces arrive through the public Riemann--Zariski import.
Already stated proof modules are also imported directly without `public`:
qcqs permanence, projective spectrum, properness/closed immersions, valuative
criteria, valuation domination and extension, Nagata compactification, spectral
spaces and spectral directed limits. The reduced-induced-closed-subscheme
proof dependency has a side record, but the public Riemann--Zariski module
already imports its exact upstream declaration; importing the duplicate side
module would declare the same name twice. This delivery consistently imports
the upstream module, as required by the duplicate-import repair instruction.
No dependency's mathematical interface is changed.

Source check: read Temkin's primary arXiv v3 PDF
https://arxiv.org/pdf/0707.3953v3, §3.2, printed pp. 15--17, including the general
integral-base hypotheses and the model/quasi-model definitions. The source URL
in the node timed out, but the identical arXiv v3 source was accessible. The
relative valuation-subspace formulation also agrees with the node's explicit
last proof step, without restricting S0 to be qcqs.

Edge cases checked before writing:

- S is nonempty because it is integral; no hidden empty-scheme exception is added.
- The finite family and selected subfamily may be empty. The identity model
  provides the empty-family refinement; the global covering premise is then
  false, while over the empty open the relative covering conclusion is empty
  and true.
- S0 is arbitrary, possibly empty or not quasi-compact. It is represented as
  an open and by actual factorizations of valuation centre morphisms, never
  as an extra qcqs base or a nonexistent generic map to the empty scheme.
- S need not be separated over Z. Both centre morphisms and their generic
  compatibility are retained, so equal underlying centre points are not used
  as substitutes for equal morphisms.
- L may equal an already separably closed function field. The algebra map
  and the generic map remain the specified ones in this case.
- Valuations of unbounded height are allowed. The older finite-type theorem's
  height conclusion is deliberately absent because the node asserts none.
- The family universe w is arbitrary, and the family is finite; no nonempty
  index assumption is introduced. Models, fields and schemes use the same
  ambient universe u as the existing interfaces.

Searches for a duplicate statement or notion:

- `msearch.py leanfinder`: "Riemann Zariski space of proper models over an integral quasi compact quasi separated scheme is quasi compact and finite quasi models have common proper refinements". Eight results concern normalization, quasi-compact maps, or covers; no matching theorem.
- `msearch.py leansearch`: "Riemann Zariski valuation proper models common finite refinement". Eight results include `IsProper.of_valuativeCriterion` and properness of finite morphisms, but no matching theorem.
- `msearch.py loogle`: "ValuationSubring, IsSepClosure". No hits.
- `msearch.py grep`: `RiemannZariski|QuasiModel|FiniteRefinement` in Mathlib AlgebraicGeometry. No hits.
- `rg` in upstream WeilConjectures for `Riemann`, `RiemannZariski`, `QuasiModel`, `LModel`, `ValuationPair`, and this node id: no Riemann--Zariski interface or theorem (Riemann--Roch hits are unrelated).
- `rg` in the side library for the same notions finds `RiemannZariskiFiniteRefinement.lean`, read in full, and consumers using its interfaces. It has the definitions needed here but its theorem requires finite type over Z. Searches for the chosen new declaration and generic-map helper names found no collisions.
- DAG search confirms `lem-trf-riemann-zariski-finite-refinement` owns the reused interfaces; the item cites this landed node rather than adding duplicate definitions or a new definition node.

Validation: `scompile.py` compiled the delivered file in sandbox and final library
positions with no errors or warnings, each in under three seconds. The only
postponed theorem is `qcqs_separable_refinement`, matching this node; all helper
data are explicit. There is no statement correction and no disputed statement.

## New nodes

`def-trf-riemann-zariski-interfaces` is the requested definition node. It records the
existing `Sheaf.AlgebraicGeometry.RiemannZariskiFiniteRefinement` module as the owner of
the plain generic-scheme, model, quasi-model, model-morphism, point/topology,
function-field, valuation-point, correspondence, lift, and push declarations. Its
statement cites the integral-scheme, proper-morphism, finite-type-morphism, and affine-
spectrum interfaces. Searches found no such node, Mathlib declaration, or upstream
`WeilConjectures` declaration; the exact module was found in `lean/Sheaf`. The separate
`FiniteRefinement` structure and `finite_refinement` theorem in that module are not
listed or used. This node replaces the former citation of the theorem node, as required
by the returned H2 review.

## Second reading by Q13

I reread the new node and its recorded module independently. The declaration list contains
each plain notion used by the item and excludes the finite-refinement theorem and structure.
The existing module's signatures and docstrings match the node's generic factorization,
proper/separated finite-type models, compatible point families and topology, canonical
field embedding, finite-separable predicate, centred valuation pair, correspondence,
lift, and push clauses. The item now cites this definition node in `stmt_deps`; no statement
clause relies on the old finite-refinement theorem. No mismatch or edge-case change was
found.
