## Worker report

Delivered statement: `SSet.Enhanced.Algebroid.Localization.enhanced_localization_universal`
in `Sheaf.CategoryTheory.EnhancedLocalizationUniversal`.
The theorem has exactly one postponed proof, `by sorry`. All twenty supporting
structures and definitions have explicit types or real constructions. None selects
an object from an existence-only theorem. The node copy changes only `lean`;
its statement, dependencies, proof, source, and bookkeeping are preserved.

This is the universal localization of **complete enriched infinity categories**,
using the already recorded operadic model. Equivalence onto the full inverting
subcategory is expressed without choosing a second full-subcategory model:
the actual restriction edge is fully faithful on coefficient mapping objects and
its essential image is exactly the inverting-object predicate. These conditions
are equivalent to the displayed full enriched subcategory equivalence in the node.

The hypotheses and clauses are rendered as follows. Names in this table are in
`SSet.Enhanced.Algebroid.Localization`, except where qualified.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Universes large enough; all categories and shapes small at the chosen bound | Explicit universes `u v`; complete algebroids use `max (u+1) v`; the integral theorem uses the recorded ambient `u+2`, object spaces at `u`, and shapes `K : SSet.{u}`. No site or coefficient universe equality is imposed. |
| V is the enhanced localization D(Z), with derived tensor | `coefficients : IntegralDerivedCoefficients.{u} p`, not the nerve of `DerivedCategory`. The parameter retains its enhanced `isLocalization`, K-flat tensor comparison, and Z[0] normalization. |
| Symmetric monoidal structure, coherent enrichment and underlying Map_V(1,Hom) | `unit : UnitSection p`, `symmetry : TensorCalculus.SymmetricExtension p`, and `S : TensorCalculus.Statement p unit symmetry`; `S.underlying.model` has the recorded unit-valued ordered-string simplices and `S.underlying.mapping` has the unit-Hom-space comparison. `S` fixes the representatives already furnished by the tensor-calculus dependency; it is not a hypothesis of localization existence. |
| Relative enriched category C and collection W in U C | `Relative.category : completeCategory unit _⦋0⦌` and `Relative.distinguished : Set ((S.underlying.model category).category _⦋1⦌)`. |
| An enriched localization functor q, inverting W | `Localized.category`, `Localized.q : SSet.Edge C.category category`, its normalized underlying map, and `Localized.inverts`. `Inverts` tests every marked edge against the recorded `IsEquivalenceEdge`. |
| Such localizations exist for every relative category | `LocalizationCalculus.localizations : ∀ C : Relative S, Localized S C`, inside the final theorem's `Nonempty`. There is no definition extracting its data from this postponed existence theorem. |
| Restriction for every enriched target E | `Localized.universal` quantifies over every target vertex of `completeCategory`. It gives an enriched edge between the two actual internal Homs. |
| Restriction is precomposition by q | The restriction edge equals `S.tensor.hom.app _ (opObjEquiv.symm q.edge, ...σ 0 B)`. This is the actual internal-Hom bifunctor applied to q and the target identity. |
| Full enriched subcategory on W-inverting functors | `InvertingObject` evaluates each actual marked edge by `S.diagrams.underlying_evaluation`. `Restriction.image` is the biconditional `TensorCalculus.InImage underlying b ↔ P b`; no functor outside this predicate is admitted, and every functor satisfying it is in the essential image. |
| Fully faithful on mapping objects, hence transformations and all higher homotopies | `Restriction.fully_faithful : Algebroid.IsFullyFaithful ((completeInclusion unit).app _ r.edge)` tests every mapping-object comparison for equivalence **in the coefficient category**. It is not an H^0 or ordinary categorical full-faithfulness assertion. `Restriction.normalized` ties the underlying map to that same enriched edge. |
| Enriched relative functor induces a functor of localizations | `LocalizationCalculus.induced`, with an actual enriched edge f, its normalized underlying F, and preservation of distinguished arrows, yields g and two composing 2-simplices with a common diagonal. This is a coherent square with fixed endpoints, not a strict equality of compositions or an arbitrary comparison between unconnected objects. |
| Transformations and specified coherent diagrams also descend | The unary restriction includes enriched mapping-object full faithfulness, `DiagramRestrictions`, and `ParameterizedRestrictions`. Thus transformations between the restrictions and every supplied coherence simplex are covered by the same restriction functor; the comparison to the input is retained in `extensionSpace`. |
| A relative functor with equivalent localized functor can be inverted under restriction | `LocalizationCalculus.inverse_restriction` applies to that localized equivalence edge. The actual contravariant internal-Hom image is an equivalence. Applying the same coherent internal-Hom functors in other variables and to free diagram parameters gives its finite-variable and diagram restrictions. |
| Opposites | `LocalizationCalculus.opposites` supplies a relative opposite and a localization whose category and q are exactly the images under `S.opposite`. `OppositeTransport` compares the source and target underlying models with their opposites and reverses the coefficient Hom entries; the underlying square with q is required to commute by a coherent natural equivalence. The marked-arrow formula transports W along that equivalence up to equivalence of arrows, necessary because an equivalent model need not contain an identical chosen 1-simplex. Such saturation gives exactly the same inversion condition, including when W is empty. |
| Relative dg categories using derived enrichment | The theorem's second conjunct quantifies over the recorded `DGRectification.Enrichment unit coefficients`, its `DGRectification.UnderlyingComparison R`, and every small dg category A. `DgSpecialization` supplies the unique ordered-string transport to the same enriched underlying model used in the first conjunct, and a `Localized` for every set of closed dg arrows. Its `strings` equation fixes the model transport on every simplex. `dgRelative` marks exactly the arrows described by `ClosedImage`: the actual localized chain map composed with the same unit and Hom comparison as `UnderlyingComparison.closed_coefficient`, saturated under equivalence of arrows. The dependency's `closed_class` and `homology` retain the H^0 normalization. The already recorded rectification theorem supplies R and U; no stronger global rectification theorem is added as a new conclusion and no Morita localization or arbitrary ordinary transformations are substituted. |
| Finitely many variables, separately inverting W_i at every fixed remaining input | `multiHom` is the iterated recorded enriched Hom; `SeparatelyInverts` recursively tests the first variable and evaluates at every fixed first input to test the rest. The first-variable equivalence in the remaining functor category is exactly pointwise equivalence by `S.diagrams.componentwise`. |
| Restriction is an equivalence of the enhanced multivariable categories | `LocalizationCalculus.multivariable` works for every `n : ℕ`, every family C, every family of unary localization representatives L, and every target B. `multiRestriction` recursively applies the actual internal-Hom bifunctor; its restriction has enriched full faithfulness and precisely the separate-inversion essential image. Currying in `S.tensor` identifies this with tensor-variable functors. |
| Compatibility with substitution, composition and identity transformations | `ParameterizedRestrictions` tests any enriched operation parameter T, including tensors of functor categories for substitution and composition. Its map is explicitly the internal-Hom image of restriction in the target variable, not an arbitrary equivalence. `ParameterCondition` requires precisely that the resulting operation land among the specified inverting functors. These restrictions include `DiagramRestrictions`; the comparison to any specified composite operation or identity and its whole coherent diagram therefore extends through the same contractible fiber. The coherent tensor/internal-Hom, currying and evaluation are the dependency's actual operations. |
| Any small homotopy coherent diagram of functors and transformations | `DiagramRestrictions` quantifies over every small simplicial set K, using the actual free enrichment `S.diagrams.free K` and the internal-Hom cotensor. `DiagramCondition` tests evaluations at the supplied vertices through `unitDiagram K`. Thus the entire specified diagram, including higher simplices and noninvertible transformations, is retained. The enriched-operation restrictions also include these cotensors. |
| Extension space over a fixed functor or specified diagram, including specified restriction, is contractible | `Restriction.extensions` asserts `IsContractible (extensionSpace underlying b)` for every admissible b, for unary, multivariable, diagram and operation restrictions. `extensionSpace` is the core of the coherent comma category restricted to **equivalence** comparison arrows. It keeps the chosen comparison with b; taking the core without first imposing this condition would incorrectly admit noninvertible comparisons. |
| A transformation is an equivalence exactly when every component is | `LocalizationCalculus.components`, with recursive `ComponentEquivalences`, states the biconditional for every finite number of variables. The unary case is the dependency's normalized component criterion. |

Dependency declarations read and used:

- `def-weil-abstract-derived-category`: full signatures and docstrings of
  `HasDerivedCategory`, `HasDerivedCategory.standard`, `DerivedCategory`,
  `DerivedCategory.Q`, and its localization instance in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`. This fixes the cochain and
  quasi-isomorphism convention; the enhanced integral coefficient object is the
  already recorded refinement, not an invented second D(Z).
- `lem-coef-enriched-category-tensor-calculus`:
  `Sheaf.CategoryTheory.EnrichedCategoryTensorCalculus`,
  `SSet.Enhanced.Algebroid.TensorCalculus.enriched_category_tensor_calculus`.
  Read the full module, especially `Statement`, `ClosedTensor`, `Underlying`,
  `IsUnderlyingEdge`, `Diagrams`, `Evaluations`, `OppositeConstruction`,
  `IntegralStatement`, `homObject`, `homAt`, `InImage`, and `arrowEdge`.
  The actual complete-category and underlying-model definitions in
  `CompleteAlgebroid` and `AlgebroidObjectSpaceFibration` were also read.
- `lem-coef-dg-enrichment-rectification`:
  `Sheaf.CategoryTheory.DgEnrichmentRectification`,
  `SSet.Enhanced.Algebroid.DGRectification.dg_enrichment_rectification`.
  Read the full theorem signature/docstring and the full owning definition module
  `DgDerivedEnrichment`, particularly `Enrichment`, `quasiEquivalences`,
  `UnderlyingComparison`, `localizedClosedArrow`, and `closedClass`.
- The listed proof dependencies are the same two project statement dependencies
  and are imported. All direct statement-dependency modules are imported publicly.

Source check: read the current main-20261015 blueprint statement and proof at
`sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint`,
particularly the derived mapping-complex adjunction in proof paragraph 2 and
its final units/counits and triangle sentence. This is an agent-formulated
foundation for that step, as the node explicitly says. Read Keller Section 4.4,
Theorem 4.7 and the refined universal properties immediately after it, pp. 16–17,
on the author's PDF:
https://webusers.imj-prg.fr/~bernhard.keller/publ/dgcat.pdf .
Those passages support dg localization and its refined functor and mapping-space
properties; they do not purport to state the entire generic multivariable
infinity-enriched formulation. That formulation follows the eight existing
DAG proof steps, reproduced in the final theorem's docstring.

Edge cases checked:

- `n=0`: `multiHom` is B, `multiRestriction` is its identity edge,
  `SeparatelyInverts` has no conditions, and `ComponentEquivalences` tests the
  sole transformation in B. The zero-variable condition is not an added
  always-true hypothesis for a positive-variable assertion.
- `n=1`: the recursive formulas reduce to exactly unary enriched precomposition.
- Empty relative category and empty object spaces: no nonempty-object binder,
  no chosen point, and no requirement that a marked collection be nonempty.
- W empty: `Inverts` and `InvertingObject` impose no inversion constraints;
  the essential image is the whole functor category. The opposite marking stays empty.
- W consisting of identities, or already invertible arrows: these remain allowed.
- Empty coherent shape K: the cotensor is the terminal diagram category and the
  diagram condition has no object tests; its specified extension space is still
  required contractible. K may be any small simplicial shape, not only a nerve
  of an ordinary category or a quasicategory.
- An empty factor in a positive-variable family introduces no spurious choice of
  an object in that factor. The recursive test evaluates only actual available
  input objects, and the component condition has the appropriate vacuity.
- Every collection of closed dg arrows, including the empty collection: `dgRelative` takes an arbitrary set of actual closed arrows and the ordered-simplex model transport is fixed in all degrees.
- Arbitrary unbounded/nonflat dg Hom complexes: the imported coefficient datum
  uses derived tensor via K-flat representatives; no projectivity, boundedness,
  flatness or pretriangulated/Morita condition is added.
- Extension spaces include restriction equivalences and higher homotopies,
  rather than strict equality of functors or a mere set of extensions.

Searches made in this attempt (prescribed launcher tool, successful responses):

- LeanFinder, `universal enriched localization relative infinity category functor categories`:
  8 hits, headed by `SSet.QCat.catEnrichedOrdinaryCategory` and ordinary enriched
  functor-category structures. No D(Z)-enriched infinity localization statement.
- LeanFinder, `Enriched localization precomposition equivalence on full functor categories inverting distinguished arrows derived enrichment`:
  8 hits, including ordinary enriched precomposition and
  `Localization.Construction.whiskeringLeftEquivalence`. Read the ordinary
  functor-category API: it does not retain the required coherent enrichment.
- LeanSearch, `enriched localization restriction equivalence coherent multivariable functors`:
  8 hits, including `Localization.functorEquivalence` and ordinary
  `Functor.IsLocalization` equivalence statements. Read
  `Localization/Predicate.lean:216–239`; the domains are ordinary functor categories.
- Loogle, `Localization, Functor`: 0 hits.
- Mathlib grep in `CategoryTheory`, `enriched.*localization|localization.*enriched`:
  0 hits. Direct Mathlib declaration-name searches found no collision for the
  new fully qualified names.
- Direct `rg` of upstream `WeilConjectures` and project `lean/Sheaf` for
  `enhanced_localization_universal|EnrichedLocalization|lem-coef-enhanced-localization-universal|enriched.*[Ll]ocalization`:
  upstream has no matching implementation; project hits include related
  simplicial mapping-cylinder and completion-localization statements and
  downstream proof docstrings citing the item. These concern different
  statements; the exact item has no declaration yet.
- `tools/lean_names_upstream.py show` and a direct item-id search of its JSON:
  no upstream binding of this item. `tools/blueprint_refs.py search enriched localization`:
  0 blueprint nodes (this is an agent-formulated foundation).

No new independent notion or dependency replacement is necessary. The twenty
supporting declarations introduce the relative localization terminology and its
universal-property interfaces in the item's own statement; each is recorded in
`lean.declarations` and has its source/blueprint docstring. The existing enhanced,
enriched, derived, opposite, and coherent-diagram notions are reused.
No statement correction, disputed statement, or remaining node fault is claimed.

Validation: the complete module passed `scompile.py` at the standard 60-second
per-file limit, with no errors and no warnings. The one theorem proof is `sorry`;
no theorem was proved, no new axiom declared, and no live source file modified.
The final packet is then checked by the prescribed `deliver2.py --no-push` before
normal delivery. Independent mathematical review is left to the maintainer as
specified in this dispatcher's brief; no second worker or subagent was started.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
