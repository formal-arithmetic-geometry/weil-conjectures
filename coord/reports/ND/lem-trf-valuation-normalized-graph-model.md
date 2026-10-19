## Worker report

Item: `lem-trf-valuation-normalized-graph-model`, group ND, stage 2.
Module: `Sheaf.TraceFormula.ValuationNormalizedGraphModel`.
Main declaration: `AlgebraicGeometry.valuation_normalized_graph_model`.
The only postponed proof is that theorem, whose entire proof is `sorry`.
The two helper definitions contain actual canonical maps, with no postponed data.
The natural-language statement, proof, and proof dependencies are unchanged.
The statement dependencies added under brief-stage2 §5 are the landed
`def-trf-modification`, owning `EtaModification`, and the landed definition node
`def-trf-relative-curve`, owning the existing `RelativeCurve` structure.
No new node or dependency-record repair is included in this delivery.
The horizontal-curve-model theorem is used only in the proof and remains in
`proof_deps`. No dependency replacement module or duplicate definition is needed.

Source read: Temkin, *Stable modification of relative curves*,
[arXiv:0707.3953v3](https://arxiv.org/pdf/0707.3953v3), Lemma 4.4.1(i), printed p. 30,
and the last paragraph of the proof of Proposition 4.4.6, printed p. 33.
The online primary PDF supplies the source; the requested archival PDF is absent
from the read-only literature tree. Lemma 4.4.1 uses normalization in the generic
fibre and identifies it with ordinary normalization when that fibre is smooth.
The last paragraph of Proposition 4.4.6 uses the normalization of the projective
graph image for the intermediate curve. The theorem docstring records all fourteen
steps of the node's expanded argument, including the extra finite-presentation,
geometric-connectedness, component-dimension, and isomorphism-locus arguments.

For the correspondence below, write `r = ProjectiveSpace.liftBaseChange f u hu.symm`,
`pI = relativeGraphImageProjection p f u hu`, and
`j = relativeGraphImageGenericInclusion p (Spec.map (CommRingCat.ofHom V.subtype)) f u hu`.
These are report abbreviations, not file-local notation. In particular,
`I = r.image`, `H = j.normalization`, `nu = j.fromNormalization`, and `g = nu ≫ pI`.

Hypothesis correspondence:

| Node hypothesis or specified object | Lean rendering |
| --- | --- |
| Separably closed field K | `(K : Type u) [Field K] [IsSepClosed K]` |
| Valuation subring V of K, fraction field K, with the element-or-inverse condition | `(V : ValuationSubring K)`; the class stores the condition for every element, and its fraction-field instance is canonical |
| Prime ideals form a finite chain | `[Finite (PrimeSpectrum V)]`; linear comparability of prime ideals follows from the valuation-ring structure |
| T = Spec V, eta = Spec K and its specified inclusion | `Spec (.of V)` and `Spec.map (CommRingCat.ofHom V.subtype)` |
| X and Y are T-schemes; f is a T-map | `p : X ⟶ Spec (.of V)` and `f : Y ⟶ X`, with the source map defined to be `f ≫ p` |
| Both are T-curves | `hX : RelativeCurve p`, `hY : RelativeCurve (f ≫ p)` |
| Curve flatness | `RelativeCurve.flat`, using Mathlib `AlgebraicGeometry.Flat` |
| Curve finite presentation | `RelativeCurve.finitelyPresented`, `.quasiCompact`, and `.quasiSeparated` |
| Pure relative dimension one | `RelativeCurve.pure : ∀ t, (y.fiber t).IsPureDimension 1` |
| Both schemes normal | `hnX` and `hnY`: at every point the stalk is an `IsDomain` and is `IsIntegrallyClosed` |
| Both generic fibres smooth | `hsX`, `hsY`: `Smooth` of the pullback second projections to `Spec K` |
| f is an eta-modification | `hf : EtaModification ... f p` |
| Properness and schematically dense isomorphism opens in that hypothesis | `EtaModification` contains `SchemeModification`, whose fields are properness and an open with schematic density on both source and target and invertible restriction |
| The specified generic-fibre map is invertible | The second conjunct of `EtaModification` uses the actual slice-pullback map, not abstract isomorphism types |
| Arbitrary T-morphism u to the projective line | `u : Y ⟶ ℙ(ULift.{u} (Fin 2); Spec (.of V))` and `hu`, its equality over T |

Using `f ≫ p` as the source structure map loses no diagrams: a separately named
source map and an equality saying f is over T can be substituted to this form.
No separatedness, properness over T, integrality, connectedness, or nonemptiness
of X or Y has been added.

Construction and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Projective graph `(f,u)` in P1_X | The existing `ProjectiveSpace.liftBaseChange f u hu.symm`, from the recorded projective-space module |
| Its first projection is f | This is the existing `ProjectiveSpace.liftBaseChange_over` |
| Its second relative projection recovers u | The existing `ProjectiveSpace.liftBaseChange_map` gives equality after composition with `ProjectiveSpace.map ... p` |
| Scheme-theoretic image, with kernel ideal | `r.image = r.ker.subscheme`, its actual image inclusion `r.imageι`, and its canonical factor `r.toImage` from Mathlib |
| Projection I to X | `relativeGraphImageProjection p f u hu = r.imageι ≫ (ℙ(...; X) ↘ X)` |
| Normalization H in product of component function fields | `j.normalization` uses Mathlib's actual integral-closure diagram and gluing in the normal generic fibre; see the equivalence explanation below |
| The normalization morphism nu | `j.fromNormalization : j.normalization ⟶ r.image` |
| I reduced | First conclusion `IsReduced r.image` |
| I a T-curve | `RelativeCurve (pI ≫ p)` |
| nu finite | `IsFinite j.fromNormalization` |
| H normal | The quantified `IsDomain` and `IsIntegrallyClosed` stalk conjunction on `j.normalization` |
| H a T-curve | `RelativeCurve (j.fromNormalization ≫ pI ≫ p)` |
| Unique factorization of h through nu | The existential q, its equation `q ≫ j.fromNormalization = r.toImage`, and the universal equality `q' = q` for every other factorization |
| g is p after nu | The term `j.fromNormalization ≫ pI` is g itself |
| Both q and g eta-modifications | The two `EtaModification` conjuncts, with the appropriate target-to-T maps |
| gq = f | `q ≫ j.fromNormalization ≫ pI = f` |
| Every geometric fibre of q connected | `∀ z, GeometricallyConnected (q.fiberToSpecResidueField z)`; geometric connectedness is equivalent to connectedness after an algebraic closure, including nonemptiness |
| A fibre component is contracted by q iff both projections contract it | For every `s`, every `A ∈ irreducibleComponents ((f ≫ p).fiber s)`, the equivalence between `topologicalKrullDim (q '' ((f ≫ p).fiberι s '' A)) = 0` and the analogous two dimension-zero assertions for f and u |
| Modification locus exactly points with positive-dimensional fibre | At every z, `(∀ W, z ∈ W → ¬ IsIso (q ∣_ W)) ↔ 0 < topologicalKrullDim (q.fiber z)` |
| q invertible over each open U of X where f is invertible | `∀ U, IsIso (f ∣_ U) → IsIso (q ∣_ (g ⁻¹ᵁ U))` |
| All component assertions refer to reduced underlying components | Irreducible components and their images are sets with the induced topology; their Krull dimension ignores nilpotents |
| Geometric fibres are algebraic-closure base changes | Mathlib `GeometricallyConnected` is the field-extension-independent encoding; its use on `fiberToSpecResidueField` specializes to the exact geometric fibre in the dependency's pullback description |
| Geometrically reduced means no nonzero fibre nilpotents | This is explanatory terminology in the node, not an additional hypothesis or conclusion; no geometric-reducedness assertion has been added |

Normalization and dimensions deserve two checks. The two existential typeclass
proofs merely allow the canonical `j.normalization` to elaborate: they are
conclusions, not extra assumptions, and proof irrelevance removes dependence on
their values. On an affine U of I, this construction takes the integral closure
of O_I(U) in O_(I_eta)(U_eta). The generic fibre is normal and schematically
dense, meeting every component. An element of the product of component function
fields integral over O_I(U) is integral over every local ring on U_eta, so lies
in every such normal local ring and hence in O_(I_eta)(U_eta). Conversely that
section ring embeds in the product of component fields. The two integral
closures are therefore the same. This uses precisely the interface already
employed by `Temkin.ValuationNormalizationPreparation`; it is not a choice of
an unspecified normalization or an integral-only replacement.

For the component criterion, the fibre inclusion is a topological embedding,
and the topology of the image inside its target fibre agrees with the induced
topology in the full target. Thus taking the images as subsets of H, X, and
P1_T gives the node's dimension-zero images. Nilpotent structures have no effect
on any of these dimensions. The criterion uses equality to zero, not dimension
at most zero: empty images have dimension bottom and are not contracted
components. Irreducible components are nonempty, so no component case is lost.

Dependency declarations read and reused:

- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (the same recorded module also
  provides `IsSepClosure`; this statement needs only the top field).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, with the node's bottom
  dimension for the empty space and the induced topology on subsets.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`:
  `AlgebraicGeometry.ProjectiveSpace`, `ProjectiveSpace.over`,
  `ProjectiveSpace.toProjInt`, `ProjectiveSpace.map`, `ProjectiveSpace.hom_ext`,
  and `ProjectiveSpace.liftBaseChange` with its projection identities.
  Two homogeneous coordinates are `ULift.{u} (Fin 2)`, so this is P1, not P2.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`; finite presentation includes
  the recorded quasi-compact and quasi-separated conditions via `RelativeCurve`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `Scheme.normalization` and `Scheme.fromNormalization`, read in full. They
  specialize Mathlib `Scheme.Hom.normalization` and `.fromNormalization` to an
  integral scheme's generic point. The general Mathlib relative-normalization
  construction is used for the potentially disconnected image here, with no
  copied definition and no integrality assumption.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.Algebra.Field.Defs`: `Field` (a Mathlib leaf without a Lean record).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`;
  `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `.fiberι`, and
  `.fiberToSpecResidueField`; the geometric-fibre dependency records this exact
  specialization of pullbacks and does not require a replacement definition.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with `IsDomain`, in exactly the recorded stalkwise inline form.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`,
  used by the existing `SchemeModification` definition.
- `Sheaf.TraceFormula.Modification`: `SchemeModification`, `EtaModification`.
- `Sheaf.TraceFormula.ValuationHorizontalCurveModels`: `RelativeCurve`, owned
  by the landed `def-trf-relative-curve` through its `existing: true` record. Its plain structure
  does not depend on `horizontal_curve_models`. The latter remains a proof input;
  no private replacement was introduced.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `Scheme.Hom.image`,
  `.imageι`, and `.toImage`, from the existing schematic-image proof dependency.
- `Mathlib.AlgebraicGeometry.Geometrically.Connected`:
  `AlgebraicGeometry.GeometricallyConnected`.

The module also imports every recorded proof-dependency module that exists,
including the normalization preparation, proper normal connectedness,
finite-birational normal isomorphism, dense finite presentation, projective charts,
schematic-image restriction, and finite-surjective dimension modules. These
imports are ordinary imports when needed only for the future proof.

Edge cases checked before and after writing:

- V a field (height zero): eta is all of T, f is invertible, and the final
  conclusion gives q invertible everywhere. No nonzero proper prime is assumed.
- Empty X and Y: `RelativeCurve` is vacuous fibrewise; normality is stalkwise;
  no `IsIntegral` or `Nonempty` binder excludes the empty normalization.
- Disconnected normal curves: relative normalization works componentwise;
  there is no single-function-field assumption.
- Nonproper and nonseparated curves over T: neither is excluded. Properness is
  imposed only on f through its modification hypothesis.
- Non-Noetherian finite-height valuation rings: no Noetherian assumption appears.
  Finite presentation of the image remains a conclusion needing proof step 5.
- Empty open U: the final restricted map is between empty schemes, as required.
- Zero-dimensional and positive-dimensional q-fibres: the locus equivalence uses
  strict positivity, and an isomorphism fibre has dimension zero. Connectedness
  is geometric, including nonemptiness, so empty q-fibres are not admitted.
- Arbitrary characteristic and rank: no characteristic or rank-one restriction.
- All schemes, fields, and residue-field base changes live in the same explicitly
  declared universe u, with the finite coordinate type lifted to that universe.
  No independent smaller universe makes a quantified condition vacuous.

Searches (all through the authorized wrapper unless noted):

- LeanFinder: “Normalized schematic graph image of a proper modification of
  normal relative curves over a valuation ring has finite normalization and
  connected fibres”. Eight hits, all general relative normalization maps and
  instances (`Scheme.Hom.normalization`, `.toNormalization`, `.normalizationDesc`,
  `.fromNormalization`, etc.); none is this graph-model theorem.
- Loogle: `AlgebraicGeometry.Scheme.Hom.normalization, AlgebraicGeometry.Scheme.Hom.image`.
  Zero hits.
- Grep Mathlib/AlgebraicGeometry: `normalization.*[Ii]mage|[Gg]raph.*normaliz`.
  Seven hits in `Normalization.lean` and `ZariskisMainTheorem.lean`, concerning
  normalization open covers and general maps, not this theorem.
- LeanSearch: “Normalization of the image of a proper graph of relative normal
  curves has geometrically connected fibres”. Eight general normalization hits;
  no valuation-curve graph theorem.
- Direct `rg` of upstream `WeilConjectures` and project `lean/Sheaf` for the item
  id and normalized-graph names: only the downstream exceptional-blowdown proof
  docstring cites the item; no existing theorem.
- Direct `rg` of Mathlib, upstream, and side sources for the two helper
  names and `valuation_normalized_graph_model`: no declarations before writing.
- Direct source reading of the returned normalization declarations, the recorded
  projective-space declaration, every statement-dependency signature and docstring,
  and the already landed valuation curve and modification interfaces.

Validation: `scompile.py ND lem-trf-valuation-normalized-graph-model` on the module
compiled the initial version of the sandbox and final library module cleanly,
in 3.1 and 2.7 seconds. A subsequent source scan found the already implemented
`ProjectiveSpace.liftBaseChange`; the final version uses it directly and removes
the redundant graph helper. The final compile and delivery preflight are recorded
below.
No errors or warnings were printed. All variables and universe u are explicit.
No theorem was proved. No statement correction or disputed statement is needed.

## Second reading by ND

This section records the author's second semantic pass; no separate agent was
started, as the dispatcher brief forbids that. The maintainer's independent
review reads this delivered packet.

The node and final source were reopened together. The two tables above check
every hypothesis and conclusion, including the different codomains of nu and g,
uniqueness over I, both modifications, the actual factorization, geometric
connectedness, both directions of the component criterion, the exact
positive-dimensional-fibre locus, and restriction over opens of X. The review
specifically checked that `hu` supplies the T-compatibility needed for the
canonical graph into P1_X, that the image is the kernel subscheme, and that H
is the genuine normalization rather than an arbitrary normal intermediate.
The normalization's qcqs conditions are existential conclusions. Its construction
allows the empty and disconnected cases. No added geometric-reducedness clause,
normality-to-integrality substitution, or extra separatedness hypothesis was
found. The finite-prime-chain hypothesis is exactly finite spectrum for a
valuation ring. The second pass found that the graph map itself already had a canonical
upstream declaration, `ProjectiveSpace.liftBaseChange`. The final version now uses
that declaration directly; the two remaining helpers only name the image
projection and its generic inclusion. No mismatch requiring a mathematical
statement change was found.

Final direct `scompile.py` validation after adopting the existing graph construction:
clean sandbox compile (2.5 s), clean library-module compile (2.5 s).


## Repair of immutable head 161df23b87b6

The return identifies one defect: `def-trf-relative-curve` was created by another
landed delivery, so it must be reused rather than delivered as a new node.
The required first dry run on the retained packet confirmed this: preflight
classified the saved copy as a dependency-node Lean-record change and rejected
its missing dependency-module report section. The old saved copy would replace
the landed NC ownership record, although its interface was already usable.

I compared the saved node with the current shared node. The current node is
reviewed, created by NC for `lem-trf-valuation-modification-proper-completion`,
and records exactly the same module, declaration and signature:
`Sheaf.TraceFormula.ValuationHorizontalCurveModels`,
`AlgebraicGeometry.RelativeCurve`,
`structure RelativeCurve {T Y : Scheme.{u}} (y : Y ⟶ T) : Prop`.
Its full statement explicitly permits nonseparated curves and empty fibres.
I reopened that declaration and its docstring at line 74. Its fields are
`flat : Flat y`, `finitelyPresented : LocallyOfFinitePresentation y`,
`quasiCompact : QuasiCompact y`, `quasiSeparated : QuasiSeparated y`, and
`pure : ∀ t : T, (y.fiber t).IsPureDimension 1`.
These are precisely the predicate required by this item on X, Y, I and H.

The repair removes the redundant definition-node copy from the sandbox. The
item retains `def-trf-relative-curve` in `stmt_deps` as an already landed node,
as brief-stage2 §5 permits, and imports its recorded module. Its Lean note now
identifies that reuse. There are no new nodes or dependency-record changes.
The item compared with current shared main changes only `lean` and adds the two
landed definition dependencies `def-trf-modification` and
`def-trf-relative-curve`. The mathematical statement, proof, proof dependencies,
and entire Lean module are retained from the returned packet.
The earlier ownership return on head `b2e1a99369e4` remains resolved: the
horizontal-curve-model theorem occurs only in `proof_deps`, and the definition
of relative curves is cited through its own landed definition node.

## Second reading by ND (repair)

I reopened the current definition node and its recorded declaration, the saved
item node and the complete Lean module. This is an author self-check; no agent
was started, as the dispatcher forbids delegation. The hypothesis and conclusion
correspondence in the tables above still applies verbatim. In particular the
five relative-curve fields exactly match flatness, full finite presentation and
pure fibre dimension one, without a separatedness or nonemptiness hypothesis.
Both canonical helper definitions contain actual maps; the only postponed
proof is the graph-model theorem. Its signature matches `lean.statement`.
No mathematical statement correction is necessary.

The repaired packet reuses NC's reviewed ownership record without modifying it.
The statement-dependency path cannot return to the graph-model theorem, because
the relative-curve node uses only foundational definitions. Empty fibres, empty
source/base, disconnected curves, arbitrary characteristic and non-Noetherian
finite-height valuation rings remain included. The item still uniquely factors
the actual graph image through its normalization, asserts both modifications,
geometrically connected fibres, both directions of the component contraction
criterion, the precise modification locus, and invertibility over the specified
opens. No Lean declaration or mathematical assertion changed during this repair.

Repair validation on 2026-10-19: direct `scompile.py` compiled both sandbox and
library forms cleanly in 3.9 s and 2.3 s. The exact theorem signature matches
`lean.statement`; every Lean line is at most 100 characters and the only sorry
is the named theorem's whole proof. The repaired `deliver2.py --no-push` passed
preflight and all per-file compiles: `OK (dry run)`, commit `8f47a3f9ae`.
The staged set is exactly the item node, its Lean module, and this report;
`def-trf-relative-curve.json` is no longer part of the delivery.
