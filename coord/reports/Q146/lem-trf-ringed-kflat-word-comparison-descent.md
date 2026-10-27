## Worker report

The module `Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent` states the entire
node in eight named theorems, each with `sorry`, source references and its corresponding
natural-language proof. The primary declaration is
`CategoryTheory.RingedKFlatWord.word_comparison_descent`; `lean.declarations` records the
remaining clauses and the concrete helper data. No original statement or proof is changed.
All writes were confined to the assigned sandbox; all compiler calls used scompile.py.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean rendering |
| --- | --- |
| Finite collection of small sites in fixed sufficiently large universes | `I : Type z`, `[Finite I]`, `S : I → Site.{u,v,r,d}`; `Site.C`, `category`, `small`, `J`. The independent site object, site morphism, coefficient, derived Hom, vertex and edge universes are `u v r d z e`. Common bounds are the fixed bounds of the size convention; object and morphism sizes are not equated. |
| Sheaves of commutative rings | `Site.R : Sheaf J CommRingCat.{r}`. |
| The actual module categories, unbounded complexes and localization Q | `CochainPullback.Modules.{r,u,v} (J := X.J) X.R`, definitionally the recorded `ringedSiteModules`/Mathlib `SheafOfModules`; `CochainComplex … ℤ`; `DerivedCategory` and `DerivedCategory.Q`, with `Site.derivedCategory : HasDerivedCategory.{d} …`. |
| Every edge is ordinary pullback of a specified ringed geometric morphism, including nonflat scalar change | `Edge.pullback : CochainPullback.RingedPullback …`, reused from the already landed cochain-coherence dependency. This has the inverse-image adjunction, finite-limit preservation, algebraic inverse image, structural ring map, actual change-of-rings object/map equations, module adjunction and additivity. No arbitrary additive functor is substituted. An identity underlying geometric inverse image and any ring map are allowed. |
| Chosen total derived functor and universal cochain counit | `Edge.derived`, `Edge.counit`, `Edge.universal : derived.IsLeftDerivedFunctor counit (HomologicalComplex.quasiIso … (.up ℤ))`. The actual universal pair, rather than a bare isomorphic functor, is used everywhere. An exact functor with its canonically identified exact derived pair is included. |
| Finite composable words and the empty identity word | `Word E i j`, with `nil`, `edge`, and `comp`. Binary parenthesizations are retained; every finite string has one, and no extra edge is assumed. `ordinary`, `complex` and `derived` evaluate the specified ordinary, degreewise and derived factors. |
| Composite counits in the specified order | `Word.counit`: for `comp w v` it applies `v.derived` to the counit of w, then the counit of v on the ordinary image of P, then the canonical Mathlib degreewise compositor. The empty counit is the identity through `mapHomologicalComplexIdIso`. |
| One quasi-isomorphism P → K of whole complexes with P K-flat and flat terms | `simultaneous_resolution`: one existential `P` and `p`, `QuasiIso p ∧ Resolving (S i) P`. `Resolving` is exactly `IsKFlatIndependentCoefficients` and the degreewise `IsFlatOnSite` conjunction. Termwise surjectivity from the stronger resolution tool is deliberately not asserted, because this node does not assert it. |
| The same P works for every intermediate of every word, every word counit invertible | The final universal quantifier of `simultaneous_resolution` ranges over every target j and `Word E i j`. Every prefix is itself a word, so this includes all intermediates simultaneously, independent of the number of words. `word_computation` additionally states this for every flat-term K-flat P, not only the chosen replacement. |
| Every ordinary natural transformation has a unique normalized derived transformation | `descent_existsUnique` quantifies `t : w.ordinary … ⟶ v.ordinary …` and concludes `∃! tL, Normalized … t tL`. `Normalized` is exactly `tL.app (Q.obj P) ≫ ε_v,P = ε_w,P ≫ Q.map (C(t).app P)` for every resolving P. Lean's composition is written in traversal order, so this is the displayed node equation. |
| Assignment with that equation | `Word.cell` extracts the uniquely determined transformation from `descent_existsUnique`; `cell_normalized` explicitly states its equation. The choice is of a unique object, never data from an unconstrained existence theorem. |
| Identities, vertical composition, input and output whiskering | `Expression.id`, `comp`, `input`, `output`; `Expression.ordinary` and `Expression.derived` use the literal identity, vertical composition and `Functor.whiskerLeft`/`whiskerRight`. The first conjunct of `word_comparison_descent` says each such evaluation is the normalized descent of its ordinary evaluation, including whiskering by an edge and by an arbitrary word. |
| Every equality of finite pastings | `Expression` also includes actual functor associators and unitors in both directions. The second conjunct says equal ordinary evaluations give equal derived evaluations. Cells may be arbitrary ordinary transformations, and this finite grammar covers every specified pasting. |
| Ordinary isomorphisms give derived isomorphisms | The third conjunct of `word_comparison_descent`: `IsIso t → IsIso (Word.cell … t)`. |
| Natural transformations determined on Q(P) | `determined_on_resolving` for any two functors from the source module derived category into the target module derived category. Taking the two derived words gives exactly the node's assertion. |
| Scalar associator c tensor (b tensor x) ↦ cb tensor x | `scalar_associator` gives an ordinary natural isomorphism with the actual sectionwise formula using the existing `scalarTensorSection`, then a unique derived natural isomorphism with the displayed composite cochain-counit equation. It uses `b.hom.app U s * t`; this equals the scalar-first node formula `t * b(s)` by commutativity. Source and target localization universes `wR wS wT` stay independent. |
| Identity scalar change s tensor x ↦ sx | `scalar_unit` gives the ordinary formula `… = s • x` and a unique derived natural isomorphism to the identity with its counit normalization. |
| Actual ringed sequence site, whole strict systems before evaluation/limit | `coefficientSequenceSite` uses the recorded `coefficientSequenceTopology`, `coefficientSequenceCommRingSheaf`, `coefficientSequenceEssentiallySmall` and `coefficientSequenceHasDerived`. Its object/morphism sizes are `v+1` and `v`, and coefficient size `max u (v+1)`. Instantiating S at this Site gives the same whole-system resolutions and equations. No component evaluation or limit occurs anywhere in the theorem or its constructions. |
| No boundedness, normalization, Tor amplitude, or structural flatness assumptions | None occurs in `Site`, `Edge`, the theorem binders or the scalar specializations. The only flatness assumptions in comparison normalization are flatness of the resolving terms, exactly as in the node. |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, via
  `CategoryTheory.CochainPullback.Modules`; this is Mathlib's category, not a copied category.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`; the full complex/morphism
  signatures, and `Mathlib.Algebra.Homology.Additive` degreewise identity/composition and
  natural-transformation maps were read.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`, `DerivedCategory`, Q.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, the recorded acyclic-total-tensor predicate.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Sheaf.SecSmoothPurity.CochainTensorCoherenceData`: existing `RingedPullback`, `Modules`,
  `pull`; its presentation theorem explains that module functor/adjunction data do not
  impose an additional restriction on a ringed geometric morphism. The older
  `RingedToposMorphism` record was read in full: its single-size noncommutative-ring
  presentation is not copied or specialized by imposing equality of the site universes.
  The already recorded, commutative-ring pullback presentation is used directly instead,
  and its owning definition node is added to stmt_deps.
- `Sheaf.Paper.PullbackTensorResolvingComputation`:
  `SheafOfModules.PullbackTensorResolving.pullback_resolving_computation` (universal cochain
  counit on every flat-term K-flat complex); imported as a proof tool.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- `Sheaf.Paper.KFlatRingedToposPullback`: `SheafOfModules.isKFlat_ringedToposPullback`.
- `WeilConjectures.CategoryTheory.NatTransFromResolvingClass`:
  `CategoryTheory.exists_natTrans_from_resolvingClass`; its full right-fraction hypotheses
  and natural-family conclusion were checked.
- `Mathlib.Algebra.Homology.DerivedCategory.Fractions`: the left/right calculus instances;
  `Mathlib.CategoryTheory.Localization.Predicate`: full faithfulness and `natTrans_ext`.
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`:
  `exists_sheafificationTensorIso` and `nonempty_sheafTensorSheafificationIso`;
  `Mathlib.LinearAlgebra.TensorProduct.Tower`: `cancelBaseChange`, its two pure-tensor
  formulas and its naturality equation.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`, with its ordinary object/map equations,
  universal cochain pair and independent derived Hom universes.
- `Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence`:
  `CategoryTheory.PrincipalQuotientCompletion.scalarTensorSection`, reused verbatim.
  This helper's own signature has no finite-free or completion hypotheses. The module's
  `BalancedScalarAssociator` and `BalancedScalarUnit` were read: they are specifications,
  whereas this node states existence and uniqueness of the normalized maps. No existing
  existence theorem for this general word descent or these fixed universal pairs was found.
- `Sheaf.Paper.CoefficientRingedSequenceSite`: the sequence-site declarations listed above.

The three added stmt_deps name definition interfaces, as permitted by brief-stage2 §5:
`def-pur-cochain-tensor-coherence-data`,
`def-sfb-derived-change-of-rings-cochain-model`, and `def-trf-scalar-tensor-section`.
The first two are landed definition owners; the third is the new definition owner
requested on return. The theorem nodes are not statement dependencies.

Edge cases checked: empty I (no source vertex), singleton I and no edges (empty words),
zero-length and parenthesized words, the zero complex, zero rings, identity ring maps,
nonflat scalar maps such as Z → Z/4 → Z/2, noninvertible natural transformations, exact
edges, arbitrary unbounded complexes, and the sequence site's unequal object/morphism
universes. There is no hypothesis that a nonexact edge preserve all quasi-isomorphisms.
All resolving and counit assertions are in the actual derived category, not merely on
its individual cohomology objects. No STATEMENT-DISPUTED flag or statement correction.

Searches performed (msearch.py Q146 with this item):

- LeanFinder: "Finite words of ringed pullbacks admit simultaneous K-flat resolutions
  and unique normalized descent of ordinary natural transformations" — 8 hits, including
  `compatiblePreservingOfFlat`, a derivability-structure lemma and additive degreewise
  left-derived maps; none states this result.
- Loogle: `CategoryTheory.Functor.leftDerivedLift` — 6 hits for the universal lift and
  its factorization/isomorphism criteria. Its full source was read; it does not assert
  simultaneous preserving models or descent between composite derived words.
- Mathlib grep: `leftDerivedLift|leftDerived_fac_app|IsKFlat` in CategoryTheory — 7 hits
  in Derived/Adjunction and Derived/LeftDerived; no match.
- LeanSearch: "Natural transformations between finite composites of derived ringed
  pullbacks descend uniquely from ordinary transformations normalized on K-flat
  resolutions" — 8 hits concerning ordinary additive degreewise derived functors or
  `rightDerivedNatTrans_app`; no match.
- rg in both lean/WeilConjectures and lean/Sheaf for word/counit/descent/pullback and the
  item id. The existing `KInjectiveDirectImageOpenWordModel` was read as a comparison:
  its scheme-specific right-derived K-injective pushforward/open-extension words have
  different functors, representatives and counit direction. Its declarations are not
  the arbitrary-site left-derived statement here.
- Related scalar searches found the already recorded scalar presentation and pure-tensor
  helper; those are reused rather than redefined. `SuccessiveDerivedQuotientData` and
  `FiniteFreeCompletionExchangeCoherence` signatures were checked before choosing the
  latter's existing scalarTensorSection. DAG id and source-module searches found no
  existing general ringed K-flat word comparison/descent declaration.

Compilation diagnosis: implicit topology inference initially explored unrelated sheaf
composition instances and exhausted the per-file limit. Supplying `(J := X.J)` explicitly
in the reused Modules interface removed that search. The recursive counit was written
with explicit dependent indices. No limit was increased, and the only local linter option
is checkUnivs=false for Site's intentional universe-bounding bundle. Profiling options and
all scratch diagnostics have been removed. The final file is compiled through scompile.py
and then through the delivery dry run.

## Second reading by Q146

A separate second pass by the dispatched worker reread the node, all eight theorem
signatures and every concrete helper against the table above. The dispatch explicitly
forbids starting other agents; the maintainer's independent reading follows delivery.

The reread checked the direction of the normalization equation, the order of the two
word counits, the ordinary degreewise compositor, every prefix in simultaneous_resolution,
identities and both whiskerings in the finite Expression grammar, inverse cells, scalar
multiplication order, and the coefficientSequenceSite universes. It confirmed that the
existence witness of Word.cell is unique, the ordinary scalar-section helper is reused,
and no map/structure is chosen from a mere Nonempty theorem. It also checked the empty
word's canonical degreewise identity identification and the use of the actual chosen
edge universal counits. A temporary duplicate scalar-section wrapper was removed in
favor of the recorded scalarTensorSection before final compilation. Overlong lines were
wrapped, and the topology parameters were made explicit to repair elaboration cost.
No mismatch with a hypothesis or conclusion of the original node remains identified.

## Returned delivery repair

The saved packet was inspected and dry-run first: commit 5599224001a passed preflight
and per-file compilation. Its mathematical content is retained. Comparing the packet
with current live DAG found only the expected lean record and three added stmt_deps;
the delivery wrapper rebases those fields on the current live base.

1. Replaced the added theorem dependency `lem-pur-derived-change-of-rings` with the
   landed `def-sfb-derived-change-of-rings-cochain-model`, whose existing:true record
   owns exactly the unchanged `SheafOfModules.DerivedChangeOfRingsCochainModel` used here.
2. Replaced the added theorem dependency
   `lem-pur-finite-free-completion-exchange-coherence` with the new definition node
   `def-trf-scalar-tensor-section`, recording the existing helper on its unchanged module.
   This is an actual repair of the returned packet, not a reviewer FIX. Neither theorem
   contributes a proposition to the statement. No base stmt_dep is removed.

Advisory addressed: PullbackTensorResolvingComputation is now a plain proof import.
KFlatIndependentCoefficients and the universal left-derived API are public imports
for the definitions and hypotheses actually used in the signatures. No Lean declaration,
mathematical signature, original node statement, proof plan, or coefficient universe changed.

## New nodes

`def-trf-scalar-tensor-section` owns the existing public definition
`CategoryTheory.PrincipalQuotientCompletion.scalarTensorSection` in the unchanged
`Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence` module (line 71).
Its source is Stacks 03EK: send the sectionwise pure tensor into sheafification and
transport through the prescribed ordinary object equality. The model F, module M,
object U, and sections s and x correspond exactly to the five explicit Lean parameters;
the site, ring-map, sheafification and independent-derived-universe assumptions are the
existing declaration's section parameters. The output is literally `(F.E.obj M).val.obj U`.
Its real definition uses `eqToHom (F.obj_eq M).symm`, `toSheafify`, and the pure tensor.
The node introduces no model inhabitance assertion and no theorem dependency.
LeanSearch returned eight sheafification/scalar-extension hits; Loogle returned unknown
identifier; Mathlib grep returned nine sheafification-unit hits. Project grep found this
existing definition and unrelated private helpers. DAG grep found only the theorem
owner, and blueprint search returned zero matches. All search queries and actual
results are recorded in the new node; existing:true prevents a duplicate definition.

Second reading of the repair by Q146: reread the existing helper and its section binders,
the new node, both scalar theorem signatures, and the two replacement ownership records.
Both scalar normalizations still reference the exact same scalarTensorSection; only its
DAG owner changes. The model structure remains the same structure with independent
source and target derived universes. Zero rings, zero sections, identity and nonflat
ring maps require no new assumptions. The new helper node only depends on landed
definition nodes, so cannot create a cycle back to this item. No statement correction
or STATEMENT-DISPUTED flag is needed. Independent review remains the maintainer's.

Validation of the repair: scompile.py accepted the changed module against current server
sources in 47.5 seconds, with no errors or unexpected warnings. The first repaired dry
run compiled the module and existing-helper probe, then identified two combined
bracket citations in the new node that must be separate bracket citations. These
were separated, and the existing signature record starts at the parser's `def` keyword
(the source's `noncomputable` modifier remains unchanged).
