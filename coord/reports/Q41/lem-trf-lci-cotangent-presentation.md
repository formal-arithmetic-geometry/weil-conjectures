## Worker report

The delivery states `AlgebraicGeometry.CotangentPresentation.exists_lciCotangentPresentation`.
It constructs a sectionwise standard-polynomial-resolution model for the intrinsic
cotangent complex and states the affine, lci, Tor-independent base-change and smooth
comparisons, with a specified family of global lci identifications.
The only postponed proof is this theorem; its docstring contains all ten
steps of the node's proof and names their supporting DAG nodes. All definitions have
actual data. In particular the intrinsic object is the module sheafification of the
specified standard differential complex, and derived change uses the published derived
pullback counit followed by the normalized chain map.

`System` is a dependent product with six named projections for the construction data; `Properties.laws : SystemLaws D` records
their generator normalizations. Separating the proof laws from the data avoids
expensive automatic constructor lemmas without changing the assertion.
`tildeComplexFunctor` directly applies the existing tilde functor to complexes
in the shared codomain; its existing additive instance is inferred. It supplies
no new mathematical operation.

The original statement is unchanged. The additional statement dependencies are existing
landed interfaces used to express its constructions. `C : Coherence` and
`κ : Naive.Comparison C` are the existing, fully normalized polynomial-resolution and
naïve-projection constructions. They are representation parameters, not additional
geometric hypotheses. The conclusion provides the scheme-level realization for every
such choice. It does not postulate a cotangent object or arbitrary base-change map as
a geometric hypothesis.

Clause-by-clause reading:

- Every scheme morphism: `System.model` quantifies over arbitrary `X S : Scheme.{u}`
  and `f : X ⟶ S`. There is no finiteness, separation, characteristic, flatness or
  smoothness hypothesis on this construction.
- Intrinsic ringed-space cotangent complex: `SchemeModel C f` uses the actual sheaf
  map `Scheme.Modules.tensorPullbackRingMap f : f⁻¹ O_S ⟶ O_X`.
  `SectionModel.sectionIso` identifies the presheaf complex on every open with
  `differentialComplex (C.differentials (C.standard ...))`; its `restriction` field
  fixes every restriction using the functorial standard map. `sheafComplex` is actual
  module sheafification, and `cotangent` applies `DerivedCategory.Q`. The alternating
  nonpositive model represents the normalized model via the existing Dold–Kan
  homotopy equivalence, explicitly cited in the proof. `Properties.nonpositive`
  records the requested nonpositive convention.
- Affine comparison maps: `SystemLaws.chartSquare_left/right` specify the ring square by
  the inverse-image adjunction unit and the identity coefficient map.
  `SystemLaws.affine_formula` fixes the chain comparison on all standard differential
  tensors, and `AffineIdentifications.iso/hom` asserts its invertibility in the
  derived category. Compatibility on smaller affine opens is encoded by the same
  section formulas together with `SectionModel.restriction`, rather than by a family
  of unrelated affine isomorphisms.
- Open `U` and factorization through a closed immersion into an open of affine
  n-space: `Properties.lci` uses arbitrary `i : U ⟶ P`, `p : P ⟶ S` and
  `T : LciPresentation i p`. Its fields `dimension`, `ambient`, `closed`,
  `open_immersion`, `structure_map` and `koszul` bundle exactly the original
  `n`, `j`, closed/open immersion hypotheses, structure-map equality and
  locally Koszul-regular ideal hypothesis. Applying this universally quantified
  assertion to an open restriction of the original morphism gives precisely the
  node's local statement. `Properties.restriction` identifies the resulting
  intrinsic complex with the pullback of the original one along that open.
- Locally finite Koszul-regular ideal: `IsKoszulImmersion i` means that around each
  point of `U` some affine ambient open has a finite `Fin r` sequence, satisfying
  the recorded `RingTheory.Sequence.IsKoszulRegular` and generating the actual
  kernel ideal. There is no fixed global rank or a strengthened regular-sequence
  predicate.
- The displayed two-term complex: `ConormalModel.negative` is the actual pullback of
  `i.ker.toModules`, hence `I/I²`, and `zero` is `i^* Ω¹_{P/S}`;
  `other` makes all other terms zero. `differential` sends each pulled-back ideal
  section to its universal differential. Thus this specifies the conormal map,
  not only the isomorphism classes of its two terms.
- Canonical derived isomorphism: `LciIdentification.iso` is
  `Q(model.complex) ≅ cotangent (D.model (i ≫ p))`. `ImmersionChart` retains the
  actual ambient coordinate ring and maps. `ConormalChartIso` specifies the
  affine conormal and differential identifications on pure sections;
  `LciIdentification.normalization` makes the inverse derived isomorphism equal
  to the existing normalized naïve projection for every lift. Consequently the
  affine comparison has the required normalized formula. Global coherence is
  asserted for `E : LciIdentifications D F κ`, supplied existentially by the
  theorem; affine normalization alone is not claimed to characterize a unique
  global derived isomorphism.
- Both terms finite locally free and Tor amplitude `[-1,0]`: `Properties.lci`
  asserts for `(E.identification i p T).model` the predicate
  `IsFiniteLocallyFree` in degree -1, rank `T.dimension` in degree 0, and vanishing
  of the homology of its derived tensor with every module in every degree outside
  `[-1,0]`. Together with the actual two-term representative this is the requested
  perfectness. `tensorModule` only applies the existing
  `schemeDerivedTensorMonoidal`; it introduces no second derived tensor product.
- Natural comparison for base change: `BaseSquare` fixes the canonical map of
  inverse-image base sheaves by its adjunction-unit formula on all smaller opens.
  `SystemLaws.change_formula` specifies the ordinary chain map in every degree on
  pullback sections. `derivedChange` is the recorded derived-to-ordinary counit
  followed by this map. `System.square` supplies it for every commuting square.
- Cartesian and Tor-independent hypotheses: `Properties.baseChange` has exactly
  `IsPullback g f' f h` and `PullbackStalkTensor.IsTorIndependent f h`, and
  concludes `IsIso (derivedChange D q)`. No flatness or lci hypothesis is substituted.
- Identity and composition: `Properties.identity` identifies the chain map with
  the recorded section-normalized identity pullback; `Properties.composition`
  gives equality of the derived composites using the published recorded
  composition isomorphism, for all composable squares.
- Conormal base change: `Properties.lci_baseChange` records Koszul regularity after
  a Tor-independent Cartesian base change. `ConormalChange.negative/zero` fix the
  comparison on actual ideal sections and universal differentials; common-open
  restrictions avoid any assumed definitional equality between inverse-image
  opens. `Properties.conormal_baseChange` states the commuting derived square
  between the conormal models in the specified family `E` and `derivedChange`,
  for arbitrary source and target `LciPresentation` records. It does not
  quantify over arbitrary `LciIdentification` records.
- Smooth specialization: `SystemLaws.augmentation_formula` fixes the augmentation by
  `b dx ↦ b dε(x)` into the existing `f.relativeDifferentials` in degree zero.
  `Properties.smooth` asserts that its image under `DerivedCategory.Q` is an
  isomorphism whenever `Smooth f`. This includes the canonical arrow and all
  cohomological degrees, not merely a degree-zero isomorphism.

Dependency declarations used (their complete signatures and docstrings were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory` and `moduleRings`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, via the recorded
  polynomial-resolution differential complexes and relative differential sheaf.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `WeilConjectures.RingTheory.KoszulRegularSequence`:
  `RingTheory.Sequence.IsKoszulRegular`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSection`,
  `tensorPullbackSectionAdjunction`, `tensorPullbackSectionId`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree`, `IsFiniteLocallyFreeOfRank`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Algebra.CotangentResolution.Coherence`, `differentialComplex`,
  `complexGenerator`, `Coherence.standardMap` and `Coherence.differentialMap`.
- `Sheaf.RingTheory.NaiveCotangentComparison`:
  `Algebra.CotangentResolution.Naive.Presentation`, `Comparison`, `complex`,
  `conormalIso`, `differentialsIso`, `kernelClass`, `tensorGenerator`,
  `standardPresentation` and `Comparison.projection`.
- `WeilConjectures.AlgebraicGeometry.DerivedPullback` and
  `DerivedPullbackRecordedComposition`: `derivedPullback`,
  `recordedDerivedPullbackCounit`, `recordedDerivedPullbackComposition`.
- `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`:
  `schemeDerivedTensorMonoidal`.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsDerivation`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`:
  `Scheme.IdealSheafData.toModules`, `toModulesι`, and `Scheme.Hom.ker`.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace` and its structure map.
- `WeilConjectures.AlgebraicGeometry.PullbackStalkTensorComparison`:
  `PullbackStalkTensor.IsTorIndependent`.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `tilde.functor`, `tilde.toOpen`.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification`, `sheafificationAdjunction`.

The modules of the already stated proof dependencies are imported as proof imports.
The affine intrinsic cotangent comparison is a proof dependency without a recorded
standalone declaration; its construction is one of the clauses stated here, with the
proof step retaining that node reference. This does not assume a missing cotangent
object or wait on a downstream theorem.

Edge cases checked before and during drafting: empty schemes and opens (all local
assertions are pointwise or universal); `n = 0` and the empty equation sequence;
zero rings/empty affine spectra; varying conormal ranks; characteristic arbitrary;
nonflat base changes (only Tor independence is used); an arbitrary module rather
than only quasicoherent or flat test modules in the Tor-amplitude assertion; identity
and composable changes; and distinct object/derived localization universe levels.
All universe variables and implicit scheme/morphism variables are explicitly bound.

Searches actually run:

1. `msearch.py ... leanfinder` with
   `intrinsic scheme cotangent complex local complete intersection conormal model Tor independent base change smooth`:
   eight results, about smooth loci, smooth algebras and low-degree naïve cotangent
   modules; none states the intrinsic scheme theorem.
2. `msearch.py ... loogle` with
   `Algebra.CotangentComplex, AlgebraicGeometry.cotangentComplex`:
   no result; `Algebra.CotangentComplex` is unknown.
3. `msearch.py ... grep` with `cotangentComplex|CotangentComplex` in
   `AlgebraicGeometry`: no Mathlib match.
4. `rg` in the project's `lean/WeilConjectures` and `lean/Sheaf` for cotangent
   declarations: found the recorded ring resolution, naïve comparison and ring
   specialization modules; no intrinsic scheme construction or this theorem.
   The required item-id search in `lean/WeilConjectures` found no declaration.
5. Read Stacks `cotangent.tex` at Tags 08T2, 08T3, 08SJ, 08SL, 08QQ and 08R5,
   and the node's complete proof. The source agrees with the statement.

No statement correction or dependency-interface repair is needed. The two existing
definition interfaces now have explicit definition nodes, as detailed below.
No `STATEMENT-DISPUTED` issue was found.

## Second reading by Q41

The dispatcher explicitly forbids starting other agents. This section records a
second manual reading by this worker, not an invented independent review. The
maintainer's independent delivery review remains required.

Re-read the node alongside the Lean: the comparisons are specified on actual
standard-resolution tensors and actual ideal/differential sections; all displayed
complex identifications are derived-category isomorphisms; the local equations
have the recorded Koszul-regular predicate; and no geometric hypotheses have been
added. During this reading I made the derived localization universe explicit on
all `Q`, single-object and homology functors, retained the original arbitrary
module Tor-amplitude test, and included preservation of the lci presentation
under Tor-independent base change. Compilation and preflight results follow below.

## Validation

For the earlier H2 packet, the prescribed
`scompile.py Q41 lem-trf-lci-cotangent-presentation` clean compile
passed both the sandbox and actual module-name checks, in 53.8 s and 54.2 s,
respectively, under the unchanged 60-second limit. There were no errors or warnings.
The delivered file has no compiler probes or profiling options, no lines over 100
characters, and exactly the main theorem's one expected `sorry`.

## Repair of returned head 9d4b939d1193 (H2)

The initial saved-packet dry run passed at 9bdc5e0cce3, but the ownership defect
identified by the independent reader remained. The packet now replaces the added
statement dependencies `lem-trf-cotangent-resolution-coherence` and
`lem-trf-lci-naive-cotangent-model` with the two definition nodes below.
Those two theorems remain proof dependencies, where their existence conclusions
are needed for the proof plan. Neither `exists_coherence` nor `exists_comparison`
is chosen in the statement. The genuine dependency
`lem-pc-recorded-pullback-composition` is retained: its canonical isomorphism uses
the recorded theorem via `asIso`.

At the earlier H2 repair, the Lean file was byte-identical to that saved packet.
The later H3/H6 repair below changes that file and its recorded signature. The mathematical
statement, ten proof steps, every normalization and all geometric hypotheses
are retained. Only definition ownership and its dependency records are repaired.

## New nodes

`def-trf-cotangent-resolution-data` registers `existing: true` on
`Sheaf.RingTheory.CotangentResolutionCoherence`, principally
`Algebra.CotangentResolution.Coherence`. It owns the existing augmented-resolution,
standard-term, differential-model, complex and generator definitions, including
`Coherence.standardMap` and `Coherence.differentialMap`. Its statement describes
the data and their laws, without asserting existence. Source: Stacks Cotangent
Complex, Tags 08PM, 08PN, 08QI, 08QL. Read the entire existing module and checked
the standard terms, tensor generators, ring-square formulas and comparisons.
LeanSearch and LeanFinder query:
`standard simplicial polynomial resolution cotangent differential complex coherence data`;
each returned eight related declarations, none this interface. Mathlib grep
`CotangentResolution|differentialComplex|complexGenerator` returned no matches.
Project and DAG searches found the definitions only in the existing theorem-owned
module, with no definition node; `blueprint_refs.py search cotangent` found two
blueprint nodes, neither owning this interface. No Lean definition is duplicated.

`def-trf-naive-cotangent-comparison-data` registers `existing: true` on
`Sheaf.RingTheory.NaiveCotangentComparison`, principally
`Algebra.CotangentResolution.Naive.Comparison`. It owns `Presentation`,
`IsLocalizedPolynomial`, `PresentationMap`, `standardPresentation`, `complex`,
`conormalIso`, `differentialsIso`, `kernelClass`, `tensorGenerator` and
`Comparison.projection`, together with the supporting definitions. Its statement
describes the actual two-term complex and normalized comparison data for a given
coherence datum, without an existence assertion. Source: Stacks Cotangent Complex,
Tags 08RB/08UP, Algebra 00S1/00S7, and localization 08SF. Read the entire module,
including the degree-minus-one projection formula and good-truncation factorization.
LeanSearch and LeanFinder query:
`naive cotangent complex presentation conormal differential comparison projection`;
each returned eight related Mathlib declarations, none this full interface.
Mathlib grep `Naive.*Comparison|conormalIso|standardPresentation` returned no hits.
The project and DAG searches found the existing module and its theorem node but
no definition node. This node cites the first definition node. All actual search
results are preserved in the new nodes' `mathlib_searches`.

## Second reading by Q41 — repair self-check

Re-read both complete dependency modules, both new node statements, and the main
node against its retained module. `C : Coherence` and `κ : Naive.Comparison C`
are binders for defined data, rather than choices from the existence theorems.
`ringComplex`, `SectionModel.restriction`, the affine/change generator formulas
and `LciIdentification.normalization` use precisely the definitions now owned
by the new nodes. The new coherence statement includes every standard-map and
comparison law. The new naive statement includes both generator formulas,
all lift quantifiers, good truncation and naturality with scalar restriction.
Arbitrary and empty variable sets, arbitrary localization submonoids, zero rings,
all commutative ring squares and universe u are preserved. No finiteness or
regularity hypothesis was added to these definition interfaces.

Rechecked `Properties`: restriction, identities, derived composition, Cartesian
Tor-independent base change, smooth augmentation, the lci two-term model with
varying local conormal rank, amplitude for every module and conormal base change
retain the clause-by-clause mapping above. The lci isomorphism is normalized
chartwise by `κ.projection` for every lift, as the independent review observed.
This is a self-check; no separate agent or fictitious independent reading was used.


## Repair of returned head 5b643677a408 (H3/H6)

The saved packet was inspected first and its prescribed dry run passed at
`29160d334d6`. That mechanical pass did not repair the independent mathematical
finding. The returned counterexample is accepted: on the non-affine hypersurface
`U = V(z²)` in `(A² ∖ {0}) × A¹`, a nonzero globally derived morphism can restrict
to zero on every affine chart. Thus `φ` and `φ(1+e)` can satisfy the same affine
normalization. The former universal quantification over both in the identity
base-change square would force them equal. No uniqueness is now inferred from
these affine restrictions.

The requested second repair option is implemented. `LciPresentation i p` bundles
exactly the original local geometric hypotheses: dimension and open embedding
into the corresponding relative affine space, closed immersion, structure-map
equality and locally Koszul-regular ideal. It is a helper for this node's existing
presentation notion, not a new independent definition. `LciIdentifications D F κ`
contains `identification i p T : LciIdentification D F κ i p` for every such
presentation. The main conclusion is now

```
∃ (D : System C) (F : AffineIdentifications D) (E : LciIdentifications D F κ),
  Properties D F κ E
```

`Properties.lci` asserts finite local freeness and Tor amplitude for exactly the
model selected by `E.identification i p T`. `Properties.conormal_baseChange`
uses exactly `E.identification i p T` and `E.identification i' p' T'`, and retains
the same canonical conormal chain map, pullback counit and `derivedChange` square.
The source/target `T,T'` express that these are the lci conormal models named in
the node. The other base-change, restriction, identity, composition and smooth
clauses have unchanged mathematical content. Koszul regularity after base change remains the unchanged
`Properties.lci_baseChange` assertion. Consequently this implements one coherent
family simultaneously; it neither assumes a family as a hypothesis nor claims
compatibility for every locally normalized global isomorphism.

The original mathematical node statement remains correct and unchanged: its
canonical natural comparisons mean a specified compatible construction, not all
possible global derived maps with identical affine restrictions. Hence this is
a Lean H3/H6 quantifier repair, not a source-statement correction. The accepted
H2 definition nodes and the recorded pullback-composition dependency are retained.
The two helper structures are added to `lean.declarations`;
the theorem signature is copied verbatim into `lean.statement`.

Read again the cited Stacks source at Tags 08T3, 08SJ, 08SL and 08QQ and the full
Lean definitions of `LciIdentification`, `ConormalChange` and `Properties`.
The source's comparisons are natural constructions. The proof docstring now
explicitly constructs the globally coherent family using the global naive
comparison, rather than claiming that equality of derived maps glues from
affine equalities. There remains exactly one `sorry`, the main theorem.

Additional searches for the helper names `LciPresentation|LciIdentifications`
in live `lean/Sheaf`, `lean/WeilConjectures` and Mathlib's `AlgebraicGeometry`
returned no matches. Comparison with the current read-clone node confirms that
only the authorized existing `stmt_deps` addition and the `lean` record differ;
all statement, proof and maintainer metadata are retained. The delivery wrapper
rebases the packet against the live server branch during each dry run.

## Second reading by Q41 — H3/H6 repair self-check

Re-read the retained node and the revised theorem with every new field open.
For any original `(n,j)` and its four geometric hypotheses, there is exactly the
corresponding `LciPresentation` datum; conversely its fields recover all four.
Empty schemes, dimension zero, empty equation sequences, variable conormal ranks,
non-affine ambient opens and nonflat Tor-independent changes remain permitted.
The chosen model's Tor test still ranges over every module and every integer
outside `[-1,0]`, with the same explicit universe parameters.

The non-affine counterexample no longer instantiates two free `N,N'` binders:
there are no such binders in the compatibility clause. An identity change compares
the single family supplied in the existential conclusion. Different geometric
presentations are still compared within this same family. `ConormalChange` still
fixes both degree maps on actual ideal and differential sections, so this repair
does not replace the comparison by an arbitrary morphism. Both new structures
contain real fields and no `sorry`; no extra theorem or axiom was introduced.

A compile-cost repair keeps the same five `SystemLaws` fields but factors their
formulas verbatim into `ChartSquareLeftLaw`, `ChartSquareRightLaw`, `AffineFormula`,
`AugmentationFormula` and `ChangeFormula`. These are definitions of the original
normalization equations, not additional assumptions or lemmas. The profiler
identified about 14 seconds in kernel checking of the former expanded bundle;
the compact fields avoid rechecking those expanded formulas there. All five
predicates have source/blueprint docstrings and are recorded in `lean.declarations`.
Temporary profiler options are removed from the delivered module.
No second agent was started, as instructed. Maintainer independent review remains
required.

The tilde wrapper was also simplified to
`(tilde.functor R).mapHomologicalComplex (.up ℤ)`, with the identical declared
source and target categories. This removes the previous local functor/additive
rebinding and the expensive generated conversion proofs; it is the same existing
Mathlib functor applied to complexes. The scoped profiling probe also exposed
a diagnostic-only parser placement issue, which was removed with all profiler
options before final validation.


## Final H3/H6 validation

The final `scompile.py Q41 lem-trf-lci-cotangent-presentation` run passed cleanly
on 2026-10-22: sandbox module 47.6 seconds, actual library module 49.1 seconds,
under the unchanged 60-second limit, nice 19 and two threads. There were no errors
or warnings. The final self-check confirms the recorded theorem signature is
verbatim, all Lean lines are at most 100 characters, every variable/universe is
explicit, the file has exactly the main theorem's one `sorry`, no arbitrary
`N,N' : LciIdentification` binders remain in compatibility, and no profiler or
compiler probes remain. The H2 definition-node ownership repair is retained.

The first repaired-packet dry run rejected an explicitly listed generated structure
projection, `LciIdentifications.identification`, because its declaration scanner
recognizes explicit declarations. Removed that generated projection from the list;
its owning structure remains recorded, as for the other structure projections.
No Lean code changed after the clean compile.
