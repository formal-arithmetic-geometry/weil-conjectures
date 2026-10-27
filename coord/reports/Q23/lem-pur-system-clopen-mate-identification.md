## Worker report

The module `Sheaf.Paper.SystemClopenMateIdentification` states the intrinsic
clopen-projector, beta, alpha, localized ordinary-arrow and proper-mate
identifications. There are three postponed theorems: `direct_eq` (the
sectionwise presentation identity needed for canonical comparisons),
`systemClopenMateIdentification`, and
`systemClopenRealizationMateIdentification`. Every proof is `sorry`;
definitions contain actual quotient sequences, adjoint comparisons,
localizations and composites. No statement correction or new DAG node is needed.
The presentation comparison helpers belong to this item's map identification,
not a replacement statement of the tensor-presentation theorem.

Hypotheses and clauses, checked against the entire node:

- The prime is `(l : ℕ) [Fact l.Prime]`. `E`, its `Field`, `Algebra ℚ_[l] E`,
  and `FiniteDimensional ℚ_[l] E` bind exactly a finite coefficient extension.
  `coefficients` is `ULift (Padic.coefficientExtensionRing l E (n+1))` and
  `transitions` is the lifted actual adjacent quotient. Thus index zero means
  exponent one, and no extra exponent-zero coefficient is introduced.
- The small-site size convention is inherited from the actual system categories:
  `Scheme.{u}`, pro-etale site objects in `u+1`, morphisms in `u`, and module
  sections in `u+1`. The first theorem follows the recorded SystemTensorMate
  interface with `E : Type (u+1)`; the realization theorem follows its recorded
  `E : Type u` convention. No equality of object and morphism universes is imposed.
- Strict systems, semilinear transitions and componentwise morphisms are exactly
  `SystemTensorMate.S` and `VaryingRing.Modules`, not a private category. Their
  `D`/`Derived` are the ordinary unbounded categories. An `o : Operations` is a
  universal presentation already supplied by the dependency, not arbitrary maps.
- `F : FiniteFieldDatum` includes the finite base field and chosen algebraic
  closure. `_hl : l ≠ F.p` is the characteristic condition. Each scheme has
  an `Over (Spec (.of F.k))` structure; `LocallyOfFiniteType` and `QuasiCompact`
  on its structure morphism give finite type, and `IsSeparated` gives separatedness.
  All four arrows have `IsOver` instances over that same base.
- The node's k₁,r,p₁,i are named k,r,p,i. The open-immersion and quasi-compact
  instances on k,i, properness instances on r,p, and `h : k ≫ p = r ≫ i`
  are explicit. There is no `IsPullback` assumption on this square.
- `pullback p i`, `pullback.fst`, `pullback.snd`, and
  `StrictTower.squareLift k r p i h` are precisely B_C,b,q,s. Clopenness is
  supplied by the recorded geometric lift; it is not an added hypothesis.
- `rho` localizes `VaryingRing.modulePi`, the ordinary identity/zero projector,
  and inserts the standard identity and composition factorizations. The first
  conjunct identifies it with `SemilinearProperOpen.pi`.
- The second conjunct identifies the exact localization of ordinary
  `VaryingRing.moduleBeta` with `SemilinearProperOpen.beta` at the canonical
  cartesian square B_C. This is the beta of the open-unit normalization.
- The third conjunct identifies `VaryingRing.alpha` with
  `SemilinearProperOpen.alpha`. The former is localization of the actual
  ordinary beta/projector/compositor word; the latter is its derived word.
  Both imported definitions use the canonical open compositor, pullback
  compositor, `pullback.lift_fst`, and `pullback.lift_snd`, with no free
  composition identifications.
- `direct_eq` states equality of the two sectionwise direct images; its proof
  plan compares the coefficient maps by constant-section sheafification
  uniqueness. `ordinaryPullComparison` and `ordinaryOpenComparison` are
  `leftAdjointUniq` isomorphisms retaining the adjunction normalizations.
  `pullComparison` and `openComparison` are their exact localizations.
  Thus `a` is the actual clopen word in the diagram-arrow coordinates.
- The fourth conjunct is exactly `o.alpha k r p i h = a l E o k r p i h`.
  The imported `o.alpha` localizes the unique ordinary arrow specified by
  the node's open-unit restriction condition; this does not introduce an
  extra uniqueness assumption or replace that arrow with an arbitrary map.
- The fifth conjunct is the requested unit--a--counit formula for `o.gamma`:
  `(o.derivedAdj p).unit`, then `pushDerived p` of `a` at `pushDerived r M`,
  then `pushDerived p` of `o.J k` of `(o.derivedAdj r).counit`.
  The components are universally quantified over the entire derived category.
- The realization theorem explicitly names `z.properOpen.gamma`, exactly
  the Gamma of `properOpenProjectionMateSystems`. Its first conjunct equates
  that natural transformation to `mateEquiv` of the actual clopen word
  `AmbientClopen.realizationAlpha`; the second displays the same
  unit--a--counit formula. That existing alpha uses only `z.canonicalBridge`.
- `o.ordinarySquare`/`o.square` and the imported clopen-word compositors are
  induced by h and the specified pullback compositions. No independent
  square comparison is supplied. `HEq` is used only for the published
  presentations of the same canonical functors, as in the ambient dependency;
  `o.alpha = a` and the realization mate equality are homogeneous equalities.
- All maps are on whole unbounded systems. No evaluation, inverse limit,
  normalization/cartesianness, faithful functor, boundedness or invertibility
  of the proper mate occurs among the hypotheses.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`; its imported coefficient module's
  `coefficientExtensionRing`, `coefficientExtensionTransition`, integer ring
  and chosen uniformizer. These are the original coefficient objects.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`, `Scheme.ProEt` and its topology.
  `def-weil-size-convention` is a convention node with no declaration;
  `def-weil-scheme-morphism-properties` is also a catalogue/convention, so
  actual Mathlib proper, open, separated and finite-type predicates are used.
- `Sheaf.Paper.SemilinearDerivedSections`,
  `WeilConjectures.SemilinearSections.semilinearDerivedSections`, `Systems`,
  `DS`, and the actual module/derived calculus imported by the concrete APIs.
- `Sheaf.Paper.SystemTensorMateArrows`, `SystemTensorMate.Operations`,
  `S`, `D`, `direct`, `Operations.ordinarySquare`, `ordinaryAlpha`, `alpha`,
  `gamma`, `P`, `J`, `derivedAdj`, `ordinaryOpenUnitInv`, and `alpha_existsUnique`.
- `Sheaf.SixFunctors.OpenTensorNormalization`,
  `SheafOfModules.openTensorNormalization` and exact derived open adjunctions.
- `Sheaf.SixFunctors.ProperOpenProjectionMate`,
  `IntegralSystemRealization.properOpenProjectionMateSystems`, whose Gamma is
  the exact `z.properOpen.gamma` named in the new theorem.
- `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`,
  `StrictTower.normalizedProperOpenCalculus` and its imported
  `squareLift`, `squareLift_clopen`, with both projections.
- `Sheaf.SixFunctors.AmbientExactClopenComparison`, `AmbientClopen.localize`,
  `localizeSquare`, `Systems.Assertion`, `realizationAlpha`, and
  `ambientExactClopenComparisonLocalizes`.
- `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`,
  `SemilinearProperOpen.pi`, `beta`, `alpha`, `gamma`, and
  `semilinearProperOpenMatePasting`.
- `Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows`, the existing
  `modulePi`, `moduleBeta`, `moduleAlpha`, `alpha` and canonical adjunctions.
- `Mathlib.CategoryTheory.Adjunction.Mates`, `CategoryTheory.mateEquiv`;
  read its full signature and unit/counit implementation.

The proof dependency `lem-pur-system-tensor-presentation-identification`
currently has no Lean record or Mathlib match. It is not needed to type this
statement: this delivery constructs only the sectionwise/adjoint comparisons
needed by the clopen map, on the already published categories. Its future
module is therefore not imported; the proof plan cites it. No missing
independent mathematical notion is hidden in a hypothesis.

Sources read: local `more-etale.tex`, lemma-shriek-proper-and-open (0F7B),
and `sites-cohomology.tex`, remark-base-change (07A7). They give the map context;
the system identification and its four-step argument are the agent-formulated
DAG statement. Read `coord/pefw-upstream-framework.md` and the live
SystemTensorMateArrows source using `scompile.py --source` as well.

Edge cases checked: empty A and its empty clopen component give the zero map;
empty complementary open gives identity projector; a cartesian square gives
s an isomorphism and recovers beta; r=identity gives a clopen refinement
section. Zero systems, nonflat adjacent quotients, identity opens and arbitrary
doubly unbounded complexes are allowed. No nonempty-index assumption or
finite-evaluation equality test is present. No STATEMENT-DISPUTED fault found.

Searches (also in the wrapper's searches.jsonl):

- LeanFinder: “Clopen projector on strict semilinear sheaf systems agrees with
  quotient diagram and proper adjunction mate”: eight hits including
  SheafOfModules.Presentation.map_π_eq and locally constant sheaf counits,
  no exact identification theorem.
- Loogle: `CategoryTheory.mateEquiv`: twelve hits, the generic mate API is
  reused; none identifies these specified system presentations.
- Mathlib grep via msearch: `clopen.*(mate|projection)|proper.*open.*(mate|compar)`
  under CategoryTheory: zero hits.
- LeanSearch: “Identify clopen projection on strict semilinear module systems
  with localized open restriction arrow and proper adjunction mate”: eight
  topology and linear-projection hits; no system-map identification.
- rg of both project Lean roots for the blueprint id and clopen/identification
  patterns: no declaration for this item. The nearby ambient localization
  theorem provides most of the intrinsic system word and is reused.
- Full new declaration names checked in Sheaf, WeilConjectures and
  dag/lean_names_upstream.json: no matches.

Validation: scompile.py compiled the final module in sandbox and library mode,
with no errors or non-sorry warnings (10 seconds per mode).

## Second reading by Q23

I reopened the complete node and the final module after compilation, and checked
the correspondence above. This is a self-review: the dispatcher explicitly
forbids starting other agents, so no independent worker was invented. The
maintainer's delivery review remains independent.

The second pass found that the first draft's diagram-arrow formula alone did
not name the Gamma actually used by the system projection-mate theorem. Added
`systemClopenRealizationMateIdentification`, naming `z.properOpen.gamma`
and both its equality to the natural-transformation mate and its explicit
component formula. Retained all four schemes' separatedness and finite-type
hypotheses, the common finite-field base and IsOver instances. Checked the
projector localization includes identity and composition factorizations,
that the beta square uses the flipped canonical pullback orientation,
and that the clopen alpha imports use precisely bs=k and qs=r. The coordinate
comparisons are adjoint-normalized and do not postulate arbitrary equivalences.
