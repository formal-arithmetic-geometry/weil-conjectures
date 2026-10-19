## Worker report

The retained packet states `AlgebraicGeometry.Etale.regular_immersion_class_calculus`
in `Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus`. Its theorem has a `sorry`
proof. The appended helper theorem is
`AlgebraicGeometry.Scheme.nonempty_finiteEtaleTwistPullbackData`, in the dependency
interface described below. Source references and the DAG proof plan are retained, with
the outstanding uniqueness argument explicitly flagged below.
Every helper definition has actual data. No source-library file was edited.

The saved packet passed the initial required recovery dry run (commit cbb953e495, no push).
That mechanical pass did not address the independent return. The repairs below preserve
the accepted mathematical statement and address the returned ownership and import defects.
The changed packet is compiled and dry-run again before pushing.

Hypotheses and conclusions are represented as follows:

- A prime is `(ℓ : ℕ) (hℓ : ℓ.Prime)`. Each level is `(n : ℕ) (hn : 1 ≤ n)`.
  `regularClassCoefficients` is `ULift (ZMod (ℓ ^ n))`, the common coefficient-universe
  lift required by the existing small-etale six-functor library. Its annihilation proof
  is `regularClassAnnihilation`. This is the stated coefficient ring up to its canonical
  ring equivalence, not a different coefficient theory.
- The schemes are `Scheme.{u}`, with `[IsNoetherian Z] [IsNoetherian X]`.
  The immersion is `(i : Z ⟶ X) [IsClosedImmersion i]`. Codimension is `(c : ℕ)` and
  `IsStalkRegularClosedImmersion i c`. The new supportwise regularity predicate uses the
  kernel of the actual stalk map, `RingTheory.Sequence.IsRegular`, and a list of length c.
  Invertibility is `IsUnit ((ℓ ^ n : ℕ) : Γ(X, ⊤))`; since n is positive this is equivalent
  to invertibility of ℓ. In laws involving further schemes the corresponding invertibility
  witnesses are written explicitly; they follow by pullback of units.
- The ordinary small-etale class is
  `Ext (i_* Λ_Z(a)) (Λ_X(c+a)) (2*c)`, in `RegularImmersionClassFamily`.
  Closed direct image is exact (`SixFunctors.Finite.Exact`), so this is the supported
  derived morphism `Ri_* Λ_Z(a) → Λ_X(c+a)[2c]`. At a=0 its adjoint under the recorded
  exceptional adjunction is exactly the node's `Λ_Z → i^! Λ_X(c)[2c]`.
  This is the supported-class formulation explicitly allowed by the node, not a choice
  of a second exceptional functor. `RegularClassTensorNormalization` makes every signed
  variant the tensor of that a=0 class. Its maps are the actual adjunction unit, lax
  direct-image tensorator, and normalized multiplication of Tate lines.
- `RegularClassNormalization` identifies c=1 with the dependency's
  `SupportedKummerBoundary` for an invertible Cartier ideal. The dependency's
  `ordinary_supported_kummer` identifies this uniquely with its supported Kummer arrow
  and gives its unit composite as the positive Chern class of O(D). Thus the sign is fixed.
- The c=0 clause says that the Ext class is the degree-zero map from the supported
  constant summand whose composite with `supportedConstantUnit` is identity. For a clopen
  immersion this determines the inclusion of that summand. For the identity immersion
  it gives 1, and for empty support it gives the unique map from zero.
- `RegularClassComposition` is the specified exceptional-transitivity equality in
  supported-Hom form: precompose the canonical `lowerStarComp` identification, push the
  inner Ext class through exact closed direct image, and take its Yoneda product with
  the outer class. The twist and degree additions are displayed explicitly. The regularity
  witness for the composite is a mathematical consequence, not an extra geometric
  restriction. Iterating this equality along the Cartier flag of regular generators,
  using the c=1 and c=0 normalizations, gives exactly the local formula in the node.
  Since the same global family occurs on the left, all such flags and regular reorderings
  give the same class; arbitrary reorderings can be made regular by shrinking near Z.
- `RegularClassFlatBaseChange` quantifies over `IsPullback` squares and `[Flat v]`.
  `regularClassExchange` is built from the existing canonical `baseChangeMap` followed
  by the normalized twist comparison. The law asserts its invertibility and the Ext
  base-change square. The additional regularity and unit witnesses on the pulled-back
  pair express consequences of flat pullback. Open immersions, localizations, and strict
  localizations are included among these flat maps whenever the pairs are Noetherian.
  For localization the same supported class is read under the canonical supported-Hom
  continuity comparison, computed from the pair and its open complement. These comparisons
  occur in the proof plan; the statement uses only the flat-pullback equality. The returned
  unused continuity and supported-Hom imports have been removed.
- `RegularClassCoefficientReduction` quantifies over positive n,N with `n ≤ N`.
  `regularClassReduction` is the actual quotient ring map, conjugated by ULift's ring
  equivalence. The equation is the canonical supported coefficient square written via
  restriction of scalars. Constants are normalized on each scalar section, the roots map
  satisfies `q ≫ kernel.ι = ℓ^(N-n) • kernel.ι`, and the degree-one map is normalized on
  pure root tensors. `RegularClassReductionComparisons` requires compatibility with all
  signed multiplications. Its a,-a case preserves evaluation, hence determines the dual
  comparisons for negative twists. There is no assumption that reduction commutes
  invertibly with exceptional inverse image on arbitrary complexes.
- Existence and uniqueness of the global normalized system are expressed by `∃! classes`.
  The uniqueness expresses the node's assertion that the local formula determines the
  global canonical class; signed tensors do not add freely chosen classes.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the published
  `AlgebraicGeometry.Etale.DerivedCategoryModule` encoding, described in its module
  docstring; the current source was read with `scompile.py --source` because the older
  slopmaster2 checkout lacks this migrated file.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`: `Scheme.finiteEtaleTateLine` and
  `Scheme.finiteEtaleTateTwist`; `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback` supplies
  the signed `finiteEtaleTateSheaf` through its recorded dependency imports and the exact
  normalized theorem `etaleFiniteTwistPullback`. The present structured interface retains
  its root, signed, derived, and exponent-change clauses.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`.
- The exceptional adjunction justifies the mathematical equivalence with the node’s
  exceptional-Hom formulation. The displayed Lean uses supported Ext directly, so its
  unused `EtaleExceptionalAdjoint` import has been removed as requested.
- `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary` supplies
  `SupportedKummerBoundary` and `supportedConstantUnit`; its definition node
  `def-asd-ordinary-supported-kummer-boundary` is now explicitly in `stmt_deps`.
- `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`:
  `ordinary_supported_kummer` and the imported `SupportedKummerBoundary`, as above.
- `Sheaf.AlgebraicGeometry.StalkRegularClosedImmersion`:
  `AlgebraicGeometry.IsStalkRegularClosedImmersion`, the new definition node below.

Edge cases read explicitly: n=1, N=n, c=0, the identity immersion, empty Z, negative
Tate twists and a=0, and either codimension zero in composition. Empty Z makes the stalk
condition vacuous and the supported source zero. A proper clopen immersion at c=0 is
allowed: the old upstream predicate instead asks for length-zero generators at every
point of X, including outside Z, so it cannot be used for this edge case. No field,
regularity of X or Z as schemes, positive-codimension assumption, or boundedness is added.

Searches are retained in `searches.jsonl` from the saved attempt, not invented from the
current reading. LeanFinder queried "Etale cohomology Kummer regular immersion fundamental
class composition flat base change coefficient reduction": eight cotangent/etale-locus
hits, no class theorem. Loogle `"Gysin"` returned only an unrelated canonical-site hit.
Mathlib grep `regularImmersion|fundamentalClass|gysin|Gysin` returned three unrelated
Canonical.lean occurrences. LeanSearch's regular-immersion/Kummer query returned closed
immersion and flat-open facts, no class theorem. The new definition's LeanSearch,
LeanFinder, Loogle and grep searches are recorded in its node, including the actual hits.
Project/source searches find the upstream `IsRegularImmersion` and side
`IsRegularImmersionOfPureCodimension`, neither an exact match for the supportwise,
codimension-zero-capable predicate. The upstream supported fundamental-class declarations are restricted to smooth schemes
over a perfect field with regular source; they do not state this general Noetherian
Kummer calculus. The item-id search finds no upstream implementation.

## New nodes

`def-per-stalk-regular-closed-immersion`, module
`Sheaf.AlgebraicGeometry.StalkRegularClosedImmersion`: a closed immersion is regular of
codimension c at its support if its stalk kernel is generated by an IsRegular list of
length c at every z. Source: ILO XVI 2.3.1 and Stacks 0638. Mathlib provides its two
constituent notions only. The upstream regular-immersion definition quantifies over every
point of X and therefore excludes a proper clopen immersion at c=0. The existing side
pure-codimension definition is over a field, insists on positive codimension, and includes
a dimension condition. Neither is this notion. The three search kinds and source/side/DAG
searches are recorded in the node. No postponed proof is needed by this definition.

## Dependency modules

`lem-asd-etale-finite-twist-pullback`, module
`Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: H13/H2 repaired by retaining NJ’s live
module and `etaleFiniteTwistPullback` main declaration and signature, then appending
`FiniteEtaleTwistPullbackData`, `nonempty_finiteEtaleTwistPullbackData`, and
`finiteEtaleTwistPullbackData` to that same module. The dependency record is copied from
current main, with only `lean` extended: its module, file, declaration, statement
and date remain unchanged, its declaration list is a superset, and `lean.note` explains
why named projections are needed. The original module text is unchanged before the
appendix, including its original theorem and sorry; that theorem remains owned by its
original node. The standalone `FiniteEtaleTwistPullbackData.lean` is removed. The consumer
imports `EtaleFiniteTwistPullback` directly. The structure retains the three witnesses and
the entire original conjunction, including derived and exponent-change comparisons.
The saved probes documented repeated 60-second kernel-normalization failures on individual
choose_spec projections, motivating this interface. Its constructor choice remains fixed
by root inclusion, constant and pure-tensor normalization, signed recursion and evaluation.

## Returned-delivery repairs

- H13/H2: preserve NJ’s binding and module, extend that owning module and its declaration
  list, and remove the former standalone module. No other dependency-node field changes.
- H9: remove `ClosedSupportHom`, `IndEtaleClosedSupportBaseChange`,
  `EtaleCohomologyContinuity`, and `EtaleExceptionalAdjoint` imports from the consumer.
- Advisory dependency: add `def-asd-ordinary-supported-kummer-boundary` to the item’s
  `stmt_deps`, since its predicate and canonical constant map occur in the signature.
- Advisory uniqueness: see the explicit disputed proof obligation below. No semi-purity
  assertion about singular ambient schemes is used or claimed.

STATEMENT-DISPUTED: the `∃!` uniqueness clause needs an additional argument. ILO XVI
Definition 2.3.1 defines the global class through the conormal and modified blowup;
Corollary the project server and Definition the project server give uniqueness of the class whose blowup image is
`G(Q)`. They do not directly show that every system satisfying just the displayed
normalization, composition, flat base change and coefficient laws has that blowup image.
Nor does local equality of derived morphisms alone imply global equality on singular X.
The existing theorem statement is retained as directed; proof step 12 now explicitly
separates this remaining obligation from the proved-by-construction uniqueness and does
not present the latter as a proof of the former. This is an advisory proof gap, not an
established counterexample or a silent statement correction.

## Second reading by Q02

Recovery self-check with the node and all three modules open; the maintainer's independent
review remains the independent reading required by this dispatcher's brief. No other agent
was started. The checks matched ℓ,n,Noetherian,closed,regular,codimension and invertibility
binders to RegularImmersionClassFamily; matched the Cartier and clopen normalizations to
RegularClassNormalization; and followed the sources and targets of the composition,
flat-exchange and coefficient squares. Tensor normalization is essential: without it the
extra signed classes would be independent witnesses and Yoneda composition would not
express the node's single class and its twists. That constraint is present. The negative
comparison is fixed by evaluation, and N=n is retained. The source's Definition 2.3.1
constructs the global class and Theorem 2.3.2 gives the composition law, so the local flag
formula is a consequence of the actual asserted equations, rather than a replacement by
arbitrary local maps. The new definition's empty-support and clopen cases were checked
against the upstream all-X definition, confirming why it cannot simply be reused. The
structured dependency's full conjunction was compared with the published source theorem.
For this returned repair the second self-reading compared the appended structure laws
with the original existential conjunction and checked that the original theorem text and
record signature remain unchanged. The item’s Lean theorem signature and natural-language
statement remain unchanged. All four requested imports are absent. The missing Kummer
definition edge is present. The earlier claim that construction uniqueness proved the full
`∃!` assertion has been withdrawn and the precise remaining obligation is identified above.
No other agent was started; the maintainer provides the independent reading.

Validation after repair: the required `scompile.py` run compiled every delivered module
without errors or non-sorry warnings: StalkRegularClosedImmersion 1.7 s,
EtaleFiniteTwistPullback 13.8 s, RegularImmersionClassCalculus 42.5 s. The self-check
verified the unchanged original module prefix and original dependency binding and signature,
the exact item signature, and the 100-character line limit.

The repaired-packet dry run rejected `lean.by = NJ`: preflight requires the delivering
group Q02. Only that provenance field was updated; NJ remains credited in the original
source header. The original module binding, main declaration, signature and date are
preserved, and the helper declaration list is a superset. No other rejection was reported.
