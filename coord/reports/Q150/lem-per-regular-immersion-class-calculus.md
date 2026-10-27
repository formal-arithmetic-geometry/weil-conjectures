## Worker report

The delivery states `AlgebraicGeometry.Etale.regular_immersion_class_calculus` in
`Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus`. Its only theorem proof is
`sorry`. Three new definition nodes supply the supported operations, class-system
predicate and local-continuity predicate needed to state it. Their data and maps
are explicit constructions from the published library. The theorem asserts the
existence of one simultaneous globally constructed class family, together with
supported continuity; there is no definition choosing data from this existence
statement.

The current base has the independently reviewed 12-step split of 2026-10-24.
The maintenance Q26 four-input decision is respected: its statement, source,
proof, proof dependencies and blueprint provenance are preserved verbatim.
All ten original statement dependencies are retained, with the three missing
interfaces added under stage-2 §1(A). The four Q26 construction inputs remain
unsplit and have no usable Lean attachment, so none is imported through the
withdrawn RegularFlagBlowupGeometry module. The theorem's docstring contains
all twelve current proof steps, with their actual cited node identifiers.
No historical proof graph, SGA route or adic purity route is used. This is the
stage-2 handoff, not a new stage-1 split or a proof of any Q26 input.

Hypothesis and clause correspondence:

| Node | Lean rendering |
| --- | --- |
| Prime ell | `(ell : ℕ) (h : ell.Prime)` on the theorem. |
| Every n >= 1 | `RegularClassFamily` quantifies `(n : ℕ) (_hn : 0 < n)` simultaneously. |
| Lambda_n = Z/ell^n | `regularClassCoefficient ell n = ULift (ZMod (ell ^ n))`; the lift only sets the module universe. `regularClassAnnihilator` transports the existing ZMod annihilation equality. |
| Noetherian schemes | `[IsNoetherian Z] [IsNoetherian X]` on every family member and every comparison pair. There is no field, regular-ambient, excellence, separatedness or finite-type assumption. |
| ell invertible | `_hX : IsUnit (ell : Γ(X, ⊤))`; the exponent helper transports the existing `IsUnit.pow` across `Nat.cast_pow`. In comparisons the extra displayed unit proofs on sources are pullbacks of this proof, not additional mathematical restrictions. |
| Regular closed immersion | `[IsClosedImmersion i]` and the existing `IsStalkRegularClosedImmersion i c`; on Noetherian schemes this is the local regular-sequence condition. The existing Mathlib `RingTheory.Sequence.IsRegular` remains in that definition. |
| Locally of codimension c >= 0 | `(c : ℕ)` on each constant-codimension part. As in the node's proof Step 1, different codimension components use their respective c. No positivity of c is imposed. |
| Ordinary small-etale categories and finite twists | `Ext` in `Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A)`, using `Scheme.finiteEtaleTateSheaf`, and `DerivedCategory.singleFunctor`. No pro-etale comparison is substituted. |
| Supported class / exceptional transpose | `RegularSupportedClass A m hA i c` is precisely `Ext (i_* A_Z) (A_X(c)) (2*c)`. `regularClassRealization` uses the actual exact-closed-direct-image comparison to give `Ri_* A_Z -> A_X(c)[2c]`. Transposition under the imported compact-support right adjoint gives the eta in the node. This is the explicitly permitted supported-class formulation. |
| Regular-generator Cartier flag | `RegularClassTransitivity` applies to every regular flag, with `RegularClassNormalization` fixing each codimension-one factor as `SupportedKummerBoundary`. Induction along the successive quotients V(t_1,...,t_k) gives exactly the displayed Kummer composite. This is a consequence of the stated two laws, rather than a separately assumed flag formula. No regularity of intermediate ambient schemes is required. |
| Independence of generators/order | Every such flag composite equals the same family member `g n hn i c hi hX` by transitivity. Thus changing a regular generating sequence or a regular order gives equal classes. The family is constructed globally in proof Step 1, not glued from equality of derived maps on charts. |
| Cartier sign +c1(O(D)) | The codimension-one clause requires the existing `SupportedKummerBoundary` predicate. `ordinary_supported_kummer` identifies its unique class with the existing Cartier Kummer morphism and gives its unit composite with the positively normalized first Chern class. |
| Codimension zero and identity | The first normalization equation is `gamma.comp (Ext.mk₀ supportedConstantUnit) = Ext.mk₀ (𝟙 _)`. In diagrammatic order it is gamma followed by the restriction unit: identity on the supported summand. For an open-and-closed immersion this characterizes the summand inclusion; its exceptional transpose is restriction. For identity it is 1. The equation is deliberately not identity on the whole ambient constant sheaf. |
| Composition eta_ji = i!(eta_j)(a)[2a] o eta_i | `RegularClassComposition` specifies the canonical nested supported product through the actual `rightDerivedLowerStarProjectionMap`, normalized Tate multiplication, exact pullback comparison, and `rightDerivedLowerStarComp`. Its intermediate delta is constrained on its whole domain by that projection square, whose comparison is invertible here (closed proper pushforward and Tate line). `RegularClassTransitivity` equates this composition to the family member for i >> j. Transposing the two supported maps gives exactly the exceptional formula. The explicit composite-regularity proof parameter is derivable by concatenating local regular sequences, as in proof Step 3. |
| Flat base change and open restriction | `RegularClassFlatCompatibility`, with `[Flat v]` and `IsPullback w i' i v`, uses `RegularClassPullback`. The latter is an alias of the actual restriction equation with the canonical `supportedConstantExchange` and `t.c`. Open immersions are included as flat morphisms. Explicit pulled-regularity and invertibility proofs are conclusions of the supplied geometric hypotheses. |
| Localization/strict localization | These structural maps are flat, so the same class equation applies to their Noetherian base-changed pairs. `IsRegularClassLocalLimit` explicitly identifies the permitted localization or published strict-localization morphism, up to the indicated scheme isomorphisms. |
| Canonical supported continuity | `RegularClassLocalContinuity` quantifies affine ind-etale diagrams of Cartesian closed Noetherian pairs and Noetherian limiting pair, restricting the limit projection by `IsRegularClassLocalLimit`. In every signed twist and nonnegative degree its first conjunct is class descent and its second is eventual killing of a kernel element. Both use `RegularSupportedRestriction`, the same canonical exchange equation as class compatibility. Thus the continuity identification takes the compatible stage fundamental classes to the limiting class. The index is `J : Type u`, with `SmallCategory` and `IsCofiltered`, and j₀ ensures a stage is specified. No general non-Noetherian limit or exceptional base change on arbitrary complexes is asserted. |
| Every N >= n coefficient reduction | `RegularClassCoefficientCompatibility` quantifies positive n,N and `n ≤ N`, with the actual `regularClassReduction` residue ring map. It states equality in the level-N Ext group after exact restriction of scalars. There is no false flatness assumption on Z/ell^N -> Z/ell^n. |
| Roots u -> u^(ell^(N-n)) | `RegularClassReductionData` fixes the root map by composition with its monic inclusion into gm: q >> kernel.ι = ell^(N-n) • kernel.ι. The generator equation fixes the coefficient-line map. Degree zero is the residue map on constant generators. |
| Negative twists by dual tensor comparisons | The reduction data quantify all `a b : ℤ` and preserve normalized multiplication on all pure tensors. Taking b=-a, together with the degree-zero normalization, is exactly the dual evaluation comparison, fixing the maps on negative lines. |

Dependency declarations read and used:

| Node/interface | Module and declaration |
| --- | --- |
| Ordinary derived category | `WeilConjectures.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategoryModule`. |
| Finite twists | `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`, `AlgebraicGeometry.Scheme.finiteEtaleTateTwist`; signed extension `Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf`, `Scheme.finiteEtaleTateSheaf`. |
| Closed immersion | `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`. |
| Regular sequences | `Mathlib.RingTheory.Regular.RegularSequence`, `RingTheory.Sequence.IsRegular`. |
| Compact support / right adjoint | `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `rightDerivedLowerShriekOfCompactification`; `...LowerShriekLeftAdjoint`, `isLeftAdjoint_rightDerivedLowerShriekOfCompactification`. |
| Cartier Kummer class | `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`, `Etale.ordinary_supported_kummer`, `ordinary_supported_kummer_uniqueBoundary`. |
| Regularity on support | `Sheaf.AlgebraicGeometry.StalkRegularClosedImmersion`, `AlgebraicGeometry.IsStalkRegularClosedImmersion`. |
| Normalized finite-Tate comparisons | `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`, `Scheme.FiniteEtaleTwistPullbackData`, `Scheme.finiteEtaleTwistPullbackData`, fields c and p. The server `--source` retrieval was also checked. |
| Relative boundary/exchange | `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary`, `Etale.SupportedKummerBoundary`, `supportedConstantUnit`, `supportedConstantExchange`. |

Other reused construction declarations are `singleFunctorCompRightDerivedFunctorIso`,
`singleFunctorObjUnitIso`, `singleFunctorObjTensorIso`, `ObjectProperty.flat_of_tensorIso`,
`derivedTensorShiftIso`, `singleFunctorCompLeftDerivedUpperStarIso`,
`commShiftLeftDerivedUpperStar`, `rightDerivedLowerStarProjectionMap`,
`rightDerivedLowerStarComp`, `Ext.mk₀`, `Ext.comp`, `Ext.mapExactFunctor`,
`Sheaf.restrictScalars`, `ZMod.castHom`, and `Scheme.strictHenselizationStructuralMap`.
The main module privately imports every proof-dependency module presently carrying
usable declarations, including ordinary cohomology continuity, the closed-support
mapping-fibre statement, filtered-colimit exactness, conormal base change,
localization flatness and strict-henselization input modules. The four Q26 inputs
have no current Lean module and remain natural-language proof inputs.

Edge cases checked: n=0 is excluded exactly as in the node; ell is prime, so ell^n
is positive. All c=0 cases, including non-surjective open-and-closed immersions,
are retained. The empty closed support is allowed (the stalk regularity condition
is vacuous there and its supported Ext carrier is zero); empty ambient schemes
are also allowed. Noetherian singular intermediate Cartier pairs are included.
Equal levels N=n use exponent ell^0=1 and the identity residue map. Negative
Tate degrees occur in coefficient and continuity predicates, using the existing
duals. Neither all permutations of a nonlocal regular sequence nor derived
open-chart gluing is assumed. The continuity index has the scheme universe,
not an independently smaller universe. There are no auto-bound variables.

Searches for existing statements and for the three added notions (actual msearch
records are retained in `searches.jsonl` and copied verbatim into every new node):

- `leanfinder` query `Regular immersion supported fundamental class composition flat base change coefficient reduction on Noetherian schemes`: 8 hits; AlgebraicGeometry.IsImmersion.isStableUnderBaseChange, AlgebraicGeometry.IsImmersion.isPullback_toImage_liftCoborder, AlgebraicGeometry.Scheme.Hom.liftCoborder_ι_assoc, AlgebraicGeometry.Scheme.Hom.liftCoborder_ι.

- `loogle` query `fundamentalClass, IsClosedImmersion, IsRegular`: 0 hits; loogle: unknown identifier 'fundamentalClass'.

- `grep` query `fundamentalClass|fundamental_class|Gysin|gysin`: 3 hits; Mathlib/CategoryTheory/Sites/Canonical.lean, Mathlib/CategoryTheory/Sites/Canonical.lean, Mathlib/CategoryTheory/Sites/Canonical.lean.

- `leansearch` query `regular immersion supported etale fundamental class composition coefficient reduction`: 8 hits; AlgebraicGeometry.IsImmersion.comp, AlgebraicGeometry.IsImmersion.of_comp, AlgebraicGeometry.IsImmersion.comp_iff, AlgebraicGeometry.IsClosedImmersion.comp_iff.

- `leansearch` query `Canonical supported cohomology tensor product and pullback of closed pairs on the small etale site`: 8 hits; AlgebraicGeometry.Scheme.smallEtaleTopology, CategoryTheory.binaryProductExponentiable, CategoryTheory.tensorClosed, PresheafOfModules.Monoidal.tensorHom.

- `leanfinder` query `System of supported classes of regular immersions normalized by Cartier Kummer with coefficient reduction and continuity`: 8 hits; AlgebraicGeometry.Scheme.Hom.normalizationDiagram, AlgebraicGeometry.Scheme.Hom.normalization, AlgebraicGeometry.Scheme.Hom.toNormalization, AlgebraicGeometry.StructureSheaf.normalize_finite_fraction_representation.

- `grep` query `supported.*[Pp]roduct|supported.*[Rr]estriction|[Rr]egular.*[Cc]lass`: 25 hits; Mathlib/Algebra/Regular/SMul.lean, Mathlib/Algebra/Regular/Defs.lean, Mathlib/CategoryTheory/SmallObject/IsCardinalForSmallObjectArgument.lean, Mathlib/Data/Finset/Finsupp.lean.

- `leansearch` query `Continuity of cohomology with closed supports under affine etale inverse limits representing localizations or strict localizations of Noetherian schemes`: 8 hits; AlgebraicGeometry.exists_mem_of_isClosed_of_nonempty', AlgebraicGeometry.exists_app_map_eq_zero_of_isLimit, AlgebraicGeometry.AffineScheme.hasLimits, AlgebraicGeometry.exists_isAffineOpen_preimage_eq.

- `loogle` query `Ext, Sheaf.restrictScalars, IsLocalization`: 0 hits; loogle: unknown identifier 'Sheaf.restrictScalars'.

Project/DAG searches used `rg` in `lean/WeilConjectures`, `lean/Sheaf` and
`dag/nodes`, and `tools/blueprint_refs.py search` for “supported class” and
“supported continuity”. The requested grep for the item id in WeilConjectures
had no match. Smooth fundamentalClass declarations and
`Sheaf.Paper.RegularImmersionClassData` require smooth/purity finite-field
settings; they do not state the arbitrary-Noetherian regular-immersion theorem.
`def-pur-supported-class-operations` owns P-dependent internal products and
pullbacks. `def-pur-supported-exterior-product` owns external products. Neither
gives this general nested supported action with the actual prime-power family
and coefficient-reduction laws. Existing generic Ext/tensor/pullback maps are
reused, not reconstructed. `lem-per-trait-test-supported-kummer-continuity`
is a prime-field theorem on regular global-equation pairs and depends on this
item; it cannot be an input defining the present local supported comparison.
A server-source query for the item module confirmed that no published item
attachment existed. No statement dispute or source correction was necessary.

## New nodes

`def-per-regular-supported-class-operations`: the ordinary supported Ext carriers,
their supported derived realization, actual shifted Tate multiplication, the
canonical nested composition square, and canonical restriction graph. Source:
ILO XVI 2.1--2.3, using the already recorded normalized finite-Tate and Cartier
exchange interfaces. This is an interface for arbitrary Noetherian pairs and
commutative coefficients killed by m; it has no PurityFiniteSetting or field
parameter and makes no purity assertion. Searches and comparisons above found
no node giving that scope and this nested product relation.

`def-per-regular-immersion-class-system`: the actual lifted residue coefficient
rings and ring reductions; signed coefficient comparison data specified on roots,
constants and tensors; a simultaneous family and its four laws. Source: ILO XVI
2.3.1--2.3.2 and 3.3.1--3.3.2. This defines a type/predicate, with no existence
proof or arbitrary choice of classes. It reuses the first new node and the
recorded regularity, Cartier and finite-Tate interfaces.

`def-per-regular-supported-local-continuity`: a predicate on the canonical
restriction graph for affine ind-etale localization presentations of Noetherian
pairs. It specifies the real localization maps and both parts of the colimit
isomorphism, in all relevant supported degrees and signed twists. Source:
Stacks Tag 03Q6, extracted by the mapping-fibre argument of the preserved proof
Step 11; ILO XVI 3.2. This is a definition only. Ordinary cohomology continuity
already exists, but its supported localization predicate does not. No theorem
or proof input is smuggled into this node.

All three new nodes have empty proof/proof_deps and `import_flags: []`, carry
the inherited blueprint ancestor and via path, and are added to the parent's
statement dependencies. Their declarations are all listed in `lean.declarations`.
There are no dependency-node replacements.

## Self-check before delivery

I reread the node, the dependency signatures and the four files. This caught
and corrected the codimension-zero equation's orientation: identity belongs to
the supported summand, not the whole ambient constant sheaf. It also caught
an initially opaque reduction-data wrapper that prevented its actual scalar
maps being used; the final reduction data are an exposed subtype, with the
true exact restriction-of-scalars Ext square. The local-continuity carrier is
an abbreviation of the existing Ext group so zero is the actual group zero.
The duplicated specialized pullback equation was replaced by an alias of the
generic canonical restriction relation.

No independent second worker was started: the dispatcher expressly forbids it.
The direct-delivery workflow leaves independent mathematical review to the
maintainer. Compilation uses only the prescribed scompile wrapper; no shared
source, build artifact, launcher script or Git state was edited directly.

Dry-run repair: a narrowed import had hidden the published ordinary derived pushforward/pullback wrappers and the projection map. Restored the recorded OrdinarySupportedCartierKummer public import, rather than copying those wrappers or constructing a second map.

Validation: scompile checked each of the four modules against the live published build, clean apart from the expected theorem sorry warning. The normal deliver2 no-push run completed with `OK (dry run)` at 754f37bd2f1: server preflight and every per-file compile passed. The final push repeats those checks against the refreshed live base.

## Second reading by Q150

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
