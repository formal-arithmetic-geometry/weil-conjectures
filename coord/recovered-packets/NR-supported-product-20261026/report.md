## Worker report

This delivery states `lem-per-noetherian-supported-product-calculus`. The source is ILO,
Expose XVI §2.1, Lemma 2.2.2.4, Proposition 2.2.3.2 and the proof of Theorem 2.3.2,
pp. 228–236. I read the PDF, including the sign convention in Definition 2.1.1.
The current stage-1 proof is copied, step by step with its dependencies, into the theorem
proof docstring. Its proof is `sorry`; all supporting definitions have actual data.
The resolved maintenance note withdraws the historical proof/module attachment. No
historical attachment or withdrawn alias is used here, and the node statement is unchanged.

The main declaration is
`AlgebraicGeometry.Etale.NoetherianSupportedProducts.noetherian_supported_product_calculus`.
Its conclusion `Nonempty (Data ell hell)` asserts a simultaneous family of the exact
operations and laws in the node, on the actual ordinary small-etale derived categories.
`LevelData`, `LevelLaws` and `Data` package the quantified operations and conclusions of this
one statement; they assert no existence by themselves. The operations are fixed by their
canonical tensor/projection/relative-boundary normalization equations. In particular they
are not arbitrary maps between abstract cohomology groups.

Hypothesis and clause matching:

| Node | Lean rendering |
| --- | --- |
| Prime ell | `ell : ℕ`, `hell : ell.Prime` in the main theorem and `Data`. |
| Every level n ≥ 1 | `Data.level n hn`, with `hn : 0 < n`; all laws and reductions retain the positive-level binders. |
| Lambda = Z/ell^n | The existing `regularClassCoefficient.{u} ell n = ULift.{u+1} (ZMod (ell ^ n))`, with the existing `regularClassAnnihilator`. The lift only fixes the universe of module sheaves. |
| Noetherian ambient scheme | `[IsNoetherian X]` in the operations/laws; `[IsNoetherian Y]` on nested actions merely spells out the consequence for the closed subscheme Y. No regularity, reducedness, separatedness, smoothness, characteristic, dimension or finite-type assumption is imposed. |
| ell invertible | At each positive level, `IsUnit (ell^n : Γ(X, ⊤))` is equivalent to ell being invertible. Reduction laws use `IsUnit (ell : Γ(X, ⊤))` and the existing `regularClassExponentUnit`; units on closed subschemes/intersections are pullbacks of that unit. |
| Ordinary small-etale sites and roots-of-unity twists | `DerivedCategoryModule A X`, `Scheme.finiteEtaleTateSheaf A m X hA b`, with `b : ℤ`, and the recorded normalized `FiniteEtaleTwistPullbackData` and `regularClassTransport`. |
| H with closed support is derived supported sections | `H` is the signed supported-Hom realization `closedConstantDerivedModule A i ⟶ (line ... X b)⟦a⟧`. `LevelLaws.sections_identification` is the normalized isomorphism of the actual kernel section functor `supportedEtaleSections` with `closedSupportHomFunctor`; composing with the kernel inclusion must be `closedSupportHomToSections`. Deriving this unique underived identification gives the recorded `closedSupportHom` comparison. Thus the carrier is cohomology of the stated derived supported-section functor, with its fixed evaluation-at-one normalization, not a separate cohomology theory. |
| Arbitrary closed subsets C,D | Closed immersions `i : Z ⟶ X`, `j : D ⟶ X` encode their supports. This includes every closed subset, by its reduced closed subscheme. The normalized section identification depends only on the open complement, so no choice of nilpotent thickening changes the represented theory. |
| Bilinear product, degrees a+a', twists b+b', intersection support | `LevelData.cup` is `H i a b →ₗ[A] H j a' b' →ₗ[A] H (intersectionSupport i j) (a+a') (b+b')`. Linear bilinear maps are equivalent to maps out of the module tensor product. All degrees and twists are integers. |
| Canonical cup product | `cup_normalization` says its composite with `closedConstantDerivedTensorMap` equals `tensorHom x y ≫ multiply ...`; `multiply` uses the recorded tensor/shift comparison, the flat signed-line comparison and the normalized Tate product. |
| Associativity | `cup_associative` includes the existing canonical `closedConstantAssociativitySupportMap` between the two iterated intersection sources. Integer degree/weight reassociation is the equality transport recorded by `HEq`. |
| Interchange sign (-1)^(aa') | `cup_interchange`, with `((-1 : ℤ) ^ (a*a').natAbs) • ...`, and the canonical symmetry support map. This is the same parity for negative as positive integer products. |
| Nested supports Z ⊆ Y ⊆ X and associative action | `LevelData.action i j` maps `H i a b` and `H j a' b'` to `H (i ≫ j) (a+a') (b+b')`; `action_associative` quantifies an arbitrary closed flag and all integer degrees/twists. |
| Projection formula for classes on Y | `LevelLaws.projection`: `(x cup y) action z = x action (y action z)`, where y is an ordinary absolute class on Y; `cupAbsolute`, `onIdentity` and `relabel` supply the canonical identity-support comparisons. |
| Action is composition under supported Hom | `action_composition` uses `IsComposition`. The intermediate arrow is fixed on its whole source by the existing canonical projection map, inverse-image line comparison, shifted multiplication and Koszul sign; `realize` inserts the exact-single/direct-image comparison. The second equation is the specified pushed-morphism composite, including the canonical direct-image composition isomorphism. |
| Exceptional composition after adjunction | `exceptional_composition` explicitly states the Hom-bijection equation for the composite of the actual `closedSupportPlusAdjunction`s. Applied to the pushed morphisms in `IsComposition`, it is precisely successive exceptional transposition. Only bounded-below objects are used here; the shifted line sheaves and closed constants are bounded below for every signed degree. |
| Pullback of pairs | `PullsTo` is the graph using the actual closed-constant exchange and normalized signed-line inverse image. `pullback_exists` asserts unique existence; `cup_pullback` and `action_pullback` assert compatibility for every Cartesian morphism of closed pairs/flags, including arbitrary, identity and nonflat base morphisms. |
| Open restriction | A special case of the preceding all-morphism pullback clauses; no smaller class of base morphisms is used. |
| Coefficient reduction | `Data.coefficientData`, `reduce`, `reduce_normalization`, `cup_reduce`, `action_reduce`, `boundary_reduce`, and `ReducesTo`. The existing residue map and `RegularClassReductionData` normalize degree zero by constant reduction, degree one by `z ↦ z^(ell^(N-n))`, and signed powers by tensor/evaluation. The reduction graph is in the original coefficient category under exact restriction of scalars; by adjunction it is precisely derived extension of scalars, not underived extension on arbitrary complexes. There is no flatness assumption on the residue map. Equal levels are included. |
| Line bundle L and trivialization s off C | `L : X.Modules` with `SheafOfModules.IsInvertible L`, and an isomorphism `s : pullback(unit X) ⟶ pullback L` over `i.openComplement`. This is exactly a specified frame, not merely triviality up to unspecified isomorphism. |
| Supported Kummer class e_C(L,s) | `LevelData.e` and `LevelLaws.boundary`; `IsFramedBoundary` uses the actual frame torsor, a short exact extension, an equivariant lift over the constant section one, and requires the specified open frame to map to zero. Composing the extension class with the actual Kummer connecting class and root coefficient map fixes e. This is the extension model of the recorded relative torsor classification and its relative connecting map. |
| Tensor additivity e(L⊗M,s⊗t) = e(L,s)+e(M,t) | `boundary_tensor`. `tensorFrame` is constructed from the existing strong monoidal module pullback, its tensor maps and the ordinary unit unitor. |
| Dual sign | `boundary_dual`, where the off-support dual frame is specified by the evaluation equation after `tensorFrame`; the conclusion is exactly `e(L^dual,s^dual) = -e(L,s)`. |
| Enlarge supports before comparing frames | `boundary_enlarge` uses the canonical support change and restriction of the frame-torsor section along the morphism of complementary opens. Hence the same tensor and dual identities apply after replacing different supports by a common closed support. |
| e_D(O(D),1) is the ordinary supported Cartier class | `cartier_positive` uses `SupportedKummerBoundary` from `ordinary_supported_kummer` and the canonical `supportedDivisorSectionPullback`, with O(D) the recorded `Scheme.Modules.dual i.ker.toModules`. |
| e_D(I_D,1) is its negative | `cartier_ideal`: the ideal frame is the inverse of its restricted inclusion; its class is `-κ.hom`, for the same positive-boundary κ. The required invertibility witnesses are canonical consequences of `i.ker.IsInvertible`, not additional geometry. |
| Pseudo-divisor operator | `gysin` is literally `O.action k i ... x (O.e i ... L s)`. Taking `k = 𝟙 Y` gives the operator on absolute cohomology of the support. |
| Extension to every smaller W ⊆ C | The same definition takes any closed `k : Z ⟶ Y`; its target is supported on `k ≫ i`. No separate extension with unspecified values is introduced. |
| Restriction is multiplication by c1(L|C) | `gysin_restriction` for every smaller support k, with the canonical self-pullback square of the monomorphism i; the result is `cupAbsolute` with `O.c1 Y ... (pullback i).obj L`. |
| Forget-support identity for ambient x | `gysin_forget`: apply `absolutePullback` and `onIdentity` to x, then gysin and `forgetSupport`; the result is `absoluteCup x (O.c1 X ... L)`. `chern_normalization` fixes c1 to the actual ordinary Kummer Chern class; `boundary_forget` identifies it with the forgotten supported class. |
| Transverse effective Cartier divisors | `cartier_interchange` has an arbitrary Cartesian square `sq : IsPullback q p j i`, with all four closed immersions having invertible Cartier ideals. Thus each divisor restricts to an effective Cartier divisor on the other. No ambient regularity is assumed. |
| Equal ideal-normalized composites | `cartier_interchange` starts with `x : H (𝟙 Z) a b`; each factor uses `-κ.hom`, identified with the ideal e by `cartier_ideal`. It compares both successive actions after the identity-support relabeling. Both results have degree `(a+2)+2 = a+4`, twist `(b+1)+1 = b+2`, and source the same Z with support arrows `p ≫ i` and `q ≫ j`, identified by `sq.w`. `HEq` is exactly transport along this equality of support arrows; no arbitrary intersection comparison is chosen. |

Dependency declarations used (full source signatures/docstrings were inspected):

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: `AlgebraicGeometry.Etale.DerivedCategoryModule`; the ordinary module-sheaf derived category.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`: `Scheme.finiteEtaleTateLine`, `Scheme.finiteEtaleTateTwist`; `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: `Scheme.finiteEtaleTateSheaf`, `FiniteEtaleTwistPullbackData`, `finiteEtaleTwistPullbackData` and `etaleFiniteTwistPullback`.
- `Sheaf.AlgebraicGeometry.EtaleSupportedSections`: `supportedEtaleSections`, `supportedEtaleSectionsι`, `derivedSupportedEtaleSections`.
- `Sheaf.AlgebraicGeometry.ClosedSupportHom`: `closedSupportHom`, and the imported `closedSupportHomFunctor`, `closedSupportHomToSections`, `closedSupportHomSource`.
- `Sheaf.AlgebraicGeometry.RelativeTorsorCohomology`: `relative_torsor_cohomology`, `relativeConnecting`; the extension model in `IsFramedBoundary` spells out the same relative class, including its specified section and connecting-map sign.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`: `Scheme.kummerSequence_shortExact`, `Scheme.kummerδ₁`.
- `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`: `ordinary_supported_kummer`, `ordinary_supported_kummer_uniqueBoundary`, and the publicly imported `SupportedKummerBoundary`, `supportedDivisorSectionPullback`, `supportedConstantUnit`, `supportedIntegralGenerator`, `ordinaryFiniteRootMap`.
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`: `Scheme.IdealSheafData.IsInvertible.isInvertible_toModules`, `.isInvertible_dual_toModules`; O(D) is the already recorded dual construction.
- `WeilConjectures.AlgebraicGeometry.Sites.GmPicard`: `Scheme.Modules.etaleIsoTorsor`, `Scheme.Modules.etaleIsoTorsorVal`, `Scheme.Pic.toCohomologicalPicardGroup`.
- `Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor`: `closedConstantModule`, `closedConstantDerivedModule`, `intersectionSupport`, `closedConstantDerivedTensorMap`, `closedConstantSupportChange`, `closedConstantAssociativitySupportMap`, `closedConstantSymmetrySupportMap`.
- `Sheaf.AlgebraicGeometry.RegularImmersionClassSystem`: only its already recorded coefficient and signed reduction constructions `regularClassCoefficient`, `regularClassAnnihilator`, `regularClassExponentUnit`, `regularClassReduction`, `regularClassTransport`, `RegularClassReductionData`; no regular-immersion family or existence theorem is assumed.
- `Sheaf.AlgebraicGeometry.RegularSupportedClassOperations`: the existing canonical shifted-target/projection-composition interface was read and generalized here to all signed degrees in the owning statement's `IsComposition`; its even-degree special case is not redefined.
- `Sheaf.AlgebraicGeometry.ClosedSupportPlusAdjunction`: `closedSupportPlus`, `closedSupportPlusAdjunction`; the actual bounded-below exceptional adjunction.

The last four owning nodes are added to stmt_deps because their published constructions now
occur in the statement. They are already landed; there are no dependency repairs or new
independent notions. Every stated proof dependency's module is imported. This adds no DAG
cycle: those definition/interface nodes do not depend on the present theorem.

Edge cases checked before writing and again against the full statement: empty scheme;
empty, full and disjoint supports; zero line cohomology classes; arbitrary negative degrees
and weights; ell = 2 (where the sign can become trivial in coefficients); n = 1; equal
reduction levels; identity pair maps; arbitrary nonflat pullbacks; nonreduced and singular
Noetherian X. None is excluded. Closed immersions are used as support presentations, and
the normalized kernel-section identification makes the interpretation independent of
nilpotent thickening. The zero coefficient ring is allowed by the generic helper interfaces;
the main theorem specializes to the required nonzero prime-power rings. Zero-ring/empty-site
cases do not create a hollow geometric hypothesis.

Searches made, with results:

- `msearch.py ... leanfinder "Cohomology with closed supports cup products nested action supported Kummer Chern classes transverse Cartier divisors"`: eight unrelated Hilbert 90, cotangent and nonabelian H1 hits; no full supported calculus.
- `msearch.py ... loogle "Ext.comp, TensorProduct, Sheaf.H"`: zero hits; the service reports `unknown identifier 'Ext.comp'`. This is a search-service name-resolution result, not evidence of an absent composition API; the actual project Ext and tensor APIs were then inspected directly.
- `msearch.py ... grep "supported.*cup|Cartier.*interchange|chernClass" AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch "Etale cohomology supported cup products Cartier Kummer first Chern class"`: eight unrelated etale-site, cotangent and algebra-etale hits.
- `rg` through `lean/WeilConjectures` and `lean/Sheaf` for the item ID, supported product/calculus names, `FramedLine`, `PseudoDivisor`, and supported Kummer/Chern names. The regular-immersion calculus only cites the item in its proof docstring. Existing partial interfaces are the ordinary supported Cartier boundary, relative torsor cohomology, signed twists, regular supported operations, and generic supported source-system cup calculus. They are reused; none states this theorem on Noetherian pairs with its framed-line and transverse-interchange clauses.
- Read `dag/lean_names_upstream.json` and matching DAG node records for those interfaces. No exact declaration exists, so `existing: true` is not appropriate.

No statement correction and no STATEMENT-DISPUTED flag is needed. Validation results are
recorded below after the final compiler and delivery checks.

## Compilation failure in the published dependency closure

The server overlay failed before compiling this module, in the mandatory statement dependency `Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor`'s transitive closure. The path runs through `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction`, smooth duality, and `Sheaf.AlgebraicGeometry.SfGraphSecondProjectionSquare`. That last module fails at line 438 with an unsolved equality in `wordProjection_graph`. Reading its current server source with `scompile.py --source` confirms the failing proof is upstream. Dropping optional imports cannot remove this mandatory path. The shared source is read-only and this unrelated theorem is outside the authorized dependency-interface repairs. No local compiler or source patch was used. A second compile of the corrected current draft returned the same overlay failure (exit 1, 30.7 seconds) before compiling this delivery. The draft is therefore unvalidated and has not been delivered.

## Saved-packet retry (2026-10-26)

Started with the required `deliver2.py NR lem-per-noetherian-supported-product-calculus
--no-push` on the retained packet. It exited 1 with `COMPILE FAILED on the server,
nothing pushed` before checking the delivery's declarations. The overlay snapshot was
`acd21cff732fb056e07e3c9a6016b35e3d452bd213205bb7e7d6e18f97f5851b`.
The diagnostic is still `SfGraphSecondProjectionSquare.lean:438:75: error:
unsolved goals` in its private `wordProjection_graph` proof. The remaining equality
starts with `sfGraphProjectionWord ... = ...`; this is not an error in this packet.

Read the current published source with `scompile.py --source
Sheaf.AlgebraicGeometry.SfGraphSecondProjectionSquare`, confirming that its lines
438--441 contain the failing `simp only` proof. Also compiled a minimal module-mode
probe under this sandbox's `scratchpad/RequiredDependencyProbe.lean`, with exactly
`module`, `public import Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor`,
`@[expose] public section`, and a check of
`AlgebraicGeometry.Etale.closedConstantDerivedTensorMap`. This reproduces the same
mandatory-overlay error before reaching the check. Therefore this is independent
of optional imports and legacy non-module import visibility. The tensor dependency
is required by the current node's accepted proof plan and by the delivered statement's
canonical normalization, so removing it would discard required content. Its private
proof-import closure contains the broken graph-square module.

No shared source, launcher tool, or compiled library was edited. The original packet
is retained. The server compilation wrapper cannot currently validate even this
minimal use of the required published dependency; delivery remains blocked by that
published closure, and nothing was pushed.

## Further saved-packet retry (2026-10-26)

Again started with the prescribed unchanged-packet `deliver2.py NR
lem-per-noetherian-supported-product-calculus --no-push`. It returned exit 1,
`COMPILE FAILED on the server, nothing pushed`, with the same overlay snapshot
`acd21cff732fb056e07e3c9a6016b35e3d452bd213205bb7e7d6e18f97f5851b`
and `SfGraphSecondProjectionSquare.lean:438:75: error: unsolved goals`.
Reattached to the unchanged `scratchpad/RequiredDependencyProbe.lean` compile with
the prescribed `scompile.py`; it returned the same upstream error and exit 1.
The live `scompile.py --source Sheaf.AlgebraicGeometry.SfGraphSecondProjectionSquare`
still shows the failing private `wordProjection_graph` and its `simp only` proof
at lines 429--441. The minimal probe imports only the required closed-constant
tensor interface, so removing optional imports from this delivery cannot repair
the failure. This is a published dependency proof failure before the packet is
compiled, not a missing or overly specialized statement interface repairable
under §1(A)/(B). The saved module and node are retained unchanged. No delivery
was pushed and no read-only source or launcher script was modified.

## Saved-packet retry, attempt 4 (2026-10-26)

Started with the prescribed unchanged-packet `deliver2.py NR
lem-per-noetherian-supported-product-calculus --no-push`. It again returned
`COMPILE FAILED on the server, nothing pushed` (exit 1), using snapshot
`acd21cff732fb056e07e3c9a6016b35e3d452bd213205bb7e7d6e18f97f5851b`.
Reattached to the unchanged minimal module-mode `RequiredDependencyProbe.lean`
with `scompile.py`; its complete diagnostic still reports
`SfGraphSecondProjectionSquare.lean:438:75: error: unsolved goals` in
`wordProjection_graph`, before the required closed-constant tensor interface
can be checked. Read the current server source with `scompile.py --source`;
the failing proof remains unchanged at lines 438--441.

This is a failure in the required published dependency closure, rather than
an elaboration diagnostic for the saved packet or an unusable mathematical
interface under section 1(B). Repair would require editing an unrelated
published proof, which this stage-2 sandbox authorization does not permit.
No source or launcher scripts were changed. The saved Lean module and node
remain unchanged and unvalidated; nothing was pushed.
