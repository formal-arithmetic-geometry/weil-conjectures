## Worker report

Repair of H1 at returned head `03fcc96b2022`. The retained sandbox contained only launcher brief markers: no node copy, module, or report. I read the current node, its reviewed proof and dependencies, the return entry, and Stacks `more-etale.tex`, `lemma-pseudo-functor` (Tag 0F7K). The mathematics accepted in that return is preserved. The delivered node changes only `lean`; the node's statement, dependencies, proof, and reviewed fields are unchanged. The delivery wrapper rebases the packet onto current `newtargets-dag`.

The module is `Sheaf.Paper.CompactSupportStaircaseExpansion`. Its main theorem is `AlgebraicGeometry.Etale.compactSupportStaircaseExpansion`, with one postponed proof, `sorry`. The other three declarations have real defining terms:

- `compactSupportStaircaseInterchange` exposes the normalized family already supplied by `unboundedProperOpenInterchange`. It chooses that theorem's family with all its normalizations, not an unspecified natural isomorphism. The sheaf normalization determines each map by its composition into the common direct image, and the representative normalization determines each derived component on every K-injective representative. These determine the chosen family up to equality, as required for a definition using a postponed characterization theorem.
- `compactSupportRawBinaryComparison` is the statement's raw Θ: whisker the specified Γ by the inner open extension and the outer proper direct image, then apply the canonical direct-image and open-extension composition isomorphisms. Its body is a composition of those actual natural isomorphisms and functor associators. It does not use compactification independence or associativity of Θ.
- `compactSupportStaircaseTargetIso` fixes the common structural identification of `R(tsp)_*D(bal)_!` with `Rt_*Rs_*Rp_*Db_!Da_!Dl_!`, expanding proper factors and open factors with the canonical composition maps. It is a component isomorphism with an explicit body, not an existence assumption.

All four declarations carry the item's blueprint tag and source. The theorem's docstring gives the node's proof step by step, including the K-injective argument for compatibility of the two structural parenthesizations. No new DAG node or dependency repair is needed: these helpers expose constructions introduced by this item's statement using its already recorded dependencies.

Hypothesis and clause correspondence (functors compose left to right in Lean):

| Node text | Lean rendering |
| --- | --- |
| Finite commutative coefficient ring A | `(A : Type (u + 1)) [CommRing A] [Finite A]` |
| Schemes X, U, V, Xbar, Y, W, Ybar, Z, Zbar, T | The ten explicitly bound objects of `Scheme.{u}` |
| All schemes Noetherian, admitting finite affine covers with Noetherian coordinate rings | Ten instances `[IsNoetherian ...]`; Mathlib's `isNoetherian_iff_of_finite_iSup_eq_top` identifies this class with the specified finite-affine-cover condition |
| Ordinary constant-A module sheaves and their unbounded derived categories | `DerivedCategoryModule A X`, definitionally `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))`, and the same coefficient category at every other scheme |
| The six open immersions l, a, b, d, k, i with exactly the displayed domains | Six morphism binders and `[IsOpenImmersion l]`, `[IsOpenImmersion a]`, `[IsOpenImmersion b]`, `[IsOpenImmersion d]`, `[IsOpenImmersion k]`, `[IsOpenImmersion i]` |
| The six proper maps m, r, p, q, s, t with exactly the displayed domains | Six morphism binders and the corresponding six `[IsProper ...]` instances |
| ra=dm, pb=kr, sk=iq and cartesianness of QA, QB, QC | `QA : IsPullback a m r d`, `QB : IsPullback b r p k`, `QC : IsPullback k q s i`; each `.toCommSq` includes the required equality |
| f=ml, g=qd, h=ti | These abbreviations are expanded throughout: `l ≫ m`, `d ≫ q`, `i ≫ t` at the scheme level, and the displayed compact-support candidates at the functor level. No independent f, g, h or extra equations are assumed |
| Candidate Ff | `D((l)_!open[ModuleCat A]) ⋙ R((m)_*[ModuleCat A])` |
| Candidates Fg and Fh | `D((d)_!open[ModuleCat A]) ⋙ R((q)_*[ModuleCat A])` and `D((i)_!open[ModuleCat A]) ⋙ R((t)_*[ModuleCat A])` |
| Candidate Fgf | `D((l ≫ a)_!open[ModuleCat A]) ⋙ R((r ≫ q)_*[ModuleCat A])`, the target of the raw QA comparison |
| Candidate Fhg | `D((d ≫ k)_!open[ModuleCat A]) ⋙ R((s ≫ t)_*[ModuleCat A])`, the target of the raw QC comparison |
| Candidate Fhgf | `D(((l ≫ a) ≫ b)_!open[ModuleCat A]) ⋙ R(((p ≫ s) ≫ t)_*[ModuleCat A])`; the other parenthesization is transported by the explicit `eqToHom` |
| A, B, C are the specified Γ maps | `compactSupportStaircaseInterchange A a m r d QA.toCommSq`, the same helper at `b r p k QB.toCommSq`, and at `k q s i QC.toCommSq` |
| Comparisons for (g,f), (h,g), (h,gf), (hg,f) | `compactSupportRawBinaryComparison` at QA, QC, `QB.toCommSq.vert_comp QC.toCommSq`, and `QA.toCommSq.horiz_comp QB.toCommSq` respectively |
| Left parenthesization represented by L | First conjunct's left side applies `Rt_*Di_!` to the raw QA component, then the raw vertical-rectangle component, then the common target identification. Its right side is successively `Rt_*Di_!Rq_* A Dl_!`, `Rt_* C Rr_*Da_!Dl_!`, `Rt_*Rs_* B Da_!Dl_!` |
| Right parenthesization represented by R | Second conjunct's left side applies the raw QC component to `Rm_*Dl_!K`, then the raw horizontal-rectangle component, transports the scheme composites' parentheses, and uses the same target identification. Its right side is successively `Rt_* C Dd_!Rm_*Dl_!`, `Rt_*Rs_*Dk_! A Dl_!`, `Rt_*Rs_* B Da_!Dl_!` |
| Same source and same target for both equations | Both elaborate from `Rt_*Di_!Rq_*Dd_!Rm_*Dl_!K` to `Rt_*Rs_*Rp_*Db_!Da_!Dl_!K`, through the single named target identification |
| Every unbounded input; two expansion identities only | `(K : DerivedCategoryModule A X)` is unrestricted, and the conclusion is exactly the conjunction of the two component equalities. Since the maps come from natural transformations, quantification over all K expresses their equality. No equality L=R or independence of the staircase is included |

Dependency declarations read and used:

- `def-weil-pbc-derived-categories`: `DerivedCategoryModule` in `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, re-exported by the recorded `WeilConjectures.AlgebraicGeometry.DerivedCategories`. I also read that current module with `scompile.py --source`. The torsion-cohomology declaration of the wrapper is not needed for these unrestricted unbounded inputs. The interchange module already publicly imports the same coefficient definition through its earlier wrapper.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` in `Mathlib.AlgebraicGeometry.Scheme`; `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in `Mathlib.RingTheory.Noetherian.Defs`, used by the standard scheme Noetherian class.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion` in `Mathlib.AlgebraicGeometry.OpenImmersion`; `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` in `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `def-pc-fibre-product`: Mathlib pullbacks from `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, with the universal-square property expressed as `IsPullback`.
- `def-amb-etale-compact-support`: `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`. Its body is exactly `D((c.i)_!open[ModuleCat A]) ⋙ R((c.g)_*[ModuleCat A])`, the functor expressions used here. No private copy of the compact-support candidate is defined.
- `lem-amb-unbounded-proper-open-interchange`: `AlgebraicGeometry.Etale.unboundedProperOpenInterchange` in `Sheaf.Paper.UnboundedProperOpenInterchange`, including the representative normalization and both pasting clauses, read in full in both the checkout and the current server source.
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`: `CategoryTheory.ringedToposDerivedPushforwardComposition` in `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`. This is publicly imported by the interchange dependency. The actual canonical constant-coefficient direct-image composition maps are the existing `AlgebraicGeometry.Etale.rightDerivedLowerStarComp` in `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`, which defines them by conjugating the exact inverse-image adjunctions. No small-site universe equality or arbitrary replacement comparison is imposed.
- `lem-cbc-extension-zero-composition`: `AlgebraicGeometry.Etale.openImmersionLowerShriekComp` and `openImmersionLowerShriekComp_coherence` in the recorded `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`, publicly imported by the interchange module. The derived comparison is the actual termwise descent `Functor.mapDerivedCategoryNatIso ... ≪≫ Functor.mapDerivedCategoryCompIso _ _`.
- Proof-only `lem-weil-pbc-kinjective-hom-derived`: `CochainComplex.IsKInjective.Qh_map_bijective` in `Mathlib.Algebra.Homology.DerivedCategory.KInjective`, imported without `public` for the proof plan. Its bounded-below and homotopy-equivalence clauses are not extra hypotheses here.

Searches performed before writing:

| Tool | Query | Result |
| --- | --- | --- |
| msearch leanfinder | Expand the two compact support comparison maps on a staircase of proper maps and open immersions into three interchange transformations | Eight hits, including open-immersion gluing/lift formulas and compactly supported continuous maps; none states this derived staircase expansion |
| msearch loogle | `AlgebraicGeometry.Etale.rightDerivedLowerStarComp, AlgebraicGeometry.Etale.openImmersionLowerShriekComp` | Zero hits; unknown project identifier in the Mathlib search service |
| msearch grep | `staircase\|rawBinary\|compactSupportStaircase\|compact.support.*expansion` | Zero Mathlib hits |
| msearch leansearch | Compact support comparison associativity staircase expansion of proper open interchange | Eight topology hits, including `CompactlySupportedContinuousMap.comp_assoc`; no matching categorical statement |
| rg in upstream WeilConjectures and project lean/Sheaf | The same staircase/rawBinary/compactSupportStaircase/expansion patterns, plus the exact item id | No matching declaration. Project staircase hits were unrelated sequential-tower and Cech arguments |
| rg in dag/lean_names_upstream.json, upstream, and project sources | `compactSupportStaircase\|compactSupportRawBinary` | No name collisions |

Edge cases checked mathematically before drafting: the zero coefficient ring is included by `[CommRing A] [Finite A]` without a nontriviality assumption; zero complexes and arbitrarily unbounded complexes are allowed by the unrestricted derived input. Empty schemes and empty opens are not excluded. If all proper maps are identities, the raw comparisons reduce to structural open composition; if all open maps are identities, they reduce to proper direct-image composition. Either normalization is covered by the recorded interchange dependency. No characteristic restriction, constructibility, invertibility of the coefficient order, or dimension bound has been added. The universe `A : Type (u+1)` is the project's recorded ordinary module-sheaf encoding; there is no new site-universe equality.

No statement dispute or source correction was needed. Every theorem newly delivered has its entire proof postponed, and every new definition has an explicit body.

Validation: the initial normalized-family-only probe compiled cleanly through `scompile.py` (27.0 s sandbox / 27.2 s library). The full-file check found a structural cast requiring `Functor.comp_obj` in addition to `Category.assoc`; that was repaired. The repaired full file compiled cleanly through `scompile.py` in 27.7 s (sandbox) and 30.0 s (library-module verification), with no errors or warnings. The final packet also checks that only the lean field changed, the recorded signature is verbatim, every Lean line is at most 100 characters, and there is exactly one postponed theorem proof. Delivery preflight is run on this complete packet.

## Second reading by NW

There is no separate second worker in this direct-delivery run, and the dispatcher explicitly forbids starting another agent. The maintainer's independent immutable-head review is the independent review. This section records my second reading, not a claim of independent authorship.

I reread the node alongside the actual Lean file, checking all ten scheme binders, all six open and six proper maps, the three cartesian squares and their orientation, and the unchanged finite constant-coefficient unbounded setting. I traced QA to `a m r d`, QB to `b r p k`, and QC to `k q s i`; the vertical rectangle has edges `b`, `r ≫ q`, `p ≫ s`, `i`, and the horizontal rectangle has edges `a ≫ b`, `m`, `p`, `d ≫ k`. These are exactly the four raw-comparison calls in the theorem. Both conclusions have the same nested source and six-factor target. The first right side reads A then C then B; the second reads C then A then B. Neither conjunct compares those two right sides.

I checked the helper bodies against the definitions in the dependencies: the extracted Γ carries the dependency's full canonical normalization, the raw comparison inserts the proper composition map in its forward direction and the open composition map in its inverse direction, and the target is expanded in the opposite directions. This avoids assuming the expansion in a helper definition. The only mismatch found during elaboration was a missing unfold of the object of a composite functor in the second route's associativity transport; `Functor.comp_obj` repairs that cast without changing any mathematical clause. No hypothesis or conclusion was dropped or added on this reading. The H1 return is addressed by supplying the item module, exact lean record, compile evidence, this Worker report, and this explicitly attributed second-reading section.
