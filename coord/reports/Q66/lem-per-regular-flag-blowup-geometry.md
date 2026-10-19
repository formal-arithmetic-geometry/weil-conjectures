## Worker report

Item: `lem-per-regular-flag-blowup-geometry`. The module
`Sheaf.AlgebraicGeometry.RegularFlagBlowupGeometry` states the entire node as
`AlgebraicGeometry.RegularFlagBlowupGeometry.regular_flag_blowup_geometry`.
Its proof alone is `sorry`. The auxiliary definitions and the conclusion record have real
bodies. They package this theorem's specified conormal and blowup diagrams; they introduce
no arbitrary geometric datum as a hypothesis. The quasi-coherence instance merely reuses
`Scheme.Modules.affine_conormal_sections.{u,u}`.

I read the node, its statement dependencies and their recorded interfaces, and ILO,
Travaux de Gabber, Exposé XVI, printed pp. 234–237 (PDF pages 240–243). The source's p. 235
text has the known P/P' misprint in the first quotient; the node and Lean use N_{B/P}.
No natural-language statement correction is needed.

The following matches every hypothesis and conclusion. All names in the right column
without a namespace prefix belong to `AlgebraicGeometry.RegularFlagBlowupGeometry`.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A single regular closed immersion W into V, with both schemes Noetherian | The first conjunct quantifies over `V W : Scheme.{u}`, `[IsNoetherian V]`, `[IsNoetherian W]`, `k : W ⟶ V`, and `[IsClosedImmersion k]`. |
| Constant codimension c ≥ 0 and locally regular defining equations | `c : ℕ` and the displayed hypothesis `∀ w : W, ∃ U : V.affineOpens, k w ∈ U.1 ∧ ∃ f : List Γ(V,U.1), f.length = c ∧ RingTheory.Sequence.IsRegular Γ(V,U.1) f ∧ Ideal.ofList f = k.ker.ideal U`. |
| Its conormal is finite locally free of rank c | `(conormal k).IsFiniteLocallyFreeOfRank c`. `conormal k` is the existing tensor pullback of the actual kernel ideal, hence I/I² by the recorded affine-conormal theorem. |
| The flag Z → Y → X consists of Noetherian schemes | The second conjunct binds `X Y Z : Scheme.{u}` with all three `IsNoetherian` instances, and binds `i : Z ⟶ Y`, `j : Y ⟶ X`. |
| The two regular immersions have constant positive codimensions m and n | `m n : ℕ`, `[IsRegularImmersion m i]`, `[IsRegularImmersion n j]`, `0 < m → 0 < n →`. For positive codimension the upstream affine-local weakly-regular generators are equivalent to regular equations near the source, including over singular ambient rings. |
| Conormal ranks m, n, m+n | The existential conclusion `∃ S : ConormalSequence i j m n` contains `rankI`, `rankJ`, `rankComposite`. |
| The natural short exact conormal sequence | `S.inclusion`, `S.quotient`, `S.zero`, and `S.shortExact`. `naturalInclusion` and `naturalQuotient` fix these maps via `IsConormalMap`; its intermediate ideal-map section equation and normalized adjunction equation specify the maps on actual ideal representatives. |
| B is Bl_Y X with its specified projection | `FirstBlowup` uses exactly `j.ker.blowup` and `j.ker.blowupMap`. These are the existing Rees-Proj construction, not existential modifications of X. |
| P is the exceptional subscheme and P(N_{X/Y}) | The existential `P`, `p`, `exceptional` with `cartesian : IsPullback p exceptional j j.ker.blowupMap` give the scheme-theoretic inverse image of Y. `projective` identifies it with the canonical symmetric algebra's `relProj`; `Classifies` makes the identification over Y and compatible with the natural quotient. |
| P is an effective Cartier divisor with ideal O_B(1) | `IsClosedImmersion exceptional`, `exceptional.ker.IsInvertible`, and `IsReesTwist j.ker exceptional.ker`. The latter compares to the recorded `Proj.twist` on every affine base chart and sends each actual pulled-back ideal generator a to aT. This normalization makes the local comparisons agree on overlaps; it is stronger than an unglued list of local line isomorphisms and expresses the intended global Rees twist. |
| P' = P ×_Y Z with its four displayed maps | `P'`, `p'`, `inclusion`, and `baseChange : IsPullback p' inclusion i p`. |
| Codimensions m and m+1 | `IsRegularImmersion m inclusion` and `IsRegularImmersion (m+1) (inclusion ≫ exceptional)`. |
| Both natural conormal maps are surjective | `quotient`, `quotient'`, their `IsConormalMap` conditions, and `Epi quotient`, `Epi quotient'`. Epimorphisms in these sheaf-of-modules categories mean sheaf-surjectivity. |
| Both kernels have rank n−1 | `(kernel quotient).IsFiniteLocallyFreeOfRank (n-1)` and the corresponding clause for `quotient'`. |
| The canonical pullback identification of kernels | `kernelIso` and its equality after composing with `kernel.ι quotient'`. The right side is the pulled-back kernel inclusion, the normalized commutative-square pullback comparison, and the pullback of `S.inclusion`. This fixes the isomorphism through its actual kernel inclusion. |
| The conormal of i' is p'^*N_{Y/Z} | `conormalIso`, with `IsConormalMap inclusion i p p' baseChange.w.symm conormalIso.hom`, fixes the usual base-change isomorphism. |
| When n=1, use instead Bl_Z X and its exceptional P(N_{X/Z}) | `n = 1 → DivisorBlowup i j m n S`. That predicate uses exactly `(i ≫ j).ker.blowup` and its blowup map. Its exceptional pullback square, Cartier ideal and `Classifies` condition give the specified exceptional projective bundle. |
| The strict transform is Bl_Z Y and is an effective Cartier divisor | The actual `strictTransform j (i ≫ j).ker.blowupMap (i ≫ j).ker.support.compl` is used. Its `strictTransformMap` kernel is invertible. `strictBlowup` identifies it with `i.ker.blowup`, and the following equation makes the identification over Y. Both sides are the specified closures of Y away from Z. |
| P' = P ∩ strict transform = P(N_{Y/Z}), scheme-theoretically | `Q`, `toP`, `toStrict`, and `_intersection : IsPullback toP toStrict exceptional (strictTransformMap ...)`. `intersectionProjective` identifies Q with the canonical `relProj` for `conormal i`; the next equation is compatibility with the Z-projections. |
| The divisors meet transversely in the stated sense | `toP.ker.IsInvertible` and `toStrict.ker.IsInvertible` say that their intersection is effective Cartier on each. Both maps are closed immersions by base change of the two displayed closed immersions. |
| π^*I ≅ I_P ⊗ I_strict, with canonical trivializations | The existential `factorization` has exactly that source and target. `IsIdealProduct` fixes its inverse by multiplication of ideal sections: whenever π(s)=ab, it sends the pullback of s to a⊗b. Locally the ideals are principal nonzerodivisor ideals, so these equations uniquely specify multiplication's inverse. Off π^{-1}Y, s=a=b=1 gives the required normalization. |
| The hyperplane ideal is p_P^*K_0 ⊗ O_P(-1), K_0=i^*N_{X/Y} | `hyperplane` identifies `toP.ker.toModules` with `(tensorPullback p).obj ((tensorPullback i).obj (conormal j)) ⊗ SheafOfModules.homObj (conormal exceptional) (SheafOfModules.unit ...)`. `Classifies` identifies `conormal exceptional` with the pulled-back degree-one tautological line, so its Hom-dual is O_P(-1). The final section equation says that the inverse followed by the actual ideal inclusion evaluates the dual section on `quotient ∘ p^*(S.inclusion)`. It is the tautological hyperplane map, with its sign and normalization. |
| No regularity of ambient schemes | There is no `IsRegular X`, `IsRegular Y`, `IsRegular Z`, smoothness, field, or characteristic assumption. |

Dependency declarations used, with their recorded modules:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`; the proof
  also has the recorded `IsLocalRing.isRegular_of_perm` available through imports.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`:
  `AlgebraicGeometry.Scheme.GradedAlgebraData.relProj`, `relProjHom` (read from current
  source with `scompile.py --source` because the older checkout lacks this module).
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`:
  `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`.
- `WeilConjectures.Compactification.StrictTransform`: `AlgebraicGeometry.strictTransform`,
  `strictTransformMap`, `strictTransformι`, imported through `StrictTransformBlowup`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules`:
  `AlgebraicGeometry.Proj.twist`, `Proj.unitToTwist`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSection`,
  `tensorPullbackSectionAdjunction`, `tensorPullbackSectionComp`, `tensorPullbackSectionId`.
- `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`:
  `AlgebraicGeometry.SymmetricAlgebraSheaf.gradedAlgebraData`.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry`:
  `AlgebraicGeometry.ProjectiveBundleQuotientGeometry.TautologicalQuotient`,
  `pulledQuotient`, `Classifies`, now owned for statement-dependency purposes by
  `def-per-projective-bundle-quotient-data`.
- `WeilConjectures.AlgebraicGeometry.AffineConormalSections`:
  `Scheme.Modules.affine_conormal_sections`. Its current node records the upstream module;
  I replaced the retained draft's retired `Sheaf` import accordingly and read its live source
  with `scompile.py --source`.

The item adds `def-per-projective-bundle-quotient-data` and
`lem-weil-pbc-affine-conormal-sections` to `stmt_deps`. The affine-conormal theorem's
first projection supplies the genuine quasi-coherence instance required to type the
canonical symmetric algebra. The projective-bundle theorem remains in `proof_deps`;
its auxiliary plain definitions are cited through their new definition node instead.
There are no dependency-module repairs. The seven plain proof imports and the unused
public import `WeilConjectures.Blowup.Principalization` were removed as requested by H9.

Edge cases checked: c=0 uses the empty regular sequence near points of W, so includes
proper clopen immersions; it does not impose the upstream positive-codimension convention
at points outside W. W empty gives a vacuous local condition and rank condition on the
empty scheme. For n=1 both excess kernels have rank zero. For m=n=1 the second blowup has
two coordinate charts and its hyperplane ideal is K_0⊗O(-1). Empty X/Y/Z do not create
extra hypotheses; all chart and point quantifiers still make sense. On a singular or
nonreduced Noetherian ambient ring the chart argument uses only the stated regular
sequences. The proof docstring explains the a-chart, the g_k-chart, and the canonical
trivialization outside Y. Every universe is explicit (`u`); there is no coefficient
category or test-universe restriction.

Searches retained from the interrupted attempt, recorded in `searches.jsonl`:

- LeanFinder, “Regular flag of closed immersions conormal sequence blowup exceptional
  divisor strict transform”: eight general closed-immersion hits, no matching theorem.
- LeanSearch, “Regular closed immersions conormal exact sequence exceptional divisor
  blowup regular flag”: eight closed-immersion characterization hits, no matching theorem.
- Loogle, `"conormal"`: no hits; `IsRegularImmersion, conormal`: no hits, upstream-only name.
- Mathlib grep, `IsRegularImmersion|conormal|blowup`, AlgebraicGeometry: no matching result.
- Direct `rg` in the upstream `WeilConjectures` and side `lean/Sheaf` sources, for conormal,
  regular immersions, blowups and this item id: found the reused regular-immersion,
  affine-conormal, tensor-pullback, symmetric-algebra, projective-bundle and blowup
  infrastructure. No theorem states this combined regular-flag result.
- Direct source search for named conormal definitions found the specialized
  `formallyUnramifiedConormal`, `diagonalConormal`, and ideal-power `ConormalGradedAlgebra.piece`;
  none supplies the general map-normalized flag conclusion. The helper `conormal` here
  only names the existing tensor-of-kernel expression used by `affine_conormal_sections`.
- `dag/lean_names_upstream.json` search for this theorem and helper names: no collision.

No statement is disputed. No proof or definition data is chosen from a bare existence
claim. The projective and strict-transform isomorphisms occur in the theorem's conclusion.
Compilation uses only the prescribed `scompile.py` wrapper; no global build or direct git
command was run.

## Second reading by Q66

This is the author's final consistency check, not an independent-agent review; the
special dispatcher brief forbids starting other agents and reserves independent review
for the maintainer. I reopened the node and the whole module and checked the table above.
I repaired the retained draft's two warnings (unused named intersection witness and long
line), switched the retired affine-conormal import to its recorded upstream module, and
made two canonical identifications explicit: the Rees-twist comparisons send a to aT on
every base chart, and the hyperplane-ideal inclusion is the evaluation of the dual line
against the pullback of the natural conormal inclusion. This prevents either clause from
being satisfied by unrelated local isomorphisms. The conormal and ideal-product relations
also fix their maps on representatives; the kernel isomorphism is fixed by its inclusion.
The first conjunct keeps c=0 and the second keeps both positive-codimension hypotheses.
No node statement, hypothesis, or geometric conclusion was changed.


## New nodes

`def-per-projective-bundle-quotient-data` records the already published definitions
`TautologicalQuotient`, `pulledQuotient`, and `Classifies` in
`Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry` with `existing: true`.
The source is Stacks constructions.tex, Tags 01OA/01OB, with the affine twist
normalization from 01NR/01O4. Its statement describes the invertible line and epi
quotient, the affine generator normalization, the composition-normalized pulled
quotient, and the existence of a quotient-preserving line isomorphism over the base.
It does not claim the theorem's existence or universal property. LeanSearch found
only general projectivization, Picard group and quasi-coherence declarations; Loogle
and Mathlib grep returned no hits. Source grep found the three exact side-library
definitions, and DAG/blueprint search found no definition node owning them. Thus the
node reuses existing definitions and adds no Lean module or duplicate construction.

## Returned delivery repaired

H2: added the definition node above, replaced the added theorem statement dependency
with its id, and retained `lem-trf-projective-bundle-quotient-geometry` unchanged in
`proof_deps`. The accepted affine-conormal dependency is retained. H9: removed all
seven plain imports and `public import WeilConjectures.Blowup.Principalization`.
The retained theorem and all auxiliary declaration bodies and signatures are unchanged.

Second reading of this repair by Q66: I opened the new node and the existing source.
The scheme and quasi-coherent-module hypotheses are the source's explicit `S`, `E`
and `[E.IsQuasicoherent]` binders. The datum's line, quotient, invertibility,
surjectivity, charts and homogeneous-generator equation are exactly the six fields
of `TautologicalQuotient`. The pulled quotient's base equality, inverse equality
transport, composition comparison and pulled map are `pulledQuotient`. The over-base
equality and quotient-preserving line isomorphism are exactly `Classifies`. This also
covers the zero module, empty schemes and arbitrary quasi-coherent modules: the new
node defines data and relations without asserting their existence. The original
hypothesis-and-clause table and edge-case check remain valid after this repair.
