## Worker report

The node is exactly the existing theorem
`AlgebraicGeometry.Etale.UniversalBaseChangeProperty.mono_baseChangeHomologyMap_and_cokernel`
in `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.CriticalMap`,
lines 204–223 of slopmaster2. Read its complete signature, section parameters,
docstring, proof, and the three component theorems in that module. The current
source returned by `scompile.py --source` agrees with the local source. Record
`existing: true`; no new Lean module, definition, proof, or dependency repair is
needed. Only the item's `lean` field changes, with its signature copied verbatim
from `theorem` up to the defining `:=`.

Source checked: Stacks Project `etale-cohomology.tex`,
`lemma-base-change-q-injective`, Tag 0F03, including the proof. The source node
explicitly uses the arbitrary-ring generalization in CriticalMap.lean. The
existing proof uses injectives in the category of module-valued sheaves, so it
imposes no annihilator or invertibility assumption. The node's `proof` and
`proof_deps` are empty; the existing upstream proof is retained, not rewritten.

Hypothesis and conclusion correspondence:

| Node text | Existing Lean |
| --- | --- |
| Scheme morphism `f : X → S` | Section parameters `{X S : Scheme.{u}} {p : X ⟶ S}`; `p` is `f`. |
| Arbitrary commutative coefficient ring | `(Λ : Type (u + 1)) [CommRing Λ]`, with no further ring hypothesis. |
| Integer `q ≥ 1` | `{q : ℤ} (hq : 1 ≤ q)`. |
| `BC(f, Λ, q-1)` universally | `(huniv : Etale.UniversalBaseChangeProperty Λ p (q - 1))`. |
| Any `a : S' → S` and the base change `f'` | `{S' X' : Scheme.{u}} {a : S' ⟶ S} {b : X' ⟶ X} {p' : X' ⟶ S'} (hp : IsPullback b p' p a)`. |
| Quasi-compact and quasi-separated `g : T → S'` | `{g : T ⟶ S'} [QuasiCompact g] [QuasiSeparated g]`. No finite-type hypothesis is imposed. |
| Second fibre product and its projections `e,h` | Section parameters `{T Y : Scheme.{u}} {e : Y ⟶ T}`, binder `{h : Y ⟶ X'}`, and `(sq : IsPullback e h g p')`. These allow any representative of the specified fibre product, including the chosen one. |
| Coefficient sheaves on `T_et` | `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`. This is the established module-valued-sheaf encoding used by `sk-def-bc`. |
| Canonical `b_F` | `Etale.baseChangeHomologyMap Λ sq q F`, the homology of the derived exchange on `F[0]`. |
| (1) Monomorphism for every `F` | First conjunct `∀ F, Mono (Etale.baseChangeHomologyMap Λ sq q F)`. |
| Every monomorphism `F ↪ G` | Each of the other two conjuncts quantifies over `{F G}` and `(α : F ⟶ G) [Mono α]`. |
| (2) Induced cokernel map is mono | Second conjunct is `Mono (cokernel.map ... source.map α target.map α (Etale.baseChangeHomologyMap_naturality Λ sq q α))`. These are exactly the natural coefficient maps, not arbitrary arrows. |
| (3) `G` injective as a module sheaf | `[Injective G]`, using Mathlib's extension-across-every-monomorphism definition in this very category. |
| Coefficient map kills the image of `b_F` | The proof argument of `cokernel.desc` is `Etale.baseChangeHomologyMap_comp_map_eq_zero_of_injective Λ sq (by lia) α`; its full signature is `baseChangeHomologyMap Λ sq q F ≫ (baseChangeTargetFunctor Λ e h q).map α = 0`. Positivity supplies `q ≠ 0`. |
| Induced `Coker(b_F) → R^q h_* e⁻¹G` is mono | Third conjunct is `Mono (cokernel.desc ... ((Etale.baseChangeTargetFunctor Λ e h q).map α) ...)`. |
| Kernels, cokernels, monos, injectives in the indicated abelian categories | `Mono`, `cokernel.map`, `cokernel.desc`, and `Injective` are instantiated in the module-sheaf categories; the source/target functors land in sheaves on `X'_et`. There is no underlying-set replacement or abelian-group-only injectivity assumption. |
| No torsion or invertibility condition | Neither the section parameters nor the theorem has such a condition. |

The vanishing in (3) is explicitly available as the named upstream lemma used in
the cokernel descent. Its presence as an argument of `cokernel.desc` supplies
that clause without a redundant restatement. The source and target functors in
Defs.lean are the established derived encodings of `(f')⁻¹R^qg_*` and
`R^qh_*e⁻¹`, respectively, as already fixed by `sk-def-bc`.

Dependency declarations read and used (no replacement definitions):

- `sk-def-bc`: `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`,
  `AlgebraicGeometry.Etale.BaseChangeProperty`, `UniversalBaseChangeProperty`,
  `baseChangeHomologyMap`, `baseChangeSourceFunctor`,
  `baseChangeTargetFunctor`, and `baseChangeHomologyMap_naturality` (with the
  `AlgebraicGeometry.Etale` prefix on all these names). Read the complete file.
- `def-weil-pbc-etale-sheaves`: its mixed record includes
  `CategoryTheory.Sheaf` from `Mathlib.CategoryTheory.Sites.Sheaf`; the theorem
  uses that category with `ModuleCat Λ`. Read the recorded
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves` source in the shared checkout;
  its extra set-sheaf predicates and torsion notions are not needed here.
- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`; the ambient sheaf categories have
  their existing abelian structures.
- `def-sp-enough-injectives`: `CategoryTheory.EnoughInjectives` and
  `CategoryTheory.Injective`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`. Read both full classes,
  including `Injective.factors`, and the injective-presentation structure.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
  The existing theorem encodes the universal property as `IsPullback`, so the
  choice of representative introduces no extra mathematical hypothesis.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` (included in the node's
  recorded declarations); its separate `LocallyOfFiniteType` notion is unused.
- `def-weil-quasi-separated-morphism`: `AlgebraicGeometry.QuasiSeparated`,
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`; read its
  `QuasiCompact (pullback.diagonal f)` field.

Also read `baseChangeHomologyMap_comp_map_eq_zero_of_injective` in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.LongExactSequence`,
lines 76–82. It asserts precisely the vanishing needed by (3), in nonzero degree,
for any morphism into an injective module sheaf.

Edge cases checked: `q = 1` requires exactly universal degree-zero BC, with no
lower cumulative hypothesis; `q = 0` is explicitly excluded by the node and by
`hq`. Zero coefficient ring and zero coefficient sheaves are permitted. Empty
schemes and identity base changes are permitted, since neither pullback square
nor the morphism binders has a nonemptiness restriction. Identity coefficient
monomorphisms are permitted. No smoothness, properness, finite type, torsion,
or invertibility condition appears. The universe convention is the same as the
recorded BC interface: `Scheme.{u}` and module sheaves in `u+1`, allowing larger
objects by increasing `u`; there is no independent smaller test universe.

Searches performed (2026-10-17):

- `msearch.py ... leanfinder`, query: "Under universal degree q minus one etale
  base change, the degree q base change map is mono, its cokernel preserves
  monomorphisms, and embeds into higher direct image of an injective coefficient
  sheaf". Eight hits on generic monos, injective resolutions, Mayer–Vietoris,
  and locally injective sheaves; no exact Mathlib theorem.
- `msearch.py ... loogle`, query:
  `CategoryTheory.Limits.cokernel.map, CategoryTheory.Mono`. One hit:
  `CategoryTheory.Abelian.mono_cokernel_map_of_isPullback`, a generic categorical
  fact, not the three-clause étale theorem.
- `msearch.py ... grep`, query:
  `mono_baseChangeHomologyMap|mono_cokernelMap|mono_cokernelDesc|UniversalBaseChangeProperty`.
  One Mathlib hit, `ShortComplex.Exact.mono_cokernelDesc`; not the theorem.
- `msearch.py ... leansearch`, query: "universal etale higher direct image base
  change critical degree injectivity cokernel". Eight hits on universally
  injective morphisms, étale stability, module cokernels, injective syzygies and
  cotangent complexes; no exact Mathlib theorem.
- `rg` in upstream `WeilConjectures` for
  `mono_baseChangeHomologyMap_and_cokernel|lem-sbc-module-bc-injectivity`
  found the exact theorem at CriticalMap.lean:204 and its aggregator docstring.
  The literal new DAG id has no upstream tag; the theorem's docstring uses
  `sbc-lem-bc-injectivity`, and its mathematical statement is the match.
- `rg` in the project `lean/Sheaf` for those same names found no duplicate.
  A broader search for base-change injectivity and cokernel names also found
  no second declaration of this theorem there.

No statement fault or disputed clause was found. No new nodes and no dependency
modules are added. The delivery dry run checks the existing declaration through
its generated `#check @...` probe with `scompile.py`; no new file requires
compilation. No delivery is pushed by this worker.

## Second reading by Q31

I independently opened the sandbox node, the unchanged repository node, Stacks
`etale-cohomology.tex` lines 16844–16944 (the preceding BC convention, Tag 0F02,
and Lemma `lemma-base-change-q-injective`, Tag 0F03, including its proof),
`CriticalMap.lean` in full, `Injectivity/LongExactSequence.lean` in full, and
`SmoothBaseChange/Defs.lean` in full. I also read the current module returned by
`scompile.py --source WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.CriticalMap`;
it agrees with the local source. No repair note exists for this item.

The node's objects, hypotheses and conclusions, matched independently:

| Node item | Lean rendering and verdict |
| --- | --- |
| Arbitrary schemes X, S and morphism f | `universe u`, section `{X S : Scheme.{u}} {p : X ⟶ S}`; `p` renders f. Exact. |
| Arbitrary commutative ring Λ | Section `(Λ : Type (u + 1)) [CommRing Λ]`; no field, characteristic, nonzero, torsion, or invertibility assumption. Exact. |
| Integer q at least one | `{q : ℤ} (hq : 1 ≤ q)`. Exact. |
| Universal BC in degree q−1 | `(huniv : Etale.UniversalBaseChangeProperty Λ p (q - 1))`; Defs quantifies over every preliminary Cartesian base change and then every qcqs g and every module sheaf, in that single degree. Exact. |
| Every a : S' → S, with X' the base change | `{S' X' : Scheme.{u}} {a : S' ⟶ S} {b : X' ⟶ X} {p' : X' ⟶ S'} (hp : IsPullback b p' p a)`. Exact universal-property formulation; chosen fibre products are included. |
| Every T and qcqs g : T → S' | Section `{T : Scheme.{u}}`, theorem `{g : T ⟶ S'} [QuasiCompact g] [QuasiSeparated g]`. Exact; no locally-finite-type, separated, smooth, or proper hypothesis. |
| Fibre product Y and projections e : Y → T, h : Y → X' | Section `{Y : Scheme.{u}} {e : Y ⟶ T}`, theorem `{h : Y ⟶ X'} (sq : IsPullback e h g p')`. Exact; the order of arguments gives e ≫ g = h ≫ p'. |
| Sheaves F and G of Λ-modules on T_et | `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`. Exact established six-functor encoding, explicitly permitted by the mixed record of `def-weil-pbc-etale-sheaves`. |
| The canonical map b_F | `Etale.baseChangeHomologyMap Λ sq q F`. Defs constructs it as homology of the derived exchange, evaluated on F[0], through `baseChangeHomologyNatTrans`; no arbitrary comparison arrow. Exact. |
| Source and target of b_F | `baseChangeSourceFunctor Λ p' g q` is H^q(p'^* Rg_* F[0]); `baseChangeTargetFunctor Λ e h q` is H^q(Rh_* e^* F[0]). Exact derived realizations of p'⁻¹R^qg_*F and R^qh_*e⁻¹F, since inverse image is exact. |
| Conclusion (1), b_F mono for every F | First conjunct `∀ F, Mono (Etale.baseChangeHomologyMap Λ sq q F)`. Exact. |
| Every coefficient monomorphism F → G in (2) | Second conjunct `∀ {F G} (α : F ⟶ G) [Mono α], ...`. Exact; arbitrary categorical monos, without requiring chosen subset presentations. |
| Conclusion (2), the induced cokernel map is mono | `Mono (cokernel.map ... (baseChangeSourceFunctor ...).map α (baseChangeTargetFunctor ...).map α (baseChangeHomologyMap_naturality ... α))`. Exact canonical map induced by the naturality square. |
| Additional hypothesis of (3), G injective | Third conjunct adds `[Injective G]` to the same arbitrary monomorphism α. Exact injectivity in the module-sheaf category, not injectivity of the underlying abelian sheaf. |
| Conclusion (3a), coefficient map kills image of b_F | The final `cokernel.desc` takes the equality supplied by `Etale.baseChangeHomologyMap_comp_map_eq_zero_of_injective Λ sq (by lia) α`. I read its full signature: `baseChangeHomologyMap ... F ≫ (baseChangeTargetFunctor ...).map α = 0`. Exact; q ≥ 1 supplies q ≠ 0. This is an existing named theorem, not an omitted or assumed vanishing. |
| Conclusion (3b), induced map from Coker(b_F) is mono | Final conjunct `Mono (cokernel.desc (baseChangeHomologyMap ... F) ((baseChangeTargetFunctor ...).map α) ...)`. Exact canonical descent into R^qh_*e⁻¹G. |
| Abelian categories, kernels, cokernels and monos | The coefficient arrows lie in module sheaves on T_et, while b_F and its cokernels lie in module sheaves on X'_et. `Mono`, `cokernel.map`, `cokernel.desc` use these categories, not sets or stalks. Exact. |
| Quantifier order | Λ, f, q, universal hypothesis, preliminary base change, qcqs test square, then F or F,G,α; injectivity of G is required only for (3). Exact. |

For the source comparison: Stacks' BC convention is cumulative and uses abelian
sheaves annihilated by n. This node explicitly names the arbitrary-ring,
single-predecessor-degree generalization and the exact existing theorem as its
source. Reading the Stacks proof confirms that only degree q−1 is used. Its
embedding into an injective module sheaf, exact inverse image, injective
acyclicity, and comparison of the two long exact sequences work for any
commutative Λ. The existing proof follows precisely those steps: obtain BC for
p' from `huniv`; embed F into an injective for (1); use the exact sequences and
vanishing on G for (3); embed G into an injective and factor the cokernel maps
for (2). There is no ambient source assumption requiring smoothness or
invertibility here. The absence of those assumptions is intentional and valid.

I opened each dependency node and the relevant recorded declarations:
`sk-def-bc` uses the above `Defs` declarations; `def-weil-pbc-etale-sheaves`
records both sheaf-module encodings (its current `EtaleSheaves.lean` was also
read); `def-sp-abelian` is Mathlib's `Abelian` (Basic.lean:112);
`def-sp-enough-injectives` uses `Injective.factors`, `InjectivePresentation`,
and `EnoughInjectives` (Preadditive/Injective/Basic.lean:31–67);
`def-pc-scheme` uses `Scheme` and `Scheme.Hom` (Scheme.lean:42,74);
`def-pc-fibre-product` uses `pullback`, its projections and universal lift
(HasPullback.lean:95–130); the corresponding `IsPullback` formulation is the
universal property of those same fibre products.
`def-weil-finite-type-morphism` includes `QuasiCompact`, whose actual field is
compactness of inverse images of compact opens (QuasiCompact.lean:43), and
`def-weil-quasi-separated-morphism` is `QuasiSeparated`, whose field is
`QuasiCompact (pullback.diagonal f)` (QuasiSeparated.lean:50). All interfaces
used here are usable. No dependency module or new definition node is needed.

Edge cases: q = 1 is covered with only universal degree-zero BC; q = 0 and
negative q are excluded exactly as in the node. Zero Λ and zero F,G are
allowed. Empty schemes, identity preliminary base changes, identity test
maps, and identity coefficient monomorphisms are allowed. No indexed family
occurs, so an empty index set adds no case. The unrestricted universe u and
the existing module-sheaf convention `u+1` match the dependency: the universal
hypothesis and tested squares use the same Scheme universe, without a smaller
independent test universe or extra equality between site universes. Every
variable in the copied signature is bound either there or in the section;
there is no new auto-implicit parameter.

Independent searches on 2026-10-17, with different queries from the first reader:

- LeanFinder via `msearch.py`: "Dimension shifting for etale sheaves makes the
  first unknown base change morphism injective and embeds its cokernel into
  the higher direct image of an injective envelope". Eight hits, including
  `DerivedCategory.to_singleFunctor_obj_eq_zero_of_injective`, generic
  injective replacement results, and locally injective sheaves. No exact
  Mathlib theorem.
- Loogle via `msearch.py`: `CategoryTheory.Injective, "cokernel"`.
  Zero hits.
- Grep via `msearch.py`: `baseChange.*[Ii]nject|cokernel.*[Ii]nject|mono_cokernel`.
  Twenty-five hits, chiefly tensor-product base change, cotangent modules and
  linear maps. No exact étale theorem.
- LeanSearch via `msearch.py`: "A natural map on higher direct images of etale
  module sheaves is a monomorphism in the next degree and its cokernel is
  monotone under inclusion of coefficient sheaves". Eight generic hits,
  including `Abelian.mono_of_epi_of_epi_of_mono`, injective resolution maps,
  and sheaf-image monos; none states this theorem.
- Direct `rg` over upstream SixFunctors and project `lean/Sheaf` for
  `critical.*map|cokernel.*base.change|cokernelDesc|mono_cokernel|baseChangeHomologyMap_and_cokernel`
  locates the exact upstream aggregate theorem and its three components.
  Project hits are generic cokernel helpers or a citation in
  `FieldFailureOfCumulativeBaseChange.lean`, not another declaration of this
  statement. This independently confirms the `existing: true` choice.

No mathematical mismatch was found, so I changed only this report by appending
this second reading. The worker's Lean binding is retained verbatim. A direct
text comparison confirms `lean.statement` equals the existing source signature
from `theorem` through the type, before `:=`; comparison against the repository
node confirms `lean` is the only changed node field. No `statement_change` or
citer audit is needed. There are no delivered Lean modules, new declarations,
new proofs, hollow definitions, or postponed theorems. The existing upstream
module supplies source and proof documentation under its older blueprint id;
its reuse does not introduce a second declaration to retag.

Validation: `deliver2.py Q31 lem-sbc-module-bc-injectivity --no-push`
completed successfully: `OK (dry run): commit 80c3678518 passes the preflight
and compiles; nothing pushed`. It checked the existing declaration through
its generated Lean probe using the prescribed compilation wrapper. No Lean
error or warning was reported. This delivery consists only of the node's
existing-declaration binding and this report.
