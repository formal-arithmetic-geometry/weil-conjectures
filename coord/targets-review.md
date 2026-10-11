> Copied from the side copy `~/weil-stage3-prep` (branch `stage3-prep`, commit e35c648c2) for coord/stage3-prep.md. It reviews the side copy's `lean/Challenge.lean` and `lean/TargetsCheck.lean` at 2e1c48405; stage 3 is not started and the live `lean/` has neither file yet.

# Target review

Written to the contract in `stages/2-statements.md` §4 and `AGENTS.md` §4. One section per target node.

## thm-weil-pbc-bounded-below

- **Reviewer:** S3-T, a sub-agent of L. S3-T did not write the target statement; `lean/Challenge.lean` and `lean/TargetsCheck.lean` were written by S3-B.
- **Date:** 2026-10-11 18:13 UTC.
- **Reviewed:** side copy `~/weil-stage3-prep`, branch `stage3-prep`. `Challenge.lean` and `TargetsCheck.lean` are as of commit 2e1c48405 and are unchanged at HEAD 5014107dc. The library is slopmaster2 7d675a263; `Proper.lean` in the side copy is byte-identical to `~/weil-conjectures-slopmaster2`.
- **Verdict: ACCEPT WITH NOTES.** No defect in either target statement or in the definitions they use. The notes, listed under open points below, are for the human. None of them requires a change to `Challenge.lean`.

### 1. The paper's statement

DAG node `thm-weil-pbc-bounded-below` (chapter `sec-proper-base-change`, unit `sk-thm-properbasechange`, blueprint order 1320). Its `statement` field, word for word:

> For a cartesian square [def-weil-pbc-cartesian-square] with $f$ proper and every $K\in\Dplus(X_{\Et})$ with torsion cohomology,
> $$\Ex_{\square,K}:g^{-1}Rf_*K\xrightarrow{\sim}Rf'_*g'^{-1}K$$
> is an isomorphism in $\Dplus(Y'_{\Et})$.

The statement depends on these nodes: def-weil-pbc-cartesian-square, def-weil-pbc-derived-categories, def-weil-pbc-scheme-conventions, def-weil-proper-morphism, def-weil-pbc-torsion-etale-sheaf and def-weil-pbc-derived-exchange.

The sources are as follows.

- **Stacks 0DDE** (`etale-cohomology.tex`, lemma-proper-base-change): "Let $f : X \to Y$ be a proper morphism of schemes. Let $g : Y' \to Y$ be a morphism of schemes. Set $X' = Y' \times_Y X$ and denote $f' : X' \to Y'$ and $g' : X' \to X$ the projections. Let $E \in D^+(X_\etale)$ have torsion cohomology sheaves. Then the base change map (equation-base-change) $g^{-1}Rf_*E \to Rf'_*(g')^{-1}E$ is an isomorphism." In equation-base-change, $D(X_\etale)$ is built from abelian sheaves, with $\mathbf Z$ as the ring.
- **Stacks 095T**, theorem-proper-base-change: the same cartesian diagram with $f$ proper; for an abelian torsion sheaf $\mathcal F$ on $X_\etale$, the map $g^{-1}Rf_*\mathcal F \to Rf'_*(g')^{-1}\mathcal F$ is an isomorphism.

The node's statement is 0DDE. 095T is its case $E=\mathcal F[0]$.

### 2. The Lean statements (`lean/Challenge.lean`)

Common variables: `Λ : Type (u+1)` with `[CommRing Λ]`, and `{X Y X' Y' : Scheme.{u}}` with `{f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}`.

```lean
theorem AlgebraicGeometry.Etale.isIso_baseChange_of_isProper [IsProper f]
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.Plus.torsionHomology Λ X K) :
    IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)

theorem AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring
    (hΛ : IsAddTorsion Λ) [IsProper f] (sq : IsPullback g' f' f g) :
    IsIso (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq)
```

These are the library's declarations at `WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/Proper.lean`, lines 99–141. They are also the node's `lean.declarations` and `blueprint_lean`.

### 3. Clause by clause (first target)

| Node | Lean | Match |
|---|---|---|
| Cartesian square $\square=(f,f',g,g',\alpha)$, with $X'\to X$ along $g'$, $X'\to Y'$ along $f'$, $X\to Y$ along $f$, $Y'\to Y$ along $g$, and a chosen $\alpha: X'\cong X\times_YY'$ | `sq : IsPullback g' f' f g`: the square with top `g'`, left `f'`, right `f`, bottom `g` is a pullback | Same orientation. `IsPullback` asserts that some identification with the fibre product exists, but does not choose one. The difference changes nothing: def-weil-pbc-derived-exchange says that of the square "only the equality $fg'=gf'$ enters", and the Lean map uses only `sq.toCommSq` (`sq.w`). The statement is invariant under the choice of $\alpha$. |
| $f$ proper (def-weil-proper-morphism: separated, of finite type, universally closed) | `[IsProper f]` (Mathlib: `IsSeparated`, `UniversallyClosed`, `LocallyOfFiniteType`) | Equal. Finite type is locally of finite type plus quasi-compact, and universally closed implies quasi-compact (Mathlib instance; the node's Lean record says the same). |
| No hypothesis on $g$ | none | Equal. |
| For every $K\in D^+(X_\Et)$ | `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat Λ))`, universally quantified | For Λ = ℤ, equal (see §5). Mathlib's `DerivedCategory.Plus` is the full subcategory of the $K$ with $K\in D^{\ge n}$ for some $n$, which is the node's definition. |
| $K$ has torsion cohomology: every $\mathcal H^i(K)$, as an abelian sheaf, is torsion | `hK : torsionHomology Λ X K`: for every `n : ℤ`, `IsTorsionSheaf` of `(DerivedCategory.Plus.homologyFunctor _ n).obj K` | Equal (see §4.3). |
| $\Ex_{\square,K}: g^{-1}Rf_*K\to Rf'_*g'^{-1}K$ is an isomorphism in $D^+(Y'_\Et)$ | `IsIso ((derivedBaseChangeMapPlus (ModuleCat Λ) sq.toCommSq).app K)`, a morphism of `DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat Λ))` | Equal (see §4.2). The conclusion is not weakened: `IsIso` is taken in $D^+$, a full subcategory of $D$, so being an isomorphism there is the same as in $D$. |

The Lean statement adds one quantifier the node does not have, `∀ Λ : Type (u+1), [CommRing Λ]`. It has no other extra hypothesis. Section 5 discusses it.

The hypotheses are not vacuous. Proper morphisms and pullback squares exist, and so do non-zero $K$ with torsion cohomology. Mathlib's derived category of a non-zero abelian category is not trivial.

### 4. The definitions, down to Mathlib

`#print axioms` was run on every definition and instance in the elaborated types (`.sandbox/S3T/Probe.lean` and `Ax.lean`). The types of both targets mention 56 and 57 constants respectively. None of these constants is a definition, instance or opaque that reaches `sorryAx`, and none is an axiom. The 14 theorem-valued instance terms in the types are all sorry-free:

- `hasSheafify_smallEtaleTopology`
- `isGrothendieckAbelian_sheaf_smallEtaleTopology`
- `preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian`
- `preservesFiniteLimits_upperStar`
- `ModuleCat.isGrothendieckAbelian_of_commRing`
- `IsGrothendieckAbelian.enoughInjectives`
- the remaining eight, which are routine (additivity, preserved colimits, shift functors, zero objects).

The following definitions are sorry-free (axioms `propext`, `Classical.choice`, `Quot.sound`):

- `derivedBaseChangeMapPlus`
- `torsionHomology`
- `HasDerivedCategory.ofIsGrothendieckAbelian`
- the bridge `Scheme.isTorsionSheaf_iff_isTorsion`
- `baseChange_eq_derivedBaseChangeMapPlus`

The statements therefore contain no hollow definition, and nothing in them depends on `sorry`. `#print axioms` of the two targets shows `sorryAx` only through their proofs. The docstring of `Etale.upperStar` still says that sheafification is "still sorried through `hasSheafify_of_essentiallySmall`"; that is no longer true at 7d675a263, where it has a sorry-free proof.

#### 4.1 Sites, sheaves, pullback and pushforward

- **$X_\Et$:** `X.smallEtaleTopology` (Mathlib) on `X.Etale`, the étale schemes over $X$. This is the small étale site of def-weil-pbc-etale-site.
- **Sheaves:** `Sheaf X.smallEtaleTopology (ModuleCat.{u+1} Λ)`, Mathlib sheaves with values in Λ-modules. This is $\Mod(X_\Et,\Lambda)$.
- **$g_*$:** `Etale.lowerStar` (`UpperLowerStar/Defs.lean`): `sheafPushforwardContinuous` along base change, $(g_*G)(V)=G(V\times_YZ)$. This is the usual direct image.
- **$g^{-1}$:** `Etale.upperStar`: pointwise left Kan extension followed by sheafification. It is left adjoint to `lowerStar` (`upperStarLowerStarAdjunction`) and exact (`preservesFiniteLimits_upperStar`, sorry-free). This is the usual inverse image, unique up to unique isomorphism as the left adjoint of $g_*$.

#### 4.2 The derived exchange map (def-weil-pbc-derived-exchange)

The node defines $\Ex_\square$ as the mate of $\theta^D_\square$ with respect to the derived adjunctions $f^{-1}\dashv Rf_*$ and $f'^{-1}\dashv Rf'_*$.

In Lean, `derivedBaseChangeMapPlus` (`BaseChange/Derived.lean:129`) is `Functor.rightDerivedDesc` of `baseChangeMapHomotopyPlus`. That is the transformation out of the right derived functor $Rf_*^+\circ g^*$ induced by the underived map `Etale.baseChangeMap`. `Etale.baseChangeMap` is the `mateEquiv` of `squareUpperStarIso` (built from `upperStarComp` and `sq.w`) with respect to $f^*\dashv f_*$ and $f'^*\dashv f'_*$. That is the node's underived exchange, and def-weil-pbc-cartesian-square's $\theta_\square$.

The library proves, sorry-free, that this Lean map is the node's map. `Etale.baseChange_eq_derivedBaseChangeMapPlus` (`BaseChange/DerivedComparison.lean:169`) shows `derivedBaseChangeMapPlus = Etale.baseChange`. `Etale.baseChange` is defined in `MorphismDefs.lean:243` as the composite of:

1. the unit of the derived adjunction `derivedUpperStarLowerStarAdjunctionPlus f'`;
2. the derived square isomorphism `pullbackSquareComparison` (built from `upperStarPlusComp` and `sq.w`);
3. the counit of `derivedUpperStarLowerStarAdjunctionPlus f`.

This is the node's explicit formula $Rf'_*g'^{-1}\varepsilon_f\circ Rf'_*\theta^D\circ\eta_{f'}$.

Two further correspondences complete the match:

- **$g^{-1}$ on $D^+$:** `mapDerivedCategoryPlus` of the exact functor `upperStar`. This is def-weil-pbc-derived-inverse-image.
- **$Rf_*$:** `rightDerivedFunctorPlus` of `lowerStar`, computed with the global `HasDerivedCategory.ofIsGrothendieckAbelian`.

#### 4.3 Torsion cohomology (def-weil-pbc-derived-categories, def-weil-pbc-torsion-etale-sheaf)

- **Cohomology sheaves:** `DerivedCategory.Plus.homologyFunctor _ n` (Mathlib). This is $\mathcal H^n$.
- **`Scheme.IsTorsionSheaf F`** (`TorsionSheaf.lean`): for every separably closed field `Ω : Type u` and every `s : Spec Ω ⟶ X`, the stalk `(pointSmallEtale s).sheafFiber.obj F` is a torsion abelian group. Torsion refers to the additive group, not to the Λ-module structure, as in the node ("as a sheaf of abelian groups").
- **The node's definition:** $F$ is torsion when $\varinjlim_nF[n]\to F$ is an isomorphism.
- **Agreement:**
  1. The sorry-free bridge `isTorsionSheaf_iff_isTorsion` identifies `IsTorsionSheaf` with `Sheaf.IsTorsion` of the underlying abelian sheaf: every section is locally of finite order (`WeilConjectures/Mathlib/.../SheafCohomology/Basic.lean:73`).
  2. That condition is equivalent to the node's colimit condition. The colimit of the subsheaves $F[n]$ is the sheafified union, and the map onto $F$ is an isomorphism exactly when every section is locally in some $F[n]$. This equivalence is the node's own pointer lem-weil-pbc-torsion-sheaf-characterizations and Stacks Section 0DDB / 03SA.
- **Universe of `Ω`:** stalks are tested only at fields in `Type u`, and that loses nothing. Every point of `X : Scheme.{u}` has a geometric point over a separable closure of its residue field, and that field lies in `Type u`. These points form a conservative family (Stacks 03PU).

### 5. Λ-modules instead of abelian sheaves

The node, like Stacks 0DDE, is about $D^+(X_\Et)=D^+(\Ab(X_\Et))$. The Lean statement is about $D^+(X_\Et,\Lambda)$ for every commutative `Λ : Type (u+1)`.

- **Λ = ℤ is admitted.** `ℤ : Type` does not live in `Type (u+1)`, but `ULift.{u+1} ℤ` does. `#check @isIso_baseChange_of_isProper.{u} (ULift.{u+1} ℤ)` elaborates (`.sandbox/S3T/Spec.lean`).
- **That instance is the node's statement.** `ModuleCat.{u+1} (ULift ℤ)` is equivalent to `AddCommGrpCat.{u+1}`, the category the DAG's Lean record of def-weil-pbc-derived-categories uses for $\Ab(T_\Et)$. Under this equivalence:
  - sheaves, $g_*$, $g^*$, $D^+$, $Rf_*$, the exchange map and "torsion as abelian groups" all correspond;
  - the equivalence is exact and commutes with the adjunctions, so it carries one exchange map to the other.

  So the Λ = ULift ℤ instance of the first target means exactly the node's statement.
- **The Lean statement is stronger than the node.** For general Λ it is also true. Restriction of scalars to ℤ is exact and conservative on $D^+$. It commutes with $g^{-1}$ and with $Rf_*$, because injective Λ-sheaves are $f_*$-acyclic as abelian sheaves (Stacks, Cohomology on Sites, 03FD and the restriction-of-scalars lemmas). It carries the Λ-exchange map to the ℤ-exchange map. The library's own docstring says the same. The DAG's def-weil-pbc-derived-categories already defines $D(T_\Et,R)$ for any ring $R$, with torsion read on the underlying abelian sheaves. The generalisation is therefore faithful: it adds no hypothesis, drops none and weakens nothing, and its ℤ case is the node. What it adds is proof burden (open point 1).
- **Universes.** Schemes are in `u` and coefficients in `u+1`. This is the library's convention, and Mathlib forces the ring and the modules to share a universe. The small étale site `X.Etale` has objects in `Type (u+1)`, so sheaves with values in `u+1`-groups are the natural category. The theorem is universe-insensitive; no level is degenerate.

### 6. The second target (`..._of_isAddTorsion_ring`)

- **What it states.** For Λ torsion as an additive group (for example `ULift (ZMod 25)`, checked), the natural transformation `derivedBaseChangeMapPlus` is an isomorphism of functors on $D^+(X_\Et,\Lambda)$.
- **Relation to the node.** It is not a separate clause of the node. It is a corollary of the first target, and the library proves it from the first target in three lines with no other sorry. Every sheaf of Λ-modules is torsion (`torsionHomology_of_isTorsion`, sorry-free), and `NatIso.isIso_of_isIso_app` does the rest. It neither adds a hypothesis to the node nor weakens it. It adds no proof burden beyond the first target, and the comparator still has to see it proved.
- **It does not cover Λ = ℤ.** ℤ is not torsion; this was checked in Lean. So it does not replace the first target.
- **Citation.** The library tags it `@[stacks 095T]`. 095T is the case of a single abelian torsion sheaf in degree 0, which is the first target with $K=\mathcal F[0]$ and Λ = ℤ. It is not the torsion-ring functor isomorphism. The correct reading of the second target is "0DDE (equivalently SGA 4 XII 5.1) for a torsion coefficient ring, as an isomorphism of functors". The attribution is loose, but the statement is right.
- **Open point 2** below records whether to keep it as a target.

### 7. TargetsCheck and the type check

- `lean/TargetsCheck.lean` imports exactly `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`. That is the one module that defines both targets, and the file imports nothing else.
- `lean/Challenge.lean` imports three modules: `BaseChange.Derived` (`derivedBaseChangeMapPlus`), `BaseChangeTheorems.TorsionSheaf` (`torsionHomology`, and all of Mathlib), and `Mathlib/Algebra/Category/ModuleCat/AB` (the high-priority instance `ModuleCat.isGrothendieckAbelian_of_commRing`). Without that instance the elaborated types differ from the library's, although the propositions are the same. These are the modules that define what the statements use.
- `cd ~/weil-stage3-prep && tools/target_types.sh check` was rerun for this review (finished before 18:13 UTC) on `.olean` files newer than both sources. Its output was "All 2 target statements agree with lean/Challenge.lean." Axioms of both targets in the library: `propext, sorryAx, Classical.choice, Quot.sound`, where `sorryAx` comes from the proof route (stage 3).

### 8. Open points for the human

1. **The general-Λ form is stronger than the node, and the library's proof route of that form uses a lemma believed false.** The statement is right; the issue is the proof route.
   - The first target goes through `hasTorsionBaseChange_of_isProper` → `ProjectiveLine.lean:121` → `hasTorsionBaseChange_of_hasInjectiveAcyclicity`.
   - `coord/HUMAN.md` (entries of 2026-10-09 evening and the addendum of 2026-10-10 10:14) records that this lemma is not provable as stated for general Λ. There is a counterexample with Λ = ℤ[x₁,x₂,…]/(pⁱxᵢ, xᵢxⱼ).
   - The target itself is still true for every Λ, by restriction of scalars to ℤ.
   - Stage 3 must therefore prove the target either through a ℤ-only (or torsion-Λ) version of the route followed by restriction of scalars, or after the fix the human chooses for that lemma: option (b), add `IsAddTorsion Λ`, or option (d).
   - Neither the target statement nor the node needs to change. If the human prefers the target restricted to Λ = ℤ, the node is still matched, but `Challenge.lean` and the library declaration would both change (`AGENTS.md` §4: only on the human's instruction).
2. **The second target is an extra target, not a clause of the node.** It is implied sorry-free by the first, so keeping it costs nothing. Its `@[stacks 095T]` attribution should read 0DDE / SGA 4 XII 5.1 for torsion Λ. Recommendation: keep it. Otherwise drop it from `Challenge.lean` on the human's word.
3. **Λ = ℤ is reached as `ULift.{u+1} ℤ`, through the equivalence `ModuleCat (ULift ℤ) ≌ AddCommGrpCat`.** That identification is mathematical and is not formalised in the library. It is standard and changes nothing, but no Lean theorem states the node verbatim with abelian sheaves.
4. **This review must be repeated when the definitions change.** A target's review holds only for the definitions as they are, so it must be redone if any of `derivedBaseChangeMapPlus`, `baseChangeMap`, `upperStar`/`lowerStar`, `IsTorsionSheaf` or `torsionHomology` changes in stage 3 (`stages/3-proving-and-pruning.md` §3). The stale "still sorried" remark in the `Etale.upperStar` docstring is cosmetic.
5. **Not part of this review.** S3-B's report lists the comparator configuration as undecided: which solution module to use (`TargetsCheck` is the natural one) and where its config lives. That is a decision for the final check, not a question about what the statements mean. The review checked S3-B's points (a)–(d) independently and agrees with them.
