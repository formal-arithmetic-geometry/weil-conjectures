## Worker report

Item: `lem-sfb-relative-abel-nonspecial-chart`, group Q22, stage 2.
Module: `Sheaf.AlgebraicGeometry.RelativeAbelNonspecialChart`.
Main declaration: `AlgebraicGeometry.RelativeAbelChart.relative_abel_nonspecial_chart`.

The theorem states the full relative chart, including its maps on arbitrary test schemes.
Only its proof is `sorry`. The eight helper definitions contain actual data or explicit
predicates; no helper theorem, axiom, arbitrary comparison map, or hollow object is introduced.
They are specializations of recorded notions, not independent replacements for them.
The theorem docstring carries all eight steps of the node's natural-language proof.

Source read: Deligne, *Le lemme de Gabber*, Lemma 4.5 and the preceding Lemma 4.4,
printed p.143, https://www.numdam.org/item/AST_1985__127__131_0.pdf (PDF page 13, zero based).
Also read the current blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`,
part (3), at `literature/blueprint/latest/blueprint/sec-six-functors-basics/`.
The item is a supporting lemma, not the blueprint unit's own statement. No statement
correction or statement dispute is needed.

Hypothesis-by-hypothesis correspondence:

| Node hypothesis | Lean rendering |
| --- | --- |
| Schemes X, S; locally Noetherian S | `{X S : Scheme.{u}}`, `[IsLocallyNoetherian S]` |
| Flat, finitely presented projective-bundle morphism | `[Flat f]`, `[LocallyOfFinitePresentation f]`, `hf : IsProjectiveBundle f`; projective-bundle properness supplies quasi-compactness and separatedness, so local finite presentation here is equivalent to finite presentation under the other hypotheses |
| Nonempty connected reduced nodal geometric fibres | `hnodal : HasNodalGeometricFibres f`, the recorded geometric-fibre predicate: connected dimension-one geometric fibres, smooth except at completed nodal local rings; smooth local rings and these nodal completed local rings are reduced, so this entails the reduced condition |
| Picard fppf sheaf represented by algebraic space P | `P : AlgebraicSpace S`, `eP : P.obj.obj ⋙ uliftFunctor ≅ (picardFunctor f).obj` |
| Open subgroup A | `A : AlgebraicSpace.OpenSubspace P`; `hA` says on every test that its sections, transported by eP, are exactly a subgroup of the existing `picardFunctorGrp` |
| s, a separable closure of its residue field, and the associated geometric point | `s`, `K`, `[Field K]`, `[Algebra (S.residueField s) K]`, `[IsSepClosure (S.residueField s) K]`, `q`, `hq` |
| g = dim H¹(O) | `hg`, using `cohomology` of the tensor unit in degree 1 and `Module.finrank K` |
| Effective divisor Es | `Es`, `hEs : Es.IsInvertible` |
| g distinct smooth K-points constituting Es | `x : Fin g → (Spec K ⟶ pullback f q)`, `hx`, `hsection`, `hsmooth`, `hpoints : Es = ⨅ i, (x i).ker`; intersection of the ideals is their scheme-theoretic union |
| H¹(O(Es)) = 0 | `hH1 : Subsingleton (cohomology ... Es.toModulesᵛ 1)` |
| H⁰(O(Es)) = K | `hH0 : Module.finrank K (cohomology ... Es.toModulesᵛ 0) = 1`, the equivalent dimension-one vector-space assertion |

Conclusion-by-conclusion correspondence:

| Node conclusion | Lean rendering |
| --- | --- |
| Etale neighbourhood of the fixed geometric point | existential `S'`, `h`, `q'`, `hq' : q' ≫ h = q`, and `Etale h` |
| It may be affine Noetherian | `IsAffine S' ∧ IsNoetherian S'` |
| Relative effective Cartier divisor extending Es | `E`, `hE : E.IsRelativeEffectiveCartier (pullback.snd f h)`, and the equality of its `comap` along the pointed base-change map with `Es` |
| Degree-g divisor scheme of the smooth locus | `H : Over S'`, the equivalences `rH` on ALL S'-schemes with `Divisor f g ((Over.map h).obj T)`, and the first conjunct expressing pullback naturality |
| Divisors of that scheme | `Divisor` is the existing Hilbert functor's degree-g points, with Cartier property and support in the relative smooth locus; these are exactly the smooth-locus divisors, and the finite support is closed in the proper ambient curve |
| W open in that divisor scheme | `W : H.left.Opens`, with underlying S'-scheme `Over.mk (W.ι ≫ H.hom)` |
| Open V in A after base change | `V : Subfunctor ((Over.map h).op ⋙ P.obj.obj)`, `IsRepresentableWith (fun _ _ a ↦ IsOpenImmersion a.left) V.ι`, and the pointwise inclusion into A restricted to S' |
| V contains the entire identity section | the conjunct quantified over every `T : Over S'` requiring the preimage under `eP` of `toPicardFunctorHom ... 1` to belong to V |
| W is isomorphic to V | the natural isomorphism `eW : yoneda.obj (...) ≅ V.toFunctor` |
| V quasi-compact | `CompactSpace W.toScheme`; through eW this is precisely quasi-compactness of V, expressed on its representing scheme |
| F maps to [O(F-E)] | the penultimate conjunct: apply `eP` to eW(a) and get `toPicardFunctorHom` of `lineClass F * (testLineClass ... E ...)⁻¹` |
| Inverse is evaluation divisor | the last conjunct, on every T and every Picard representative L of eW(a), identifies the divisor of a with `evaluation ... (twist ... L) |>.zeroLocus` |
| Direct image of L(E) invertible and compatible with arbitrary base change | the same last conjunct asserts pushforward invertibility and `UniversalBaseChange`; the latter requires `IsIso` of the recorded canonical `moduleBaseChangeMap` for EVERY map T' → T |
| Evaluation is Cartier, degree g, and supported in smooth locus | its ideal equals the `rH` divisor in the last conjunct; the defining properties of `Divisor` provide exactly these conditions |
| g = 0 included | `g : ℕ` with no positivity hypothesis; `Fin 0` is allowed, and its empty infimum ideal is the unit ideal, cutting out the empty divisor |

`cohomology` is the recorded O-module right-derived global-sections functor,
with restriction of scalars along `K → Γ(X_K,O)` induced by the structural morphism.
It does not replace it by cohomology of the underlying abelian sheaf. `lineClass`
uses the recorded dual ideal and `Pic.ofIsInvertible`; `testLineClass` uses the
recorded relative-Cartier base-change theorem, so its line is really O(E_T).
`evaluation` uses `tensorPullbackSectionAdjunction`, whose section-normalized unit
is `1 ⊗ m`; its counit is the actual evaluation, with no unspecified map chosen.
`UniversalBaseChange` uses the published `moduleBaseChangeMap`, whose source
adjunction existence theorem also fixes its unit sectionwise. A Picard class is
represented by the same `fromSkeleton` object already used throughout the Picard
library. Testing that representative entails the formula for any isomorphic one;
classes having representatives only fppf locally are covered after those test
base changes, since all tests and all representatives are quantified over.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`: `IsProjectiveBundle`.
- `Sheaf.AlgebraicGeometry.NodalGeometricFibres`: `HasNodalGeometricFibres`.
- `WeilConjectures.AlgebraicGeometry.Picard.Defs`: `picardFunctor`, `toPicardFunctor`.
  Its sibling `Picard.Group` supplies `picardFunctorGrp`, `toPicardFunctorHom`,
  `Scheme.Pic.ofIsInvertible`, and the Picard tensor-product group law.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`: the recorded
  `IdealSheafData.IsInvertible.isInvertible_dual_toModules`, and `toModulesᵛ`.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`: `RingedSpace.moduleCohomology`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier`:
  `IdealSheafData.IsRelativeEffectiveCartier` and
  `IsRelativeEffectiveCartier.isRelativeEffectiveCartier_comap_of_isPullback`.
- `WeilConjectures.AlgebraicGeometry.Hilbert.Defs`: `hilbertPresheaf` and
  `IsHilbertSubscheme`; the existing node `def-pc-hilb-functor` is added to stmt_deps.
- `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`: `Modules.Hom.zeroLocus`;
  the existing node `def-pc-zero-scheme` is added to stmt_deps.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Modules.tensorPullbackSectionAdjunction`; the existing node
  `def-pc-module-pullback` is added to stmt_deps. Its interface publicly reuses the
  upstream tensor pullback rather than declaring another pullback construction.
- `WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction`:
  `Modules.moduleBaseChangeMap`, the canonical ordinary module base-change arrow.

All recorded statement modules and all stated proof-dependency modules are imported.
The following proof dependencies have no recorded Lean module in the read clone and
are not imported: `lem-sfb-flat-space-smooth-locus`,
`lem-sfb-proper-flat-space-derived-base-change`,
`lem-sfb-section-finite-cartier-open-locus`,
`lem-sfb-projective-smooth-divisor-parameter`, and
`lem-sfb-proper-space-curve-qcoh-bound`. Their mathematical roles are retained in
steps 1, 3, 4, 5 and 6 of the theorem docstring. They are proof prerequisites, not
missing notions required to type this statement. The scheme-as-space input is
imported directly from `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`.

Edge cases checked before and after drafting:

- `g = 0`: no point choices required, empty divisor and the degree-zero Hilbert
  point allowed; no nonzero or positive-degree hypotheses occur.
- Empty base excluded only by the specified `s : S`, exactly as in the node.
- Arbitrary disconnected and nonreduced test schemes are allowed; there is no
  Noetherian, affine, reduced, flat, or field restriction on a test scheme.
- Arbitrary nonflat base changes and identity maps are included in UniversalBaseChange.
- Reducible nodal fibres are allowed; no smoothness or integrality of X is imposed.
- P need not be a scheme, and A need not be connected or quasi-compact. Only the
  constructed V has the asserted scheme representation and quasi-compactness.
- A is any open subgroup, not just Pic^0; all inclusion tests use that supplied A.
- K is separably closed through the supplied separable-closure datum, not forced
  to be algebraically closed or perfect; this retains positive-characteristic cases.
- All scheme, field, and test objects use the common scheme universe u. The
  algebraic-space sections are only lifted into u+1 for the existing Picard sheaf;
  no universe equality or smallness assumption is added.

Searches made with the prescribed msearch.py wrapper:

1. `leanfinder`: “Relative Abel map is an isomorphism from nonspecial degree genus
   divisors onto an open subspace of the relative Picard space”. Eight hits:
   Proj localizations, ring relative Picard groups and Weierstrass point classes;
   none is a relative Abel chart of a nodal family.
2. `loogle`: `AlgebraicGeometry.picardFunctor, IsOpenImmersion`. Zero hits;
   service reports the project identifier is unknown to its Mathlib index.
3. `grep`: `abelMap|nonspecial|relativePicard|PicardFunctor`, Mathlib
   `AlgebraicGeometry`. Zero hits.
4. `leansearch`: “The nonspecial Abel Jacobi map for a relative nodal curve
   identifies an open locus in its degree genus divisor scheme with an open
   neighbourhood of zero in its Picard algebraic space”. Eight Weierstrass
   Jacobian-coordinate hits, no match.
5. Repository rg searches in both `lean/WeilConjectures` and `lean/Sheaf` for
   `relative_abel_nonspecial_chart|RelativeAbelChart|nonspecial|abelMap`.
   Read `WeilConjectures.AlgebraicGeometry.Picard.Jacobian.abelMapPresheaf`:
   its hypotheses are a smooth relative curve over a FIELD, so it does not state
   this nodal-family chart. Other matches are labelMap substrings, projective
   nonspecial embedding arguments and smooth-field Hilbert-to-Picard applications.
6. Search for the exact item id under `lean/WeilConjectures`: no match. No existing
   declaration states this item. Searched declarations used by the helpers and
   read their full signatures and docstrings before reusing them.

Validation: scompile.py, prescribed Q22/item invocation, clean sandbox and library
compiles (about 4 s and 10 s). The only postponed proof is the named main theorem.
All variables and universes are explicit; autoImplicit is false. No line exceeds
100 characters. Final dry run and push are performed by deliver2.py.

## Second reading by Q22

The dispatcher explicitly forbids starting another agent, and states that the
maintainer supplies the independent delivery review. This section records the
worker's own second pass, not an invented independent reader.

Reopened the node and the final module and checked the two tables above against
all binders and conjuncts. The second pass retained the full identity section
condition (all tests, not just the specified geometric point), both map formulas,
the arbitrary nonflat base-change condition, and the degree-zero case. It checked
that the field action on cohomology comes from q, and that the support condition
is in the fibre product's smooth locus. It checked that the inverse's zeroLocus
is applied when its source and target are invertible: the target is a tensor of
invertible lines and the direct image is asserted invertible in the same clause.
The canonical evaluation was made explicit through the already recorded
section-normalized tensor adjunction. No mathematical statement was changed.
