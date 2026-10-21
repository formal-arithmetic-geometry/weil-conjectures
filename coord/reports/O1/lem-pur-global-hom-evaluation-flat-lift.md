## Worker report

Item: `lem-pur-global-hom-evaluation-flat-lift`, stage 2, group O1.
Delivery module: `Sheaf.Paper.GlobalHomEvaluationFlatLift`.
Main declaration: `AlgebraicGeometry.Etale.ExternalRHom.globalHom_evaluation_flat_lift`.
The theorem is stated with `sorry`; no theorem is proved. The three supporting definitions
have actual bodies. The node changes only in `lean`: no statement correction, extra
hypothesis, new independent notion, or dependency-node replacement is needed.

### Hypotheses and objects

- A commutative ring: explicit `A : Type (u + 1)` and `[CommRing A]`.
  There is no nonzero-ring or characteristic hypothesis.
- A scheme and its small etale site: `X : Scheme.{u}`, and the existing
  `ExternalRHom.Modules A X = Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)`.
  `Complexes A X` is the ordinary cochain-complex category over it. This is the
  recorded ordinary-coefficient encoding, not a replacement by arbitrary ringed-site data.
  The site lies within the module universe; its existing essentially-small model supplies
  the prescribed representative. No universe equality is imposed on unrelated sites.
- E is bounded with flat terms: `E : Complexes A X`, `hE : IsBoundedFlat A E`.
  That existing predicate gives two integer bounds and zero terms outside them, together
  with `IsFlatOnSite` of each term in the canonical scalar realization. Both bounds are
  existential; none is fixed to zero. Flatness is the recorded exact-tensor condition.
- K is bounded below in the unbounded derived category:
  `K : DerivedCategoryModule A X`, `hK : IsPlus A K`. The latter is
  `exists n : Int, DerivedCategory.IsGE K n`, with arbitrary integer n.
- Q_X and Q_A are the existing `siteQ A X` and `moduleQ A`, both `DerivedCategory.Q`.
  Termwise constants are `constantComplex A X`. `chainEvaluationSource A X U E`
  is precisely their native total tensor with E, with direct sums and the Koszul differential.
- C is the existing `globalHom A X` applied to `(Q_X E, K)`: internal derived Hom followed
  by module-valued derived sections. `HomModel A E I` canonically identifies Q_A(C_E)
  with its value at `(Q_X E, Q_X I)`. Any given representative isomorphism Q_X I ≅ K
  transports this to C by functoriality in the second variable.

### Every conclusion

1. Existence of a K-injective representative is the first conjunct
   `exists I, I.IsKInjective ∧ Nonempty (Q_X.obj I ≅ K)`.
2. The following universal quantifier ranges over **every** I, its `IsKInjective`
   instance, and every isomorphism `_i : Q_X.obj I ≅ K`. It then supplies
   `m : HomModel A E I`. This is the existing evaluation-normalized comparison,
   not an arbitrary uncharacterized isomorphism or arbitrary map.
3. `homComplex A E I` is the existing global A-linear Hom complex. Its degree-n module
   is `ModuleCat.of A (CochainComplex.HomComplex.Cochain E I n)` and its differential
   is `HomComplex.δ_hom A E I n m`, hence d_I f - (-1)^n f d_E. It retains A-linearity.
   The existence conjunct supplies U and `alpha : U ⟶ homComplex A E I` with
   `QuasiIso alpha` and `IsFlatKFlatCoefficientComplex A U`. The latter is exactly the
   recorded K-flat acyclic-test predicate and flatness of all terms, on the existing
   one-object-site realization of an ordinary A-complex.
4. The next universal quantifier covers every U and alpha satisfying these conditions.
   It asserts existence of t with `IsChainEvaluation A E I U alpha t`, and the remaining
   conclusions hold for every t satisfying that formula. The existing formula quantifies
   over all integer degrees r,q, every etale object W, every w in U^r and every local e
   in E^q. The pure tensor of the sheafification-unit image of w and e is sent to
   `((alpha.f r).hom w).v q (q+r) rfl`, evaluated on e. No interchange sign is inserted.
   Since t is a morphism of cochain complexes, the chain-map condition is included.
5. `IsFlatKFlatEtaleComplex` is asserted for the constant complex, E, and the actual
   total tensor source. This predicate merely conjoins the dependency's K-flat predicate
   on `ringedComplex` with `IsFlatOnSite` on each canonically realized term; it defines
   neither a new tensor nor a new flatness condition.
6. `IsResolvedGlobalEvaluation A E I m U alpha t` states that the canonical derived
   transpose of the localized t equals `Q_A.map alpha ≫ m.iso.hom`. Its left side is
   the existing `chainModelTransposeOf`, which first applies the constant-model counit,
   the localization's tensor constraint and Q_X(t), and then the existing composite
   constant/sections and tensor/Hom adjunction. Thus, under the resolution isomorphism,
   it is exactly the derived counit/internal-evaluation map. This is an equality in
   D(A), not an equality of cohomology groups. The fixed Hom-model normalization and
   alpha determine the comparison; no new comparison map is chosen. Transport along
   `_i` gives the stated evaluation into K. Writing the equality at Q_X I makes it
   independent of the arbitrary presentation isomorphism without excluding any such choice.
7. The nested existential gives N, `v : source ⟶ N`, and `c : N ⟶ I`, with
   `IsFlatKFlatEtaleComplex A X N`, `QuasiIso c`, and
   `Nonempty (Homotopy (v ≫ c) t)`. Here v is the node's map u; its different Lean name
   avoids confusing it with the universe u. This includes flatness of every term of N.
8. `Q_X.map v ≫ Q_X.map c = Q_X.map t` is separately asserted. Lean's composition order
   renders the node's Q_X(c)Q_X(u). Homotopy and this equality are both retained.
9. For every `Z : Scheme.{u}` and arbitrary `f : Z ⟶ X`, the last quantifier ranges
   over the four-element list `[constant(U), E, source, N]`. For each P it asserts
   flat-term K-flatness of `(pullComplex A f).obj P` and `IsIso (pullModel A f P)`.
   The latter is the existing canonical left-derived counit from the derived pullback
   of Q_X P to the localization of the ordinary termwise inverse image. Its invertibility
   says exactly that this ordinary pullback computes derived pullback. There is no
   etale, flat, smooth or proper condition on f. Repeated/zero entries in the list
   simply repeat the same assertion.

### Recorded dependency declarations used

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-size-convention`: a metatheoretic convention, recorded with null declaration;
  rendered by explicit universes and the existing small-etale size instances.
- `def-weil-pbc-derived-categories`: `Etale.DerivedCategoryModule`,
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, publicly exposed through the
  recorded `WeilConjectures.AlgebraicGeometry.DerivedCategories`.
- `def-kun-constant-sheaf`: `CategoryTheory.Functor.mapHomologicalComplex`,
  `Mathlib.Algebra.Homology.Additive`, specialized in the existing `constantComplex`.
- `def-sfb-site-derived-constant-module-functor`:
  `CategoryTheory.realizationRing`, `realizationRingIso`,
  `commutativeSiteConstantModuleFunctor` and `commutativeSiteDerivedConstantModuleFunctor`,
  `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`. The scalar realization
  in `ringedComplex` uses this ring comparison and the recorded scalar-extension functor.
- `def-pc-tensor-complex-sheaves`: `CochainComplex.mapBifunctor`,
  `Mathlib.Algebra.Homology.BifunctorShift`; the native complex monoidal instance is its
  direct-sum total-tensor specialization.
- `def-pc-cochain-complex-modules`: `CochainComplex`,
  `Mathlib.Algebra.Homology.HomologicalComplex`.
- `def-pc-flat-sheaf-modules`: `SheafOfModules.IsFlatOnSite`,
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`.
- `def-pur-derived-internal-hom`: generic `CategoryTheory.derivedInternalHomOfUniverses`
  and its ordinary-etale specialization `Etale.derivedHom` exposed by
  `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`. `ExternalRHom.internalHom`
  uses exactly the same ordinary-etale closed structure.
- `def-kun-constant-projection-morphism`:
  `Etale.derivedConstantGlobalSectionsAdjunction`,
  `Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap`; this is the adjunction used
  by `ExternalRHom.constantSectionsAdjunction` and its normalized transpose.
- `def-pur-kinjective-complex`: `CochainComplex.IsKInjective`,
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective` (Mathlib match, no lean record).
- `def-pur-hom-complex`: `CategoryTheory.homComplex`,
  `WeilConjectures.Algebra.Homology.HomComplex`; the global A-linear cochains are the
  already existing `ExternalRHom.homComplex`, related by the stated proof dependency
  `CategoryTheory.homComplex_global_cochains`,
  `WeilConjectures.Algebra.Homology.HomComplexGlobalCochains`.
- `def-pc-kflat-complex`: `CochainComplex.IsKFlatIndependentCoefficients`,
  `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`.
- `def-pc-quasi-iso-modules`: `QuasiIso`, `Mathlib.Algebra.Homology.QuasiIso`
  (Mathlib match, no lean record).
- `def-weil-pbc-inverse-image`: `Etale.upperStar`,
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, specialized termwise in
  `pullComplex` and through its existing left-derived counit `pullModel`.

All currently recorded proof-dependency modules are imported without `public` unless
also needed for the statement. `lem-sfb-hom-kflat-chain-transpose` has no recorded Lean
module in this checkout, so there is no module for that proof-only dependency to import.
Its mathematical role is included in the proof docstring; it is not an added assumption.

### Existing helper reuse and import-cycle notice

The existing helpers in `Sheaf.Paper.ExternalRHomConePairing` supply `Modules`, `Complexes`,
`siteQ`, `moduleQ`, `homComplex`, `constantComplex`, `chainEvaluationSource`,
`constantSection`, `tensorComplexSection`, `IsChainEvaluation`, `ringedRealization`,
`ringedComplex`, `pointRealization`, `pointComplex`, `IsBoundedFlat`, `constantModel`,
`pullComplex`, `pullModel`, `globalHom`, `transpose`, `chainModelTransposeOf`,
`IsHomModel`, `HomModel`, `HomModel.iso`, and `IsPlus`. Their definitions and signatures
were read. No duplicate of those definitions is introduced, and the theorem
`external_rhom_cone_pairing` is never used. This is ordinary reuse of existing data, not
an assumption of the downstream theorem.

Process notice for the maintainer: the downstream node `lem-pur-external-rhom-cone-pairing`
lists this item as a proof dependency, while its existing module owns the helper definitions
needed here. Consequently the automatic backward proof import from that module to this
one would close an import cycle and must be skipped under stages/2-statements.md §3.7.
To use this lemma in a future proof of that downstream theorem, the maintainer should
factor those existing definitions into a shared dependency module first. No DAG edge to
the downstream theorem is added, and no live source is changed by this delivery.

### Searches and sources

Read the item's full statement, source and all ten proof steps; read every statement
in its `stmt_deps`, every recorded signature/docstring used above, and the Mathlib matches
for K-injectivity and quasi-isomorphisms. No repair note exists for the item.
The specified CompactObject example currently consists only of a withdrawal notice;
the delivered header/docstrings follow the current active statement modules instead.
Read Stacks `sites-cohomology.tex`, lemma-factor-through-K-flat (0G7D), including its
flat-terms clause and cone proof, and the Hom-complex/internal-Hom source sections.

- `msearch.py ... leanfinder` query: "A K-flat resolution of the global Hom complex gives
  a chain evaluation with K-flat flat terms and homotopic factorization through a K-flat
  target". Result: eight unrelated Mathlib LeftResolution/ProjectiveResolution results;
  none states this sheaf-theoretic result. Examples returned were
  `CategoryTheory.Abelian.LeftResolution.chainComplexMap` and
  `CategoryTheory.ProjectiveResolution.liftHomotopy`.
- `msearch.py ... loogle` query: `CochainComplex.IsKFlat, Homotopy, QuasiIso`.
  Result: zero hits, unknown identifier `CochainComplex.IsKFlat` in the Mathlib search
  index. The project's separately recorded K-flat definition is used instead.
- `msearch.py ... grep` query: `global.*evaluation|KFlat.*factor|kFlat.*factor`,
  restricted to `Algebra/Homology`. Result: zero Mathlib hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for global Hom/evaluation/flat-lift
  names found the existing ordinary-etale helper definitions in ExternalRHomConePairing
  and K-flat factorization in KFlatMapFactorization. Neither theorem states this complete
  lemma: the former lacks this existence/factorization/pullback conclusion, and the
  latter has no global evaluation or canonical derived identification.
- Exact item-id search of `lean/WeilConjectures` and `dag/lean_names_upstream.json`
  found no existing declaration for this node. Searches for the four new declaration
  names in Mathlib, WeilConjectures and Sheaf found no clashes.

### Edge cases and validation

Checked the empty scheme, zero complex E, zero ring, zero/acyclic coefficient resolutions,
unbounded U, negative degrees, arbitrary integer bounds for E and K, identity scheme
morphisms and general non-flat/non-etale morphisms. No clause assumes nonempty schemes,
nontrivial coefficients, positive degrees, a nonzero complex, or a geometric property of f.
The identity case uses the same `pullModel`, without a separately chosen comparison.
The signed Hom differential and the tensor differential use the same degree of w,
so no extra Koszul sign appears in the formula. Every degree variable is Int.

The initial expanded derived-evaluation equation caused a kernel timeout. It was replaced
by the same equality expressed via the already existing normalized derived transpose,
bundled as `IsResolvedGlobalEvaluation`; the statement's mathematical content is unchanged.
The predicate-only probe compiled cleanly, and the revised complete statement compiled
cleanly in both sandbox and library contexts even under a lowered diagnostic heartbeat
limit. The final module retains the default limits and is checked by scompile.py and
by the prescribed delivery dry run. No local/global build is run.

No STATEMENT-DISPUTED flag or source-based correction is required.

## Second reading by O1

Author's second pass; the maintainer supplies the independent review. Reopened the node
and the final signature and checked every quantifier and conjunct against the mapping
above. In particular, I is not fixed to a chosen resolution; U and alpha are universally
quantified after their existence; t is constrained by its formula on every tensor summand;
N has flat terms as well as K-flatness; both the homotopy and localized equality remain;
and the final clause includes constant(U), E, their tensor and N for every f. The comparison
is normalized in D(A), not replaced by abstract existence of some isomorphism. No bound
on U, no flatness condition on f, and no universal choice of derived comparison has been
added. The only implementation adjustment was expressing the long derived equation via
its existing adjunction transpose to make the kernel check small. All helpers have real
definitions, all four declarations are listed in lean.declarations, and the only sorry
is the main theorem. No dependency or node statement was changed.
