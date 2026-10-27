## Worker report

The module `Sheaf.Algebra.Homology.ProjectiveHomScalarUnitNormalization` states
`CochainComplex.projective_hom_scalar_unit_normalization`, with its proof `sorry`.
The DAG statement, statement dependencies and proof plan are unchanged. There are
no new nodes or dependency repairs. The helpers only abbreviate existing functors,
select the existing uniquely evaluation-normalized projective model, or compose
actual adjunction and tensor maps. No mathematical hypothesis is added.

Source read: `literature/stacks-project/more-algebra.tex`, lines 28763–28818,
Tag 0E1W (`lemma-upgrade-adjoint-tensor-RHom`) and Equation 0E1X
(`equation-base-change-RHom`). The former constructs the Hom comparison by
precomposition with the scalar unit; the latter defines the scalar comparison
as the adjoint of Hom applied to that unit. The current blueprint ancestor
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`
was also consulted; this is an auxiliary algebraic input, not that unit's own statement.

Hypothesis and clause correspondence:

| DAG clause | Lean rendering |
| --- | --- |
| Commutative rings and flat ring map | `{R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.Flat)` |
| Ordinary modules; F = S tensor_R -, termwise | `ModuleCat.{u} R`, `projectiveHomScalarComplex φ = (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)` |
| Restriction U, on complexes and derived categories | `projectiveHomRestrictionComplex φ`, `ModuleCat.derivedRestrictScalars φ`, with `projectiveHomRestrictionComparison φ` the existing canonical localization comparison |
| Q_R and Q_S | `DerivedCategory.Q`, with endpoints inferred from the explicitly typed module complexes |
| LF, canonical flat comparison on every complex | The recorded `ModuleCat.ordinaryDerivedExtendScalars φ`; natural iso `c`, whose hom on every `C` is exactly `(ModuleCat.ordinaryDerivedChangeOfRings φ).counit.app C` |
| The derived unit and counit agree with ordinary scalar adjunction | The next two conjuncts are the localization/unit square and counit square for `(ModuleCat.extendRestrictScalarsAdj φ).mapHomologicalComplex (.up ℤ)`. They quantify over every unbounded complex. The ordinary unit is 1 tensor x and counit is scalar multiplication. |
| Identification with the punctual sheaf categories | Work in the ordinary-module presentation permitted by the node, importing `singleton_site_module_comparison`. Its exact tensor equivalence identifies the sheaf Hom and scalar functors with these module functors; the chosen ordinary derived APIs are the already recorded specializations, not a second construction. |
| P bounded above | `hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i)` |
| All terms of P projective | `hp : ∀ i : ℤ, Module.Projective R (P.X i)` |
| N any complex | `(N : CochainComplex (ModuleCat.{u} R) ℤ)` with no condition on it |
| Product total Hom and its differential | The shared `CochainComplex.moduleHomComplex`, whose terms are `HomComplex.Cochain` and whose differential is the recorded signed `δ_hom`. `f.v p (p+n) rfl` is its actual product coordinate. |
| Canonical projective-source comparison | `projectiveHomModelIso` selects exactly the `e` family in `projective_hom_evaluation_model`. That theorem fixes evaluation on every generator with sign `(-1)^(pn)` and its localization tensor-Hom transpose, uniquely fixing `e`; its naturality clause is retained by this selection. |
| FP is an admissible projective model | Existential `hbS` and `hpS` are conclusions, not additional hypotheses; they permit that same existing projective model over S. |
| The normalized chain map χ | The existential chain morphism `χ`, followed by the first coordinate equation, states `χ(s tensor f)_p(t tensor x) = st tensor f_p(x)`. These coordinates determine the map, hence identify it with the normalized map of `normalizedRingHomExtension_exists`. |
| Evaluation-normalized derived internal-Hom scalar adjunction | Natural iso `α : projectiveHomScalarAdjunctionSource φ ≅ projectiveHomScalarAdjunctionTarget φ`; the evaluation equation fixes every component by tensor-Hom transposition. `projectiveHomRestrictionTensor` is exactly the scalar-counit mate of the published strong tensor map, so the equation includes the restriction lax tensor, not an unspecified comparison. |
| β for arbitrary derived E,L is the stated unit transpose | `projectiveHomScalarBeta` is the actual term `(adj.homEquiv _ _).symm (RHom.map (id, adj.unit.app L) ≫ α.inv.app (op E, LF.obj L))`. The component equation for `β` is equality with this exact term for every derived E,L. |
| Naturality for all derived morphisms, including inverse quasi-isomorphisms | `β : projectiveHomScalarSource φ ⟶ projectiveHomScalarTarget φ` is a natural transformation on `D(R)ᵒᵖ × D(R)`. Its naturality quantifies over all morphisms of this derived category, not only localized chain maps. Similarly α and c are natural isomorphisms. |
| The chain isomorphism representing α | `a : U(Hom_S(FP,FN)) ≅ Hom_R(P,U(FN))`, with forward coordinate formula `a(g)_p(x) = g_p(1 tensor x)` and inverse formula `a.inv(h)_p(t tensor x) = t • h_p(x)`. The first derived-model equation identifies `Q(a)` with α, using the canonical exact-restriction comparison and the projective models, including the `c_P` source transport. |
| Hom applied to the unit | Chain map `k` has formula `k(f)_p(x) = 1 tensor f_p(x)`. The second derived-model equation identifies `Q(k)` with derived Hom applied to the normalized unit, with the `c_N` and restriction transports written out. |
| Its scalar adjoint is the same χ | `χ = (ordinaryChainAdj.homEquiv _ _).symm (k ≫ a.inv)`, together with the pure-tensor formula for χ. |
| Q_S χ equals β under canonical comparisons | The last equation is `β = LF(e_R.inv) ≫ c_H ≫ Q_S.map χ ≫ e_S.hom ≫ RHom_S.map(c_P.op,c_N.inv)`, exactly the model-transport equality in proof step 5. |
| Compatibility with changes of projective representatives and arbitrary target quasi-isomorphisms | The last equality holds for every P,hb,hp,N, using the single natural projective-model family from the existing theorem. Naturality of β, c and that model family makes its transported squares commute for arbitrary derived morphisms; in particular they commute for a changed projective representative and for any target quasi-isomorphism and its inverse. |
| No finite generation, perfectness, bounds on N, or invertibility of χ | None of these appears as a binder or conclusion. Only a is declared a chain isomorphism; χ is a morphism. |

The ordinary and punctual presentations have different category encodings. No
unusable dependency is replaced: the recorded ordinary presentations of LF and
RHom are used verbatim, and the scalar-Hom isomorphism is specified by precisely
the evaluation equation of the sheaf theorem after the permitted module
identification. Its evaluation equation uniquely determines it, so the existential
α is not a freely chosen map. Likewise c is the exact universal derived counit,
and the ordinary unit square fixes adj. No unrelated additional structure is assumed.

Dependency declarations read and used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat` (line 27), and
  `Mathlib.Algebra.Module.Projective`: `Module.Projective` (line 71).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory` and `DerivedCategory.Q` (lines 74, 87, 95).
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
  `ModuleCat.OrdinaryDerivedChangeOfRings`, `ordinaryDerivedChangeOfRings`,
  `ordinaryDerivedExtendScalars`, and its normalized monoidal structure.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`.
- `WeilConjectures.Algebra.Homology.ModuleHomComplex`:
  `CochainComplex.moduleHomComplex`, using Mathlib `HomComplex.Cochain` and `δ_hom`.
- `WeilConjectures.Algebra.Homology.HomComplex`:
  `CategoryTheory.homComplex_exists`, `homComplexFunctor`, `homComplex`; the
  corresponding punctual presentation has the same full product coordinates.
- `Sheaf.ProperBaseChange.SingletonSiteModuleComparison`:
  `CategoryTheory.singleton_site_module_comparison` (full signature and proof
  docstring at lines 683–770), including scalar-unit and derived localization compatibility.
- `Sheaf.Algebra.Homology.NormalizedRingHomExtension`:
  `CategoryTheory.normalizedRingHomExtension_exists`, fixing χ by product coordinates.
- `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`:
  `CategoryTheory.scalarInternalHomAdjunction_exists`; its data declarations in
  `ScalarInternalHomData` specify the evaluation equation, the counit-mate
  restriction tensor and the K-flat normalization square.
- `Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel`:
  `CochainComplex.projective_hom_evaluation_model`, including the full generator
  evaluation formula, derived evaluation square and representative naturality.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`:
  `CategoryTheory.Adjunction.mapHomologicalComplex` for the actual chain adjunction;
  `ModuleCat.derivedRestrictScalars` and its factors are the upstream exact restriction.

All recorded statement/proof dependency modules that exist are imported. The
proof-only node `lem-trf-flat-projective-hom-models` has no Lean record/module in
the read clone; its mathematical proof is retained in the theorem docstring.
No unstated notion from it is assumed: c, the normalized adjunction and the
extended projective-model bounds/projectivity are existential conclusions here.

Edge cases checked before writing: P=0, N=0 and the zero coefficient ring yield
zero formulas and admit the asserted adjunctions; φ=id yields restriction of a
linear map at 1 tensor x and its ordinary adjoint, without asserting a literal
identity between unequal representative objects. Degrees p and n range over all
integers, including 0 and negative degrees; the pre-existing projective comparison
retains the Koszul sign. Infinite projective modules and arbitrarily unbounded N
are allowed. All Hom factors are genuine products; no interchange of tensor with
an infinite product is asserted. The arbitrary universe u is explicitly bound,
and the project uses its published small-Hom ordinary-module derived category.
There are no auto-bound variables, local notation, private helper definitions or
local instances in the delivered module.

Searches actually run:

- `msearch.py ... leanfinder "projective Hom complex scalar extension derived unit transpose"`
  returned eight projective-resolution/Ext declarations (`ProjectiveResolution.extMk_hom`,
  `ProjectiveResolution.isoExt`, etc.). None states this chain/derived normalization.
- `msearch.py ... loogle "ModuleCat.extendRestrictScalarsAdj"` returned six hits,
  including the ordinary adjunction, its unit formula, counit-at-one formula and
  hom-equivalence evaluation. These are used; none identifies Qχ with β.
- `msearch.py ... grep "baseChangeHom|extendRestrictScalarsAdj" Algebra/Category/ModuleCat`
  returned eleven hits in `Monoidal/Adjunction`, `ChangeOfRings` and `Descent`;
  they concern ordinary scalar adjunction, not the required derived comparison.
- `rg` searched the full `lean/WeilConjectures` and `lean/Sheaf` trees for
  projective-Hom/scalar/unit patterns and the item id; `grep -rn` searched the exact
  id in `lean/WeilConjectures`; `rg` also checked the proposed names in
  `dag/lean_names_upstream.json`. No exact match or name collision was found.
- Nearby `PseudoCoherentRHomFlatBaseChange.lean` imposes pseudo-coherence and a
  bounded-below target when claiming invertibility, and does not state the present
  unrestricted projective-model equalities. `FlatScalarEvaluationModel.lean` is
  a sheaf K-injective evaluation/coherence package; it does not state this node.
  Both were opened and checked, so neither is recorded as an exact existing match.

Validation: the module compiled through scompile.py in both sandbox and library
module mode, within the 60-second limit. Initial elaboration faults were repaired
by publicly importing the existing chain-adjunction API and making the S-module
carrier explicit in the inverse coordinate formula. No proof was written.

## Second reading by Q63

This is a separate self-reading by the dispatcher worker; no additional agent was
started, as explicitly instructed. The maintainer performs the independent delivery
review. I reread the unchanged node and the completed module side by side. In
particular, the scalar evaluation square uses the actual counit mate of the
normalized derived tensor, the chain isomorphism includes both inverse formulas,
and the two RHom arguments in the final transport have opposite variances:
`c_P.hom.op` and `c_N.inv`. The k square has all unit/restriction transports.
The natural transformation β covers the whole derived product category, so the
claim is not restricted to chain maps. The selected projective model is the
existing evaluation-normalized family, not a bare existence choice. No statement
mismatch or source correction was found. The only revisions were the elaboration
repairs described above and explicit dependency imports.
