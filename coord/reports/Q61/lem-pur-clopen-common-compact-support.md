## Worker report

The delivery states `lem-pur-clopen-common-compact-support` in
`Sheaf.Paper.ClopenCommonCompactSupport`, with 18 listed declarations. Every new
theorem has proof `sorry`. Definitions build specified maps from existing
functors, adjunction comparisons, and unique canonical comparisons. No definition
chooses an arbitrary isomorphism from an uncharacterized existence assertion.
The DAG node is unchanged except for `lean`; there are no new nodes or dependency
repairs and no statement correction.

The pre-interruption sandbox contained an incomplete module and searches, but no
node record or report. I resumed that module, compiled it, and added the explicit
naturality and compactification-agreement equations for the finite-sum clause.
No delivery invocation from this continuation was repeated after interruption.

Hypothesis-by-hypothesis correspondence:

| Node hypothesis | Lean rendering |
| --- | --- |
| Fixed algebraic closure of the finite field and prime ell different from its characteristic | `P : PurityFiniteSetting.{u}` bundles the recorded `FiniteFieldDatum` and its `CoefficientDatum`; the latter includes ell prime and ell different from the field characteristic. |
| Finite extension E inside the fixed coefficient closure, its valuation ring, uniformizer, positive n, and A_n | `P.extension`, `P.finiteExtension`, `P.level`, `P.level_pos`; `P.Ring` is exactly the recorded `Padic.coefficientExtensionRing ... P.level`. `P.Coefficient` is its ordinary universe lift, used solely in the fixed-scalar realization of the same sheaf category. |
| Finite-type k-schemes X,Y | `X Y : Over (Spec (CommRingCat.of P.field.k))`, with `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]` and the corresponding two instances on Y. |
| Separated finite-type k-morphism g | `g : X ⟶ Y` and `[IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]`. No separatedness instance for `Y.hom` occurs. |
| Finite index set, including the empty set | `{I : Type w} [Finite I]`, with w independent of u. There is no `Nonempty I` binder. |
| Component inclusions | `Xi : I → Over ...`, `j : ∀ i, Xi i ⟶ X`, and both `[∀ i, IsOpenImmersion (j i).left]` and `[∀ i, IsClosedImmersion (j i).left]`. No component is required to be nonempty. |
| Pairwise disjointness and cover | `hdisjoint : ∀ i k, i ≠ k → Disjoint (Set.range (j i).left) (Set.range (j k).left)` and `hcover : (⋃ i, Set.range (j i).left) = Set.univ`. |
| Ordinary small pro-etale unbounded derived categories | `Scheme.proEtaleDerivedCategory ... P.Ring`, which is the recorded derived category of modules over the constant ring sheaf on `Scheme.ProEt.topology`. |
| r_i = Lj_i^* | `Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left`, the canonical exact constant-coefficient pullback used by the recorded `finiteDerivedPullback`. |
| E_i = zero insertion under finite-clopen decomposition | The canonical model is `Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left`, i.e. the termwise derived recorded extension by zero. `clopenSupport_insertion` states its diagonal invertible unit, off-diagonal zero restriction, both adjunctions and the splitting; these characterize precisely the zero coordinate insertion under the recorded equivalence, without making a second definition of that notion. |

Clause-by-clause correspondence:

| Node conclusion | Lean rendering |
| --- | --- |
| Existence of a compactification | First conjunct of `clopenSupport_geometry`, `Nonempty (Compactification g.left)`. |
| Every chosen c gives c_i with the identical proper part | Throughout, `c_i` is the already defined `c.precomp (j i).left`. Reading `Compactification.precomp` shows `.Z := c.Z`, `.g := c.g`, `.i := (j i).left ≫ c.i` and the actual factorization equation; this is real data rather than an existential unrelated compactification. |
| X,Y,X_i,bar X Noetherian | The two main Noetherian conjuncts, the component conjunct and `∀ c, IsNoetherian c.Z` in `clopenSupport_geometry`. |
| j_i,g_i separated and of finite type | Three component conjuncts for each map: `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, where `g_i = (j i).left ≫ g.left`. |
| Finite nonnegative integer dimension bound, zero for the empty ambient scheme | `∃ d : ℕ, topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞) ∧ (IsEmpty c.Z → d = 0)`. A natural number represents exactly a nonnegative integer, including zero. |
| E_i exact and left and right adjoint to r_i | The two actual `Adjunction` families L and R in `clopenSupport_insertion`, with triangulated exactness `(sfIntrinsicDerivedOpen ...).IsTriangulated`. Ordinary exactness is the published `sfIntrinsicExtensionByZero_exact`; the functor is its exact termwise derived extension. |
| E_i preserves bounded constructibility | The implication for each M in `clopenSupport_insertion`, with precisely `intrinsicFiniteTorsionConstructible` on source and target. `clopenSupport_restriction_constructible` also makes explicit the corresponding restriction clause used in the final comparison. |
| E_i agrees with j_i,! | E_i is represented by this existing functor itself. Its equality with zero insertion is expressed by the diagonal/off-diagonal statements, using the equivalence of `lem-pur-finite-clopen-derived-decomposition`. No independently chosen extension or alternate coefficient category is used. |
| K is the finite direct sum of E_i r_i K | Final clause of `clopenSupport_insertion`: invertibility of `biproduct.lift (fun i ↦ (R i).unit.app K)`. This is the specified decomposition map in the derived category, not a list of cohomology isomorphisms. |
| Identity normalization on X_i | `(L i).unit = sfIntrinsicDerivedOpenUnit ...`, `IsIso (L i).unit`, and `(L i).unit.app M ≫ (R i).counit.app M = 𝟙 M`. The diagonal restriction is identified with identity by this specified open unit; the right counit is its inverse. |
| Natural unit-compatible a_!E_i ≅ (a j_i)_! descending the ordinary comparison | The existing `sfIntrinsicDerivedOpenComp` used in `clopenSupportComponentComparison`. Its body is `mapDerivedCategoryNatIso (sfIntrinsicOpenComp ...)` followed by exact-derived composition. `sfIntrinsicOpenComp` is constructed by uniqueness of left adjoints to the identical composite restriction and its composite unit; this fixes its normalization. |
| b_i,n is obtained by applying the same Rp_* | `clopenSupportComponentComparison`: the associator followed by `Functor.isoWhiskerRight (sfIntrinsicDerivedOpenComp ...).symm (proEtaleConstantDerivedDirectImage c.g P.Ring)`. Its source is `E_i ⋙ sfIntrinsicCompactSupport c P.Ring` and its target is `sfIntrinsicCompactSupport (c.precomp ...) P.Ring`. |
| Natural finite-sum compact-support isomorphism, the image of the decomposition | `clopenSupportSumMap` is the lift whose ith projection is `F_g^c.map ((R i).unit.app K)` followed by `b_i,n`. `clopenSupport_sum` states its invertibility; `clopenSupportSumIso` supplies the actual derived isomorphism with exactly that forward map. `clopenSupportSumMap_naturality` states the naturality square, with `biproduct.map` of the component functors on its right. |
| The supplied R and hR in the sum declarations introduce no extra geometric hypothesis | They are the decomposition adjunction and invertibility furnished by `clopenSupport_insertion`. The sum result works for any such decomposition data; choosing the previously supplied data gives the node's assertion. |
| Canonical compactification comparisons on bounded constructible inputs | `clopenSupportCanonicalComparison_existsUnique` supplies a unique natural isomorphism of functors from the full recorded constructible subcategory. For every bounded-below etale representative and every identification with K, its component equals the conjugate of `clopenSupportEtaleComparison`. The latter is the published canonical `fixedCompactSupportOriginIso` transported through the fixed constant-ring realization. |
| Canonical identity and cocycle normalization | `clopenSupportCanonicalComparison_coherence`. The definition `clopenSupportCanonicalComparison` chooses only from the preceding unique characterized comparison. |
| Agreement of b with compactification-independent functors | `clopenSupportConstructibleInsertion` is the actual insertion restricted to the full constructible subcategories. `clopenSupportIndependentComponentComparison` is exactly theta_g inverse, b, theta_i. `clopenSupport_independent` states independence of the auxiliary common c. Arbitrary chosen representatives c0,d0 of the compactification-independent functors are allowed. |
| Agreement of the finite sum through the same canonical comparisons | `clopenSupportSumMap_compactification` is the explicit commuting square with the source theta and the biproduct of component theta_i. `clopenSupportIndependentSumComparison` constructs exactly theta_g inverse, the common sum, then the biproduct of theta_i, for any c0 and family d0. `clopenSupportIndependentSumComparison_eq` states independence of c. |
| Empty index family | `clopenSupport_sum` explicitly concludes `IsZero K ∧ IsZero (F_g^c.obj K)` under `IsEmpty I`. Its isomorphism target is the empty biproduct. All other statements retain the same empty index family. |

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `.Ring`,
  `.Coefficient`, the recorded finite field/coefficient structures and positive level.
  The existing `ringFinite`/`coefficientFinite` instances are reexported by
  `Sheaf.Paper.ConstructibleExceptionalInverseImage`; this import is needed for
  these coefficient instances, not for any exceptional-adjoint assumption.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `.FiniteType`, `.QuasiCompact`,
  `.ClosedImmersion`, `.Separated`, and `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `IsProper`, `LocallyOfFiniteType`, `QuasiCompact`, `IsClosedImmersion`,
  `IsSeparated`, `IsOpenImmersion`. These definitions appear transitively in the
  public imports; their full class fields/docstrings were checked in the source.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `.topology`;
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `proEtaleDerivedCategory`.
  The site has its recorded object universe u+1, morphism universe u.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`, a full subcategory defined by finite
  cohomological support and intrinsically constructible cohomology.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `WeilConjectures.finiteDerivedPullback`,
  which is precisely the published `sfIntrinsicDerivedPullback` at the positive
  exponent (that API names it n+1). This delivery uses P.level directly and never
  excludes level 1.
- `Sheaf.Paper.FiniteClopenDerivedDecomposition`:
  `finiteClopen_module_equivalence`, `finiteClopen_unbounded_decomposition`,
  `finiteClopen_finite_bounds`, `finiteClopen_finite_restriction_identification`.
  These give restriction/gluing and its actual intrinsic identification; they are
  the proof inputs for the zero-coordinate characterization above.
- `WeilConjectures.Compactification.RefinementCategory` and its public `Defs`:
  `Compactification`, `.Refinement`, `.category`, `.precomp`; the actual proper
  part, open part and factorization were read.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `sfIntrinsicExtensionByZero`, `sfIntrinsicModuleEquivalence`;
  `ProEtaleIntrinsicExtensionByZeroExact`: `sfIntrinsicExtensionByZero_exact` and
  its additive/left-exact/right-exact instances.
- `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`:
  `sfIntrinsicOpenAdjunction`, `sfIntrinsicOpenComp`, `sfIntrinsicDerivedOpen`,
  `sfIntrinsicDerivedOpenUnit`, `sfIntrinsicDerivedOpenComp`;
  `ProEtaleIntrinsicFiniteOperations`: `sfIntrinsicDerivedPullback`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: `sfIntrinsicCompactSupport`,
  literally exact open extension followed by `proEtaleConstantDerivedDirectImage`.
- `Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange`:
  `ProEtale.sfIntrinsicCompactSupportComparison`; and
  `Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction`:
  `ProEtale.fixedCompactSupportOriginIso`. Both canonical realization/comparison
  bodies and full signatures were read. They normalize the bounded-constructible
  comparison; no ordinary ambient exceptional adjunction is assumed.
- Proof imports: `NagataCompactification`, `exists_topologicalKrullDim_le`,
  `sfIntrinsicExtensionByZeroAdjunction`, `constructible_proEtale_origin`,
  `compactification_coherence`, `ProEtaleConstantRingOperations`, the exactness
  theorem, `CategoryTheory.unit_conjugateEquiv_symm`, and
  `CategoryTheory.Localization.lift` (with its natural-transformation descent).
  The Mathlib Noetherian and finite-type composition/base-change declarations
  are the recorded matches for the geometry proof dependencies.

Edge cases checked before completing the statement: arbitrary finite I in an
independent universe; I empty; empty individual components; X empty with either
empty or nonempty I; compactifications with additional boundary components;
empty and nonempty c.Z; level n=1; zero complex; unbounded nonconstructible K.
The ambient formulas impose no boundedness and no etale-origin assumption.
Compactification independence is confined to the bounded constructible full
subcategory, and its etale normalization ranges over every representative and
every isomorphism to K. Y may be nonseparated over k throughout. The dimension
conclusion does not infer the dimension of c.Z from X (extra boundary components
are allowed); it uses c.Z finite type over k through the proper part.

Sources opened: the current `def-pur-section-invariant.md`, the detailed
compact-support definition and compactification-coherence blueprint unit;
Stacks `sites-modules.tex` at `lemma-extension-by-zero` (03DI) and
`lemma-extension-by-zero-exact` (03DJ), and `sites.tex` at
`lemma-mapping-property-glue` (04TS). The theorem docstrings expand the node's
proof steps 1--8 and name the relevant dependency declarations for stage 3.

Searches actually run (the initial three are preserved in searches.jsonl):

- msearch leanfinder, query `finite clopen decomposition compact support direct image common compactification zero insertion extension by zero`: 8 hits, headed by `HasCompactSupport.extend_zero`; these concern functions, not derived module-sheaf compact support. No exact match.
- msearch grep, query `clopen|zeroInsertion`, Mathlib subdirectory `CategoryTheory`: zero hits.
- msearch loogle, query `Compactification, Functor.pi`: zero hits, with diagnostic `unknown identifier 'Compactification'`; recorded as an unsuccessful identifier query, not evidence that compactifications do not exist. The existing project Compactification declaration is used.
- msearch leansearch, query `Finite clopen decomposition compact support pushforward by shared compactification`: 8 hits including `HasCompactSupport`, `exists_clopen_partition_of_clopen_cover`, `HasCompactSupport.comp_isClosedEmbedding`, and `OnePoint.isClosed_image_coe`; none states the sheaf-derived assertion.
- rg of Mathlib CategoryTheory for finite-clopen/zero-insertion and product adjunctions found no matching common-compactification theorem. Biproduct map/lift/isomorphism primitives were read and reused.
- rg of both project roots and dag/lean_names_upstream.json for `clopenSupport|commonCompactSupport|lem-pur-clopen-common-compact-support` found only the existing private support-under-iso helper in FiniteClopenDerivedDecomposition. The actual dependency modules were searched/read for `sfIntrinsicDerivedOpenComp`, `sfIntrinsicDerivedOpenUnit`, `sfIntrinsicOpenComp`, `sfIntrinsicDerivedPullback`, and `fixedCompactSupportOriginIso` and reused rather than recreated.

No STATEMENT-DISPUTED finding. No weakened or corrected statement.

## Second reading by Q61

This section is the worker's explicit self-audit above, not a claim to an
independent second agent. The dispatched brief assigns independent review to the
maintainer and prohibits spawning agents. Re-reading the node against the module
found that the inherited draft only described sum transport in a docstring; the
final module now states naturality, the explicit compactification square, the
actual transported sum isomorphism and its independence. The diagonal open unit,
common proper part, bounded-constructible restriction of independence, empty
family and nonseparated Y cases were checked explicitly.

Final signature audit: the section instances are named and explicitly included
in theorem binders. In particular `clopenSupport_geometry` retains all finite-type
and quasi-compact hypotheses on X,Y,g and separatedness of g. Insertion and
restriction statements retain finite type of X, finiteness of I and closedness
of every component inclusion, in addition to the open/disjoint/cover data.
Lean must not drop these hypotheses merely because a stage-2 proof is `sorry`.
The explicit result types on the two finite-sum definitions also keep their
elaboration within the per-file limit.
