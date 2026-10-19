## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleStalkConservative` states all four clauses of
`lem-cbc-proetale-stalk-conservative`. Every theorem proof is `sorry`. The definitions
contain real data. No node statement or dependency list changes; no new node or dependency
module is needed. The additional declarations are helpers for notions explicitly introduced
by this node: functorial restriction/cohomology stalks and its concrete quotient sheaf.

Hypotheses and clauses:

- `T : Scheme.{u}` is arbitrary. `Λ : Type (u + 1)`, `[Ring Λ]`, `[Finite Λ]`,
  `[TopologicalSpace Λ]`, and `[DiscreteTopology Λ]` express precisely finite discrete
  left coefficient rings, without commutativity or nontriviality. All derived objects use
  the recorded `FiniteCoefficientDerivedCategory T Λ`, not degreewise isomorphisms.
- Clause 1 is `finiteCoefficient_cover_detection`. An arbitrary index set `ι : Type v`
  and `U : ι → T.ProEt` give the covering arrows. `hU` is membership of their actual
  `Presieve.ofArrows` in `Scheme.proetalePrecoverage T`, not mere surjectivity.
  Its first conjunct is `IsIso f ↔ ∀ i, IsIso (...mapDerivedCategory.map f)` for
  every ambient derived morphism. `SheafOfModules.overFunctor` expresses inverse image
  on the slice site; the slice of the small pro-etale site over `U i` is canonically
  the small pro-etale site of `(U i).left`. Thus this is exactly restriction along the
  covering arrow, with its coefficient sheaf restricted. The helper exactness theorem
  supplies the additive/exact structures required to descend this actual functor.
  The second conjunct is `K.Acyclic ↔ ∀ n : ℤ, IsZero (K.homology n)` for cochain
  complexes. The third is `IsZero H ↔ ∀ i, IsZero (...overFunctor.obj H)`.
- Clause 2 on affine T is `finiteCoefficient_affine_basis_detection [IsAffine T]`.
  Its first conjunct tests vanishing by `Subsingleton` of every underlying module
  of sections on `T.AffineProEt` via the recorded `AffineProEt.toProEt` inclusion.
  Modules contain zero, so this is exactly a zero module. Its second conjunct tests
  `IsIso` on `.val.app` of every `DerivedCategory.homologyFunctor ... n` map.
  These are sections of cohomology sheaves, not homology of evaluated complexes.
  `finiteCoefficient_affine_open_basis_detection` gives the stated general-T version:
  `V i` are affine, `g i` are open immersions, and `hg` says they cover every point.
  Test objects are the actual composite weakly etale maps `W → V i → T`.
- Clause 3 is `finiteCoefficient_etale_origin_stalk_detection`. Its first conjunct
  quantifies `F G : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat Λ))`
  and their morphism `f`. `finiteCoefficientDerivedComparison` is the recorded exact
  comparison functor, applied through `DerivedCategory.Plus.ι`.
  The equivalence tests every integer n and every `t : Spec Ω ⟶ T` with Ω a field
  and algebraically closed in the chosen universe. `finiteCoefficientCohomologyStalk`
  takes ambient cohomology, forgets scalars via `SheafOfModules.toSheaf`, then uses
  the precise pointed-neighbourhood diagram of `proEtaleGeometricStalk` and `colim`.
  Invertibility of the underlying additive stalk map is equivalent to invertibility
  of its coefficient-linear map. The second conjunct uses the recorded predicates
  `isBoundedConstructibleFiniteCoefficient T Λ F/G`, and quantifies every ambient
  morphism `f : F ⟶ G`; it does not assume f was itself supplied as a comparison image.
- Clause 4 is `proEtaleFunctionsQuotient_counterexample`. Here k is any algebraically
  closed field, and A is any nontrivial abelian group in the larger universe, with
  no finite-ring hypothesis. `proEtaleAllFunctionsPresheaf` uses pointwise groups of
  all set maps `U.left → A`, restricting by precomposition. The actual constant-function
  natural map is sheafified, and `proEtaleFunctionsQuotient` is its sheaf cokernel.
  This is the sheafified quotient by the constant abelian sheaf; it is not an arbitrary
  sheaf selected from a mere existence assertion. The first conjunct identifies all
  affine sections with the quotient by the range of `LocallyConstant.coeFnAddMonoidHom`.
  The remaining conjuncts assert zero sections on Spec k, zero recorded geometric
  stalks at every geometric point (including field extensions), and `¬ IsZero Q`.
  `proEtale_abelian_cover_zero_detection` and
  `proEtale_abelian_affine_basis_zero_detection` explicitly retain the warning's positive
  cover/basis criteria for arbitrary abelian sheaves. The latter and cover criterion
  also implement the affine-open-cover extension. There is no false conservativity
  assertion for geometric stalks on arbitrary pro-etale sheaves.

Recorded statement dependencies used:

- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `finiteCoefficientRingSheaf`,
  `FiniteCoefficientModules`, `FiniteCoefficientDerivedCategory`,
  `finiteCoefficientDerivedComparison`, `isBoundedConstructibleFiniteCoefficient`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` (transitively public):
  `Scheme.ProEt`, `Scheme.ProEt.topology`, the coefficient and derived-size convention.
  Its commutative specialization is not substituted for the finite-ring category.
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`:
  `Scheme.AffineProEt`, `Scheme.AffineProEt.toProEt`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` (transitively public): the comparison
  adjunction and exact module inverse image used by `finiteCoefficientDerivedComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk`:
  `Scheme.ProEtaleGeometricNeighbourhood`, `proEtaleGeometricNeighbourhoodForget`,
  `proEtaleGeometricStalk`. The stalk functor is exactly its colimit, including on morphisms.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`, through sheafification
  of the constant presheaf in the quotient construction.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`.

All seven dependency-node statements, their records, and the actual signatures/docstrings
were read. The published `ProEtaleFiniteModules` source was also checked through
`scompile.py --source`; it agrees with the shared source. Available proof-dependency
modules are imported privately, including the canonical comparison-stalk, classical-stalk,
functions-quotient-sections, basis, strict-localization, ind-etale and spectrum interfaces.
The full natural-language proof is split across the clause docstrings; the only helper
proof obligation is exactness of the specified slice restriction and has its own docstring.

Edge cases checked: empty scheme; empty covering family when it really covers; zero ring;
zero sheaves and complexes; negative as well as positive cohomological degrees; disconnected
basis objects; arbitrary ambient morphisms between Dbc objects; noncommutative finite rings;
and geometric points extending k in the counterexample. The nonzero-A assumption is confined
to the counterexample, where it is necessary; it is not imposed on Λ. No degreewise
isomorphism or ordinary-complex evaluation criterion was introduced.

Searches (before writing):

- `msearch.py leanfinder`, query “Isomorphisms in the derived category of pro-etale sheaves
  detected by covers and cohomology sheaves on the affine ind-etale basis”: eight hits,
  mainly scheme etale topology/formal-etale lemmas, `Scheme.Modules.Hom.isIso_iff_isIso_app`,
  and `GrothendieckTopology.W_sheafToPresheaf_map_iff_isIso`. None states the node.
- `msearch.py loogle`, query `DerivedCategory.isIso_iff, Sheaf.isIso_of_isIso_app_of_mem`:
  zero hits and unknown identifier for the latter short name. Generic tools were inspected
  directly in the actual sources instead of treating this as evidence they do not exist.
- `msearch.py grep`, query `proetale.*stalk|stalk.*proetale|isIso_iff.*homology`:
  one Mathlib hit in `ModuleCat/Topology/Homology.lean`, not this statement.
- `msearch.py leansearch`, query “Pro-etale sheaf geometric stalks conservativity
  counterexample all functions modulo locally constant functions”: service unavailable
  (Internal Server Error), recorded without a no-match inference.
- `rg` in Mathlib, `WeilConjectures`, and `lean/Sheaf`, including `conservative`,
  `AffineProEt`, `proEtaleGeometricStalk`, functions-quotient names, and all new declaration
  names. The existing cover-conservativity, dense-basis and stalk-comparison tools supply
  parts of the proof, but no declaration states all clauses. The existing functions
  quotient theorem quantifies an F and i; it does not give the actual constructed quotient
  data needed by the node. The definitions here use sheafification and cokernel directly.
- Required `grep -rn "lem-cbc-proetale-stalk-conservative"` in the upstream source:
  no occurrence. `scompile.py --source Sheaf.AlgebraicGeometry.ProEtaleStalkConservative`:
  source unavailable, confirming no recorded published module with that intended name.
- `tools/blueprint_refs.py search 'functions quotient'`: no indexed blueprint hit;
  DAG/node and source searches did locate `lem-cbc-proetale-functions-quotient-sections`,
  which is reused as a proof dependency, rather than duplicated.

Source check: the exact Stacks [0991](https://stacks.math.columbia.edu/tag/0991) and
[0F6D](https://stacks.math.columbia.edu/tag/0F6D) pages were opened, especially the affine
quotient formula and nonzero sheaf with zero geometric stalks. The inherited blueprint
paths are not materialized in this read-only mirror; the node contains the full repaired
statement and proof, and the cited primary source agrees. No statement dispute or
source-based correction is needed.

Validation: every delivered module is compiled separately with the prescribed `scompile.py`
wrapper, under the unchanged 60-second limit. Expected theorem `sorry` warnings alone are
permitted. The final dry-run result is recorded below after running `deliver2.py --no-push`.

Final validation: `scompile.py` passed both sandbox and library modes without errors or
warnings. `deliver2.py Q13 lem-cbc-proetale-stalk-conservative --no-push` printed
`OK (dry run)` for commit `bfbcdf9459`: compilation and preflight passed except for the
second-reading section reserved for the independent reader. Nothing was pushed.
The first dry run encountered a concurrent Git config lock; retrying the prescribed
wrapper succeeded without any direct Git command or shared-repository edit.

## Second reading by Q13

I opened the item node `dag/nodes/sec-smooth-purity/lem-cbc-proetale-stalk-conservative.json`, the
module `lean/Sheaf/AlgebraicGeometry/ProEtaleStalkConservative.lean`, and all seven `stmt_deps`.
The node introduces a finite discrete ring `Λ`, an arbitrary scheme `T`, left module sheaves,
and the recorded pro-etale derived categories. The file renders these as
`(T : Scheme.{u)}`, `(Λ : Type (u + 1))`, `[Ring Λ] [Finite Λ] [TopologicalSpace Λ]
[DiscreteTopology Λ]`, `FiniteCoefficientModules T Λ`, and
`FiniteCoefficientDerivedCategory T Λ`. The universe lift is the same size convention used by
the dependency module; no commutativity, nontriviality, Noetherianity, finiteness of `T`, or
extra coefficient hypothesis is present.

For clause 1, the node's pro-etale covering family is the Lean `U : ι → T.ProEt` together with
`Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
Scheme.proetalePrecoverage T`. The derived assertion is exactly
`∀ F G f, IsIso f ↔ ∀ i, IsIso ((SheafOfModules.overFunctor ... (U i)).mapDerivedCategory.map f)`;
`overFunctor` is the slice-site inverse image recorded by the restriction dependency. The
acyclicity clause is `∀ K : CochainComplex ..., K.Acyclic ↔ ∀ n : ℤ, IsZero (K.homology n)`,
so the cohomology objects are the module sheaves of the node. The sheaf-vanishing clause is
`IsZero H ↔ ∀ i, IsZero (overFunctor ... (U i)).obj H`. All three directions and quantifier
orders match. The exactness and derived-category helper declarations preceding the theorem are
real interfaces with postponed proofs, not altered hypotheses.

For clause 2, the affine hypothesis is precisely `[IsAffine T]`. The first conclusion is the
vanishing test on every `W : T.AffineProEt`, rendered as
`Subsingleton (H.val.obj (op ((Scheme.AffineProEt.toProEt T).obj W)))`; a module section has a
zero element, so this is the zero-module condition. The isomorphism test is on every integer
`n` and every `W`, and is the component of
`DerivedCategory.homologyFunctor ... n` at that basis object. The general version introduces
`V : ι → Scheme.{u}`, affine instances, open immersions `g i`, and the point-cover condition
`∀ t : T, ∃ i x, g i x = t`, then tests the composite weakly-etale objects
`W → V i → T`. This is exactly the affine-open-cover extension, including an empty index only
when the displayed cover condition permits it; ordinary complex evaluation is not asserted.

For clause 3, the first conjunct quantifies exactly `F G : DerivedCategory.Plus
(Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`, `f : F ⟶ G`, and compares the map of
`finiteCoefficientDerivedComparison` (the recorded `ν_T^*`) with every
`Ω : Type u`, field/algebraically-closed instances, geometric point `t`, and `n : ℤ`. The
stalk functor is the colimit over `ProEtaleGeometricNeighbourhood t` after taking cohomology
and forgetting to additive groups, which is the node's geometric stalk of the cohomology
sheaf. The second conjunct quantifies arbitrary ambient morphisms between objects satisfying
`isBoundedConstructibleFiniteCoefficient`; this is the recorded essential-image definition of
`Dbc`, and does not require the morphism itself to be presented as a comparison image.

For clause 4, the file constructs the all-functions presheaf by precomposition, the constant
map, and the sheafified cokernel `proEtaleFunctionsQuotient`. For algebraically closed `k` and
an arbitrary nontrivial abelian `A`, it gives the affine formula for every affine `U`, zero
sections on `Spec k`, zero `proEtaleGeometricStalk` at every algebraically closed field point
(including extensions), and `¬ IsZero` for the quotient sheaf. The affine formula is encoded by
`Nonempty ((U.left → A) ⧸ range(LocallyConstant.coeFnAddMonoidHom) ≃+
Q.obj.obj (op U))`, the standard Lean encoding of the node's additive-group isomorphism/value
identification. It does not choose an arbitrary sheaf or a mere existence witness: the quotient
is the explicit cokernel of the sheafified constant-function map. The nontriviality assumption
is confined to this counterexample, as in the node.

I read the declarations and docstrings of `ProEtaleFiniteModules`, the pro-etale site and
`AffineProEt`, site comparison, geometric stalk, constant sheaf, and sheafification modules.
Their objects, coefficient categories, comparison functor, basis inclusion, and stalk colimit
are the exact notions used above. No duplicate declaration exists in Mathlib, `WeilConjectures`,
or `lean/Sheaf`; `rg` found no prior item module or theorem with this statement. The searches
run independently were `msearch.py ... leanfinder 'pro-etale sheaf geometric stalk conservative
derived category'` (only generic etale/stalk hits), `msearch.py ... loogle 'IsIso homologyFunctor
proEtale'` (zero hits; the service reports `IsIso` unknown), and `msearch.py ... grep
'proEtaleFunctionsQuotient|proEtaleGeometricStalk|cover_detection'` (zero existing match).
The source pages opened were Stacks Tags 0991 (points and the geometric-stalk counterexample),
0993 (strict-local evaluation), 0GLZ (comparison inverse image), and 0F6D (functions modulo
locally constant functions); the four clauses follow those source places.

Edge cases checked are the empty scheme and genuinely empty covering family, zero coefficient
ring and zero sheaf/complex, arbitrary disconnected affine basis objects, all positive and
negative integer degrees (including degree zero), noncommutative finite rings, empty/zero
sections, arbitrary geometric field extensions of `k`, and nontrivial versus zero `A`. No
extra characteristic, field, properness, or universe-equality condition is introduced.

No mismatch was found between the node and the Lean signature, and no file or node change was
needed. The module compiles cleanly with the required `scompile.py` wrapper; only the expected
`sorry` theorem warnings occur. The only delivery repair was this independent second-reading
record.
