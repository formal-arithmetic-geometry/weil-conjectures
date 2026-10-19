## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ProEtaleVanishingDetection.lean` states the two clauses of `lem-sf-proetale-vanishing-detection` for the landed finite discrete coefficient ring presentation.  Its declarations are `AlgebraicGeometry.ProEtale.finiteCoefficient_isZero_iff_forall_affine_weaklyContractible` and `AlgebraicGeometry.ProEtale.finiteCoefficient_acyclic_iff_forall_affine_weaklyContractible`; all three proofs (including the concluding joint conservativity theorem) are deliberately `sorry`.

The variables `(T : Scheme.{u})` and `(Λ : Type (u + 1)) [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]` render “a scheme” and “a finite discrete ring”.  The first theorem's `(F : FiniteCoefficientModules T Λ)` renders a sheaf of left modules over the coefficient sheaf from `def-weil-pbc-proetale-modules`; `IsZero F` renders `F = 0`.  For each `(W : T.ProEt)`, `IsAffine W.left` renders “affine object”, and `(Scheme.ProEt.topology T).IsWeaklyContractible.{u + 1} W` renders “weakly contractible for the full small pro-etale site”.  The conclusion `Subsingleton ((SheafOfModules.evaluation (finiteCoefficientRingSheaf T Λ) (op W)).obj F)` renders `F(W)=0`, since the displayed object is the module of sections and a module is zero exactly when its carrier is subsingleton.

The second theorem's `(K : CochainComplex (FiniteCoefficientModules T Λ) ℤ)` renders an unbounded integer-indexed complex of coefficient module sheaves.  Its left side `K.Acyclic` is acyclicity.  The right side quantifies the same affine weakly contractible `W` and applies the canonical `SheafOfModules.evaluation` functor termwise through `mapHomologicalComplex`; `HomologicalComplex.Acyclic (...)` is the acyclicity of the evaluated complex.  Thus every hypothesis and both numbered clauses are represented without adding a cover choice or a boundedness assumption.  The final “detection device” sentence in the node is the immediate interpretation of these two equivalences and introduces no extra formal proposition.

Dependency declarations used:

* `def-weil-pbc-proetale-site`: `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` in `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` (the pro-etale site and derived-category presentation).
* `def-weil-pbc-proetale-modules`: `AlgebraicGeometry.ProEtale.finiteCoefficientPresheaf`, `finiteCoefficientRingSheaf`, `FiniteCoefficientModules`, and `FiniteCoefficientDerivedCategory` in `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`.
* `lem-weil-pbc-proetale-affine-wcontractible-covering-family`: `AlgebraicGeometry.Scheme.ProEt.exists_affine_weaklyContractible_covering_family` in `Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover`.
* `lem-cbc-proetale-stalk-conservative`: `AlgebraicGeometry.ProEtale.finiteCoefficient_cover_detection` (and the accompanying finite-coefficient detection declarations) in `Sheaf.AlgebraicGeometry.ProEtaleStalkConservative`.

The imports include all four statement-dependency modules.  The source-side weakly contractible framework was read in `WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible`: its declarations `isZero_iff_forall_isWeaklyContractible` and `acyclic_iff_forall_isWeaklyContractible` are for `[CommRing Λ]`, so they do not exactly state this node for an arbitrary finite (possibly noncommutative) ring.  The present declarations retain the node's `Ring` hypothesis and use the finite-coefficient ringed-site presentation.

Edge cases checked against the source and dependency docstrings: the empty pro-etale object and empty covering family; the zero coefficient ring; disconnected schemes and nonconstant continuous coefficient functions; arbitrary finite noncommutative rings; and unbounded complexes (the statement has no boundedness restriction and quantifies every integer degree through `Acyclic`).  `IsAffine W.left` and weak contractibility are separate hypotheses, as required by the source.

Searches for an existing exact declaration:

* `msearch.py ... leanfinder "vanishing finite coefficient module sheaf sections affine weakly contractible pro-etale object acyclic complex evaluation"`: eight unrelated affine-transition/étale and cotangent hits; no exact match.
* `msearch.py ... loogle "IsZero SheafOfModules evaluation Acyclic"`: zero hits (`IsZero` was not resolved by the service).
* `msearch.py ... grep "weaklyContractible|Acyclic|finiteCoefficient" Mathlib/AlgebraicGeometry/Sites`: zero hits.
* `rg` over `lean/Sheaf` and the side `lean/WeilConjectures` found the commutative-only upstream theorems above and the generic cover/evaluation dependencies, but no theorem with the node's finite `Ring` hypotheses.

No `STATEMENT-DISPUTED` marker or node fault was found.

The concluding joint conservativity assertion is also stated explicitly by
`finiteCoefficient_isIso_iff_forall_affine_weaklyContractible`: for every pair of
coefficient module sheaves and morphism `f`, `IsIso f` is equivalent to every affine
weakly contractible evaluation being an isomorphism. The final geometric-stalk
warning is the already recorded and imported
`Scheme.proEtaleFunctionsQuotient_counterexample`; its general failure assertion
is not restated. The module docstring points to this exact warning declaration.

The recorded `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`
module publicly re-exports `ProEtaleFiniteModules`, whose coefficient module
category is the notion used here. We import this smaller owning module directly:
importing the intrinsic-comparison extension together with the required
stalk-conservativity module duplicates the legacy and reorganized upstream
UpperLowerStar notation declarations. The smaller import preserves exactly the
recorded finite coefficient notion; the commutative intrinsic-comparison extension
is not needed to state this item. Proof-only imports
include the site/sheaf equalizer framework, `ringedSiteModules`, the module
sheafification interface, and the evaluation-preserves-homology dependency. The
latter source was read through `scompile.py --source`, since the shared mirror lacks
that file; its signature is exactly the commutative ring-sheaf statement recorded
in the DAG, and its proof is already present in the published source.

Additional searches: `msearch.py ... leansearch` with the vanishing/acyclicity
criterion returned `UNAVAILABLE`, Internal Server Error. Direct `rg` searches in
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id and
`WeaklyContractible|weaklyContractible` found no declaration there. The matching
commutative-only theorem is in the newer read-only side upstream tree. Sources
were checked directly at [0990](https://stacks.math.columbia.edu/tag/0990),
[0946](https://stacks.math.columbia.edu/tag/0946), and
[0947](https://stacks.math.columbia.edu/tag/0947), since the shared literature mirror
has no local source files. Tag 0947 (1) concerns modules over an arbitrary ring
sheaf and applies to each three-term segment, so there is no commutativity or
boundedness restriction hidden in the stated conclusion.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader assigned by the dispatcher. This worker has
not performed or claimed that independent reading. This section is a placeholder
required by preflight even for the prescribed worker-only dry run; the next worker
must replace it with their actual clause-by-clause review before delivery.

## Second reading by NG

I read the node statement, its Stacks source tags 0990, 0946, and 0947, the four
statement dependencies, and the module independently. The clause-by-clause match is:

* The finite discrete ring Λ is rendered by `Λ : Type (u + 1)` with `[Ring Λ]`,
  `[Finite Λ]`, `[TopologicalSpace Λ]`, and `[DiscreteTopology Λ]`; `T : Scheme.{u}`
  is the arbitrary scheme. The coefficient sheaf is exactly the recorded
  `FiniteCoefficientModules T Λ`, built from the sheafified continuous functions on
  connected components. Verdict: matches, including possibly noncommutative finite rings.
* Clause (i), `F = 0 ↔ F(W) = 0` for every affine weakly contractible pro-etale object,
  is rendered by `finiteCoefficient_isZero_iff_forall_affine_weaklyContractible`.
  `IsZero F` is the categorical zero-object condition, and `Subsingleton` on the
  evaluated module is exactly zero section module. The quantifiers and implication
  order match the node.
* Clause (ii), for an arbitrary integer-indexed complex, is rendered by
  `finiteCoefficient_acyclic_iff_forall_affine_weaklyContractible`. Its
  `CochainComplex ... ℤ` is unbounded, and `mapHomologicalComplex` evaluates the
  complex termwise at the same W; `HomologicalComplex.Acyclic` is the evaluated
  acyclicity conclusion. No boundedness or extra coefficient hypothesis occurs.
* The consequence that these evaluations form a detection device is rendered by
  `finiteCoefficient_isIso_iff_forall_affine_weaklyContractible`, which states the
  corresponding isomorphism criterion for every morphism. The imported
  `Scheme.proEtaleFunctionsQuotient_counterexample` supplies the node's warning that
  geometric-point stalks are not conservative in general.

The edge cases are covered: empty schemes and empty covering families are allowed by
the covering-family dependency; the zero ring and zero module satisfy the same
subsingleton criterion; disconnected schemes and nonconstant continuous coefficient
functions are represented by `finiteCoefficientRingSheaf`; `n = 0` and every integer
degree are included by `ℤ`-indexed `Acyclic`; and no characteristic, Noetherian,
separation, or universe equality is added. The scheme universe is `u`; the small pro-etale site has object universe
`u + 1` and morphism universe `u`, and section modules live in `u + 1`, as in
the dependency declarations.

I searched the project and source trees with `rg`, and ran the prescribed
`msearch.py` LeanFinder, Loogle, and grep searches for finite-coefficient vanishing,
weak contractibility, evaluation, and acyclicity. No exact declaration exists. The
source's `isZero_iff_forall_isWeaklyContractible` and
`acyclic_iff_forall_isWeaklyContractible` require `CommRing`, so they do not replace
this node's arbitrary `Ring` statement. The four dependency declarations were opened
and match the objects used here; no new node or dependency repair is needed.

No mathematical mismatch was found, and no node statement or definition was changed.
The only Lean changes are whitespace at the three theorem endings; the recorded
main signature agrees verbatim with the file up to the proof delimiter. All three
proofs remain `sorry`. I verified every declaration docstring carries the source,
the node proof steps, and `(blueprint: lem-sf-proetale-vanishing-detection)`.
The independent searches used LeanFinder query "Exact evaluation functors on weakly
contractible objects jointly reflect zero sheaves and acyclic unbounded complexes"
(eight generic homological exactness hits), Loogle query `"evaluation", "Acyclic"`
(no hits), and grep for the existing weakly-contractible theorem names (no Mathlib
match). Direct reads of the newer upstream matches confirmed their commutative
fixed-ring encoding, unlike this node's arbitrary finite ring-sheaf encoding.
Compilation through `scompile.py` passed cleanly for the delivered module.

I also located and read the launcher's local `.tex` source mirror: `proetale.tex`,
`lemma-proetale-enough-w-contractible` (0990), and `sites-cohomology.tex`,
`lemma-w-contractible` (0946) and `proposition-enough-weakly-contractibles` (0947).
The surrounding text introduces only a general site and weak contractibility; the
pro-etale specialization assumes only a scheme. I read `sites-modules.tex`,
`lemma-sheafification-presheaf-modules` (03CY) and `lemma-abelian` (03DA), to check
the coefficient-forgetting and integer-action proof plan. These impose no extra
commutativity or boundedness assumption. No `statement_change` is present or needed;
the statement agrees with these source places.
