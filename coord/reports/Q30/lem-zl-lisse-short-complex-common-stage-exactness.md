## Worker report

The module `Sheaf.Paper.LisseShortComplexCommonStageExactness` states
`WeilConjectures.LisseShortComplex.simultaneous_exactness`. Its only postponed proof is
that theorem, with the node's seven-step proof in its docstring. The node's statement
and proof are unchanged. Its statement dependencies now also name the three landed
owners requested by the returned review. All definitions have explicit data.
The owning helpers merely package the finite diagram and the assertions of this theorem;
no independent coefficient category, heart, fibre or realization is introduced.

Clause-by-clause reading:

- `D : FiniteFieldDatum.{u}` fixes p, a >= 1, q = p^a, the field of q elements and its
  fixed algebraic closure. `c : D.CoefficientDatum` fixes the distinct prime l and its
  algebraic closure Qbar. No complex embedding of Qbar is assumed.
- `Y₀ : Over (Spec (.of D.k₀))` with `LocallyOfFiniteType`, `QuasiCompact` and
  `IsSeparated` is exactly a separated finite-type k₀-scheme. Every coefficient
  category is over the existing `(D.geometricFiber Y₀).left`. The existing
  `sfWeilPrimeInvertible` supplies residue-field invertibility; it is not an extra
  hypothesis.
- `F` is a quiver prefunctor into the actual `sfCommonStageHeart`. `Finite V` and
  `∀ i j, Finite (i ⟶ j)` give finitely many vertices and generating arrows. This
  allows loops and inverse arrows without requiring the path category to be finite.
  A vertex's actual pair `((F.obj i).obj.stage, (F.obj i).obj.obj)` is its prescribed
  finite model. `_models` requires exactly that model to lie in the finite lisse heart,
  using the recorded `rationalLisseHeartProperty`; it does not assume integral
  lissity or integral exactness.
- `Presentation` gives finitely many path equations (`Q`) and short complexes (`J`).
  A path is evaluated with Mathlib `Paths.lift`; `none` denotes zero. Identity paths
  are allowed, so specified inverses are ordinary generating arrows and their two
  inverse equations. Composite-zero equations are also allowed. `first`, `middle`,
  `last`, `f`, `g`, `zero` specify precisely the displayed short complexes.
- `_fibres` requires injectivity, `Function.Exact` and surjectivity for every complex
  and every scheme map `Spec k ⟶ Y`, with no k-linearity restriction. These maps are
  the explicit composite of heart inclusion, `commonStageDerivedPullback`,
  `pointQbarFibre`, and `DerivedCategory.coefficientQbarCohomology ... 0`.
  The prime-invertibility arguments are `dlAdicGeometricResidueInvertible`. As objects are in the heart this
  is the stated normalized point-fibre short exactness, rather than exactness of
  an arbitrary stalk or of an integral representative.
- The first conclusion is `(∀ j, (P.complex j).ShortExact)` in the sf common heart.
  The second chooses one finite `E`, upper-bound witnesses `h` for every prescribed
  vertex stage, and representatives `A` for every generating arrow.
- `model K E h` is literally `K.obj.toStage h`, the existing scalar extension of
  the original finite object. `StageAssertions` requires that each such object is
  in `rationalLisseHeartProperty`, that `ofHom ... (A a)` is the original arrow,
  and that every prescribed path equation holds at E. Thus neither vertex models
  nor rational arrow classes are replaced.
- The sf short exactness conjunct provides heart objects equal to these literal
  models and arrows heterogeneously equal to the prescribed `A(f)` and `A(g)`.
  It uses Mathlib `ShortComplex.ShortExact`, including mono, middle exactness and
  epi, rather than just zero composite.
- The PBC conjunct uses the normalized comparison's actual `family.Φ E`; its
  `finite_functor` field identifies it with `stage E`'s identity-normalized rational
  equivalence. It supplies a `ShortExact` complex in the actual localized standard
  PBC heart, with those image objects and those image arrows. The quantified
  Noetherian, dimension and prime-unit instance arguments are all consequences of
  the given geometry; they introduce no assumptions in the theorem's hypotheses.
  Quantifying over normalized comparison systems does not permit an arbitrary
  equivalence. `HEq` deliberately accommodates the two canonical Shrink coefficient
  presentations without expensive conversion of their category instances.
- For every `L >= E`, the theorem repeats all `StageAssertions` for the original
  vertices extended directly to L and arrows `(stageSystem ...).tr k (A a)`.
  This is the existing associator-conjugated scalar transport, not an arbitrary
  second choice of representatives.
- `Presentation.weil` optionally supplies the original Frobenius isomorphisms,
  including inverses through `Iso`, and `equivariant` is their actual intertwining
  equation. The last conjunct supplies finite `θE` with `WeilAt`: equivariance for
  every arrow and equality to the original Weil maps under canonical `isoToStage`
  and `sfWeilStagePullbackIdentification`. `frobeniusScalar` uses the existing
  tensor-normalized `rationalPullbackScalarComparison` and transition identification.
  `extendWeil` conjugates its scalar extension by the recorded scalar associators.
  `WeilAt` is required for this very extended structure at every L >= E, retaining
  both equivariance and the same original realized structure through every extension.
- No nonempty assumption is imposed on vertices, equations, complexes, or geometric
  points. Zero complexes and an empty family are allowed. An empty diagram can use
  the base finite coefficient field; the empty scheme is not excluded.

Dependency declarations read and used (the modules are imported publicly when they
serve the statement):

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `CoefficientDatum`, `geometricFiber`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `FiniteFieldDatum.geometricFrobenius`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`
  and its publicly imported coefficient constructions (not a new coefficient field).
- `Sheaf.Paper.LisseIntegralSmallCoefficients`: `Scheme.LisseIntegralSheafOfUniverses`,
  retaining the classical lisse categories through its public original lisse module.
- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalHeart`, `sfCommonStageHeart`, their properties.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Stage`, `stageSystem`,
  `inclusion`, `ofHom`, `Coefficient`, and the upstream `toStage`, `tr`, `isoToStage`.
- `Sheaf.Paper.LisseRationalRealization`: `LisseRealization.lisse_rational_realization`,
  with public `rationalLisseHeartProperty` and its local finite-free interpretation.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointQbarFibre`.
- `Sheaf.Paper.CoefficientCohomologyModules`: `DerivedCategory.coefficientQbarCohomology`,
  owned by `def-weil-coefficient-cohomology-modules`.
- `Sheaf.Paper.DlLocallyConstructibleAdicHeart`: `dlAdicGeometricResidueInvertible`,
  owned by `def-dl-a1-locally-constructible-adic-heart`.
- `Sheaf.Paper.DlConstructibleFibresExact`: `dlConstructibleFibresExact`, imported
  only as a proof dependency. Its current theorem has an unrelated complex embedding
  argument, so this statement does not inherit that additional hypothesis.
  No declaration from this statement node occurs in the theorem signature.
- `Sheaf.Paper.SfWeilSheafComplex`: both Frobenius pullbacks,
  `sfWeilPrimeInvertible`, `sfWeilStagePullbackIdentification`.
- `Sheaf.Paper.DerivedPullbackTensorHom` (public through the dependency modules):
  `operationStageTransitionIso`, `rationalPullbackScalarComparison`.
- `Sheaf.Paper.RationalCoefficientCategoryComparison`: the normalized
  `FdCoefficientComparisonSystem`, `FdCoefficientComparison.family`, `finite_functor`,
  and `rationalCoefficientCategoryComparison`.
- `Sheaf.Paper.LocalizedTStructure`: `Scheme.pbc_localized_tstructure` and its uniquely
  determined integral-image standard halves, owned by the explicitly cited
  `prop-weil-localized-tstructure`.
- `Mathlib.Algebra.Homology.ExactSequence` and
  `Mathlib.Algebra.Homology.ShortComplex.ShortExact`: `ComposableArrows.Exact`,
  `ShortComplex`, `ShortComplex.ShortExact`.

The stated proof dependencies are imported, including intrinsic scalar exactness,
constructible truncations, the heart-triangle interface, both integral/standard
half interfaces, integral stratified-perfect comparison, and the triangulated axioms.
No missing dependency repair or new node was necessary.

Edge cases checked before finalizing: empty diagram, empty equation set, empty complex
family, all-zero complexes, rank zero, repeated vertices, loops and inverse identities,
identity coefficient extension, arbitrary further coefficient extension, and empty Y.
Optional Weil structures use geometric Frobenius on schemes, never a k-linear replacement.
All universe parameters are explicitly declared; no auto-bound implicits are enabled.

Searches actually run:

- msearch leanfinder: `finite lisse diagram short complexes exact on geometric fibres
  simultaneous finite coefficient stage exactness`: eight hits on abstract short
  exact sequences and related algebra; no coefficient-stage descent theorem.
- msearch loogle: `CategoryTheory.ShortComplex.ShortExact, CategoryTheory.Functor`:
  twelve hits, including `ShortExact.map`, abstract exact functors and derived
  short-exact triangle maps; none has the lisse/common-stage content.
- msearch grep: `commonStage.*[Ee]xact|[Ll]isse.*[Ss]hort|[Ss]hort.*[Ll]isse`:
  zero Mathlib hits.
- msearch leansearch: `finite diagrams descend along a filtered colimit of coefficient
  categories with prescribed equations`: eight abstract filtered-colimit or filtered
  category hits; none is this theorem.
- rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `lisse-short-complex`, `LisseShortComplex`, `FiniteLisseDiagram`,
  `shortComplexCommonStage`: no existing declaration of the assertion.
- rg for common-stage short exactness found `AdicNormalizedFibreCommonStage`'s PBC
  single-sequence representatives, and `CommonStageFiniteHomLifting`'s Hom lifting.
  Both were read; neither retains this finite sf lisse diagram, prescribed vertex
  models, all equations, sf/PBC exactness and optional Weil assertions.

Sources read: the current blueprint `thm-zl-real-mixed-by-curves.proof.md` first
paragraph and the local BS PDF, Corollary 6.8.5, Lemma 6.8.7, Proposition 6.8.14(1),(2),
Remark 6.8.15. Their abelian lisse/constructible categories and finite coefficient
assembly agree with this node. No statement correction or dispute was found.

Validation: scompile.py compiled both the sandbox and named library module cleanly
within the required 60-second per-file limit. The PBC map expression initially
triggered expensive elaboration through its rational equivalence; using its existing
stage-system `family.Φ E` (identified by `finite_functor`) resolved that issue without
changing the mathematical comparison or raising the time limit. The one line-width
warning was fixed. All proofs remain postponed.

## Second reading by Q30

I reread the node and complete module after the clean compile. This is a second pass
by the dispatched worker, not a claimed independent worker review; the dispatch brief
forbids starting another agent, and the maintainer's independent review follows delivery.
The pass checked the finite-field and finite-type hypotheses, the prescribed literal
models and arrow classes, all path equations including identity and zero paths,
normalized H^0 point fibres, both short-exact heart conclusions, every further field,
and the optional Weil clause against the node. It found that merely re-choosing Weil
maps at further fields would not explicitly preserve the chosen finite structure;
`frobeniusScalar`, `extendWeil` and the final `WeilAt` tower clause were added to retain
that exact scalar extension. No other mismatch remained. No integral exactness or
complex embedding assumption was introduced. Empty families and zero ranks remain allowed.

## Repair of returned delivery

The retained delivery is the version reviewed at immutable head `a82e23b1fef2`.
Comparison with the current shared node shows the same mathematical statement and
proof. This repair changes the module and the node record, rather than re-pushing
the returned version unchanged.

1. Replaced all four occurrences of `dlAdicHeartFibre` in `_fibres` by its literal
   composite body. Read the complete signatures and docstrings of its component
   cohomology and residue-invertibility declarations. Added the landed owners
   `def-weil-coefficient-cohomology-modules` and
   `def-dl-a1-locally-constructible-adic-heart` to `stmt_deps`, with public imports
   of their modules. `DlConstructibleFibresExact` is now a plain proof import; its
   helper no longer appears in the signature. The composite is definitionally the
   original normalized H^0 fibre, including its two residue-invertibility arguments.
2. Added landed `prop-weil-localized-tstructure` to `stmt_deps`, owning the existing
   `.choose.heart` in `StageAssertions`. Its integral-image characterization and
   public module import are unchanged. No arbitrary t-structure is substituted.

Neither repair changes a mathematical hypothesis, conclusion, model, or equation.
No new nodes or dependency modules are required. The shared-universe advisory for
`Q` and `J` does not affect these finite index types or their edge cases.

Repair validation: scompile.py compiled the repaired sandbox module in 23.9 seconds
and the named library module in 16.8 seconds, with exit code 0 and no warnings.
The signature record was regenerated verbatim from the repaired file; only `lean`
and the three requested `stmt_deps` additions differ from the current shared node.
A second reading confirmed that no `dlAdicHeartFibre` occurrence remains in the
module, and each of the four expanded composites is its literal definition body.
