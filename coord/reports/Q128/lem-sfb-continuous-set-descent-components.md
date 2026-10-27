## Worker report

Delivery: `Sheaf.Paper.ContinuousSetDescentComponents`, declaration
`AlgebraicGeometry.ProEtale.continuousSet_descent_components`.
This is one theorem with `sorry`, matching this node's complete package. It introduces
no definitions, helper axioms, new nodes or dependency-module repairs. Only the item's
`lean` field changes. Its docstring gives all seven proof steps and their DAG inputs.

Sources read: Bhatt--Scholze, *The pro-etale topology for schemes*, Lemma 4.2.12
and the paragraph after its proof, printed p.30, and Lemma 4.3.2(1), printed p.31;
Hemo--Richarz--Scholbach, *Constructible sheaves on schemes*, Example 3.1, printed p.6.
The existing set-function presheaf removes the ring structure of HRS, as explicitly
required by the node; the arbitrary topological-space hypotheses are those of BS.

### Every hypothesis and conclusion

- Compatible sizes: explicit `universe u`, `X : Scheme.{u}`, and
  `D : Type (u + 1)`. This is the size convention of the recorded continuous-set
  presheaf and the small pro-etale site. `set_option autoImplicit false` forbids
  auto-bound variables. Every coefficient comparison space E is also in `Type (u + 1)`.
- Any topological D: `[TopologicalSpace D]` is the sole global hypothesis on D.
  There is no Hausdorff, compactness, group, nonemptiness or disconnectedness hypothesis
  on either of the first two clauses.
- On compact Hausdorff totally disconnected test spaces, finite jointly surjective
  descent: the first conjunct is `Presheaf.IsSheaf (coherentTopology Profinite.{u})`
  of `ContinuousMap.yonedaPresheaf (CompHausLike.compHausLikeToTop ...) D`.
  This Mathlib presheaf has values C(S,D) and precomposition restrictions, by its
  actual definition in `Topology/Category/TopCat/Yoneda.lean:37`. The coherent topology
  on Profinite is the topology of finite jointly surjective covers, including the
  empty cover of the empty space. This is the raw presheaf, not an assumed sheaf.
- On the small pro-etale site of X, the second conjunct is
  `Presheaf.IsSheaf (Scheme.ProEt.topology X) (continuousSetPresheaf X D)`.
  This uses the dependency's recorded presheaf itself.
- A scheme U over X, without requiring U to be weakly etale: the third conjunct
  quantifies `U : Over X`. Quasi-compactness is `CompactSpace U.left` and
  quasi-separatedness is `QuasiSeparated (toSpecZ U.left)`, precisely the scheme
  notion, rather than the relative property of U -> X.
- The quotient target is profinite: the first three conclusions for each such U are
  `CompactSpace (ConnectedComponents U.left)`, `T2Space ...`, and
  `TotallyDisconnectedSpace ...`. `ConnectedComponents` carries Mathlib's quotient
  topology and quotient map `ConnectedComponents.mk`; this is not the set of
  components with a separately imposed topology.
- If D is totally disconnected: only the remaining conclusions inside this qcqs-U
  clause require `TotallyDisconnectedSpace D`. Precomposition is explicitly
  `fun g : C(ConnectedComponents U.left,D) =>
    g.comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩`,
  and `Function.Bijective` asserts both uniqueness and existence of the factor.
  No `T2Space D` is inserted; the older realization module's component theorem had
  that extra hypothesis and therefore does not give this whole statement.
- Naturality in U: for every qcqs `V : Over X`, `a : V ⟶ U` and component function g,
  the first equality says `(g ∘ q_U) ∘ |a| = (g ∘ pi_0(a)) ∘ q_V`.
  The actual map pi_0(a) is Mathlib's
  `a.left.base.hom.continuous.connectedComponentsMap`, bundled with its existing
  continuity theorem. This is the canonical quotient map induced by a, not arbitrary
  map data. Both schemes carry exactly the qcqs hypotheses of the node.
- Naturality in continuous coefficient maps: for any topological totally disconnected
  E, `b : C(D,E)` and g, the next equality says
  `b ∘ (g ∘ q_U) = (b ∘ g) ∘ q_U`. Again there is no Hausdorff assumption on E.
- If D is discrete: the final clause is conditional only on `DiscreteTopology D`.
  Its pointwise open-neighbourhood assertion says that, for any site object U,
  section `s : C(U.left,D)` and point x, there are `W : U.left.Opens` and d with
  `x ∈ W` and `∀ y : W, s y = d`. These neighbourhoods form the required open
  covering on which sections lift from the constant presheaf. The direct C(U,D)
  section type is exactly the value of the dependency's presheaf, without requiring
  Lean to unfold its imported categorical functor composition during function application.
- Local surjectivity and local injectivity on that site are separately asserted as
  `Presheaf.IsLocallySurjective (Scheme.ProEt.topology X)
    (continuousSetConstantPresheafMap X D)` and the corresponding
  `Presheaf.IsLocallyInjective`. Their definitions are the covering image-sieve and
  equalizer-sieve conditions respectively. The latter exactly allows unequal constants
  on the empty scheme to become equal on its empty covering.
- The associated constant sheaf comparison is an isomorphism:
  `IsIso (continuousSetConstantMap X D)`. This map is the existing sheafification
  adjunct of `continuousSetConstantPresheafMap`, whose objectwise formula is
  `d ↦ ContinuousMap.const U.unop.left d`. Its domain is the actual
  `(constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj D` and its target
  is the actual continuous-function sheaf. Thus the map asserted invertible is the
  specified canonical comparison, not an unspecified existential isomorphism.

### Dependency declarations read and used

All seven statement dependencies were read, including their full recorded signatures:

- `def-weil-size-convention`: metatheoretic convention, no Lean definiendum; rendered
  by the explicit universe levels above.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom`; these are schemes and locally ringed-space morphisms.
- `def-sfb-continuous-set-presheaf`: `Sheaf.Paper.TotallyDisconnectedCoefficientRealization`,
  `AlgebraicGeometry.ProEtale.continuousSetPresheaf`; read locally and again with
  `scompile.py --source` from the server. Its actual definition is the restriction
  `(Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙ continuousMapPresheaf D`.
  That same module supplies the existing canonical maps
  `continuousSetConstantPresheafMap`, `continuousSetConstantMap`, and target
  `continuousSetSheaf`; their real data and docstrings were read.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt` and `Scheme.ProEt.topology`, read at lines 100,
  120 and 156; no replacement site is introduced.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf` at line 66, sheafification of the constant presheaf.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`,
  `CompactSpace` at line 283, with no separation axiom.
- `def-weil-quasi-separated-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
  `AlgebraicGeometry.QuasiSeparated` at line 50; the diagonal is quasi-compact.
  Applied to `toSpecZ U.left` it gives precisely quasi-separatedness of the scheme.

The recorded module of the presheaf is imported publicly and already publicly imports
these scheme, site, topology and constant-sheaf interfaces. The raw profinite presheaf
uses `ContinuousMap.yonedaPresheaf` from `Mathlib.Topology.Category.TopCat.Yoneda`;
the same construction occurs inside Mathlib's existing `TopCat.toSheafCompHausLike`.
The canonical quotient and induced map are the existing `ConnectedComponents` and
`Continuous.connectedComponentsMap`, whose signatures and docstrings were read.
`Mathlib.CategoryTheory.Sites.LocallyBijective` supplies the local-bijection predicates.

The stated proof-dependency modules are imported: the spectral-component theorem,
`Sheaf.AlgebraicGeometry.EtaleComparison`, `Sheaf.RingTheory.IndEtaleStability`,
`Mathlib.AlgebraicGeometry.AffineScheme` and `Mathlib.Topology.Separation.Hausdorff`.
The remaining Mathlib proof inputs (fpqc continuous functions, qcqs spectrality,
open-immersion etaleness and local-bijection sheafification) are already in the public
imports above. The future proof-dependency import back into the older realization
module would close an import cycle, because the statement dependency's presheaf and
canonical maps currently live there; the maintainer should omit that backward import
under stages/2-statements.md section 3(7). No proof dependency is removed from the DAG.

### Edge cases checked before writing

1. D empty and U nonempty: there is no section U -> D, so local lifting has no input.
   Both component-function sets are empty, and precomposition is still bijective.
2. U empty, D arbitrary, including empty: both continuous-function sets are singletons.
   The pointwise open-lifting assertion is vacuous; empty coverings witness the
   sieve-based local assertions. No point or coefficient is chosen in the statement.
3. Empty finite covering of a profinite target: joint surjectivity forces empty target,
   whose continuous-map set is a singleton, also for D empty.
4. D a singleton and an infinite discrete D: no finite-coefficient assumption occurs;
   fibre neighbourhoods need not constitute a finite open cover on a non-qcqs U.
5. An arbitrary non-Hausdorff D is allowed in both descent clauses. A non-Hausdorff
   totally disconnected D is also allowed in factorization and coefficient naturality.
6. U the spectrum of a DVR: it is connected although not a one-point scheme;
   factorization uses connected components, not individual closed points.
7. U -> X arbitrary: `Over X` retains schemes over X that are not pro-etale objects
   in the component clause, as required by the node. No extra flatness is assumed.

No statement correction and no disputed statement. The earlier worker's live-wins
refusal confused the existing stage-1 split review with stage-2 completion: the live
node has no `lean` record, and its stage-1 split report explicitly says no Lean work.
This delivery adds the still-missing Lean statement and preserves that review.

### Searches actually run

- `msearch.py ... leanfinder`: query "Continuous maps form a sheaf on profinite spaces
  and pro etale schemes, factor through connected components, and discrete targets
  give the constant set sheaf". Eight results, including `Condensed.lanSheafProfinite`,
  `Condensed.isSheafProfinite` and LightCondensed discrete constructions. None states
  the complete scheme/profinite/component/discrete package.
- `msearch.py ... loogle`: query `"continuousMapPresheaf"`. Ten hits, including the
  fpqc and Zariski sheaf theorems and
  `continuousMapPresheafEquivOfTotallyDisconnectedSpace`. Read their actual signatures
  and Mathlib source. They supply existing notions/partial clauses, not the whole node.
- `msearch.py ... grep`: query
  `continuousSetPresheaf|continuousSetRealization_components|continuousSetConstantPresheafMap`.
  Zero Mathlib hits, as expected for project-only declaration names.
- `msearch.py ... grep`: query `continuousMapPresheaf|ConnectedComponents`, subdirectory
  `AlgebraicGeometry/Sites`. Seven hits, the constant-sheaf file and its use in
  elladic cohomology. Read ConstantSheaf.lean in full.
- `msearch.py ... leansearch`: query "Continuous maps to a discrete space give the
  constant set sheaf on the small pro etale site, with natural factorization through
  the connected components of qcqs schemes". Eight results including
  `CategoryTheory.constantSheaf` and CompHausLike locally constant/continuous
  comparisons. None is the complete statement on the small pro-etale site of a scheme.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`: searched `continuousSetPresheaf`,
  component/discrete constant-function names and the exact item id. The existing
  realization module supplies the constructions used here. Upstream additive
  constant-sheaf results and the etale set-valued comparison have extra algebraic
  structure or a different site, and do not state this node for arbitrary D.
- `rg` for `continuousSet_descent_components` in Mathlib, WeilConjectures and Sheaf:
  no existing declaration with the proposed new full name.

### Validation

Only the prescribed `scompile.py` was used. The first compile found that Lean did
not automatically view an imported functor value as a function during application;
the local-lifting binder was written directly as `C(U.left,D)`, its exact section
space. The final sandbox compile and library-path compile both passed, in 8.0s and
7.5s, with no errors or warnings. No project/global build was run.

## Second reading by Q128

I reread the node and the completed file, independently of writing the signature,
without claiming a second agent's review. The maintainer supplies the independent
review required by this dispatch. I checked each of the four outer conjuncts against
the matching paragraphs of the node. In particular, the first clause concerns the
raw profinite presheaf, the third uses all qcqs schemes over X rather than only
pro-etale ones, and the fourth asserts both local predicates for the specified
constant-section map. Every component quotient uses the quotient topology; the
scheme and coefficient naturalities have the correct variance and endpoints.
The canonical comparison's sheafification source is the associated constant set
sheaf. No hidden `T2Space D` or `Nonempty D` occurs. The only compiler-driven change
was making the open-lifting section type explicit as described above; it changes
no mathematics. All seven proof steps occur in the theorem docstring, and the sole
postponed theorem corresponds to the delivered DAG node.
