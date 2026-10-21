## Worker report

The delivery states every clause of `lem-pc-vector-bundle-principal-parts` in
`Sheaf.AlgebraicGeometry.Curve.VectorBundlePrincipalParts`. The natural-language node,
its statement dependencies, proof, and proof dependencies are unchanged. All six new
theorems have exactly `sorry` as their proof. The remaining declarations are explicit
canonical maps or restriction-of-scalars instances; none chooses data from an existence
statement with a postponed proof.

Source read: Tate, *Residues of differentials on curves*, §3, pp. 156–157 (the exact
sequence before Theorem 4) and §4, pp. 157–158 (divisor version and finite locally free
coefficients). Tate's displayed construction uses completed local quotients; the node's
agent-written proof gives the uncompleted finite locally free version. The statements
follow that node, including its more general nonproper regular Noetherian curve, not an
extra properness or finite-type assumption. The whole eight-step node proof is rendered
in the theorem docstrings, with the cited dependency ids.

Hypotheses and objects:

- `k : Type u`, `[Field k]`: the base field, in arbitrary characteristic.
- `X : Scheme.{u}`, `[IsIntegral X]`: the integral scheme; `IsIntegral` includes
  irreducibility and hence nonemptiness. The actual generic point is `genericPoint X`.
- `[X.Over (Spec (.of k))]`: the specified structure over k. No finite type, separatedness,
  properness, perfectness of k, or constant rank is assumed.
- `[hN : IsNoetherian X]`, `[hR : IsRegular X]`,
  `hdim : topologicalKrullDim X = 1`: exactly the Noetherian, regular, dimension-one
  hypotheses. `include hN hR hdim` retains all three in the resolution, cohomology,
  naturality, and differential theorem signatures. `hdim.le` is used only to apply the
  existing principalPartsMap interface, without replacing equality by an assumption of
  dimension at most one.
- `X.functionField`: the actual structure-sheaf stalk at `genericPoint X`, as specified
  by `def-sc-function-field`'s integral-scheme clause. The compatible k-algebra is
  expressed by `[Algebra k X.functionField] [Scheme.IsFunctionFieldAlgebra k X]`, following
  the upstream principal-parts API. These specify the canonical structure induced by
  the given k-scheme, and add no geometric restriction: upstream `functionFieldAlgebra k X`
  and `isFunctionFieldAlgebra_functionFieldAlgebra k X` supply it. The latter's source
  formula is precisely the structure map followed by the generic germ.
- `E : X.Modules`, `[E.IsFiniteLocallyFree]`: the recorded variable-rank predicate
  `SheafOfModules.IsFiniteLocallyFree`, with no global rank chosen.
- `V` is always `E.presheaf.stalk (genericPoint X)`, with its existing module structure
  over `X.functionField`. `vectorBundleGenericStalkModule` restricts that structure to
  k by `Module.compHom`; its scalar tower is the existing `IsScalarTower.of_compHom`.
  There is no free variable V or assumed injection of E into an arbitrary V.
- The two independent `HasDerivedCategory` universe binders in the cohomology theorem
  are the usual infrastructure for the existing canonical `rightDerivedδ`. They are
  on the module-sheaf category and the category of modules over global functions,
  exactly the domain and codomain of the recorded global-sections functor; neither
  identifies those universes or restricts the curve or coefficients.

Clause-by-clause rendering:

1. The inclusion `E → j_*V` is the definition `vectorBundleToGeneric E`, namely
   `toSkyscraper LinearMap.id` on the actual generic stalk. Upstream
   `toSkyscraper_app_apply` says its value on a section is its generic germ.
   `finiteLocallyFree_generic_germs` asserts sectionwise injectivity, injectivity of
   each actual stalk specialization map `E.presheaf.stalkSpecializes`, and equality of
   its range with the existing `stalkLattice k (vectorBundleToGeneric E) x`. This makes
   the node's identification of E_x as a subspace of V explicit.
2. `j_*V` is the existing `skyscraper (genericPoint X) V`. Its section type is the
   function type `SkyscraperSections (genericPoint X) V U = (PLift (η ∈ U) → V)`.
   Thus a nonempty open has value V because it contains η, and the empty open has
   the one-element zero group. The restriction maps are those of this construction.
3. `finiteLocallyFree_principalParts_resolution` asserts
   `(residueShortComplex k (vectorBundleToGeneric E)).ShortExact` in `X.Modules`.
   This short complex has exactly the preceding inclusion as f and the existing
   `toPrincipalParts k (vectorBundleToGeneric E)` as g. The upstream definition
   `toPrincipalParts_app_val` sends a rational section to its class at every point.
4. The last term is the existing `principalParts`, identified with the stated sheaf
   direct sum by the same resolution theorem: for EVERY open U there is an additive
   equivalence with `Π₀ x : {x : closedPoints X // x.1 ∈ U}, V ⧸ E_x`, and the equation
   identifies each coordinate with its actual `PrincipalParts.val`. The second equation
   says restrictions discard precisely the coordinates outside the smaller open.
   This is the direct sum of closed-point skyscrapers, not a product or a replacement
   by arbitrary local quotients. Its O_X-action is already the upstream `quotSMul`
   action (germ of a function acting on a representative), and coordinate evaluation
   therefore respects the quotient scalar actions as well. The additive equivalences
   characterize the module-sheaf identification with this direct sum.
5. Both `TopCat.Presheaf.IsFlasque` assertions are present for these precise two terms.
   On abelian-group presheaves this means all restrictions are epimorphisms, equivalently
   surjective additive maps; the imported upstream construction supplies that equivalence.
6. The finite-poles assertion is
   `{x : closedPoints X | v ∉ stalkLattice k (vectorBundleToGeneric E) x.1}.Finite`
   for every actual generic vector v. `vectorBundle_generic_generates` supplies the
   genuine generic-representability proof required by the existing `principalPartsMap`.
7. H^p is literally `(RingedSpace.moduleCohomology X.toRingedSpace p).obj E`, the recorded
   right derived global-sections functor on MODULE SHEAVES. The cohomology theorem's
   family e₀ identifies H^0 with the subtype of `⨅ x : closedPoints X, E_x`. Its formula
   says the image in V is the generic germ of the section identified by the standard
   degree-zero derived isomorphism `vectorBundleModuleH0Iso`.
8. The same theorem's family e₁ identifies
   `(Π₀ x : closedPoints X, V ⧸ E_x) ⧸ LinearMap.range (principalPartsMap ...)` with H^1.
   This is the displayed cokernel, with the orientation reversed to state its induced
   boundary map directly. For every genuine global principal part s, the formula says
   e₁ of its finite-support class equals the actual
   `ShortComplex.ShortExact.rightDerivedδ` for the exact sequence in clause 3, after
   identifying H^0 of its last term with its global sections. Thus this is the
   connecting-map isomorphism, with its normalization specified, not an arbitrary
   existence of two isomorphic groups.
9. Naturality is explicit at both levels. `finiteLocallyFree_principalParts_naturality`
   provides the map on principal-parts module sheaves, gives the two commutative
   squares for the canonical generic and residue maps, and specifies [v] ↦ [f_eta(v)]
   on every local coordinate. The cohomology theorem states naturality of e₀ with
   respect to the actual derived map. For each finite-support family d it supplies
   the induced finite-support family d', characterizes every coordinate by all its
   representatives, and gives `e₁ F [d'] = H¹(f) (e₁ E [d])`. These are simultaneous
   families of equivalences for all finite locally free modules, rather than unrelated
   existential choices for individual pairs of modules.
10. Under the extra hypothesis `[Smooth (X ↘ Spec (.of k))]`, the differential theorem
    sets E to the recorded `(X ↘ Spec (.of k)).relativeDifferentials`. It gives a
    K-linear equivalence from that module's actual generic stalk to `Ω[X.functionField⁄k]`.
    Its generic-germ formula identifies it with the existing canonical
    `differentialsToGeneric k X`. For each x, the image of E_x under this equivalence is
    exactly the range of `KaehlerDifferential.map k k (localSubalgebra k X x) X.functionField`.
    Here `localSubalgebra k X x` is the existing image of O_{X,x} in K, with the existing
    `stalkEquivLocalSubalgebra k X x : O_{X,x} ≃+* localSubalgebra k X x` identifying the
    actual local ring. Thus this is precisely the specified image of Ω[O_{X,x}/k] in
    Ω[K/k], using its canonical k-structure, not a completed local ring or a substitute
    coefficient object.

Dependency declarations read and reused:

- `def-sc-finite-locally-free-sheaf`: module
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`, declaration
  `SheafOfModules.IsFiniteLocallyFree` (docstring and complete class at lines 153–160).
  It is the varying-local-rank notion; `IsFiniteLocallyFreeOfRank` is not substituted.
- `def-sc-function-field`: module `WeilConjectures.AlgebraicGeometry.FunctionField`,
  declaration `AlgebraicGeometry.Scheme.functionFieldOfComponents` (full file read).
  For this integral scheme use the node's recorded integral-case interface
  `Mathlib.AlgebraicGeometry.FunctionField`, `AlgebraicGeometry.Scheme.functionField`
  (line 37), its field instance, and its actual specialization maps (lines 78–99).
- `def-sc-relative-differential-sheaf`: module
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`, declaration
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` (full definition and universal
  derivation interface read at lines 91–155). It is used literally in the specialization.
- `pqf-def-cohomology`: module `WeilConjectures.AlgebraicGeometry.PQFCohomology`, declaration
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages` (complete signature and proof
  read). Its H^p is the recorded `RingedSpace.moduleCohomology`, reused throughout.
- Proof imports include the recorded `CategoryTheory.moduleSheaf_coproduct_localSupport`
  in `Sheaf.AlgebraicGeometry.ModuleSheafCoproductLocalSupport`,
  `AlgebraicGeometry.moduleCup_flasque_acyclicity` in `Sheaf.Paper.ModuleCupFlasqueAcyclicity`,
  and `Scheme.Hom.isFiniteLocallyFree_relativeDifferentials` in
  `WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree`.
  The other proof dependencies are supplied by the imported function-field,
  Krull-dimension, locally-surjective, right-derived delta-functor, and Kähler-localization
  modules (including the transitive imports of the listed upstream modules).
- Existing construction modules read: `Curve.ResidueSequence`, `Curve.AdelicH1`,
  `Curve.AdelicStructureSheaf`, `Curve.AdelicDifferentials`,
  `Modules.FlatPullbackStalk`, `Topology.RingedSpaceModuleCohomology`, and
  `CategoryTheory.Abelian.RightDerived.Connecting`, all under `WeilConjectures`.
  These supply the canonical skyscraper, stalk adjunction, lattices, principal-parts
  sheaf, finite-support map, and boundary. Their `Modules.H` cohomology formulas alone
  do not state the present module-cohomology theorem and assume a generic embedding,
  so they cannot be attached as an exact existing match for the entire item.

Edge cases checked before writing and on reading the result:

- Rank zero: all stalks, quotient sections, and both cohomology groups vanish; the
  formulas and naturality still apply. No positive-rank assumption appears.
- Empty open: the skyscraper's section group and the empty-support DFinsupp are zero,
  so the equivalence and restrictions include this case.
- X = Spec of a DVR (with its given k-structure): one closed point and one generic
  point; the principal-parts term is the expected V/E_x and its restrictions have
  exactly the specified behavior.
- A¹ over k: no properness assumption was inserted; the short exact SHEAF sequence
  does not assert that rational sections globally surject onto all principal parts.
- Zero morphisms, identity morphisms, and compositions: the coordinate formula for
  the induced map and the cohomology equations give the expected natural maps.
- Arbitrary characteristic and imperfect k: the differential clause requires smoothness
  and uses the full Ω[K/k]; it does not assume a rational parameter, separability of
  all closed residue extensions, perfectness, or one-dimensional Ω without justification.
- Empty scheme and dimension zero are excluded exactly by the node's integral,
  dimension-one hypotheses, not by an added restriction on opens or rank.

Searches actually made (the remote msearch calls are logged by that tool):

- `msearch.py ... leanfinder "principal parts resolution of a vector bundle on a regular curve"`:
  eight hits on tangent/vector bundles of manifolds and local frames; no theorem about
  algebraic principal-parts resolutions.
- `msearch.py ... loogle "SheafOfModules, VectorBundle, principal parts, flasque"`:
  zero hits, with an unknown-identifier diagnostic for `principal`; this query was
  inconclusive, not used as a valid no-match search.
- `msearch.py ... loogle '"principalParts"'`: zero hits.
- `msearch.py ... grep 'principalParts|principal.parts|residue.sequence' Mathlib`:
  zero hits.
- `msearch.py ... leansearch "principal parts flasque resolution of a finite locally free sheaf on an integral regular curve"`:
  eight hits on finite presentation, free sheaves and local freeness of flat modules;
  none states this result.
- `rg -n` on both project roots for principal parts, rational sections, finite locally
  free and vector bundles: found the upstream `Curve.ResidueSequence`, `Curve.AdelicH1`,
  `Curve.AdelicStructureSheaf`, `Curve.AdelicDifferentials`; their complete relevant
  definitions and theorem signatures were opened and reused. No full existing result
  combines generic-stalk vector-bundle construction, direct-sum flasqueness, module
  cohomology and naturality with the differential specialization.
- `grep -rn 'lem-pc-vector-bundle-principal-parts' lean/WeilConjectures`: no hits.
- DAG search for `stalkLattice|principalParts|residueShortComplex`: no separate definition
  node for this full vector-bundle construction. `tools/blueprint_refs.py search
  'principal parts'`: zero matching blueprint nodes. The ancestor command identifies
  `sk-thm-picard-duality`.

No statement dispute, correction, new node, or dependency-record repair was needed.
The module compiled cleanly with `scompile.py` against the published live build.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
