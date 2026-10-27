## Worker report

The delivery states `AlgebraicGeometry.RationalHighestWeight.top_bottom_cohomology_simple_image`
in `Sheaf.AlgebraicGeometry.GroupScheme.TopBottomCohomologySimpleImage`. Its only proof is
`sorry`. The item's natural-language statement and accepted proof are unchanged.
One new definition node supplies the missing interface for the actual homogeneous
character-line cohomology with its specified algebraic left action. Both delivered
modules compile cleanly through scompile.py against the live server library. No
unproved theorem was introduced in the definition module, and no data is chosen
from an unproved existence assertion.

Hypothesis and clause correspondence:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
  Positive characteristic is `(p : ℕ) [CharP F p] (hp : 0 < p)`. A field forces a
  positive characteristic to be prime; no characteristic is omitted, including 2.
- `S : Grp (Over (Spec (.of F)))` is the actual group scheme. `hS` is the recorded
  `IsSemisimpleGroupScheme`, with smoothness, connectedness, affineness, finite
  type and the exclusion of solvable smooth connected normal subgroups. `hsc`
  is the same finite-central-isogeny definition of simple connectedness as in
  `exists_rho_section_modules`: it tests centrality over every commutative
  F-algebra, including nonreduced algebras. The affine instances expose the
  canonical coordinate rings of S, T and U; they are properties of these given
  affine groups, rather than extra restrictions on the source objects.
- `iT`, `iB`, `j`, with `hB : IsRhoBorelPair iT iB j`, specify a split maximal
  torus inside the positive Borel. `iBm`, `jm`, `hBm` give a Borel containing the
  same torus. The equalities `hconjS`, `hconjB`, `hconjBm` fix all three tangent
  actions to actual conjugation. `hopp` says the nonzero weights of Lie(Bm) are
  precisely the negatives of the positive roots. Thus Bm is the specified
  opposite Borel, not an unrelated solvable subgroup.
- `Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))` is the actual
  character lattice X. The cocharacter lattice is the reverse Hom group.
  `Φ`, `P : RootDatum ...`, `b : P.Base`, `[P.IsReduced]`, `hroot`, `hpair`,
  `hweights`, and `hpos` are the recorded reductive Borel-pair interface, with
  pairing fixed by composition with integer powers and roots fixed by the
  character weights on Lie(S). The simple roots are `b.support`. The root
  lattice ZΦ is the span of these roots; it is not a separate hypothesis or
  an object used in the conclusion, so no additional lattice variable occurs.
- `ρ` is integral in X, and `hρ` is `2 • ρ = sum of positive roots`. This is
  the half-sum in the character lattice, never division by 2 in F.
- `n` and `e` specify the actual normalizer representative and its torus
  automorphism. `he` fixes the action as conjugation by n inverse, exactly as
  in the dependency `simple_module_dual_highest_weight`. `hlongest` sends the
  positive roots to their negatives. This presents the longest element of
  N_S(T)(F)/T(F), without introducing a second Weyl-group action. Its dot
  action on x is `Additive.ofMul (e.hom ≫ (x + ρ).toMul) - ρ`.
  N is the cardinality of the positive-root filter of `Finset.univ : Finset Φ`.
- `U`, `iU`, and `hUclosed`, `hUnormal`, `hUsmooth`, `hUconnected`,
  `hUunipotent`, `hUmax` specify the actual positive unipotent radical, using
  precisely the radical interface from the reductive Borel-pair theorem.
  `pm : Bm ⟶ T`, `hpm`, `hpmU` specify the torus projection of the opposite
  Borel: it is identity on T and kills its unipotent radical. Consequently
  `pm ≫ χ.toMul` is exactly the character defining F_χ, trivial on the radical.
- `Y`, `π`, `hY`, `hYft`, `hYqc`, `hπf`, `hπs`, `hπi`, `hπt` are the flag
  quotient with its proper finite-type structure map and faithfully flat
  right Bm-torsor, as furnished by `reductive_borel_pair_structure`. In
  particular, Y and π are not arbitrary replacements for S/Bm.
- `D χ` is the presentation of the associated character-line bundle for
  `pm ≫ χ.toMul`, and its cohomology. The underlying bundle is the existing
  `AssociatedCharacterLineBundle.Presentation`, with the exact right relation
  `(g,z)b = (gb,χ(b)⁻¹z)` and section trivialization. Hence its sections are
  the regular maps specified in the node. `cohomology Y (D χ).bundle.L i`
  is exactly right-derived module global sections with scalars restricted
  along F → Γ(Y,O_Y); it is not abstract-group cohomology or a substituted
  module. `D` supplies the source's family for all characters and all i≥0.
  The convention at negative i is unused: only degrees 0 and N occur here.
- The new definition pins the linearization in every scheme-valued atlas:
  `IsNaturalLinearization` transports the coordinate z unchanged from [g,z]
  to [sg,z]. Its `IsNaturalCoaction` demands coassociativity, the counit, and
  the universal cohomological identity on S×Y. For every finite expression
  c(z)=sum(v_j tensor a_j), its image under canonical flat base change is
  sum(p₁*a_j times p₂*v_j), equal to pullback along (s,y)↦s⁻¹y followed by
  the specified inverse linearization. The maps are the existing
  `moduleCohomologyFMap`, using actual pullback adjunctions. This determines
  the coaction; no arbitrary action or comparison map is a hypothesis.
  In particular, the statement does not rely on testing only F-valued points.
- Dominance is exactly `∀ α ∈ b.support, 0 ≤ P.toLinearMap x (P.coroot α)`.
  The first conclusion explicitly includes `Nontrivial H⁰(x)`.
- The witness `L : Submodule F H⁰(x)` is stable and nonzero. Its minimality
  among nonzero stable subspaces says it is simple. Every other stable,
  nonzero, minimal subspace K equals L, expressing the unique simple
  submodule, rather than just an isomorphism class.
- The U-fixed subspace of L is its intersection with the ambient `invariants`
  for `iU ≫ iB`. Its finrank is 1, and the displayed coaction equation says
  T acts on that line by `characterElement x.toMul`. This is precisely the
  positive-Borel highest weight x, using the recorded definitions.
- The map binder has domain the degree-N cohomology of the longest-dot
  character and codomain H⁰(x). `f ≠ 0` is the nonzero condition. The equation
  `f.rTensor F[S] ∘ₗ c_top = c_zero ∘ₗ f` is S-linearity as a coaction
  identity, and `LinearMap.range f = L` is the equality of the image with
  the particular simple submodule. Equivariance therefore remains true
  after every commutative scalar extension. No distinguished comparison map
  or its nonvanishing is assumed or concluded. The contragredient convention
  occurs in the proof's Serre-duality input; the recorded dependency provides
  exactly the inverse-transpose dual action.
- The final conjunct universally quantifies x again, assumes dominance of
  x+ρ and failure of dominance of x, and concludes `Subsingleton H⁰(x)`.
  This is vanishing of the vector space, including its zero element.

Dependency declarations read and reused:

- Mathlib Algebra/Field/Defs: `Field`; FieldTheory/IsAlgClosed/Basic:
  `IsAlgClosed`; CategoryTheory/Monoidal/Grp: `GrpObj` and `Grp`.
- `Sheaf.AlgebraicGeometry.RhoSectionModules`:
  `AlgebraicGeometry.IsRhoBorelPair`, `exists_rho_section_modules`.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `reductive_borel_pair_structure`, `semisimpleGroupScheme_isReductive`;
  its root datum, base, conjugation weights and radical signatures were read.
- `Sheaf.AlgebraicGeometry.GroupScheme.SimpleModuleDualHighestWeight`:
  `RationalHighestWeight.simple_module_dual_highest_weight`, and its
  public dependency RationalHighestWeightData: `coordinateAlgebra`,
  `coordinateMap`, `IsStable`, `IsSimple`, `invariants`, `characterElement`,
  `HasHighestWeight`, `IsContragredient`.
- `Sheaf.AlgebraicGeometry.GroupScheme.AssociatedCharacterLineBundle`:
  `Presentation`, `trivializationAt`, and the fixed character-line construction.
- `Sheaf.AlgebraicGeometry.GroupSchemeLinearization`: `act`, `Linearization`.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology` and
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `RingedSpace.moduleCohomology` (right-derived global sections).
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap`:
  `moduleCohomologyFMap` and its normalized resolution construction;
  Mathlib `Scheme.Modules.pullbackPushforwardAdjunction` supplies the
  ordinary coefficient maps.
- The stated proof dependency `Sheaf.AlgebraicGeometry.GroupScheme.RhoRegularWeylOrbit`
  is imported privately. The other proof-only nodes have no Lean record in
  the current DAG; their mathematical steps remain fully reproduced in
  the theorem docstring. No unstated proof lemma is assumed in the signature.

Edge cases checked before and after writing:

1. Rank zero: the positive-root filter and `b.support` can be empty. N=0,
   rho=0, e is the longest (identity) action, and both cohomology degrees are
   zero. No nonempty root hypothesis or positive degree is imposed. The
   nondominant-boundary hypothesis is impossible in this case.
2. Characteristic 2: rho is specified by an integral character equation, so
   there is no inverse of 2 in the coefficient field. Arbitrary positive
   characteristic is retained.
3. The zero map is excluded only in the image implication. The statement
   does not claim all maps are nonzero or choose any comparison map.
4. Nondominant x with x+rho dominant pairs -1 with some simple coroot; the
   boundary vanishing is the accepted rank-one argument. For SL₂ at x=-1,
   H⁰(O(-1)) vanishes, consistent with both signs.
5. The associated-character inverse sign gives O(x) on SL₂/Bminus, and
   w₀ dot x=-x-2. Thus top-to-bottom is H¹(O(-x-2))→H⁰(O(x)), as in the
   source. The top module is dual to H⁰(-w₀x), not dual to an unrelated H⁰.
6. All schemes, coefficients and finite-dimensional objects fit an arbitrary
   common universe u. No equality between independently sized sites has
   been imposed. General rational coactions use the existing coordinate Hopf
   algebra and all-scheme identities; infinitesimal scalar extensions are
   retained.
7. In the new normalization, n=0 tests c(z)=0 correctly (both finite sums
   are empty); zero cohomology is permitted. Taking zero coactions on a
   nonzero module fails the counit, so the data do not allow that vacuity.

Searches actually run (logged in searches.jsonl):

- LeanFinder: "Every nonzero homomorphism from top flag line bundle
  cohomology at longest dot reflected weight to dominant global sections
  has simple image". Eight LieModule weight-chain hits, no matching
  algebraic-group/flag-cohomology statement.
- Loogle: `"IsSimple", "cohomology"`: zero hits.
- Mathlib grep: `Weyl.module|simple.*socle|socle.*simple|flag.*cohomology`:
  zero hits.
- LeanSearch: "Homogeneous vector bundle on algebraic group quotient
  equivariant regular maps sheaf cohomology": eight MulActionHom and
  abstract/continuous group-cohomology hits, no matching construction.
- LeanFinder: "Cohomology coaction of a homogeneous character line bundle
  normalized by pullback and left translation": eight abstract/continuous
  group-cohomology hits, no homogeneous bundle coaction interface.
- Loogle: `"cohomology", "coaction"`: zero hits.
- Mathlib grep: `HasNaturalCohomologyCoaction|translationLinearization|characterCohomology`:
  zero hits. The same source grep in lean/WeilConjectures and lean/Sheaf
  found no declaration. Exact item-id search in those trees also found none.
- DAG searches located the existing associated-character bundle and general
  group-scheme linearization nodes, which are reused. Blueprint searches
  "homogeneous line bundle cohomology", "cohomology coaction" and
  "associated character" returned no matching blueprint nodes. The
  ancestor tool reports the item's inherited null blueprint ancestor; the
  precise inherited proof place and via chain are retained for the new node.
  The current latest direct-images blueprint proof (3) was read, rather
  than an older snapshot.

No STATEMENT-DISPUTED flag or source correction is needed. Milne pp.467--471
were read locally for the socle, highest-line and dual conventions. The Andersen
article remains absent locally as already recorded in the accepted node; the
accepted seven-step proof, including its separate equivariant Serre pairing
and one-dimensional Hom-space argument, is copied in the theorem docstring.

## New nodes

`def-sfb-character-line-cohomology` defines
`AlgebraicGeometry.CharacterLineCohomology.Data` and its five helper declarations
in `Sheaf.AlgebraicGeometry.GroupScheme.CharacterLineCohomology`. It packages
existing associated character-line bundles, the existing all-test-scheme
linearization, and actual right-derived module global sections. The additional
compatibility pins the coactions to the canonical universal cohomology pullback
and base-change formula. Sources are Milne Section 18c and Definition 22.21,
and Stacks 01F7/01FB/02KH. The searches above found no existing definition of
this combined normalized presentation. The generic node
lem-sfb-linearized-qcoherent-cohomology-coaction asserts existence and naturality
of the canonical action; it does not supply this missing definition and is not
assumed as an arbitrary witness. No helper copies its theorem. All data in
the definition module are actual constructions or explicitly specified structure
fields, and every compatibility law is a Prop. The item cites the new node.

## Second reading by Q26

This is a second pass by the delivering worker, not a claim of an independent
subagent review: the dispatch brief forbids starting other agents and assigns
independent review to the maintainer. I reopened the node and both source files
and matched the hypotheses and clauses above. I checked the sign of the inverse
translation and inverse linearization in universalAction: together they produce
(s f)(g)=f(s inverse g), not the right action or its dual. I checked that
universalPullback uses the canonical ordinary adjunction unit, and that the
scalar factor in its tensor expansion is the actual pullback of a regular
function along p₁. The unique-simple-submodule condition concerns ambient
coaction-stable subspaces, and its highest line is exactly L intersect H⁰(x)^U.
The final universal map condition states equality of its actual range with L,
and the boundary clause uses x+rho rather than the longest-dot weight. The
positive roots allow the empty family. No theorem is proved, no extra
nonvanishing or duality assumption appears, and the new definition has no sorry.
Compilation repairs only made the implicit group binders syntactically correct
and exposed the existing module carrier for scalar multiplication and finrank;
they did not change the mathematical statement.
