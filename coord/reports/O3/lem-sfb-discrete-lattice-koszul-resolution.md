## Worker report

The module `Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution` states
`Profinite.DiscreteLattice.discrete_lattice_koszul_resolution`. It supplies the discrete
lattice action, actual invariant-limit functor, the recorded universal total right derived
functor, finite Koszul coordinates, and the normalization of the derived coefficient map.
The main theorem asserts a family of natural derived isomorphisms with all the node's
normalizations. Nothing is proved in this stage: the four theorem proofs are `sorry`.
All definitions contain real data. No complex, coefficient map, or isomorphism is defined
by choosing arbitrary data from a sorried mere-existence theorem.

The previous worker's retained directory had only dispatcher brief markers. The live
node is split and reviewed, which is the prerequisite for stage 2, and has no Lean record.
This delivery leaves every original node field unchanged and adds only `lean`.

Source read: the node's complete ten-step proof and its main-20261015 blueprint source,
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3). That paragraph delegates
open direct-image preservation to the coefficient results; the node records the algebraic
lattice input below that delegation. The source's mention of Tags 0623 and 062F is only
for the algebraic Koszul ingredients, not a claim that Stacks states the condensed result.

Hypotheses and clauses, matched against the Lean:

- A commutative condensed ring is `R : Profinite.CondensedRing.{u}` together with
  `[IsCommMonObj R.X]`. The input is an arbitrary ring object on the coherent profinite
  site, without a topological-ring presentation. The coefficient and site universes are
  inherited from the recorded condensed-ring definition.
- The rank is `r : ℕ`, so zero is included.
- An internal module with the commuting automorphisms is `P : Equivariant R r`, the
  existing `Action (Modules R) (Multiplicative (Fin r → ℤ))`. Its underlying internal
  module is `P.V`. `generator i` is the integral ith basis vector, and `P.ρ (generator i)`
  is T_i. A group action makes these maps invertible; commutativity of the group makes
  them commute. This is exactly the equivalent lattice-action formulation in the node.
- `Modules` refers to the existing internal-module category, and introduces no new
  module structure. The underlying category is Mathlib `Mod` with the recorded tensor
  structure on abelian sheaves.
- `invariants R r` is the limit functor after the existing one-object action equivalence.
  Its projection at `PUnit.unit` is the fixed-submodule inclusion. This is an actual
  limit, not an arbitrary functor supplied as a hypothesis.
- `derivedInvariants` applies the dependency's
  `rightDerivedFunctorOfQuasiIsoResolutions` to this functor, using `resolutions`.
  `derivedUnit` explicitly transports its recorded unit from the homotopy-category
  presentation to actual complexes. `invariantUnit` specializes this to P[0], using the
  canonical single-complex comparison. Thus RGamma is the ordinary total derived functor.
- The finite cochain complex is specified by `KoszulModel.functor` and its coordinates.
  In integral degree a, `Subsets r a` is precisely the set of subsets of `Fin r` with
  cardinality a. `coordinates` identifies its term with the finite biproduct of copies
  of P. This also specifies the zero terms outside 0 through r, by an empty biproduct.
  The model and all comparisons are existential conclusions of the main theorem; there
  is no assumption of a preexisting Koszul resolution.
- `KoszulModel.differential` identifies every (I,J) matrix entry with
  `differentialEntry P I J`. That definition sums over i in J, using `J.erase i = I`,
  the sign `(-1 : ℤ) ^ (J.filter (fun j ↦ j < i)).card`, and `T_i - 𝟙 P.V`.
  This is exactly the node's displayed differential. `KoszulModel.maps` specifies the
  diagonal coefficient maps. Functoriality and the complex axioms are part of the actual
  `Functor` and `CochainComplex` data, not unbound assertions.
- `Comparison.iso` is a natural isomorphism
  `K.functor ⋙ DerivedCategory.Q ≅ singleFunctor _ 0 ⋙ derivedInvariants R r`.
  This is the required ordinary derived-category isomorphism, rather than just a
  per-cohomological-degree claim. Natural transformations give naturality in every
  equivariant morphism. The main theorem chooses K and the comparisons simultaneously
  for every coefficient ring and rank.
- `KoszulModel.augmentation` is from invariant modules concentrated in degree zero.
  Its `augmentation_zero` fixes its only potentially nonzero component to the actual
  invariant inclusion in the empty-subset coordinate. `Comparison.normalization`
  requires its composite with lambda to equal `invariantUnit`.
- An arbitrary coefficient morphism is `φ : R ⟶ R'`; both rings have their commutativity
  instances. `restriction φ` is the existing `Mod.comap φ.hom`. It keeps the underlying
  abelian sheaf and changes only its scalar action. `equivariantRestriction` is its
  existing `Functor.mapAction`, so the group action is retained. This is the internal
  form of the dependency `SheafOfModules.restrictScalars`, through the recorded
  internal/section-module equivalence; no constant-ring specialization is imposed.
- `restrictionInvariants` is the canonical limit-preservation isomorphism; its extension
  to complexes is `restrictionInvariantComplex`. No arbitrary fixed-point comparison
  is supplied as a premise.
- `CoefficientComparison.iso` is a conclusion of the theorem. Its `normalization`
  quantifies over every pair of K-injective resolutions s,t of the two degree-zero
  modules, and every extension beta from the restricted second resolution to the first.
  It requires the inverse coefficient comparison, composed with the normalized first
  resolution isomorphism, to be the localization of invariants(beta), after the canonical
  restriction/invariants and derived-restriction comparisons. This is precisely the
  inverse-resolution comparison of proof steps 8 and 9. No assertion that restriction
  preserves injectives is made. This normalization characterizes the canonical map;
  it is not merely an unspecified map making the desired square commute.
- The first conjunct of the main theorem supplies `c : CoefficientComparison φ r` and a
  complex isomorphism k between K_R(Res P') and Res K_R'(P'). Its coordinate equation
  requires the identity in each matching subset and zero in every other subset.
  Thus k is the termwise scalar-restriction identification. The following equation
  quantifies over every P and `f : P ⟶ (equivariantRestriction φ r).obj P'` and states
  exactly the coefficient square: lambda_R followed by RGamma(f) and c equals K(f)
  followed by k and scalar restriction of lambda_R'. The `mapDerivedCategoryFactors`
  arrow merely identifies localization of restricted complexes with derived restriction.
- The rank-zero conjunct supplies the canonical invariant identification e, fixed by
  `e.hom ≫ invariant inclusion = 𝟙 P.V`, and the canonical complex identification k,
  fixed in degree zero by the unique empty-subset coordinate. It requires lambda to be
  Q(k), then e[0], then the ordinary derived unit for the identity invariants functor.
  Under these specified identifications the comparison is exactly the identity P[0].
  This formulation handles Lean's separately chosen limit and localization objects.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, its action-compatible
  morphisms, and `Mod.comap`; no duplicated module or scalar-restriction definition.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q`, `quotientCompQhIso`, and
  `DerivedCategory.singleFunctor`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`, its Unit, and
  `rightDerivedFunctorOfQuasiIsoResolutionsObjIso`. The recorded interface accepts
  arbitrary quasi-isomorphisms to K-injectives, exactly as required here.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, the recorded general sheaf-ring restriction.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`, the link to the
  section-ring module presentation used in the proof.
- `Sheaf.CategoryTheory.CondensedActionModule`:
  `Profinite.CondensedAction.Modules`, an abbreviation for precisely that internal
  category; no continuous-action category is used for the discrete lattice.
- `Mathlib.CategoryTheory.Action.Basic` and `.Limits`: `Action`, its equivariant
  morphisms, `functorCategoryEquivalence`, `mapAction`, and its abelian structure.
- Proof-only imports include every available recorded proof-dependency module, together
  with the Mathlib modules recorded as matches for enough injectives, resolution lifting,
  and lifting along an injective quasi-isomorphism. The integral cubical-contraction
  dependency has no recorded Lean module, so there is no import to add for it.

The named postponed helper theorems belong to this node's construction, as permitted by
the missing-helper rule: `invariants_additive` is the additive invariant functor in step 1;
`resolutions` is the resolution existence in step 1; `restrictionInvariants_naturality`
is the termwise restriction comparison in step 8. Each has the source, blueprint id,
and complete natural-language proof plan in its own docstring. The fourth sorry is the
main theorem, whose docstring follows all ten DAG steps. All are in `lean.declarations`.
The model structures specify this node's own complex and canonical comparison; they
introduce no independent mathematical notion needing a separate definition node.

Edge cases checked:

- Rank zero: there is exactly the empty subset in degree zero, no other terms, and the
  explicit canonical identifications in the final conjunct give the identity.
- Rank one: the single matrix entry is T_0-1 with positive sign.
- Rank two: the second differential has entries minus (T_1-1) from subset {0} and
  plus (T_0-1) from subset {1}; the composite is zero by commuting automorphisms.
- Negative degree and degrees greater than r: subset types are empty; biproducts are zero.
- The zero module and zero ring are allowed, with zero complexes and unique maps.
- Identity coefficients, zero equivariant maps, and arbitrary non-flat coefficient maps
  are included. No flatness, nonzero condition, finite presentation, finite rank of P,
  trivial action, or injective-preservation hypothesis has been introduced.

Searches actually run:

- `msearch.py leanfinder`, query “Derived invariants of a discrete lattice acting on
  condensed modules are the finite Koszul complex of commuting automorphisms”: eight
  hits, including `Condensed.finFree`, discrete locally constant-module identifications,
  `Rep.standardComplex.forget₂ToModuleCat`, and the finite cyclic chain complex. None
  states this internal condensed-module lattice comparison with coefficient normalization.
- `msearch.py loogle`, query `KoszulComplex, groupCohomology, Action`: no hits;
  the service reports unknown identifier `KoszulComplex`, not an exact-match theorem.
- `msearch.py grep`, query `lattice|koszul|Koszul`: 25 displayed hits, initially unrelated
  category-theoretic lattice files. Targeted project searches below disambiguate them.
- `msearch.py leansearch`, query “Koszul complex in an additive category from commuting
  endomorphisms”: eight hits on short complexes, Hom complexes and additive instances;
  no finite commuting-endomorphism Koszul construction or lattice comparison.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, first for lattice/Koszul, then
  for discrete lattice and Koszul/invariants or automorphisms: the relevant consumer
  `TameBoundaryScalarComparison` cites the informal dependency but does not state it.
  The existing signed ringed Koszul coordinate and scalar-comparison modules concern
  scalar sections and inverse towers, not arbitrary commuting module automorphisms.
- `grep -rn` for the exact item id in `lean/WeilConjectures`: no match.
  The exact-id search in `dag/lean_names_upstream.json` also has no match.
- `tools/blueprint_refs.py search 'discrete lattice Koszul'`: zero blueprint nodes.
  `ancestor` returns None for the node's inherited chain, consistently with its live
  blueprint metadata. No new node is created here.

No statement correction, disputed statement, new node, or dependency-record repair.
Only the owning module, the item's `lean` record, and this report are delivered.

Validation: every compilation used the prescribed `scompile.py` server wrapper. The
complete module compiled both as an isolated sandbox file and at its final module path,
with no errors or warnings; each compiler run was below the 60-second limit.

## Second reading by O3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
