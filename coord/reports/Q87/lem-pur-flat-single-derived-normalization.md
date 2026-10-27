## Worker report

The module `Sheaf.Algebra.Homology.FlatSingleDerivedNormalization` states
`SheafOfModules.FlatSingleDerivedNormalization.flat_single_derived_normalization`
with `sorry`. There are two transparent abbreviations, `collapse` for the existing
canonical single-factor totalization isomorphism and `derived` for the published
site-derived tensor with Q(L[0]). Neither abbreviation selects data or introduces
a second tensor. The node statement, dependencies and proof are unchanged; only
its `lean` field is set. No new nodes or dependency repairs are needed.

Hypotheses and every clause of the node:

- The site is `C : Type u`, `[Category.{v} C]`, `J : GrothendieckTopology C`.
  `[EssentiallySmall.{r} C]` expresses smallness relative to the module universe,
  as in the recorded site-descent interface. Object, morphism, coefficient and
  derived morphism universes `u v r w` remain independent.
- The commutative ring sheaf is `R : Sheaf J CommRingCat.{r}`.
  `L : KFlatFixedTensor.Modules R` is precisely `ringedSiteModules` / Mathlib
  `SheafOfModules.{r}` for its underlying sheaf of rings. The abelian structure is
  Mathlib's, induced by sheafification. `[HasDerivedCategory.{w} ...]` specifies
  the chosen morphism-size localization, as in the dependency.
- Flatness is exactly `hL : IsFlatOnSite (J := J) (R := R) L`, not local freeness
  or invertibility. This is exactness of `siteSheafTensorRight L`. The existing
  `siteSheafTensorRightIso R L` identifies it with the monoidal `tensorRight L`.
  The existential `hLim` and `hCol` provide that exactness as typeclass data for
  Mathlib's derived-factorization API; they are conclusions, not extra hypotheses.
  The instance-lambda applications name their instance arguments explicitly.
- `T_L` is the existing `tensorRight L`; `C(T_L)` is its
  `mapHomologicalComplex (.up ℤ)`. By its definition, objects are `E.X i ⊗ L`,
  differentials are `(tensorRight L).map (E.d i j) = E.d i j ▷ L`, and maps have
  components `f.f i ▷ L`. No alternate complex is introduced.
- `L[0]` is `(CochainComplex.singleFunctor _ 0).obj L`, the actual degree-zero
  complex. `hK` states its `IsKFlatIndependentCoefficients`; `hF` states
  `∀ i : ℤ, IsFlatOnSite (... .X i)`. These witnesses are reused in normalization.
- Total tensor is `KFlatFixedTensor.totalTensor R`, i.e. the recorded
  `CochainComplex.mapBifunctor` of the canonical sheaf tensor with direct sums
  and the prescribed signs. `collapse R L` is the existing
  `CochainComplex.map₂HomologicalComplexFlipObjSingleIso` for this tensor.
  It is a natural isomorphism on the entire unbounded complex category.
- The first component equation precomposes `collapse` with
  `HomologicalComplex.ιMapBifunctor ... i 0 i (Int.add_zero i)`. The result is
  tensoring the canonical degree-zero identification
  `HomologicalComplex.singleObjXSelf (.up ℤ) 0 L`. After identifying that term
  with L this is the identity on the sole surviving `(i,0)` summand. This records
  the requested normalization, rather than merely asserting some totalization iso.
- `derived R L` is exactly `(KFlatFixedTensor.derivedTensor R).flip.obj (Q.obj L[0])`.
  `derivedTensor` is the published `siteDerivedTensorIndependentCoefficients`,
  curried; `derivedTensor_eq_published` records this equality in the dependency.
- `eta : derived R L ≅ (tensorRight L).mapDerivedCategory` is the natural
  isomorphism of functors on D(R). `mapDerivedCategoryFactors` is the specified
  termwise factorization phi, used literally in the normalization equation.
- `chi` is the inverse of the fixed-factor theorem's right representative
  comparison on every complex. It is normalized on each flat-term K-flat E by
  `chi.app E = (KFlatFixedTensor.representativeIso ...).symm`. Naturality and
  localization then determine its value on arbitrary E uniquely: restricting to
  resolving complexes is fully faithful by site-derived-tensor descent. Thus chi
  is precisely the fixed-factor comparison, not an arbitrary natural iso.
- The equation `eta.app (Q.obj E) ≪≫ phi.app E = chi.app E ≪≫ Q.mapIso
  ((collapse R L).app E)` is quantified over every E. The K-flat/flat-term
  binders occur only in the preceding characterization of chi on resolving E;
  no such binder occurs in this required equation or its cohomology analogue.
- Integer shifts: `NatTrans.CommShift (collapse R L).hom ℤ`,
  `NatTrans.CommShift chi.hom ℤ`, and `NatTrans.CommShift eta.hom ℤ` express the
  three compatibility squares for every integer, with coherent shift data `s`.
  The total-complex shift instance is the recorded unsigned first-variable shift.
  The termwise shift equation says its component in every degree is `𝟙 _`.
  The additional differential equation is exactly
  `n.negOnePow • (tensorRight L).map (E.d (i+n) (j+n))`, including negative n.
  The derived shift structure is characterized by chi's compatibility, so it
  cannot be independently altered from the fixed-factor one.
- Triangles and connecting maps: `(derived R L).IsTriangulated` states preservation
  of all distinguished triangles, not just some cone triangles.
  `(tensorRight L).mapDerivedCategory.IsTriangulated` is the existing exact-functor
  instance. `NatTrans.CommShift eta.hom ℤ` together with eta's naturality is exactly
  compatibility of all three triangle arrows, including the last arrow into X[1].
  This is not replaced by a per-degree assertion.
- For every `i : ℤ`, `c` is a natural isomorphism
  `derived R L ⋙ DerivedCategory.homologyFunctor ... i ≅
   DerivedCategory.homologyFunctor ... i ⋙ tensorRight L` on D(R).
  Its representative equation composes homology of chi followed by Q(collapse),
  `DerivedCategory.homologyFunctorFactors` on the termwise complex, and the exact
  cycle-and-boundary comparison `(E.sc i).mapHomologyIso (tensorRight L)`.
  The left side uses `tensorRight L` applied to `homologyFunctorFactors` on E to
  identify H^i(QE) with H^i(E). All equalities are ordinary iso equalities, with no
  heterogeneous equality or hidden transport assumptions.
- Complexes and degrees are unbounded integer-indexed throughout. There is no
  constructibility, invertibility, boundedness, or flat-cohomology hypothesis.

Dependency declarations read and used:

- `def-weil-size-convention` is a convention record: explicit universes and
  `EssentiallySmall.{r}` / `HasDerivedCategory.{w}` render it.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`; read its docstring and Mathlib's
  object, morphism and abelian instance definitions.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`,
  `SheafOfModules.IsFlatOnSite`, and `CategoryTheory.exactFunctor`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
  `cochainModulesMonoidal`, `cochainModulesPreadditive` and tensor-colimit
  instances; this is the recorded sheaf tensor at independent universes.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`,
  `SheafOfModules.tensorClosed`: additivity and closure, imported for the proof.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and its triangulated/shift instances.
- `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`,
  `Functor.map₂CochainComplex` and its `CommShift₂Int` instance; the signed
  first/second shift maps and mixed-sign formula were read.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`,
  `SheafOfModules.site_derived_tensor_descent_independentCoefficients` and
  `siteDerivedTensorIndependentCoefficients`, through the fixed-factor module.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
  `CochainComplex.IsKFlatIndependentCoefficients`, the acyclic-total-tensor predicate.
- `Mathlib.CategoryTheory.Triangulated.Functor`, `Functor.IsTriangulated`, and
  `Mathlib.CategoryTheory.Shift.CommShift`, `NatTrans.CommShift`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`, their `CommShift`
  and `IsTriangulated` instances; `Functor.mapCochainComplexShiftIso` has identity
  degree components in `Mathlib.Algebra.Homology.HomotopyCategory.Shift`.
- `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`,
  `SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated`,
  `Modules`, `ordinaryTensor`, `totalTensor`, `derivedTensor`, `representativeIso`.
  The main theorem gives cR on all complexes, shift compatibility and its exact
  resolving normalization, which our chi expresses in the inverse orientation.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`,
  `ShortComplex.mapHomologyIso` / `Functor.homologyFunctorIso`, the recorded
  exact-functor cohomology comparison. The former is the component of the latter.
- `Mathlib.CategoryTheory.Localization.Predicate`, `Localization.natTrans_ext`,
  `liftNatIso`, `liftNatTrans`, `Lifting`, `fac`, for extending comparisons.
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`,
  `CochainComplex.map₂HomologicalComplexFlipObjSingleIso`, an actual construction
  using the single surviving summand. Also `HomologicalComplex.singleObjXSelf`.
- `Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`,
  `SheafOfModules.siteSheafTensorRightIso`, to identify the flatness-definition
  tensor functor with the monoidal tensor functor without a new hypothesis.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`.

Sources opened locally: sites-cohomology.tex definition-K-flat and the entire
fixed-factor construction immediately before definition-derived-tor (06YU);
derived.tex lemma-right-derived-exact-functor; homology.tex lemma-exact-functor.
These explicitly allow every unbounded varying complex. The main docstring gives
all eight node proof steps and names the dependencies they use.

Edge cases checked before writing: L=0 (both tensors and every comparison are
zero-object isomorphisms); L=R (ordinary and derived unit identifications);
E concentrated in a nonzero integer degree (only `(i,0)` survives, with no sign);
arbitrary unbounded E (still just one nonzero summand per total degree);
acyclic E (exactness makes the termwise tensor acyclic); n=0 and positive/negative
n (the shift differential uses n.negOnePow); i arbitrary including negative i;
empty site / zero sheaf category (no nonempty-site hypothesis); independent site
object/Hom universes and larger coefficient universe. No statement fault or
STATEMENT-DISPUTED issue was found.

Searches for existing statements (all via the prescribed msearch wrapper except
local rg):

- LeanFinder: “For a flat module sheaf L derived tensor by L in degree zero agrees
  with termwise tensor on every unbounded complex compatibly with shifts and
  cohomology”. Eight hits: total tensor-unit infrastructure, HasTensor,
  ιTensorObj, good-tensor instances and ordinary-module flat exactness. No full match.
- LeanSearch: “A flat module sheaf in degree zero has a normalized derived tensor
  naturally isomorphic to termwise tensor on unbounded complexes”. Eight hits
  (Module.Flat tensor exactness and faithful-flat descent); no full match.
- Loogle: `CategoryTheory.Functor.mapDerivedCategory`. Twelve hits, all generic
  exact-functor descent/shift/composition infrastructure; used the exact-functor
  declarations rather than restating them. An initial combined query containing
  a guessed `CochainComplex.mapBifunctorSingleIso` returned unknown identifier;
  local source search found the actual existing BifunctorSingle declarations.
- Mathlib grep: `mapBifunctor.*Single|single.*[Tt]ensor|[Tt]ensor.*single` in
  Algebra/Homology. Five hits in Monoidal.lean, tensor-unit/zero-differential
  infrastructure, no flat-sheaf normalization theorem.
- rg in project Sheaf and WeilConjectures for flat/single/tensor variants found
  `SignedLineDerivedBaseChange.collapse` and `LineUnbounded.collapse`, but these
  concern signed lines on a larger max-universe site and pro-etale locally free
  lines respectively. `RingedKFlatSingleTensorComparison` allows an arbitrary
  second sheaf but requires K-flatness of the varying first complex; it does not
  state the present all-complex flat-second comparison. Reused their underlying
  existing BifunctorSingle construction. No full attachment exists.
- rg of WeilConjectures for the exact node id, and rg of Sheaf, WeilConjectures
  and dag/lean_names_upstream.json for the new namespace/theorem: no hits.

Validation: scompile.py compiled the sandbox module and the delivery's real module
path. An initial instance-lambda application was repaired by explicitly naming its
instance parameters. Every final theorem proof is `sorry`; definitions/abbreviations
contain real existing constructions. `autoImplicit false` enforces bound variables.
The dry-run and push results are supplied by deliver2.py.

## Second reading by Q87

The dispatcher explicitly forbids starting another agent. I performed a separate
second pass with the unchanged node and the complete module open; the maintainer's
independent delivery review remains the external second reading. I checked the
hypothesis and clause mapping above, in particular that hE/hf are confined to
chi's resolving characterization, while the eta/phi equation and cohomology
normalization quantify over arbitrary E. The component equation includes the
canonical single-degree identification rather than assuming its type is literally
L. I added the explicit signed shifted-differential clause during this reading.
The cohomology normalization includes both homologyFunctorFactors transports and
the canonical ShortComplex.mapHomologyIso, so it has the source's cycle/boundary
normalization. Shift-compatible naturality controls the connecting maps of every
distinguished triangle. No statement change, extra hypothesis or omitted clause
was found. The main conclusion is a derived natural isomorphism, with cohomology
as an additional clause, as required by the 2026-10-21 convention.
