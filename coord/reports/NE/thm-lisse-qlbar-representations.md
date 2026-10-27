## Worker report

The delivery states `AlgebraicGeometry.ProEtale.LisseRepresentation.lisse_qlbar_representations`
in `Sheaf.Paper.LisseQlbarRepresentations`. Its only postponed theorem is this theorem;
its docstring reproduces all sixteen complete natural-language DAG proof steps. Definitions
and structural instance wrappers have actual data. The source statement and proof are unchanged.
Seventeen already-landed definition dependencies are added to `stmt_deps`: the precise
lisse predicate, continuous representation predicates, ordinary ring scalar extension,
and the fourteen declaration owners required by the returned H2 review below.
No new independent notion or dependency interface repair is needed.

The algebraic closure fixed in the statement is the library's `PadicAlgCl ell` model.
`PadicAlgCl.FiniteIntermediateField ell` supplies every finite subextension E inside it.
The scheme universe is u, the small site's objects have universe u+1 and arrows universe u;
module sheaves and representation spaces use universe u+1. Coefficients themselves are small.
Finite quotient coefficients are lifted by ULift only for the recorded classical interface.
No equality between the site's object and morphism universes is imposed.

Hypotheses and conventions, clause by clause:

- Prime ell: `(ell : ℕ) [Fact ell.Prime]`.
- Scheme connected, locally Noetherian and quasi-compact: `(X : Scheme.{u})`,
  `[ConnectedSpace X] [IsLocallyNoetherian X] [CompactSpace X]`.
- Geometric point: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`,
  `(x : Spec (.of Ω) ⟶ X)`.
- Profinite fundamental group: `(G : ProfiniteGrp.{u})`, its actions on every finite-etale
  fibre, and `[IsFundamentalGroup (Scheme.FiniteEtale.fiber x) G]`. This is the project's
  standard abstract model of the profinite fundamental group, not an unrelated group.
- Pulled-back coefficient modules: `Modules Λ X` is an abbreviation for the existing
  `Mod (Sheaf (Scheme.ProEt.topology X) Ab) (condensedRingObj Λ.X X)`.
  Integral and rational coefficients use the existing continuous-map condensed construction.
  Algebraic-closure coefficients use `Profinite.padicAlgClRingObj ell`, whose values lie
  in finite subextensions, not all continuous maps into the algebraic closure.
- Lisse: the recorded `IsLisseCoefficientModule` throughout, including zero local rank.
  This is the finite free specialization of the recorded finite constant local-model notion.
- Fibre: `fibre Λ x` is sections at the final object of the actual
  `CondensedRing.upperStar Λ.X x` module. `fibreUnderlying` is the canonical comparison
  with ordinary additive inverse image, built from `Mod.extendScalarsIsoComapInv` for
  the cartesian coefficient isomorphism. `fibreScalar` transports the actual constant
  coefficient action using this comparison. It is not an arbitrary module on a set.
  The integral/rational/algebraic-closure fibre conjuncts of `Conclusion` assert finite freeness for
  every lisse object, including those outside the integral subcategories.
- Integral rational module: `IntegralRational` requires lissity and `HasLattice`.
  The latter quantifies an actual lisse O_E-module N, a monomorphism into restriction
  of scalars of L, and invertibility of its specified adjoint localization map.
  This is equivalent to the embedded full ell-localization lattice convention; no
  mere unspecified rationalization isomorphism replaces the embedded map.
- Integral algebraic-closure module: `IntegralAlgCl` is lissity plus an integral E model
  and an isomorphism from its extension along the existing E-to-Qbar coefficient map.
- Continuous representations: integral coefficients use `IsContinuousIntegral`, with
  `Module.Free` added because clause (1) requires free modules; finite generation is
  already part of that recorded predicate. Rational coefficients use
  `IsContinuousCoefficient`. `ContinuousAlgCl` requires finite dimension and continuity
  of all matrix coefficients `g ↦ f (ρ g v)` for every linear form f and vector v.
  In finite dimension this is the usual valuation-topology continuity of GL(V),
  independent of a basis. `IsLAdic` is exactly the recorded existence of a stable
  continuous finite-field structure with canonical scalar-extension map.

The conclusions are packaged as follows:

1. `C.integral E` is a fully faithful functor, with exactly the stated
   essential image and essential surjectivity, naturally identified with the actual
   additive fibre and its O_E scalar action. Those are the standard equivalence
   criteria onto the indicated full subcategory; no lattice or basis is added to objects.
   The finite-reduction conjunct of `Conclusion` supplies `IntegralNormalization`
   for every E. Its existentially bound
   `reduction n` is a functor to the existing category of finite classical etale module
   sheaves. `projection` and the first law give the actual cokernel of pi_E^(n+1) on the
   underlying module sheaf. The next scalar law identifies its quotient-ring action, on all
   constant integral coefficients. Since the finite coefficient sheaf is locally
   constant, this also fixes the full sheaf action after local lifting of its sections.
   `finiteFibre.germ` normalizes comparison with etale stalks on every pointed etale
   germ using the actual two adjunction units and restriction to the point.
   The third law then fixes the maps to the representations of the recorded
   `GaloisLisseFiniteCorrespondence c`; the fourth law fixes the integral monodromy
   to those finite actions. The fifth law gives their surjections and precisely
   the pi-power kernels. the sixth law fixes the adjacent quotient maps;
   the seventh law and the final `Nonempty (∀ N, IsLimit ...)` assert that these actual fibre projections form
   the inverse-limit cone. Thus the action is the limit action and its reductions
   are the cited finite correspondence, not just some isomorphic finite actions.
2. `C.rational E` is the fibre equivalence for integral rational lisse
   modules and all continuous finite-dimensional E representations.
   The rationalization conjunct of `Compatibilities` quantifies EVERY localization presentation:
   for every integral lisse N, every integral rational L and every embedded map
   whose adjoint is invertible, it gives an equivariant scalar-extension isomorphism.
   The displayed pure-tensor equation identifies it with the actual map on geometric
   fibres. This simultaneously states rationalization of the integral action and
   its independence of the lattice. Source objects are L alone, not lattice pairs.
3. `C.algCl` is the equivalence on integral Qbar modules, with exact
   essential image the continuous representations defined over a finite E.
   The finite-model conjunct of `Compatibilities` quantifies EVERY finite integral model and EVERY
   scalar-extension presentation; its pure-tensor equation uses the actual
   coefficient-change map on the fibre. This states model independence as well as
   the required scalar-extension action.
4. The normal-lattice conjunct of `Conclusion` says that on a stalkwise normal scheme every lisse E
   module has a lattice. Its algebraic-closure conjunct says every lisse Qbar module is integral.
   The existing `IsRegularScheme` is used by its regular-implies-normal conjunct, with conclusion
   `∀ z, IsDomain (X.presheaf.stalk z) ∧ IsIntegrallyClosed (...)`.
   Thus the equivalences already recorded on integral objects apply to all lisse
   objects on normal X, and in particular on regular X. Normality is a conclusion
   condition, not an additional hypothesis on the five-clause theorem.
5. The fields-of-definition conjunct of `Conclusion` is `ContinuousAlgCl ... V → IsLAdic ... V` for
   every finite-dimensional representation. Combined with (3),(4), it gives exactly
   the theorem's full equivalence for normal and regular X.

Tensor and scalar compatibility: the three tensor conjuncts of `Compatibilities`
require closure under actual internal relative tensor products
and the unit. `TensorCompatible` gives equivariant linear tensor isomorphisms normalized
on pure tensors by `fibreTensor`; that map is built from the sheafification unit,
strong monoidal inverse image and the actual relative-tensor projection. The unit
has the trivial action. Normalization on generators forces naturality, associativity,
symmetry and unit coherence. The finite-extension conjunct uses the actual inclusions E⊆F of
condensed coefficient rings and the existing ordinary scalar-extension functor.
`ScalarCompatible` also explicitly requires closure under actual coefficient extension,
and fixes the comparison on every pure tensor. Hence compatibility with successive
extensions and their unit follows by evaluating on generators. This handles the
identity inclusion E=F as well.

The last paragraph of the node is the motivating warning recalled from
`sk-lem-stratified-lattice`: the nodal-curve ell-monodromy example explains why the
normality condition in (4) cannot be removed. It is recorded as source commentary
in the module, as in that dependency's module; it is not used as an extra hypothesis
or asserted as integrality for nonnormal schemes.

Dependency declarations read and used:

- `def-galois-fibre-functor`: `Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber`, `AlgebraicGeometry.Scheme.flcFiber`.
- `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing`, `Profinite.CondensedRing`.
- `sk-def-sfb-qlbar-condensed`: `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`, `Profinite.padicAlgClCondensedRing`.
- `sk-def-sfb-constructible`: `Sheaf.Paper.ProfiniteFiniteConstantLocalModel`, `AlgebraicGeometry.ProEtale.HasFiniteConstantProfiniteLocalModel`.
- `lem-sfb-separably-closed-lisse-split-trivialization`: `Sheaf.Paper.SeparablyClosedLisseSplitTrivialization`, `AlgebraicGeometry.ProEtale.separablyClosed_lisse_split_trivialization`.
- `det-pe-condensed-point-coefficients`: `Sheaf.Paper.CondensedPointCoefficients`, `AlgebraicGeometry.ProEtale.condensed_point_coefficients`.
- `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`.
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`.
- `det-pe-finite-local-systems-twist`: `Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsTwist`, `AlgebraicGeometry.ProEtale.finiteLocalSystemsTwist`.
- `cor-galois-lisse-representations`: `Sheaf.Paper.GaloisLisseRepresentations`, `AlgebraicGeometry.Scheme.galois_lisse_representations`.
- `sk-lem-stratified-lattice`: `Sheaf.Paper.StratifiedLattice`, `AlgebraicGeometry.ProEtale.CondensedRing.exists_stratified_lisse_integral_lattice`.
- `sk-def-sfb-module-pushforward-pullback`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`, `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar`.
- `sk-def-sfb-pulled-back-coefficients`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `AlgebraicGeometry.ProEtale.coefficientRing`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-geometric-point`: `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`, `CompactSpace`.
- `def-sfb-lisse-coefficient-module`: `Sheaf.Paper.CoefficientHeartStratificationDefs`, `AlgebraicGeometry.ProEtale.IsLisseCoefficientModule`.
- `def-pod-l-adic-representations`: `Sheaf.RepresentationTheory.LAdic`, `Representation.IsLAdic`.
- `def-pod-ring-scalar-extension`: `WeilConjectures.Algebra.Category.ModuleCat.RingScalarExtension`, `ModuleCat.ringExtendScalars`.

The dependency `cor-galois-lisse-representations` is used only for its finite-ring
correspondence. Its rational/adic clause assumes separatedness and ell invertibility
and is not substituted for this item. The upstream `exists_lisseMonodromy` and
`Sheaf.Paper.NormalProEtaleMonodromy` likewise are not exact matches for this theorem.
The new helper `linearAction` is the existing Rep-to-invertible-action expression with
independent ring/module universes; the recorded Scheme helper artificially ties them.
This is a canonical coercion helper, not a redefinition of the representation notion.

Edge cases checked before writing: rank zero and the zero representation are allowed
by all lisse, free and finite predicates and by the tensor statements. Positive
reduction levels n+1 include n=0 (the residue ring), and do not silently use an inverse
limit containing only one level. E=F and successive finite inclusions are included.
The geometric point excludes the empty connected scheme. No separatedness, finite-type
base field, characteristic restriction or ell-invertibility hypothesis is introduced.
Nonnormal X remains in (1)--(3),(5); (4) alone is conditional. All finite subextensions
are quantified, not just Q_ell itself.

Searches for existing declarations (2026-10-25):

- `msearch.py NE thm-lisse-qlbar-representations leanfinder` with query
  "Lisse pro-etale modules over l-adic integers rational numbers and their algebraic
  closure correspond to continuous representations of the etale fundamental group":
  eight InfiniteGalois results, no matching statement.
- `msearch.py ... loogle "Representation, Continuous, FiniteDimensional"`: no results.
- `msearch.py ... leansearch` with query "An equivalence between lisse sheaves and
  continuous finite dimensional representations of the fundamental group": eight results,
  including the abstract PreGaloisCategory action equivalence, no condensed comparison.
- `msearch.py ... grep "LisseMonodromy|IsContinuousCoefficient|IsContinuousIntegral"
  RepresentationTheory`: no Mathlib result.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the node id, lisseMonodromy,
  continuous representation predicates, finite-field models and embedded lattices:
  found and reused the lisse predicate, IsContinuousIntegral/IsContinuousCoefficient/
  IsLAdic, coefficient maps, Galois finite correspondence and canonical scalar extension.
  The existing normal-monodromy results have more restrictive hypotheses and do not
  include all five clauses or the integral and rational equivalences on arbitrary X.
- Further `rg` for HasLattice, IntegralRational, IntegralAlgCl, EmbeddedEllLattice,
  and integral-lattice structures: the sectionwise embedded-lattice and lattice-pair
  interfaces already exist. Here `HasLattice` spells out the existence criterion for
  the item's actual internal coefficients and its specified embedded localization map;
  it does not introduce another lattice object or another coefficient sheaf.
  `StratifiedLattice.HasCoefficientLattice` is private to that module, so it cannot
  supply a public statement interface; `HasLattice` uses the recorded public lisse
  predicate and the same actual embedded extension/restriction adjunction criterion.

No STATEMENT-DISPUTED issue or source statement correction was found. The helpers are
parts of this node's stated conventions and its normalized comparison assertions;
all are public, documented with this node's blueprint id, and listed in `lean.declarations`.

All recorded proof-dependency modules, including the lattice descent, integral tower,
finite descent, normal finite-section and Baire inputs, are imported for stage 3.
They use plain imports where their declarations are not part of the statement interface.

Previous-delivery validation: clean server compilation passed with no errors or warnings. The main
module took 39.8 s (sandbox check 40.3 s); the dependency import repair took 42.4 s
(sandbox check 41.7 s). Both are below the 60 s limit. No profiler, trace or diagnostic
commands remain. `deliver2.py --no-push` returned OK for commit
`f6de2a423fb`: preflight and per-file compilation passed, including the consumer-module
honesty check for the import-only repair.

## Second reading by NE

The dispatcher's explicit instruction forbids starting other agents and says the
maintainer's independent review reads this delivery. No independent group review is
claimed here. I performed a separate self-check with the complete node and file open:
matched the prime, scheme, point, group model and coefficient convention; matched all
five clauses as listed above; checked rank zero, all positive levels, the actual
embedded map and the pure-tensor equations. The self-check caused the fibre to be
written using the actual ringed-topos pullback and its canonical underlying comparison,
and caused explicit closure under scalar extension to be added. Independent mathematical
acceptance remains with the maintainer, as prescribed by the dispatch brief.

## Historical proof-import build repair

The original delivery fixed the missing public import of
`Sheaf.Paper.SemilinearSystemModels` in `NormalizedCompletionRealization`.
The return advises that this repair is now live at `2bce1dee`; the read clone confirms
the import is present. Its sandbox copy has been removed from this repair packet.

## Returned-delivery repair

Return: independent stage-2 review L of immutable head `474e7aefc2ea`, fault H2.
The review accepted the mathematics and the entire Lean statement. The repair adds
all fourteen requested existing declaration-owner nodes to the item's `stmt_deps`.
The Lean module is byte-for-byte unchanged from the returned sandbox version:
SHA-256 `364ef9d1e0c29c907cf4224383f29481c5a1e1b8635abcd4816229123f164896`.
The node's statement, proof, proof dependencies, hypotheses, and Lean signature are
unchanged. Comparison with the current read clone found no other node-field changes;
the delivery wrapper rebases the packet on the current live branch.

Added owners and the declarations used by this statement and its helpers:

- `def-pod-galois-correspondence-data-e4`: `Sheaf.Paper.GaloisLisseCorrespondenceData`,
  `AlgebraicGeometry.Scheme.GaloisLisseFiniteCorrespondence`.
- `def-sfb-coefficient-map`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`,
  `AlgebraicGeometry.ProEtale.coefficientMap`.
- `sk-def-sfb-change-of-scalars`: `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`,
  `CategoryTheory.Mod.extendScalars, CategoryTheory.Mod.comap, CategoryTheory.Mod.extendRestrictAdjunction`.
- `def-sfb-qlbar-subextension-to-qlbar`: `WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`,
  `Profinite.padicSubfieldRingObjToPadicAlgCl`.
- `def-sfb-qlbar-subextension-map`: `WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`,
  `Profinite.padicSubfieldRingObjMap`.
- `def-sfb-padic-subfield-condensed-ring`: `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
  `Profinite.continuousMapRingObj`.
- `def-sfb-padic-int-condensed-ring`: `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
  `Profinite.continuousMapRingObj`.
- `def-sfb-upper-star-from-point`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.upperStarFromPoint`.
- `def-sfb-finite-upper-star`: `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.ProEtale.upperStar`.
- `sk-def-sfb-coefficient-morphisms`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.condensedPullbackHom`.
- `def-sfb-modobj-extension-along-iso`: `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`,
  `CategoryTheory.Mod.extendScalarsIsoComapInv`.
- `def-sfb-modobj-relative-tensor`: `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`,
  `CategoryTheory.Mod.monoidalCategory, CategoryTheory.Mod.tensorObjπ`.
- `sk-def-sfb-transport`: `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`,
  `CategoryTheory.Functor.mapMod`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt, AlgebraicGeometry.Scheme.ProEt.topology`.

H2 and the advisory are both addressed. Repair validation: `scompile.py` returned
exit 0 with no errors or warnings; the library check took 42.0 s. The source digest,
verbatim signature, dependency uniqueness, and preservation of all base dependencies
were checked. `deliver2.py --no-push` returned OK at `c26190469f9`: the repaired
packet passes preflight and compilation; the only delivered Lean module is the
reviewed `LisseQlbarRepresentations.lean`.
