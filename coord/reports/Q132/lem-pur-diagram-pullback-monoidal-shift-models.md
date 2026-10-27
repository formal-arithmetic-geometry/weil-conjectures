## Worker report

Item: lem-pur-diagram-pullback-monoidal-shift-models. Group Q132, stage 2.
Module: `Sheaf.SixFunctors.DiagramPullbackMonoidalShiftModels`.
Main declaration: `WeilConjectures.DiagramPullbackShift.diagramPullbackMonoidalShiftModels`.

The theorem asserts existence of simultaneous geometric presentations and all the
specified resolving, chain and derived coherence identities. All auxiliary data
constructions are explicit. The only postponed proof is the named main theorem;
its docstring contains the complete six-step natural-language proof from the node,
with all proof dependencies. There is no private derived tensor or abstract
substitute category. The node statement and proof are unchanged. The only node
changes besides `lean` are two added, already landed statement dependencies for
existing canonical geometric helpers.

Clause-by-clause rendering (names below are in
`WeilConjectures.DiagramPullbackShift` unless qualified):

1. **Arbitrary inverse sequence of commutative rings.** The explicit parameters
   `A : ℕ → CommRingCat.{u+1}` and `δ : ∀ n, A (n+1) ⟶ A n` have no hypotheses.
   Index zero is the paper's first index, a relabelling of its positive integers.
   `rings A W n` is the actual constant sheaf, and `transitions A δ W n` is
   `constantSheaf.map (δ n)`, not an arbitrary sheaf map. Composites of adjacent
   transitions are furnished by the dependency's existing system-ring construction.
2. **Small pro-etale site; strict semilinear systems and their ordinary unbounded
   derived category.** `ring` is exactly `SemilinearSections.systemRing` on
   `ProEt.topology W`; `Modules` is the dependency's modules on that entire ringed
   vertical sequence site. `Complex` is its integer-indexed unbounded cochain
   category. `Derived` is `SemilinearSections.DS`, the ordinary localization of
   that category, not diagrams in separately localized coefficient categories.
   Scheme universe `u`, site object universe `u+1`, site morphism universe `u`
   and coefficient universe `u+1` follow the existing pro-etale size convention;
   the site object and morphism universes have not been identified.
3. **Exact termwise inverse image and its specified shift comparison.** `Pullback`
   fixes the right adjoint on sets to the existing continuous sequence-site direct
   image (`rightSets`) and on modules to `SheafOfModules.pushforward` for the
   actual structural ring map (`rightModules`). `rho_component` fixes that map
   at every coefficient and every site object to
   `coefficientProEtaleDirectRingMap v (A n)`. The `geometric` datum is the
   dependency's `RingedPullback`, with finite-limit and finite-colimit preservation
   for its module inverse image. `comparison` is its existing pure-tensor
   `Comparison`. `unit_normalization` identifies the module adjunction unit,
   after forgetting, with the set adjunction unit followed by `comparison.q`;
   this rules out arbitrary choices of adjunction scalar normalization.
   `Pullback.derived` is that exact functor's `mapDerivedCategory`. All shift maps
   used are the standard termwise/localized `commShiftIso` of that exact functor.
   These are existential presentation fields, not extra assumptions on A or δ.
4. **Shift convention.** The existing `CochainComplex ... ℤ` shift has
   `E[r].X p = E.X (p+r)` and differential `(-1)^r d`. There is no replacement
   shift. `CompositorModels` and `EqualityShifts` explicitly use `p+r`.
5. **Canonical pullback compositors, inverses and equality identifications.**
   `Models.compose` uses `CochainPullback.CompositePresentation` on the actual
   three geometric pullbacks. `compose_sections` fixes its right-module
   identification to the existing scheme fiber-product `pullbackComp.inv`
   on every section `(n,U)`. Its canonical adjunction mate is
   `compositionModule`; `Models.compositor` localizes precisely that mate and
   uses `mapDerivedCategoryCompIso`. `CompositorModels` states the degree-p
   comparison on `E[r]` is the ordinary component at `E.X(p+r)`, for **both** hom
   and inv. `CompositorShifts` states `NatTrans.CommShift` for both orientations.
   `EqualityShifts` covers any equality `v=w`, hence equalities of composites,
   using `eqToHom (congrArg ... e)` before and after localization. It includes
   the degree-p formula and the intrinsic derived shift square. Its quantifier
   includes `e.symm`, so inverse equality identifications are included.
6. **Fixed derived tensor, representative maps, unsigned associator, Koszul
   symmetry and action unitors.** `tensor` is the dependency's fixed K-flat
   tensor. `TensorConstraints.normalized` is exactly its existing `IsNormalized`
   predicate, with its representative squares for the two-shift map, associator
   and symmetry. `unitComplex` is the native cochain monoidal degree-zero ring
   unit; `unit_resolving`, `left_model`, and `right_model` fix the two natural
   derived unitors to localizations of the native action unitors. Thus none of
   these constraints can be an arbitrary natural isomorphism.
7. **Two-shift coefficient (-1)^(bp).** `TensorConstraints.shift` is normalized
   by the existing `chainShift`, whose construction extracts the second shift
   before the first. `ChainSignedCoherence` specializes the existing
   `RingedDerivedNative.TotalTensorSignedCoherence` to this module category.
   That predicate includes the actual signed chain formula, naturality,
   associator/symmetry calculations and inverses. Degree p is the shifted degree.
8. **Canonical pullback/tensor comparison; bidegrees and coefficient transitions.**
   `TensorPullback.iso` is fixed by `normalized`, an explicit equality through
   `representative`, `mapDerivedCategoryFactors`, and the existing total
   `CochainPullback.comparison` built from the pure-tensor `comparison.mu`.
   `ChainPullbackCoherence` first states the `ιTensorObj` equation in every
   bidegree: applying the total comparison on the summand equals ordinary
   `mu` at the two component modules followed by the target summand inclusion.
   Its second clause is the actual simultaneous two-shift chain square with
   the fixed `chainShift`. Because these are maps of modules on the whole
   sequence site, all their horizontal semilinear transition squares are part
   of the morphism types, before coefficient evaluation or restriction.
9. **Simultaneous resolving representatives.** `Models.Coherence.resolutions`
   gives flat-term K-flat `Model` representatives and quasi-isomorphisms to
   every finite tuple of unbounded inputs, on the whole diagram site.
   `TensorPullback.preserves_resolving` retains this class under pullback.
   The existing `totalModel` and `shiftModel` constructions close it under the
   total tensors and all integer shifts that occur, and `unit_resolving` puts
   the ring unit in the same class. Thus diagrams use the same chosen inputs
   and their actual operations, not independent coefficientwise resolutions.
10. **Unsigned reassociation and unit coefficients.** The normalized associator
    uses the native unsigned cochain associator. `ChainSignedCoherence` includes
    the triple-degree equations with exponents `bp+c(p+q)` and `cq+(b+c)p`.
    `ChainUnitCoherence` gives the two actual summand equations at degrees
    `(0,p)` and `(p,0)`, through `singleObjXSelf` and the module action unitors;
    no sign or scalar is inserted. `TensorCoherence.associativity` is the
    explicit simultaneous derived associator square, including the `add_assoc`
    transport. `left_unitor` and `right_unitor` give both derived shift squares.
11. **Signed symmetry.** The existing chain predicate gives exactly the two
    exponents `bp+(p+a)(q+b)` and `ab+pq+aq`, equal modulo two, and the identity
    with scalar `(-1)^(ab)`. `TensorCoherence.symmetry` explicitly states its
    derived version, with `add_comm` transport at the output. The swapped pair
    `(N,M)` follows the shifted occurrence to its permuted position. Setting
    either shift to zero gives each required single-input square.
12. **Intrinsic descent, all occurrence squares and naturality.**
    `TensorPullback.ShiftCoherence` is the full two-input derived pullback/tensor
    square. `TensorCoherence.associativity`, `.symmetry`, `.left_unitor`, and
    `.right_unitor` give the other derived equations. `CompositorShifts` and
    `EqualityShifts` supply the unary cases, including inverses. Single-occurrence
    cases are their specializations with other shifts zero, using the stated
    zero-shift laws. All structure comparisons are natural transformations or
    natural isomorphisms, so naturality in all inputs is retained. All equalities
    are in `Derived A δ W`, never equalities only after coefficient evaluation.
13. **Zero, addition and interchange.** `TensorConstraints.firstShift` and
    `.secondShift` are explicit extraction maps formed from `shift` and the
    canonical zero-shift isomorphism, not new free data. `TensorCoherence.shift_laws`
    asserts the existing `Functor.CommShift ℤ` structures have precisely those
    maps; this includes zero and addition laws in each slot. `.extraction` fixes
    the simultaneous t to second-then-first extraction. `.interchange` explicitly
    gives the scalar `(-1)^(ab)` for the opposite extraction order, including
    the canonical output addition comparison. Exact-pullback CommShift and
    natural-transformation CommShift use their standard zero/addition laws.
14. **No normalization or boundedness assumption; quotient transitions retained.**
    The only main theorem parameters are A and δ. No cartesianness,
    normalized-system condition, finiteness of amplitude, flatness of δ,
    or coefficient evaluation is assumed. In particular choosing the arbitrary
    ring homomorphisms to be `R/t^(n+1) → R/t^n` is permitted. Every equality
    remains an equality of morphisms of the strict whole-system category.

Dependencies read and used:

- `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.semilinearDerivedSections`, with its
  `systemRing` and `DS` interfaces; the actual module-system category.
- `Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints`:
  `SheafOfModules.DerivedTensorConstraints.existsUnique_derived_tensor_constraints`,
  and the public `Model`, `resolvingComplex`, `tensor`, `representative`,
  `IsNormalized`, `totalModel`, `shiftModel` and `chainShift` interfaces. These
  retain the fixed representative maps and finite-variable localization method.
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`:
  `CategoryTheory.CochainPullback.cochainPullbackTensorCoherence`, with its
  `RingedPullback`, `Comparison`, `CompositePresentation`, `comparison`,
  `compositionModule` and `composition` constructions.
- `Sheaf.Algebra.Homology.TotalTensorSignedCoherence`:
  `CategoryTheory.RingedDerivedNative.totalTensor_signed_coherence`, with the
  actual `TotalTensorSignedCoherence` predicate for the signed chain calculations.
  This was already a proof dependency and is public because its predicate occurs
  in the statement.
- `Sheaf.Paper.IntegralComparisonSequenceSystems`:
  `WeilConjectures.integralComparisonSequenceBaseChange`, including its
  continuity instance. This particular helper is coefficient independent:
  `(𝟭 ℕ).prod (proEtaleBaseChange v)`; no integral coefficient specialization
  is used. Its owning landed node
  `def-trf-integral-comparison-sequence-systems` is added to `stmt_deps`.
- `Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses`:
  `AlgebraicGeometry.Scheme.coefficientProEtaleDirectRingMap`, the existing canonical
  constant-sheaf coefficient map obtained from sheafification adjunction.
  Its owning landed node `def-weil-proetale-inverse-image` is added to `stmt_deps`.
- Proof-only import `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- Proof-only import `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
- Mathlib `Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategoryFactors`, `mapDerivedCategoryNatIso`,
  `mapDerivedCategoryCompIso` and exact-functor shift structures.
- Mathlib `Algebra.Homology.BifunctorShift`:
  `CategoryTheory.Functor.instCommShift₂IntCochainComplexIntMap₂CochainComplex`.

Edge cases checked before finalizing the statement: zero ring, zero module/complex,
zero coefficient homomorphisms, empty scheme, empty finite tuple `Fin 0`, first
coefficient index, shifts 0, 1 and -1, negative bidegrees, characteristic two,
odd/odd shifts and arbitrary nonflat quotient transitions. The explicit exponent
identities give difference zero for reassociation and `2*b*p` for symmetry;
the latter is even for all integers. The interchange sign is necessary for two
odd shifts. The unit normalization prevents a sign-twisted adjunction from
changing the intended pullback comparison. No nonzero-ring or nonempty-scheme
hypothesis has slipped into the statement.

Searches for an existing full statement:

- `msearch.py ... leanfinder "Strict semilinear inverse systems derived pullback
  compositors monoidal tensor shifts simultaneous K flat models signed associator
  symmetry coherence"`: eight hits, including
  `HomologicalComplex.leftUnitor'_inv_comm_assoc`,
  `CategoryTheory.NatTrans.PullbackShift.natIsoComp`, and
  `CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc`; no full diagram-system
  resolving/descent statement.
- `msearch.py ... loogle "CategoryTheory.NatTrans.CommShift,
  CochainComplex.mapBifunctorShift₁Iso, CochainComplex.mapBifunctorShift₂Iso"`:
  zero hits.
- `msearch.py ... grep "totalShift|mapBifunctorShift|commShift"
  Algebra/Homology/BifunctorShift.lean`: five hits, lines 10, 17, 19, 22, 77;
  the existing shift machinery is reused, but it does not assert this full theorem.
- `msearch.py ... leansearch "Canonical strict semilinear system pullback
  compositors and derived monoidal tensor shift squares with signed symmetry"`:
  eight hits, including `CategoryTheory.MorphismProperty.Over.pullbackComp` and
  `CategoryTheory.pullbackShiftFunctorZero_inv_app`, plus unrelated seminorm and
  ordinary pullback results; none is the item.
- `rg` in the read-only `lean/WeilConjectures` and `lean/Sheaf` sources for
  `DiagramPullback`, `monoidalShift`, resolving/shift combinations and the item id;
  no existing declaration of the item. Follow-up namespace/declaration searches
  for `DiagramPullbackShift`, `diagramPullbackMonoidalShiftModels` and
  `ChainSignedCoherence` found no collision. The relevant existing semilinear,
  K-flat, tensor, pullback and signed-coherence definitions were read and reused.

There are no new independent definition nodes, no dependency-record replacements,
and no statement correction or unresolved STATEMENT-DISPUTED issue. The helper
structures express only the simultaneous presentations and coherence data of this
item; all are listed in `lean.declarations` with source/blueprint docstrings.

## Second reading by Q132

The dispatcher's brief explicitly forbids starting another agent and assigns the
independent delivery review to the maintainer. This section records the worker's
second pass, not an independent reader's review. With the node and full module
open, I checked all fourteen correspondences above. During that pass the adjunction
unit normalization and the explicit two-slot interchange equation were added so
the geometric pure-tensor normalization and the (-1)^(ab) rule are both retained.
I checked hom and inverse compositor components, equality-of-composites maps,
all three associator slots, both unitor slots, the permutation of symmetry slots,
coefficient transition preservation, and the representative/localized map squares.
The primitive chain and derived maps all come from the recorded dependencies;
no free replacement map, evaluation-only equality, extra hypothesis, or changed
node statement remains. Definitions contain real data; the sole sorry is the
main theorem with its full proof docstring.
