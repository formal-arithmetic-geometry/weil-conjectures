## Worker report

The delivery states `AlgebraicGeometry.ProEtale.integral_models` in
`Sheaf.Paper.IntegralModels`. Its only postponed proof is `sorry`. The embedded coefficient presentation is now
owned by this same module. It reuses N1's general section-ring and small-site transport
without modifying N1's module or node record. All definitions have real terms; the
theorem docstring retains the source and all twelve reviewed proof steps.

Hypotheses and objects:

- `k : Type u`, `[Field k]`, `p ℓ : ℕ`, `[Fact p.Prime]`, `[Fact ℓ.Prime]`,
  `[CharP k p]`, and `hℓp : ℓ ≠ p` give exactly the positive-characteristic,
  distinct-prime setting. Primality entails positive characteristic.
- `X : Scheme.{u}`, `[X.Over (Spec (.of k))]`,
  `[LocallyOfFiniteType (X ↘ Spec (.of k))]`,
  `[QuasiCompact (X ↘ Spec (.of k))]`, and
  `[IsSeparated (X ↘ Spec (.of k))]` express a separated finite-type k-scheme.
  `[IsNoetherian X]` writes the node's explicit standing Noetherian hypothesis.
  Every universally quantified Y, S, and V in the operations and reduction assertions
  has these same structures; `f.IsOver`, `j.IsOver`, and `i.IsOver` retain k-morphisms.
- `E : PadicAlgCl.FiniteIntermediateField ℓ` represents the finite extension inside
  the chosen algebraic closure `PadicAlgCl ℓ`. This is the existing coefficient and
  generator convention. `π : PadicAlgCl.integers ℓ E.1` together with
  `hπ : Ideal.span {π} = IsLocalRing.maximalIdeal ...` specifies the uniformizer.
- `integralCoefficientObject X ℓ E` is the existing pullback of the continuous
  condensed integral ring; `finiteCoefficientObject` and `qlbarCoefficientObject`
  are the existing E and finite-subextension-valued algebraic-closure coefficients.
  The constant scalar object is `condensedRingObj (IntegralModelsEmbedded.discreteObj
  (PadicAlgCl.integers ℓ E.1)) X`: the pullback of the constant commutative ring sheaf
  on the point, hence the usual constant scalar sheaf on X. The canonical map is
  `IntegralModelsEmbedded.scalarMap`, obtained from constant continuous functions
  by sheafification and the existing monoidal inverse image. No arbitrary map or
  coefficient isomorphism is quantified over.
- All ambient categories are the existing unbounded `DerivedCategory (Mod ...)`.
  `constantModelBoundedConstructible` uses bounded cohomology and the finite constant
  scalar models of the node `sk-def-sfb-constructible`, without inserting completeness.

Conclusion, clause by clause:

- The opening equality is literally the equality of the object predicates
  `(constantModelBoundedConstructible ... ⊓ DerivedCategory.finiteTorAmplitude _)`
  and `constantModelBoundedConstructible ...`. Their full subcategories are precisely
  Dctf and Dbc, with the same ambient morphisms.
- Clause (1) is the existential equivalence between the full subcategories selected by
  `completedComplete` and `constantComplete`. The natural isomorphism after composing
  their inclusions identifies its forward functor with the actual
  `IntegralModelsEmbedded.restriction` (`Mod.comap scalarMap` applied termwise).
  Thus the equivalence is specifically restriction of scalars.
- Both completeness aliases use the already existing `ConstantCompletion.IsComplete`
  on `IntegralModelsStacks.smallMap` and `smallDerivedObject`. The latter are the
  sectionwise equivalence and equivalent-site transport, not a condition on K.
  The former is local derived ideal completeness for the kernel of the actual
  first quotient, i.e. the uniformizer ideal. By the recorded constant-completion
  equivalence this is precisely invertibility of the canonical quotient-tower
  completion unit, as in `sk-def-pe-derived-completion`. This uses the existing
  general predicate to accommodate the embedded coefficient presentation, rather
  than forcing the scheme universe to zero to call the spectral E : Type u API.
- Clause (2), first equivalence: for *every* completed-coefficient K, membership in
  Dbc is equivalent to `stacksConstructible` of its actual restricted complex.
  That predicate is completeness, constructible cohomology of the constant-residue
  derived extension of scalars, and finite relative Tor amplitude. It is the
  coefficient specialization of the existing `IntegralModelsStacks.stacksConstructible`.
  Over the finite residue field on this Noetherian scheme, the constructible
  cohomology is classical by the recorded constructible comparison.
- Clause (2), equivalent criterion: for that same arbitrary K, the second iff states
  completed completeness and `integralModelResidueEtaleOrigin`. The latter takes
  the derived reduction at n = 1, applies the *existing canonical*
  `integralModelIntrinsicRealization`, and asks for essential-image membership in
  the restriction of `finiteCoefficientIntrinsicDerivedComparison` to the full
  bounded constructible etale category. It therefore includes boundedness,
  constructibility, and etale origin together. The existential `Finite` and
  `DiscreteTopology` structures on the actual residue ring are conclusions needed
  to invoke that realization, not hypotheses that shrink the theorem's domain.
- Clause (3), inverse image: for every morphism f : X -> Y in the setting and every
  bounded constructible K on Y, `CondensedRing.moduleObjectDerivedPullback ... f`
  sends K to a bounded constructible complex on X. This is the recorded total
  left derived functor of the full module inverse image. Exactness identifies it
  with the termwise inverse image used in the operations dependency.
- Clause (3), tensor: for any two bounded constructible K, M, the actual ambient
  `CondensedRing.derivedTensor` lies in the same Dbc. No completion functor occurs.
- Clause (3), extension by zero: for an open j : S -> V followed by a closed
  i : V -> X, `moduleObjectDerivedPushforward ... i` of the termwise derived
  `openImmersionLowerShriek ... j` sends every L in Dbc(S) to Dbc(X). This is
  exactly i_* j_!, since both functors are exact for these immersions.
- Clause (4), E: every K in Dbc(X,E) belongs to the intersection of all isomorphism
  closed triangulated object properties containing `integralModelGenerator X ℓ E`.
  This is finite cones and integer shifts. The generator is the existing degree-zero
  scalar extension of `integralLowerShriek` of a `CondensedRing.LocallyFree` lattice.
- Clause (4), algebraic closure: an E' is chosen *before* the same triangulated
  closure of `qlbarModelGenerator X ℓ E'`. The field may depend on K, but cannot vary
  from generator to generator in its finite construction. These are the existing
  Qbar_X tensor a_!L0 generators, with finite-subextension-valued Qbar coefficients.
- Clause (4), final assertions: every specified locally free L0 has
  `integralReductionHasEtaleOrigin X ℓ E π j i L0`, the existing fully expanded
  predicate from the generator dependency. Its first conjunct is a_!L0 in Dbc(X,O_E).
  For *every n >= 1*, its next conjunct is the isomorphism between the *derived*
  scalar extension of that very object and the degree-zero extension by zero of
  the ordinary reduced lattice. Its remaining conjuncts are bounded
  constructibility and essential-image membership of the bounded constructible
  etale inverse image. The same j, i, L0 are fixed before quantifying n.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField` and its over-field scheme convention.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, `upperStarFromPoint`, and their commutative ring structures.
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`:
  `sfb_integral_coefficient_limit`; the spectral finite-extension interface remains
  imported, while the embedded coefficient specialization uses the actual
  `completedResidue`/`completedReduction` maps already used by the generators.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions`, with Mathlib's actual
  localization `DerivedCategory` and upstream `leftDerivedFunctor`/`mapDerivedCategory`.
- `Sheaf.Paper.CondensedConstantConstructibility`: `IsConstantModelConstructible`,
  `constantModelBoundedConstructible`, `ConstantModelConstructibleFiniteTor`.
- `Sheaf.Paper.ConstantModelTorAmplitude`: the recorded well-definedness interface;
  finite Tor amplitude is the existing `DerivedCategory.finiteTorAmplitude`.
- `Sheaf.SixFunctors.ProEtale.DerivedCompletion`: `IsDerivedComplete` and its
  explicit canonical augmented quotient Roos construction, read against the generic
  `ConstantCompletion.IsComplete` presentation used here.
- `Sheaf.AlgebraicGeometry.IntegralModelsStacks`: `discreteObj`,
  `constantToContinuous`, `restriction`, `stacksConstructible`, `integral_models_stacks`,
  `smallMap`, `smallDerivedObject`; the independent-coefficient helpers now belong to the item module, preserving the
  general-field API and its original ownership.
- `Sheaf.Paper.ConstantCompletionEquivalence`: `IsComplete`, `kernelIdeal`, and
  `equivalence`, identifying local ideal completeness with canonical tower completeness.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: `moduleObjectDerivedPullback` and
  `moduleObjectDerivedPushforward` of the full underived composites.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`: `derivedHom`,
  with its imported relative `derivedTensor` and tensor/internal-Hom adjunction.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `openImmersionLowerShriek`, its underlying extension by zero and exactness.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `padicAlgClCondensedRing`, `padicAlgClRingObj`, `padicIntegersRingObj`.
- `Sheaf.SixFunctors.IntegralModelsGenerators`: `integralModelGenerator`,
  `qlbarModelGenerator`, `integralReductionHasEtaleOrigin`, coefficient objects,
  `integralModelReductionMap`, `integralModelIntrinsicRealization`, and the theorem
  `integral_models_generators`. The theorem remains in proof_deps; the new definition node
  def-sfb-integral-model-generator-data supplies these unchanged definitions in stmt_deps.
- Proof imports also retain `LocalizingClosureCtfEqualsBc`,
  `SheafificationFlat`, `BoundedAboveFlatSheafKFlat`,
  `ConstructibleProEtaleComparison`, `IntegralModelsOperations`, and
  `CartesianCoefficients`, exactly the recorded proof plan where declarations exist.
  `det-prop-integral-criterion-constant-coefficients` has no recorded declaration;
  no import is invented for this proof-only dependency. Nothing in the statement
  takes its theorem as an assumption.

Edge cases checked before writing: the empty scheme is allowed, as are zero complexes,
rank-zero locally free lattices and empty stratifications. There is no nonempty-scheme,
nonzero-object, positive-rank, or nonempty-stratum binder. Finite generation uses
triangulated closure, not thick closure under retracts or localizing closure under
infinite sums. Degree-zero integral lattices may have variable local finite ranks.
All positive exponents are retained, including n = 1; the existing reduction convention
uses n-1, so the first quotient is level 0. No assertion is made at n = 0. The universe u
of the scheme is arbitrary and is not identified with the Type-zero coefficient field.
The criterion is for arbitrary unbounded K. Inverse image includes identities and all
k-morphisms, not just smooth/proper/etale maps. The tensor is uncompleted. The algebraic
closure is the actual existing algebraic closure, not its completed valued field.

Searches:

- `msearch.py NZ sk-lem-integral-models leanfinder` with query
  `Integral models of constructible l-adic complexes equivalence of complete constant
  and completed coefficients and finite cones of lattices`: 8 hits, all unrelated
  algebraic adic-completion product/coordinate equivalences; no combined statement.
- `msearch.py ... loogle 'DerivedCategory, SheafOfModules.restrictScalars'`: 0 hits.
- `msearch.py ... grep 'integral.models|integralModels|integral_models'`: 0 Mathlib hits.
- `rg -n 'integral.models|integralModels|integral_models'` in the specified upstream
  WeilConjectures tree: no hit; `grep -rn sk-lem-integral-models` there: no hit.
- The same rg in `lean/Sheaf` finds the separate Stacks, operations and generators
  statements and unrelated integral-model notions; none states this unit's complete
  conjunction. Their declarations are reused rather than replaced.
- Source read via the authorized `scompile.py --source
  Sheaf.Paper.ContinuousCoefficientModuleEncoding` where that current source was absent
  in the shared checkout, to verify the canonical continuous module equivalence used
  by the existing generator realization.

No statement correction or STATEMENT-DISPUTED flag is needed. The two new definition
nodes record existing notions; neither adds a new Lean declaration.

## New nodes

`def-sfb-integral-model-generator-data` records the unchanged plain definitions and
instances in `Sheaf.SixFunctors.IntegralModelsGenerators`, with `existing: true`.
The primary declaration is `WeilConjectures.SixFunctors.integralReductionHasEtaleOrigin`;
the declaration list includes all coefficient objects, scalar extensions, lattice
generator classes, reduction maps, and intrinsic realization. The node defines the
reduction-origin predicate; it does not assert that a lattice satisfies it. Its source
is the generator detail of the integral-model blueprint. The item cites this definition
node, while `det-lem-integral-models-generators` remains only a proof dependency.

`def-sfb-quotient-kernel-completeness` records the unchanged `kernelIdeal` and `IsComplete`
in `Sheaf.Paper.ConstantCompletionEquivalence`, with `existing: true`. Its predicate is
local derived completeness for the kernel of an arbitrary ring-sheaf map. The kernel
is determined uniquely by its section formula; no datum is chosen from the comparison
theorem. The item cites this definition node, while
`lem-weil-pbc-constant-completion-equivalence` remains only a proof dependency.

For both nodes the repeated searches were:

- LeanFinder: `Integral lattice generators of constructible l-adic complexes and local
  derived completeness for the kernel of a quotient of sheaves of rings`: eight hits
  about finite presentation, local cohomology and condensed modules, none exact.
- Loogle: `SheafOfModules, DerivedCategory`: zero hits.
- Mathlib grep: `integralModelGenerator|integralReductionHasEtaleOrigin|IsComplete`:
  25 hits about topological completeness, none about these ring-sheaf predicates.
- The same named-declaration search in the upstream WeilConjectures tree: no hit.
  In the project it finds precisely the two unchanged modules being recorded.
  DAG grep finds the theorem records and theorem consumers, with no definition node
  carrying these exact APIs; blueprint_refs.py searches for `integralModelGenerator`
  and `local derived completeness` each return zero nodes.

The raw msearch JSON results are retained verbatim in each new node's mathlib_searches.
No Lean module is delivered for either existing-definition record.

## Returned-delivery repairs

R1: deleted the sandbox replacement of `det-lem-integral-models-stacks.json`.
N1's landed node record, all 22 declarations, and `IntegralModelsStacks.lean` remain
unchanged. In particular `smallMap` and `smallDerivedObject` retain their original
DAG ownership, and the item imports that module. Moved the embedded presentation into
`Sheaf.Paper.IntegralModels`, which this delivery owns, and recorded every helper in
its lean.declarations. Removed the redundant embedded `integral_models_stacks` theorem;
the item's unchanged combined theorem already asserts its criterion. The scalar maps,
restriction functor and adic predicate are independent-universe specializations: N1's
`A : Type u` ties coefficients to `Profinite.{u}`, whereas these coefficients are
`Type 0` and the scheme universe is arbitrary. The existing N1 signatures cannot be
instantiated to them without lifting the coefficient type and transporting its scalar
objects; no extra equality of universes is imposed. The generic section-ring and
small-site constructions are reused verbatim by name, without copies.

R2: the item's stmt_deps now adds only the two new definition nodes above. Neither
of the two theorem nodes is added to stmt_deps; both remain in proof_deps, and their
existing modules and records are unchanged. The new definition records have no
module files and do not claim the theorem declarations.

## Second reading by NZ

The dispatcher forbids other agents; this is the required author self-check, followed
by the maintainer's independent review. Re-read the returned head's saved signatures,
the current base node and N1 record, the blueprint unit, and the revised single module.
The maintainer had accepted the mathematical statement clause by clause; this repair
retains that theorem signature byte for byte. The same first residue reduction, both
criteria for arbitrary K, identified restriction equivalence, arbitrary inverse image,
uncompleted tensor, open-then-closed extension, finite triangulated generation, one E'
per algebraic-closure object, and all positive reductions remain. Standing field,
characteristic, Noetherian and separated finite-type hypotheses and all scheme universes
are unchanged. The moved helper bodies are unchanged except for their owning blueprint
identifier. No new theorem or sorry definition was introduced. The previously unowned
specialized theorem was removed. The base node changes only lean and stmt_deps, with
exactly the two new definition-node additions; no existing dependency node is delivered.


## Saved-packet dry-run repairs

The initial dry run rejected the saved packet for three metadata issues. The
existing generator predicate's recorded signature now begins at `def`, matching
`stage2_delivery.py signature` and the current published declaration. Both new
nodes use the empty `blueprint.from.via` required for a child of this blueprint
unit itself. Both now record the actual LeanSearch query and its raw JSON result
in addition to the saved LeanFinder, Loogle and grep searches. LeanSearch returned
eight hits about ordinary adic completion and module-sheaf local generators;
none defines these notions. No Lean declaration or theorem signature changed.

The renewed author self-check opened the item node and full module, N1's unchanged
22-declaration record and module, both existing definition modules, and the blueprint
unit. The item differs from the current base only in `lean` and the two added
definition dependencies. The sandbox contains no replacement Stacks dependency node
or module. All 19 declarations of the item module are recorded, including its
17 embedded scalar/completeness helpers, the residue-origin predicate and theorem.
The new definition records select only definitions and instances; the generator
and completion-equivalence theorems remain in `proof_deps` and are not assumed by
the statement. Empty schemes, arbitrary scheme universes, zero complexes, n = 1,
arbitrary unbounded K, the single E' per Qbar object and uncompleted tensor are
retained. The only postponed proof in the delivered module is `integral_models`.
