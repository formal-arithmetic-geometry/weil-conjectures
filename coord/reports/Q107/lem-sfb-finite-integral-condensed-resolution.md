## Worker report

The module `Sheaf.NumberTheory.Padics.FiniteIntegralCondensedResolution` states
`Padic.finite_integral_condensed_resolution`, with its proof `sorry`. There is exactly
one postponed theorem. Its docstring gives all ten steps of the node's proof, including
the zero-ring case, full-rank Smith form argument, inverse-continuity argument, finite
clopen lifting argument, and the sheaf kernel/cokernel universal properties.

The declaration `Padic.FiniteIntegralCondensedResolution` is a transparent packaging of
this node's entire conclusion, not an alternative definition of condensed coefficients
or module objects. It allows the theorem to specify the existing valuation topology
without a `let` binder in its statement. Its body has real logical data throughout;
its local algebra structure is exactly `a.toAlgebra`, its continuous scalar action is
Mathlib's `continuousSMul_of_algebraMap O A ha`, and its finite-biproduct instance is
`HasFiniteBiproducts.of_hasFiniteProducts`. No arbitrary maps, module structures, or
unproved existence choices replace the required constructions.

`Padic.finiteIntegralIntegersTopologicalRing` is an abbreviation exposing the existing
subring topological-ring instance under the spectral norm. It is not a new postponed
arithmetic or topological assertion: its body installs `spectralNorm.normedField` and
returns the inferred Mathlib instance. There is no `sorry` in either helper.

Hypothesis-by-hypothesis correspondence:

- The prime ell is `(l : ℕ) [Fact l.Prime]`.
- The finite field extension is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`.
- O is exactly `Padic.coefficientExtensionIntegers l E`, publicly imported through
  the coefficient-extension node's recorded module. It is never replaced by an
  arbitrary DVR or an independently chosen ring.
- Its topology is explicitly `Padic.coefficientExtensionIntegersTopology l E`, the
  recorded subspace topology for the extending spectral absolute value. This topology
  is supplied to both `ha` and the conclusion predicate by explicit instance arguments;
  no topology on E or O is left arbitrary.
- A is `(A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
  [DiscreteTopology A]`. No nontriviality, nonemptiness of a test space, or positive
  rank is assumed. The discrete topology's topological-ring instance is inferred.
- The continuous unital homomorphism is `(a : coefficientExtensionIntegers l E →+* A)`
  with `ha : @Continuous _ _ (coefficientExtensionIntegersTopology l E) inferInstance a`.
  Inside the transparent conclusion, `a.toAlgebra` makes every O-action the specified
  action through a, including the action on the condensed A module.

Clause-by-clause correspondence after unfolding the transparent conclusion:

- `∃ (r : ℕ)` is an integer r >= 0, with `Fin r → O` the coordinate O^r with its
  product topology. Nothing requires r > 0.
- `q : (Fin r → O) →L[O] A` is O-linear and continuous; `Function.Surjective q`
  asserts its surjectivity.
- `φ : (Fin r → O) →L[O] (Fin r → O)` is O-linear and continuous.
  `∃ M : Matrix (Fin r) (Fin r) O, ∀ x, φ x = M.mulVec x` explicitly states the
  integral-matrix clause. Continuity of this finite matrix is implied by the node's
  valuation-topology setup, so bundling it as a continuous linear map loses no case.
- `Function.Injective φ ∧ Function.Exact φ q`, together with surjectivity of q,
  is the algebraic short exact sequence, including both zeros.
- `∃ e : (Fin r → O) ≃ₜ LinearMap.ker q.toLinearMap, ∀ x, (e x).val = φ x`
  states precisely that this same φ is a homeomorphism onto the kernel with its
  inherited subtype topology. The homeomorphism is not unrelated to φ.
- For every `S : Profinite.{u}`, the three conditions `Function.Injective`,
  `Function.Exact`, `Function.Surjective` are applied to
  `ContinuousLinearMap.compLeftContinuous O S φ` and
  `ContinuousLinearMap.compLeftContinuous O S q`. These are the canonical
  postcomposition maps on C(S,-), not existentially chosen group homomorphisms.
  They are O-linear, hence additive, as required for exactness of abelian groups.
- The free condensed term is the existing
  `Profinite.continuousSectionsModule O (Fin r → O)`. Its underlying sections are
  `ULift C(S,Fin r → O)`, with pointwise C(S,O)-action. An explicit `Nonempty` of
  an isomorphism to `biproduct (fun _ : Fin r ↦ Mod.regular
  (Profinite.continuousCoefficientRingObj O))` records its finite direct-sum
  interpretation. This is an isomorphism asserted in the conclusion; no definition
  chooses data from an unproved existence assertion.
- The condensed target is the same existing constructor with T=A, with the scalar
  map a supplied by `a.toAlgebra` and ha. It is the node's underlined A.
- `F`, `G` are morphisms in Mathlib's `CategoryTheory.Mod` over the recorded
  `Profinite.continuousCoefficientRingObj O` on the coherent profinite site.
  Their formulas on every S, lifted section f, and point s force them to be
  postcomposition by the same φ and q. Thus no arbitrary exact arrows are allowed.
- `(h : F ≫ G = 0)` and `(ShortComplex.mk F G h).ShortExact` state short exactness
  as condensed O-module objects. Using the displayed finite-biproduct identification
  is exactly the final sequence of underlined O^{oplus r} in the node.
- Empty profinite S and the zero ring A are included. When A is zero, r=0, the empty
  matrix, and the unique maps satisfy every clause, including the empty biproduct.
  For nonzero A, the surjectivity clause itself excludes r=0; no extra restriction
  on the existential rank was added. No assumption that a is surjective is made:
  enumerating all elements of A in q works for every continuous unital a.

The ambient universe u is explicit in the field and coefficient carriers and in the
profinite site. The continuous sections are lifted to `Ab.{u+1}`, exactly the existing
site/module convention, not a discrete-coefficient `CondensedMod O` category. There
are no auto-bound variables, private definitions, or file-local instances/notations.
The constructor's same-universe convention uses a common ambient universe for these
objects; it does not impose a finiteness or countability restriction on profinite sets.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (recorded module of
  `def-weil-l-adic-coefficient-extension`) publicly supplies
  `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionAbsoluteValue`,
  and the field-extension conventions from `CoefficientExtension`.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` is the general
  ring-object encoding; its public imports supply the continuous coefficient
  ring sheaf/object constructors and their canonical tensor-ring structures.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `Mod.regular`,
  `Mod.comap`, and action-compatible module morphisms are the module-object node's
  recorded declarations, used via the existing continuousSectionsModule constructor.
- `Sheaf.NumberTheory.Padics.IntegersProfiniteTower`:
  `Padic.coefficientExtensionIntegersTopology` fixes the valuation topology.
  Its definition is owned by the new existing:true node
  `def-sfb-coefficient-extension-integers-topology`, cited in stmt_deps.
- `Sheaf.Topology.ProfiniteSectionsFiniteQuotient`:
  `Profinite.continuousSectionsModule` supplies exactly the needed pointwise
  continuous-function module, and `continuousSections_finiteDiscrete_shortExact`
  is available but its conclusion is not used in the statement. The constructor
  is owned by the new existing:true node `def-sfb-continuous-sections-module`,
  cited in stmt_deps. Neither definition node depends on this item.
- Proof-only import `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr` supplies
  `Padic.extension_integers_dvr`, whose full signature and docstring were read.
- Proof-only import `Mathlib.LinearAlgebra.FreeModule.PID` supplies the recorded
  `Submodule.exists_smith_normal_form_of_le` for
  `lem-sc-dvr-saturation-line-smith-normal-form`. Its full signature and docstring
  were read, including the distinct ambient indices via `Fin.castLE`.

Searches for an existing exact statement (all before writing):

- `msearch.py leanfinder`, query "A finite discrete algebra over the integers of a
  finite p-adic field has a two term finite free resolution exact on continuous
  functions from every profinite set": eight hits, including
  `Profinite.NobelingProof.succ_exact`, `LocallyConstant.freeOfProfinite`,
  `Condensed.finFree`, `Condensed.profiniteFree`, `Condensed.profiniteSolid`, and
  period-ring constructions. None asserts this valuation-ring resolution and all
  its topological and condensed clauses.
- `msearch.py loogle`, query `Condensed, Module.Free`: zero hits.
- `msearch.py grep`, query
  `(Condensed.*(resolution|[eE]xact)|([eE]xact|resolution).*Condensed)`:
  seven hits in Nobeling Successor, Condensed Discrete Module, Light Epi, AB, and
  TopCatAdjunction. None is this arithmetic/topological resolution statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, using finite-resolution,
  integral-condensed, continuous-module and continuous-ring patterns: found the
  existing continuous ring and continuousSectionsModule constructors used above;
  no exact match for the item. Search for the exact item id in WeilConjectures
  returned no occurrence.
- Collision search for `FiniteIntegralCondensedResolution`,
  `finite_integral_condensed_resolution`, and `finiteIntegralIntegersTopologicalRing`
  in Mathlib, WeilConjectures, Sheaf, and `dag/lean_names_upstream.json`: no hits.

The two existing constructors now have dedicated definition nodes (see below);
no dependency interface or Lean source was changed. There is no statement
correction and no STATEMENT-DISPUTED flag: the source and node agree, and the edge
cases above support the statement as written. The two helpers belong to this exact
assertion and are listed in the item's lean.declarations with blueprint/source docstrings.

Validation: scompile.py compiled both its isolated sandbox view and the final library
module against the live server build, exit code 0, no warnings (12.0 s and 24.7 s).
All compile attempts used only scompile.py. No live source was edited.

## Second reading by Q107

No second worker was started. Under the dispatcher's current direct-delivery brief,
the maintainer's independent review supplies the independent second reading. The
worker's clause audit and the actual compile results are recorded above.

## Repair of return L, immutable head 10dcaeb5956f

H2/H13 repaired: the theorem nodes `lem-sfb-integers-profinite-tower` and
`lem-pe-profinite-sections-finite-quotient` were removed from the added stmt_deps.
The unchanged Lean imports remain necessary to access their concrete definitions.
Two existing:true definition nodes now own precisely those definitions. Neither
constructor is chosen from a theorem: the topology is `TopologicalSpace.induced`,
and the section module is `Mod.comap` applied to the regular module. No proof
dependency change, statement correction, or Lean source change was needed.
The saved packet initially passed the mechanical dry run (6cfa4195425); the
independent return nevertheless required this semantic dependency repair. Against
the current shared base the item still differs only in lean and added stmt_deps.

## New nodes

`def-sfb-coefficient-extension-integers-topology` records the existing
`Padic.coefficientExtensionIntegersTopology` in
`Sheaf.NumberTheory.Padics.IntegersProfiniteTower`, with its full signature verbatim.
Its sole input definition is the finite coefficient extension. The source's
valuation topology is exactly the subspace topology from the spectral norm.
LeanSearch, LeanFinder, Mathlib grep, project/DAG grep and blueprint search were
run again; raw msearch records are in mathlib_searches. No definition node owned
this specialized construction; only theorem nodes referenced it. No new module
or copy is introduced. This includes every finite extension, including ramified E.

`def-sfb-continuous-sections-module` records the existing
`Profinite.continuousSectionsModule` in
`Sheaf.Topology.ProfiniteSectionsFiniteQuotient`, with its full signature verbatim.
The hypotheses are commutative topological A,T, their topological-ring structures,
an A-algebra structure on T, and continuous scalar multiplication. The conclusion
is an internal module on the coherent profinite site. The real definition
restricts the regular continuous-T module along continuous postcomposition by
algebraMap A T, so its sections, restrictions and action are exactly the
pointwise construction in the node. ContinuousSMul is equivalent here to the
continuity of that unital scalar map. LeanSearch, LeanFinder, Mathlib grep,
project/DAG grep and blueprint search found the existing project constructor
but no definition node owning it. Mathlib ContinuousMap.module' is sectionwise,
and CondensedMod uses ordinary coefficients; neither replaces this internal
module constructor. Empty test spaces and zero coefficient rings remain allowed.

The new nodes use the item's chapter/unit and blueprint ancestor
`det-prop-scalar-six-direct-image`, via this item. Their dependencies cite the
existing coefficient, condensed ring, module object and postcomposition nodes.
No imported theorem conclusion is required to define either constructor.
