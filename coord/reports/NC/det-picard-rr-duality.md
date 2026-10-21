## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.PicardRRDuality` states
`AlgebraicGeometry.Scheme.picard_rr_duality`, with one `sorry` and no proved theorem.
Its three helpers have actual data: the transported residue trace, the value of the
canonical base-change map on pure tensors, and the predicate expanding clause (4).
The source is the complete current blueprint detail
`literature/blueprint/main-20261015/blueprint/sec-picard-framework/sk-thm-picard-rr/sk-thm-picard-rr-duality.md`.
The theorem docstring contains all nine steps of the DAG's natural-language proof.
The returned dependency bookkeeping is repaired below; the mathematical statement,
proof plan, and all declaration signatures and bodies are unchanged.

Hypotheses and objects, individually:

- A field k: `(k : Type u) [Field k]`.
- A curve over k: `(C : Scheme.{u}) [C.Over (Spec (.of k))]`.
- Smooth projectivity and dimension one, integrality, separatedness and finite type:
  `[IsSmoothProjectiveCurve (C ↘ Spec (.of k))]`, the recorded upstream class.
  Smooth relative dimension one and properness are existing consequences, not added binders.
- Geometric connectedness: `[GeometricallyConnected (C ↘ Spec (.of k))]`.
  Neither algebraic closure, perfection of k, nor geometric integrality is assumed.
- The genus g is exactly the recorded `arithmeticGenus k C`, defined as dim H1(O).
  Its abelian-cohomology presentation is the recorded genus interface; the constructed
  common-resolution comparison identifies it with the module-derived cohomology here.
- Omega is exactly `(C ↘ Spec (.of k)).relativeDifferentials`, the dependency's definition.
- The invertible sheaf: `(L : C.Modules) [L.IsInvertible]`, using the scheme-level class.

Clauses, individually:

1. The first existential is a k-linear equivalence from
   `scalarCohomology f (dual L tensor omega) 0` to
   `Module.Dual k (scalarCohomology f L 1)`. Inverting it and using tensor symmetry
   gives the exact displayed isomorphism in the node. `MonoidalCategoryStruct.tensorObj`
   specifies `C.Modules` explicitly to avoid elaborating tensor notation in a bare
   sheaf-of-modules category. The equation `e b a = ...` identifies this equivalence
   with cup product, `evalTensor`, and the normalized residue trace. It is not an
   arbitrary linear isomorphism or merely a dimension equality.
2. The next three conjuncts state h0(omega)=g, h1(omega)=1, and deg(omega)=2g-2.
   The dimensions are `Module.finrank k (scalarCohomology f omega i)`.
   The integer degree is the recorded `Modules.degree`, not a new degree.
3. The strict integer inequality `2 * (arithmeticGenus k C : Z) - 2 < L.degree k`
   implies `Subsingleton (scalarCohomology f L 1)` and the integer equation for h0.
   This is actual vanishing of a vector space, rather than `IsZero` on a bare Type.
   Genus and h0 are cast before subtraction, so there is no natural-number truncation.
4. The last universal quantifies over `(K : Type u) [Field K] [Algebra k K]`, with
   the standard scheme/base-field universe convention. Its predicate explicitly gives:
   (a) `IsSmoothProjectiveCurve` of `C.baseChangeField k K` (as an existential proof,
   then installed only inside the predicate), and geometric connectedness;
   (b) equality of its recorded arithmetic genus with g;
   (c) equality of the tensor-pulled L's recorded degree with L.degree;
   (d) an isomorphism from tensor-pulled omega to relative differentials over K,
   specified on every `1 tensor da` by `relativeDifferentialsPullbackGenerator`;
   (e) K-linear cohomology equivalences in all natural degrees for line bundles,
   specified on EVERY pure tensor by the existing `H.baseChange` transported through
   the constructed module/Ext comparison and the section-normalized pullback adjunction;
   (f) the full pairing scalar-extension equation, with both scalars c and d.
   For (f), a section b of `L-dual tensor omega` is equivalently a sheaf morphism
   phi:L -> omega. Under this identification evaluation after cup is H1(phi).
   The equation uses the actual pulled morphism `(tensorPullback p).map phi` followed
   by the normalized differential isomorphism. Its left side is the residue trace of
   d times H1(phi_K) of the canonical image of c tensor a; its right side is
   `c * d * algebraMap k K (trace_C (H1(phi) a))`. Thus it is exactly the pure-tensor
   equation for the pairing, using the canonical dual/evaluation identification.
   Pure tensors span the cohomology by (e). A basis and its dual identify extension
   of the finite-dimensional dual with the dual after extension. Therefore this equation
   says precisely that the pairing-induced isomorphism, and its inverse in (1),
   extends by K. No arbitrary comparison, unconstrained map, or extra separability
   assumption appears. The isomorphism in (1) over C_K is the same universally stated
   theorem applied to the curve structure supplied by (a).

Dependency declarations used (full source signatures and docstrings were read):

- `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`:
  `AlgebraicGeometry.IsSmoothProjectiveCurve`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral` and `.Connected`:
  `AlgebraicGeometry.GeometricallyIntegral` and `.GeometricallyConnected`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`:
  `AlgebraicGeometry.Scheme.arithmeticGenus`, `.Modules.degree`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `.Modules.eulerChar` (via degree), `.Modules.finrankH` (via genus and degree).
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`; `.Modules.Dual`: `.dual`.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`, `.relativeDifferentialsDerivation`.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages` (the recorded
  `RingedSpace.moduleCohomology` right-derived interpretation).
- `Mathlib.LinearAlgebra.Dimension.Finrank`: `Module.finrank`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, with `Field` on both fields.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`:
  `AlgebraicGeometry.Scheme.Modules.moduleBaseChange`, i.e. tensor pullback along
  the fibre-product map; the used field specialization is the existing
  `Scheme.baseChangeField` with its second projection as structure map.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction`; upstream
  `.tensorPullback` and `.pullbackPushforwardAdjunction`. Left-adjoint uniqueness
  supplies the comparison preserving the sectionwise unit, without arbitrary choice.
- `Sheaf.AlgebraicGeometry.Curve.PicardDuality`:
  `AlgebraicGeometry.Scheme.picard_duality_one`, with normalized residue trace and
  the scalar module-cohomology pairing. This is a proof-only dependency and its
  module is imported without `public`.
- `WeilConjectures.AlgebraicGeometry.Curve.ResidueTrace`:
  `AlgebraicGeometry.Scheme.residueTrace`, with `functionFieldAlgebra` and
  `isFunctionFieldAlgebra_functionFieldAlgebra` fixing its scalar structure. The
  owning statement dependency is `def-pc-residue-trace-pairing`; the module is public.
- `WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`:
  `.Modules.scalarCohomology`, `.scalarCohomologyMap`, `.scalarCohomologyCup`.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality`:
  `.Modules.moduleCohomologyExtResolutionEquiv` (constructed common-resolution map),
  owned by `def-pc-module-cohomology-ext-resolution-equiv`; the module is public.
- `WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison`:
  `.Modules.H.baseChange`, `.baseChangeFst`, `.baseChangeSnd`, `.baseChangedScheme`.
- `Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap`:
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGenerator`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.CupProduct`:
  `.Modules.evalTensor`; its Hom/evaluation interpretation is used in clause (4).

The added statement dependencies already have landed declarations: scalar cohomology
operations, the canonical flat comparison, the differential generator, the definition
of the constructed module/Ext comparison, and the residue trace with its canonical
function-field scalar structure. They introduce no new hypotheses or definitions.
All available recorded proof-dependency modules are imported without `public` unless
already public statement dependencies. The unstated local Tate residue field-extension
lemma has no module to import. The parent `PicardRiemannRoch` module is deliberately
not imported: it is a broader statement with different conclusions and would make the
parent's future proof import cyclic. Its helpers do not state the present node on the
module-derived carriers, so those were not rebound as an exact existing match.

Edge cases checked:

- g=0: the canonical degree is -2 in Z; the bound is strict and includes degree -1.
- g=1: degree zero is excluded by the strict bound, so H1(O)=1 is not contradicted.
- L=O, or L=omega, is covered without positivity assumptions in (1), (2), (4).
- At deg(L)=2g-2 the vanishing implication has false premise and asserts no vanishing.
- Cohomology comparison includes q=0 and all q>1, including zero cohomology spaces.
- K=k and arbitrary inseparable or transcendental extensions are allowed. No finite,
  algebraic, separable or perfect-field assumption occurs. The pure-tensor formula also
  covers c=0 and d=0, and determines all tensors by linearity.
- The empty scheme is excluded by the integral dimension-one curve definition itself,
  not by an additional hypothesis. The zero module is not spuriously declared invertible.
- All binders and the universe u are explicit; `autoImplicit false` is enabled.
- No data is selected from a mere existence theorem. Existing adjunctions have their
  normalized universal property, and the cohomology comparisons are constructed maps.

Searches made before writing (all msearch calls use NC and det-picard-rr-duality):

- LeanFinder: 'Serre duality for smooth projective curves canonical degree 2g-2 high
  degree vanishing and compatibility with extension of ground field'. Eight hits on
  projective Weierstrass curves/points and base-change equivalence; no exact theorem.
- Loogle: `AlgebraicGeometry.Scheme, "duality"`: zero hits.
- LeanSearch: 'Serre duality canonical sheaf degree high degree line bundle vanishing
  cohomology smooth projective curve': eight hits, on Kaehler differentials of smooth
  relative dimension zero, H1 cotangent and ideal sheaf structure; no matching theorem.
- msearch grep: `serreDuality|picard.*duality|canonical.*genus`, Mathlib AlgebraicGeometry:
  zero hits.
- rg of project WeilConjectures and Sheaf for RR/duality/genus/base-change expressions:
  found `Curve.PicardDuality`, upstream RiemannRoch numerical results, and
  `PicardRiemannRoch`. Opened these; none is this exact four-clause theorem.
  `PicardRiemannRoch` is broader, uses abelian H, and omits h0/h1(omega) in its actual
  conclusions. It cannot be attached as an exact existing declaration for this node.
- rg of `det-picard-rr-duality` in WeilConjectures and Sheaf: no existing declaration
  tagged with this node. rg of every newly introduced full-name suffix in Mathlib,
  WeilConjectures, Sheaf and the upstream name index found no existing name.
- rg for scalar cohomology base change/trace and the common-resolution comparison
  found and reused the existing cohomology, trace and canonical comparison APIs;
  no existing transport on these module-derived scalar carriers was found.

Validation: prescribed scompile.py compiled both the sandbox module and its library
module path cleanly (10.2 seconds and 4.7 seconds, respectively). An initial missing
base-changed Over instance and tensor elaboration issue were repaired by explicit
choices of the existing structures, without changing any hypothesis or clause.

## Second reading by NC

This is the author's fresh reading, as this dispatcher assignment explicitly forbids
starting another agent; the maintainer supplies the independent review.
Opened the node and final module together and compared each binder and conjunct.
The first existential goes in the inverse orientation to the displayed duality;
its inverse and canonical tensor symmetry give exactly that display. The trace equation
pins the isomorphism and prevents an arbitrary equivalence from satisfying the statement.
Checked all three separate omega invariants, strict integer inequality and both high-degree
conclusions. Opened the field-extension predicate and the real-data helpers: it asserts
the base-changed curve properties, genus, degree, canonical differential isomorphism,
canonical cohomology comparisons, and the cd equation for the pairing on all morphisms
L -> omega. The latter is the Hom presentation of H0(L-dual tensor omega), using the
pulled map and evaluation rather than a second chosen dual comparison. It determines
the induced isomorphism after scalar extension. No clause is a mere Nonempty choice.
The unused Over proof inside the predicate is structure bookkeeping for `.degree K`,
not a new hypothesis. No mismatch with the node was found in this reading. The compile
repairs concern only explicit category and structure inference; the node statement and
proof remain unchanged.


## Returned delivery repair

The saved packet passed its initial prescribed dry run as commit `352a3a4bcf7`.
That mechanical pass did not resolve the return on immutable head `850e357f3fd5`.
The sandbox was compared with the current live node: only `lean` and `stmt_deps`
differ; all mathematical statement and proof fields agree.

1. Replaced `new-module-cohomology-ext-resolution-naturality` in `stmt_deps` by
   the landed Q12 definition node `def-pc-module-cohomology-ext-resolution-equiv`.
   Read its node and the existing definition's complete signature and docstring in
   `WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality`.
   Both trace transport and base-change transport apply that definition, not the
   coefficient-naturality theorem. None of the nine proof steps cites that theorem,
   so it was not added to `proof_deps`. The construction module is now an explicit
   public import. No comparison was redefined.
2. Added `def-pc-residue-trace-pairing` to `stmt_deps` and publicly imported
   `WeilConjectures.AlgebraicGeometry.Curve.ResidueTrace`. Read the node and the
   full source signatures and docstrings of `residueTrace`, `functionFieldAlgebra`,
   and `isFunctionFieldAlgebra_functionFieldAlgebra`. The first helper uses exactly
   these declarations. `sk-thm-picard-duality` remains in the base statement list:
   the repair dry run forbids dropping that pre-existing edge without a mathematical
   statement correction. Its declarations are not used by the statement, so its
   import is now proof-only; it remains in `proof_deps`, as used by steps 3, 4, and 8.
   The scalar operations
   module is imported publicly so the statement does not rely on PicardDuality's
   public exports.

Self-check after repair: reopened the node, imports, three helper bodies and final
signature. The four clauses and all edge cases listed above remain unchanged.
Clause (1) still pins the equivalence by trace after evaluation after cup product;
clause (4) still expresses the actual scalar-extension pairing on Hom(L, omega).
The repair changes neither presentation. No new node, dependency module, statement
correction, or new theorem was introduced. The supplied return explicitly directs
this dependency-list repair; no live source or DAG file was edited directly.

Validation of repair: scompile.py compiled the sandbox and library module names
cleanly, each in 5.6 seconds. The first repaired dry run rejected removal of the
base `sk-thm-picard-duality` edge: "without a statement correction the item's
stmt_deps may only gain new definition nodes; your copy drops
['sk-thm-picard-duality']". Restored that base edge, retaining both requested
repairs (the definition-owner substitution and added residue-trace node). This
requires no artificial change to the mathematical statement or proof fields.
