## Worker report

The module `Sheaf.SixFunctors.FiniteExceptional` states
`WeilConjectures.FiniteExceptional.finite_exceptional`. It uses the actual intrinsic
small-pro-etale derived categories and the specified transported etale exceptional
functor. The item statement, proof, statement dependencies and proof dependencies
are unchanged. The resolved stage-1 repair note was read: its fourteen-step
Verdier/ordinary-adjunction/absolute-trace route is retained in the theorem docstring;
no ambient exceptional adjunction or six-functor axiom package is assumed.

### Hypotheses and clauses

* The global algebraic closure of a finite field is `D : FiniteFieldDatum.{u}`.
  The coefficient prime is `(l : ℕ) [Fact l.Prime]`, with `hl : l ≠ D.p`.
  The finite extension is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The quotient is the existing
  `Padic.coefficientExtensionRing l E (n + 1)`, using its recorded valuation ideal.
  Natural-number index `n` denotes positive exponent `n+1`; hence every allowed
  positive exponent is covered, without adding a level-zero coefficient ring.
* `X Y : Scheme.{u}`, their `Over (Spec (.of D.k))` structures,
  `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` on their structure maps
  render exactly the two separated finite-type k-schemes. `f : X ⟶ Y`,
  `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, and `QuasiCompact f`
  render the separated finite-type k-morphism. All these binders are retained in
  `operations_preserve` and consequently in the restrictions and main theorem.
* `c : Compactification f` keeps the actual construction of compact support
  explicit, as required by its dependency definition. It is arbitrary; no extra
  existence hypothesis is imposed. Nagata supplies one on the stated domain.
* `domain` abbreviates the existing `finiteTorConstructible`, the conjunction of
  intrinsic bounded constructibility and finite pro-etale Tor amplitude.
  Its `FullSubcategory` is precisely C_(T,n+1), with all its morphisms retained.
* `F` is the restriction of `sfIntrinsicCompactSupport c`, namely proper derived
  image after exact extension by zero; `G` is the restriction of the published
  `ProEtale.sfFiniteExceptional` for the identical c and coefficient quotient.
  `operations_preserve` asserts the two needed domain checks, not additional
  assumptions about the input morphism.
* `dual` is the contravariant `finiteIntrinsicDerivedInternalHom` with second
  argument `integralDualizingFiniteTerm`. That term is the recorded structural
  exceptional image of the regular coefficient unit. `H` is the covariant
  composite D_X f* D_Y, using `rightOp` and `op` for its two contravariances.
  `dualFormulaIso` is a specified natural isomorphism between G and this ambient
  composite after the full inclusions. `dualFormula_existsUnique` fixes it by
  `FormulaNormalized`, the trace/evaluation transpose equation. Clause 1 asserts
  that equation for this specified comparison.
* `reduction` is the actual `pbcDerivedExtend` along
  `PurCompactSupport.finiteQuotientChange.map`, with the inequality translated
  from n≤m to n+1≤m+1. `reduction_preserves` checks the target domain; `Q` is
  its full restriction. This does not assume that a quotient ring map is flat.
* `supportMap` is exactly the existing canonical compact-support coefficient
  comparison, conjugated by `finiteImageIso` to the intrinsic realization.
  `qMap` lifts that transformation through the fully faithful full inclusion.
  `qMap_isIso` certifies this already specified map. `q` uses its inverse,
  with direction Q_Y F_m → F_n Q_X as in the node.
* The constructible adjunction is fixed by `AdjunctionNormalized`, which compares
  its Hom equivalence with `specifiedExceptionalHomEquiv` on every bounded
  etale-origin representative. `fixedExceptionalIso` uses uniqueness of the
  ordinary etale right adjoint at the same c; `fixedHom` transports that specific
  Hom chain. `adjunction_existsUnique` determines the adjunction uniquely, and
  `adjunction` selects only that uniquely normalized object. This is not a
  choice of arbitrary adjunction from a bare nonempty type.
* `b` is defined as `mateEquiv` of inverse q under those adjunctions. Its map is
  fixed before invertibility is asserted. The second conjunct is `IsIso b`.
  Both endpoints are the stated finite-Tor full subcategories, so it gives the
  requested canonical natural coefficient isomorphism.
* The third conjunct is the quotient cocycle, with all endpoint identifications
  displayed: first `Q_X.map b_(m,n)`, then b_(n,t) on `Q_Y L`, then G_t of the
  Y associator, equals the X associator followed by b_(m,t). `reassoc` is the
  recorded actual derived tensor associator lifted through the full inclusion.
* The fourth conjunct gives b_(r,r) as the identity after the multiplication-unit
  isomorphisms `selfReduction` at both endpoints. `quotient_comp` and
  `quotient_id` state the actual quotient-ring-sheaf equalities needed to use
  the published tensor composition/identity maps.
* The fifth conjunct is the displayed unit equation, in Lean's left-to-right
  composition order: Q_X(eta_m), b at F_m K, then G_n(q_K) equals eta_n.
  The sixth is exactly the counit equation: q at G_m L, F_n(b_L), then epsilon_n
  equals Q_Y(epsilon_m). No tower, reconstructed object or additional input
  datum appears in either identity.

### Dependency declarations

The statement dependency `def-fix-six-functor-datum` is imported from
`Sheaf.Paper.SixFunctorOperationDatum`. Only its global datum and named underlying
constructions are needed: the theorem establishes an operation property and does
not assume a six-functor package asserting that property already.
`def-weil-finite-torsion-constructibility` contributes
`AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible` from
`Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`.
`def-weil-finite-tor-amplitude` contributes the existing
`WeilConjectures.finiteTorConstructible` from `Sheaf.Paper.FiniteTorAmplitude`
without changing the dependency record (H13 repair below).
`def-weil-exceptional-inverse-image` is imported through
`Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: its recorded
`RingSystem.finiteRight` identifies exactly the same
`AlgebraicGeometry.ProEtale.sfFiniteExceptional` with the constructible right
functor. Its reexported `sfFiniteExceptionalAt` is used in the normalized Hom
chain; the original construction in `SfFiniteExceptionalInverseImage` supplies G.
`def-compact-support-direct-image-detailed` contributes
`AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport` from
`Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`.
`def-weil-derived-pullback-tensor-hom` contributes
`finiteDerivedPullback` and `finiteIntrinsicDerivedInternalHom` from
`Sheaf.Paper.DerivedPullbackTensorHom`, both among its recorded declarations.

The source of the dualizing term is `Sheaf.SixFunctors.FiniteDualizing`.
The support comparison, tensor composition and tensor identity are the existing
`PurCompactSupport` constructions reexported by the coefficient modules.
`Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom` gives the specified Hom
chain; `Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange` gives the canonical
intrinsic support realization comparison. The ordinary etale adjunction used
by `fixedExceptionalIso` is imported publicly from
`WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`.
All already stated proof dependencies are imported for stage 3, including
finite Verdier duality, ordinary direct image, bounded flat models, coefficient
reduction of flat models, Tor comparison, constructible etale origin, pullback
Tor amplitude, open finite Tor, finite Hom change, duality pairing, absolute
trace exchange, compact-support composition and its coefficient compatibility.
The Mathlib mate and natural-Hom-adjunction constructors are already reexported.
`fix-prop-projection-formula` has no usable recorded module; its construction is
already part of the imported ordinary coefficient/projection interfaces, and
no unrecorded replacement theorem is assumed in this statement.

### Edge cases and data discipline

The minimal exponent r=1 is index zero; equal indices and repeated indices in
the cocycle are explicitly included. The identity quotient is not silently
identified with an identity functor: `selfReduction` retains the unit maps.
Zero objects and empty schemes are not excluded. Empty chart families enter
only the proof's dimension-bound check and may use bound zero. No nonemptiness,
smoothness, properness of f, flatness of A_m→A_n, site-perfectness, or ambient
exceptional-admissibility condition has been added. The actual small sites keep
their object/morphism sizes; no equality of those universes is assumed.

Every definition contains real data assembled from the published constructions.
The data chosen from postponed theorems are the uniquely Hom-normalized
adjunction and the uniquely evaluation/trace-normalized dual formula. The postponed
named theorems are `finitePull_comp`, `dualFormula_existsUnique`, `reduction_preserves`,
`operations_preserve`, `quotient_comp`, `quotient_id`,
`adjunction_existsUnique`, `qMap_isIso`, and `finite_exceptional`; each has its
own source and proof docstring and is listed in this item's lean.declarations.
These helpers express domain checks and normalizations of this same node,
not independent new notions or renamed copies of existing operations.
No statement dispute or source correction was necessary.

### Searches and validation

Read the current main-20261015 statement and proof of
`sec-six-functors/sk-thm-sf-package/lem-coef-finite-exceptional`, the full item
node, its statement-dependency nodes and their recorded source declarations.
The node's expanded fourteen-step proof fixes the precise canonical maps.
LeanFinder query `exceptional inverse image Verdier duality coefficient reduction
finite Tor constructible adjunction` returned eight derived-category and Serre
quotient results, none this theorem. Mathlib grep `exceptional|Verdier` in
CategoryTheory found only unrelated triangulated/topological terminology.
Loogle `Adjunction, conjugateEquiv` had an unknown unqualified identifier;
the corrected query `CategoryTheory.mateEquiv, CategoryTheory.Adjunction`
returned the mate API, including `mateEquiv_counit`, `unit_mateEquiv` and pasting
lemmas. LeanSearch query `finite coefficient exceptional inverse image commutes
with coefficient quotient reduction Verdier duality` returned sheaf equivalence
and generic derived-functor results, no exceptional coefficient theorem.
Project/upstream rg searches for the item id, finite exceptional names,
exceptional coefficient comparison and Verdier formulas located the existing
etale-origin functor, its system interface and the ordinary etale tools; none
states the full intrinsic quotient/duality assertion here. The existing system
record alone does not state the first dual formula.

The repaired full module passed the prescribed scompile.py wrapper: sandbox
13.0 seconds, library import 11.9 seconds, no errors or warnings. The ordinary
pullback comparison needed explicit module-category universes, standard localization
instances and its existing additive instance. These were made explicit with the
original site and coefficient universes retained. Probe files stay in scratchpad
and are not delivered.

## Returned delivery repair

H3: the returned clause used `Nonempty` and did not specify the canonical formula.
The repaired module adds `FormulaNormalized`, `dualFormula_existsUnique`, and
`dualFormulaIso`. The normalized comparison is an actual natural isomorphism;
its uniqueness statement determines the data before the definition chooses them.
The first clause of `finite_exceptional` now asserts its normalization.

The equation is the finite analogue of the landed integral sibling's
`CoefDualFormulaScalarTranspose.FormulaNormalized`. For every normalized K-flat
`IntegralHom.TensorPresentation` on X, the compactification and Y, and its
`IntegralVerdier.SignedSymmetry`, the left side is canonical compact-support
projection, pullback presentation comparison, Koszul swap, tensor of the formula
component, internal-Hom evaluation, support realization, then the relative trace.
The right side is tensor of the specified exceptional counit followed by Y's
evaluation. `CoefDualFormulaScalarTranspose.finiteTrace` is reused directly: its
body is `finiteEtaleTrace`, the absolute structural counit transposed under
`finiteDualizingEtaleAdjunction` through `finiteSupportComposition`, followed by
the prescribed site/coefficient transports. Thus no relative exceptional formula
or arbitrary trace is assumed to define this normalization. The ordinary counit
is already fixed inside `PurCompactSupport.projectionMap`; `formulaPullIso` is
the termwise descent of its constant-section-normalized `finitePullbackIso`.
`finitePull_comp` is a named postponed coherence theorem for those same constant
ring maps. Each new theorem has a source and complete proof plan in its docstring
and is listed in the item's declarations; all theorem proofs remain `sorry`.

The finite trace helpers were found by `rg` of FormulaNormalized,
trace_existsUnique, absoluteTraceExchangeHomEquiv and dualFormulaIso in both Lean
roots. Reading the full scalar-transpose normalization and its finiteTrace body
identified the reusable trace construction. Reading DerivedPullbackTensorHom,
IntegralHomReduction, IntegralCompactSupportCoefficientData and its comparison
module identified the actual tensor, evaluation, projection and pullback maps.
No new notion node or duplicate definition of any operation was introduced.

H13: the sandbox dependency-node replacement has been removed from the packet.
The landed `def-weil-finite-tor-amplitude` node and its NW record on
`Sheaf.Paper.FiniteTorAmplitudeSites` / `finiteTorConstructibleEtale` are left
unchanged, including every recorded declaration. This module imports the original
`Sheaf.Paper.FiniteTorAmplitude` for its intrinsic finiteTorConstructible domain.
The item's lean.note explains this use. Neither presentation is rebound, and
none of the at least ten current etale consumers loses its interface.

## Second reading by NH

Self-check by the dispatched worker; no other agent was started. I reread the
main-20261015 blueprint statement and both proof paragraphs, the expanded node
proof steps 3--5, and the retained module. The coefficient prime inequality,
algebraic closure datum, E, separated finite-type X/Y/f hypotheses, arbitrary
compactification, and positive n+1 exponent binders are retained. G is still the
specified transported exceptional functor and H still D_X f* D_Y, on the intrinsic
small-site category. The clause-1 defect was repaired by a specified uniquely
normalized natural iso; its equation uses the actual evaluation, structural trace
and counit, and excludes scalar rescaling. The cited finite-adjunction-diagram
realization can use this equation directly rather than a bare existence witness.

I checked the types and order of each factor: projection starts at
F(G L) tensor D_Y L; pullback comparison and swap put f*D_Y L first, the formula
component replaces G L by Hom(f*D_Y L,omega_X), and evaluation and trace end in
omega_Y. The other side is the exceptional counit tensor identity, then evaluation.
The two sides have the same endpoints. Uncurrying and the trace-exchange Hom
bijection force the formula component, so the unique choice is permitted.
The redundant tensor identity on the right is simply the identity map and changes
no normalization. Zero objects, empty schemes, f=id, minimal exponent n=0 (r=1),
and equal/repeated coefficient indices remain included; Koszul symmetry is the
recorded representative symmetry, not an unsigned replacement.

Clause 2 remains IsIso of b defined by mateEquiv of q.inv; q was fixed before its
IsIso theorem. Clause 3 retains both quotient associators; clause 4 retains both
selfReduction units; clauses 5 and 6 retain the displayed adjunction unit and
counit equations, respectively. I compared their signatures with the saved packet:
only clause 1 changed. The H13 repair removes the dependency record edit altogether.
The item statement/proof/dependencies in JSON remain unchanged outside lean.
All variables and universes are explicitly bound, all definitions have real data,
and every theorem proof is sorry. The full module compiled cleanly in both wrapper
checks. No launcher scripts or read-only library sources were modified.
