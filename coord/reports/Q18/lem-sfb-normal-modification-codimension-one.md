## Worker report

Item: `lem-sfb-normal-modification-codimension-one` (Q18, stage 2).

The module `Sheaf.AlgebraicGeometry.NormalModificationCodimensionOne` states
`AlgebraicGeometry.normal_modification_isomorphism_open_contains`, with precisely one
`sorry` and no definitions or auxiliary theorems. Its docstring gives all eight steps
of the node's proof and names their dependency nodes. The node copy changes only `lean`;
the statement, statement dependencies and proof dependencies are unchanged.

### Source and hypothesis-by-hypothesis correspondence

I read the node's statement, source, complete eight-step proof and every statement
dependency record. I opened Stacks `varieties.tex`, label
`lemma-modification-normal-iso-over-codimension-1`, Tag 0BFP, lines 3297--3377, including
all four clauses and the proof of the quasi-finite-point case. The node agrees with it.

- The schemes and map are `{X Y : Scheme.{u}}` and `(f : Y ⟶ X)`, with the same single
  arbitrary scheme universe and no integral, irreducible, nonempty, separated-target or
  field-base hypotheses.
- Noetherianness of X is exactly `[IsLocallyNoetherian X] [CompactSpace X]`. Mathlib's
  `AlgebraicGeometry.IsNoetherian` has precisely these two parents. Compactness here means
  every open cover has a finite subcover; no Hausdorff assumption is present.
- Properness is `[IsProper f]`; reducedness of the source is `[IsReduced Y]`.
- The generic points of the components of a scheme Z are rendered literally as
  `{η : Z | ∃ C ∈ irreducibleComponents Z, IsGenericPoint η C}`. `hgeneric` uses
  `Set.BijOn f` between those source and target sets. This includes both mapping generic
  points to generic points and bijectivity on those sets.
- `hstalk` states `IsIso (f.stalkMap η)` at each source component generic point. The
  actual stalk map has source `X.presheaf.stalk (f η)` and target `Y.presheaf.stalk η`.
  This is an isomorphism of the specified local rings, rather than an unrelated abstract
  ring isomorphism, a residue-field-only condition or an arbitrary dense-open assumption.
- `(U : X.Opens)` and `hU : IsGreatest {V : X.Opens | IsIso (f ∣_ V)} U` express the
  maximal isomorphism open. `IsGreatest` includes that U is an isomorphism open and that
  every other such open is contained in U. The Mathlib construction `morphismRestrict f V`
  restricts the source to the full inverse image of V and the target to V; it is not a
  restriction to an arbitrarily chosen source open. No chosen canonical U construction
  is needed because, exactly as in the node, U is an input with its defining property.

### Clause-by-clause correspondence

1. Every codimension-zero point: the first conjunct is
   `∀ x : X, ringKrullDim (X.presheaf.stalk x) = 0 → x ∈ U`.
2. Every codimension-one DVR point: the second conjunct quantifies over x and its
   `IsDomain (X.presheaf.stalk x)` instance, then assumes local Krull dimension one and
   `IsDiscreteValuationRing (X.presheaf.stalk x)`, and concludes membership in U. Mathlib's
   DVR class takes the domain structure as an instance parameter, so this binder supplies
   part of the DVR hypothesis itself. It is scoped to this clause and imposes no domain
   hypothesis on the target scheme or on the other three clauses. The DVR class extends
   local ring and principal ideal ring and requires its maximal ideal to be nonzero.
3. Every normal-local-ring point with finite underlying fibre: the third conjunct uses
   `IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)` and
   `(f ⁻¹' {x}).Finite`, and concludes `x ∈ U`. The fibre is the set-theoretic fibre,
   exactly as specified, not a finite scheme morphism or a scheme-length condition.
4. Every normal-local-ring point with a quasi-finite point over it: the fourth conjunct
   uses the same local normality condition and
   `∃ y : Y, f y = x ∧ f.IsQuasiFiniteAtPoint y`, and concludes `x ∈ U`.
   The pointwise predicate is the dependency's Stacks definition, including its local
   finite-type condition; no global quasi-finiteness assumption was substituted.

For (3) and (4), a normal local ring in the node's prime-localization sense is exactly
an integrally closed domain: localization at the maximal ideal is the local ring
itself, and localizations of an integrally closed domain remain integrally closed
domains. This is also the convention used by the existing finite-birational-normal
and proper-birational-normal-curve statements. All normality assumptions remain local
at the point x, not on an entire neighbourhood or on all of X.

### Statement dependency declarations used

I read the recorded declarations, signatures and docstrings in the following modules.
Their recorded modules are imported publicly, with inherited foundational declarations
reused rather than copied.

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; paired with the existing `CompactSpace` class.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`. Its universally closed parent supplies quasi-compactness,
  so its locally-finite-type formulation agrees with the node's finite-type formulation.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced`, with the existing reduced-stalk equivalence.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`, defined by
  `closure {η} = C`; `irreducibleComponents` is the existing topological notion.
- `def-weil-locally-ringed-space-morphism`:
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`,
  `AlgebraicGeometry.LocallyRingedSpace.Hom`. Scheme morphisms inherit this interface;
  their `Scheme.Hom.stalkMap` is the actual induced local ring map, read in Scheme.lean.
- `def-sc-discrete-valuation-ring` (Mathlib leaf, no lean record required):
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, `IsDiscreteValuationRing`.
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed`, together with `IsDomain`, in the recorded normal-domain form
  appropriate to a local ring, as explained above.
- `pqf-def-quasifinite`: `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`,
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint`. I read its full affine-open,
  finite-type, quasi-finite-at-prime definition and reused it without modification.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`, with values in `WithBot ℕ∞`, retaining dimensions -infinity and infinity.

The already stated proof dependencies are imported privately from their recorded modules
or their Mathlib-match files: ProperBasic, Noetherian, QuasiCompact, SpreadingOut,
QuasiFiniteAtPrimePrincipalLocalization, QuasiFiniteAtFiniteSubalgebraAway, FunctionField,
AffineScheme, IntegralClosure.Algebra.Basic, Stalk, Morphisms.Separated,
Morphisms.ClosedImmersion, Morphisms.ProperQuasiFinite, DiscreteValuationRing.Basic,
PrincipalIdealDomain, Polynomial.RationalRoot, QuasiFiniteAtPointIsolated, Fiber,
ZariskisMainTheorem, Morphisms.Proper, Morphisms.UniversallyClosed and Morphisms.QuasiFinite.
Public imports already supply several of these modules, and Fiber is supplied by the
public QuasiFiniteMorphism import. The two as-yet unstated proof-only nodes,
`lem-sfb-birational-isomorphism-dense-open` and
`lem-sfb-generically-finite-quasifinite-over-dimension-one`, have no usable declaration
or module in the current node records, so there is no module to import for them yet.
They are named in the proof docstring and remain proof dependencies unchanged. They are
not prerequisites for typing this statement; no import cycle or extra theorem was added.

### Edge cases checked

- Empty X and Y: component-generic sets are empty; all four pointwise conclusions are
  vacuous. No Nonempty or integral-scheme hypothesis excludes them.
- Disconnected or reducible Noetherian schemes: `Set.BijOn` on component-generics retains
  every component. No single chosen generic point or function field is used.
- Identity maps on reduced Noetherian schemes: U is the whole target; all clauses hold.
  These examples also show that none of the geometric hypotheses is a dummy True binder.
- Nonreduced target: no `IsReduced X` assumption was added. Birationality still uses
  generic local rings, not just residue fields, so it cannot ignore generic nilpotents.
- DVR: the nonfield condition is retained; fields belong to the codimension-zero clause
  rather than being silently counted as DVRs. The domain binder is restricted to (2).
- Normalization of a cusp: its singular nonnormal point is excluded by the local
  normality hypotheses of (3) and (4), as required.
- Blowup of a regular surface at a closed point: the exceptional centre has local
  dimension two and infinite fibre, with no quasi-finite point above it. No clause
  incorrectly forces an isomorphism there. Generic and codimension-one points are covered.
- Finite empty fibre: the formula for (3) does not strengthen 'finite' to 'finite nonempty'.
  Proper birationality supplies surjectivity in the proof; no extra assumption is needed.
- Arbitrary scheme universe u is retained, with every variable explicitly bound. No
  auxiliary coefficient, index-universe, finiteness or characteristic condition is added.

### Searches for existing declarations

The following searches ran through the prescribed msearch.py wrapper for Q18 and this
item. They are retained in the wrapper's search log.

- LeanFinder: "A proper birational morphism with reduced source to a Noetherian scheme
  is an isomorphism near codimension one points with discrete valuation local rings,
  and normal points with finite fibre". Eight results, including normalization-map
  properties and IsIntegral; none states the four-clause result.
- Loogle: `AlgebraicGeometry.IsProper, IsDiscreteValuationRing`: zero hits.
- Mathlib grep: `birational|isoLocus|isomorphismLocus`, subdirectory AlgebraicGeometry.
  Eight displayed hits in the birational/rational-map files; none is this theorem.
- LeanSearch: "proper birational morphism reduced scheme isomorphism near normal point
  finite fibre". Eight results about finite morphisms, properness and finite fibres;
  none includes the birational normal-point isomorphism conclusion.
- Direct rg of `lean/WeilConjectures/AlgebraicGeometry` for
  `birational|normal_modification|modification_normal|isomorphismLocus|isoLocus|0BFP`,
  and of `lean/WeilConjectures` for this node id: no matching theorem. Nearby results
  concern normal dense-open sections or generic fibre models.
- Direct rg of Mathlib and `lean/Sheaf/AlgebraicGeometry` for birational notions,
  generic-component signatures and isomorphism loci found
  `FiniteBirationalNormalIso`, `ProperBirationalNormalCurveIso`,
  `BirationalQuasiModification` and `ProperPairRadicialPreparation`. I read their
  relevant declarations. The first two require integral schemes (and respectively
  finiteness or curve hypotheses); the third is a different specialized notion and
  the fourth states a preparation theorem. None renders the current four-clause node.
  Mathlib `Scheme.Birational` means existence of a partial isomorphism between schemes,
  not this specified morphism's bijection on component-generics and stalk isomorphisms.
  Therefore I kept the node's explicit hypothesis rather than substituting that notion.

### Validation and previous dispatcher failure

The sandbox contained no report, node or Lean module at the start of this attempt,
only dispatcher markers. The current DAG has Q03's accepted stage-1 split and no `lean`
record for this node. A stage-1 review therefore does not complete this stage-2 task.
I wrote the actual theorem, with no alteration to that accepted split.

The prescribed scompile.py server wrapper compiled the module both as a sandbox and
at its final library module name, initially in 6.1 and 5.2 seconds respectively, with
no errors or non-sorry warnings. Every Lean line is at most 100 characters. The node's
lean.statement is extracted verbatim from the theorem keyword up to (excluding) `:=`, as required by preflight.
The final wrapper compile and delivery preflight are run on this completed packet.
No proofs, hollow definitions, statement corrections, new nodes, dependency modules,
or statement disputes are present. Only the authorized sandbox is written; no direct
Git command, live source edit, global build, or launcher-tool modification is used.

The first dry run found only a signature-record delimiter mismatch: the node included the
`:=` token, while preflight compares the signature preceding it. I removed that token from
lean.statement. No Lean source or mathematical statement changed.

## Second reading by Q18

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
