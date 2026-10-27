## Worker report

The module Sheaf.AlgebraicGeometry.AdjunctionCotangentDeterminantNormalization states
AlgebraicGeometry.exists_adjunctionCotangentDeterminantNormalization with one `sorry`.
It defines the actual two-term model, a bridge to the dependency's specified global lci
identification, the local determinant comparison, and the full normalization conclusion.
These helpers belong to this node's canonical comparison and are all listed in
lean.declarations. Their data contain no `sorry`, no arbitrary-map parameter replacing
an intrinsic comparison, and no choice from a bare existence theorem.

Hypotheses, one by one:

- Schemes W and S and their morphism p are `{X S : Scheme.{u}} (p : X ⟶ S)`.
  The scheme universe u and derived-category universe w are explicitly bound.
- The Noetherian base is `[IsNoetherian S]`. This is Mathlib's globally Noetherian
  scheme condition, not merely locally Noetherian: it includes quasi-compactness,
  equivalently the finite affine cover in the node.
- Flatness is `[Flat p]`; finite presentation is the three separate assumptions
  `[LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]`.
- The nonnegative relative dimension is `(d : ℕ)`. The exact dependency predicate
  `HasPureFlatLCIGeometricFibres p d` expresses the dimension of every irreducible
  component of the algebraic-closure geometric fibre, excluding empty components.
- The regular polynomial factorizations covering W are `hlci`: every x belongs to
  an open U with a `FlatLCIPresentation p d U`. That existing structure contains
  the ambient open immersion into A^n_S, closed immersion, factorization, c regular
  equations locally at every source point, and `rank_eq : n = c + d`.
- The adjunction line K and its specified comparisons are the existing
  `FlatLCIAdjunctionSystem p d` with its existing `IsNormalized` predicate. This
  includes the determinant sign repaired in the current dependency; no copy of
  the old unsigned predicate is used. Its line at `FlatLCIBaseChange.identity p`
  is the original line; its other lines are the dependency's base-changed lines.
- The intrinsic cotangent object and specified lci identifications are exactly the
  dependency's `CotangentPresentation.System A` (datum D), `AffineIdentifications D` (datum F),
  `Naive.Comparison κ`, `LciIdentifications E`, and `Properties D F κ E`.
  These are the supplied representation data for the objects named by the node,
  not additional smoothness, separatedness, Tor-independence or geometric hypotheses.
  The Coherence and Naive.Comparison data have existing definition nodes, now cited.
- The derived-category instance families only choose the ambient localizations.
  No equality between u and w is assumed. Ring module localizations retain the
  dependency's u+1 convention. No site or coefficient universe is collapsed.

Conclusions, clause by clause:

- `T : TwoTermPerfectDeterminantData` is now an input, universally quantified, with
  `hT : T.IsCanonical`. It retains the dependency's functor, evaluation, zero and coherent
  pullback data. The added predicate fixes its exterior-model transitions by the signed
  exact-cone formula and fixes pullback by the K-flat counit and pure-wedge formula.
  `perfect B` places the actual cotangent object in that functor's domain.
- `FlatLCIPresentation.determinantModel` has the actual terms C.conormal and
  C.differentials, the actual ranks c and n, and the conormal differential.
  Its line is definitionally C.line, including the dual-first tensor order.
- `FlatLCICotangentChart` supplies the same geometric presentation to E: dimension
  and ambient are pinned to C, and its chain comparison is fixed in degrees -1
  and 0 by the dependency's negative/zero identifications and Mathlib's canonical
  doubleXIso components. Its differential satisfies the existing section formula
  C.IsConormalDifferential. None of these bridges are assumed as a hypothesis of
  the main theorem: the theorem supplies them for every chart.
- `FlatLCICotangentChart.lambda` is a real composite of Q.mapIso of that chain
  isomorphism, the specified E.identification.iso, and the inverse of the actual
  canonical cotangent restriction comparison. It is not an independently chosen λ.
- `theta B` is K.line B ≅ det(L_B), in particular θ for the identity base change.
- `normalization` states exactly a_i followed by the restriction of θ equals the
  exterior-model identification followed by det(λ_i). The definition
  `determinantComparison` spells this out as modelIso inverse, functorial det(λ),
  and determinant pullback inverse. Thus its target is the ordinary restriction
  of det(L), exactly as in the natural-language node.
- `overlap` is a_j inverse after a_i = α_j inverse after α_i. Both presentations
  are on an arbitrary common open U; restricting presentations from two original
  charts to their overlap gives this formula, with no affineness assumption on U.
  Functoriality of det identifies its right side with det(λ_j inverse λ_i).
- `square` supplies the canonical ring-sheaf BaseSquare for EVERY Cartesian
  geometric square. Therefore subsequent quantification over BaseSquare is not
  vacuous. Its inherited square and unit equations pin the structure-ring map.
- `change` supplies an isomorphism on the actual derived pullback of the actual
  cotangent complex, and `change_hom` pins its forward map to D.derivedChange q.
- `baseChange` is the exact square: pull back θ_B, apply determinant pullback,
  then det of the intrinsic cotangent base change, equals the specified adjunction
  base change followed by θ_B'. The square is given for every Cartesian base change
  between base changes, so it includes identity and successive changes. The dependency's
  identity and composition comparisons are the ones used in this equation.
- B and B' have arbitrary scheme bases: no IsNoetherian binder is imposed on them.
  In particular the local normalization applies to the pulled-back regular models
  over a non-Noetherian new base. No map from differentials to K is introduced.

Dependencies used:

- Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction:
  FlatLCIPresentation (and conormal, differentials, line, IsConormalDifferential),
  FlatLCIBaseChange, FlatLCIAdjunctionSystem (and IsNormalized),
  HasPureFlatLCIGeometricFibres. The source, full signatures and normalization
  docstrings were read, including the corrected sign in IsFlatLCIDeterminantComparison.
- Sheaf.AlgebraicGeometry.LciCotangentPresentation:
  CotangentPresentation.System, AffineIdentifications, LciIdentifications,
  LciPresentation, BaseSquare, cotangent, derivedChange, Properties and the specified
  identification's model and iso. Read the full signatures and docstrings, including
  the warning that affine equality does not imply equality of global derived maps.
- Sheaf.TraceFormula.TwoTermPerfectDeterminant and its public data module:
  TwoTermDeterminantModel, its complex/line, TwoTermPerfectDeterminantData,
  isTwoTermPerfect, twoTermDeterminantValue, twoTermDeterminantIso. The model and
  pullback components use the shared derivedPullback and ordinary tensorPullback.
- The three added stmt_deps are existing definition nodes:
  def-trf-two-term-determinant-data, def-trf-cotangent-resolution-data,
  def-trf-naive-cotangent-comparison-data. Their recorded modules and declarations
  are imported publicly. No independent new definition node is needed.
- Mathlib: IsNoetherianRing, Flat, LocallyOfFinitePresentation, QuasiCompact,
  QuasiSeparated, IsClosedImmersion, RingTheory.Sequence.IsRegular,
  topologicalKrullDim and Limits.pullback are the existing notions in the nine
  remaining original dependency nodes. Their records and source signatures/docstrings
  were read. The geometric fibre and rank assumptions are the existing specialization
  from the adjunction dependency, not a new private definition.
- Every currently recorded proof dependency with a module is imported privately,
  except the three principal dependencies and the naive data already imported publicly.
  Retired Sheaf twins are avoided in favor of the recorded WeilConjectures modules.

Edge cases checked before writing: d=0, c=0 and n=0 are allowed; no positive-rank
assumption or nonempty scheme binder occurs. Empty charts impose no nonexistent regular
sequence at a point. Identity base change is explicitly present in FlatLCIBaseChange;
BaseSquare existence and canonical ring-map normalization are retained. The affine-base
calculation is not made a global separatedness hypothesis. Every arbitrary new base is
allowed. The acyclic [E --id--> E] orientation uses the repaired dual-first evaluation
sign rather than the obsolete negative version. General rings and noninvertible ambient
lifts of frame matrices are allowed. There is no unproved assertion about differentials
mapping into K.

Searches made: msearch.py LeanFinder for the full canonical adjunction/cotangent
normalization returned standard-smooth cotangent formulas, localization comparison and
naive differential maps, none the desired derived/sheaf comparison. Loogle on
TwoTermPerfectDeterminantData, FlatLCIAdjunctionSystem reported an unknown Mathlib
identifier and no hits; it is not evidence that project declarations are absent.
Mathlib grep `cotangent.*determinant|adjunction.*determinant` returned zero hits.
Additional LeanSearch and LeanFinder queries for regular-presentation adjunction data
and intrinsic scheme-cotangent comparison data returned standard-etale/standard-smooth
presentations and algebraic cotangent maps. These are not this statement. Exact-name
Mathlib grep returned zero hits. Searches of lean/WeilConjectures for the item id found
no attachment. Searches of lean/WeilConjectures and lean/Sheaf for FlatLCIPresentation,
FlatLCIAdjunctionSystem, CotangentPresentation and LciIdentifications found exactly the
recorded dependency modules. They are reused. Blueprint searches for `flat lci adjunction`
and `cotangent comparison` found no matching blueprint node; the inherited synthetic
ancestry remains unchanged. Actual search records are retained by the prescribed wrapper.

Source read: duality.tex Tags 0B6V and 0BQZ; dualizing.tex Tag 0BZJ with its combined
polynomial-coordinate refinement; perfect.tex Tags 0FJX and 0FJY. These support the local
formulas and gluing route. The full normalized comparison is agent-formulated, as the
node's existing source field already explains. No statement fault or dispute was found.

## Repair of the returned delivery

The returned head 92de00459ac was a stage-1 proposal, not a Lean statement packet. The
retained sandbox had the same six-node split and no Lean file. That material and its
report are preserved under working-records/returned-stage1, outside the delivery packet.
The current assignment is explicitly stage 2, and the current main DAG has the accepted
Q02 split with no Lean record. I restored that current node in the sandbox before adding
its Lean record. The accepted statement, nine proof steps, proof_deps and all other node
fields stay byte-for-byte equivalent as JSON values. Only lean and three additional
already landed definition dependencies change. The old five unsplit statement proposals
are not submitted as stage-2 new definition nodes and do not replace the current split.

I re-read every original statement dependency on current main. In particular the
adjunction dependency now records Q33's sign repair copied from Q131, the cotangent
presentation records Q41's specified global family, and the determinant data are now
owned by def-trf-two-term-determinant-data. The current proof imports also follow the
upstream moves of regular-sequence/Koszul/conormal declarations. Thus this is substantive
stage-2 work on the rebased accepted input, not an unchanged re-push of the rejected split.
The wrappers build the actual delivery commit on current origin/sheaf-dag; no direct
git command or write in the read-only shared repository was used.


## Repair of H3 at immutable head d60bba2950e8

The saved packet was inspected first and its initial dry run passed at 8ddaaf7b70b.
A mathematical self-check still reproduced the returned defect: the theorem concluded
`∃ T`, and `modelIso` had only an acyclic constraint. That mechanical success did not
repair H3. The saved packet and current-main item differ only in lean and the three
landed definition stmt_deps. The accepted natural-language statement and its nine proof
steps have been retained. No direct Git commands or edits of the shared repository were
used; the required wrappers rebase each delivery onto the current server branch.

The repair adds the predicate `TwoTermPerfectDeterminantData.IsCanonical` in the §1(B)
dependency module. Its `model` field quantifies over every scheme X, every two displayed
models P,Q, every chain map q, and every derived isomorphism e whose hom is Q.map q.
For every equality of their Euler ranks, it requires
`IsFlatLCIDeterminantComparison` for the composite
`(T.modelIso P).symm ≪≫ det(e) ≪≫ T.modelIso Q`.
The maps in degrees -1 and 0 are the actual chain-map components, transported through
Mathlib's specified doubleXIso components. Thus changes of frames, insertion/deletion
of contractible complexes, kernel-first contraction and good-diagram composites have
the fixed signed exact-cone formula. This constrains comparison maps independently of
any K, theta, or conormal chart.

Its `pullback` field quantifies over every scheme morphism g and every displayed
termwise pullback identification q. The derived e is required to equal the original
K-flat counit followed by Q.map q, not an arbitrary map. When its two term maps are
isomorphisms, the composite of pullback(modelIso inverse), pullbackIso, det(e), and
modelIso is required to satisfy `IsFlatLCIPullbackDeterminantComparison` for those same
term maps. Hence it sends the pulled-back dual basis wedge tensor basis wedge to the
corresponding target orientation. The original datum already supplies naturality for
all derived isomorphisms and compatibility with identity/composition of pullbacks;
this additional representative condition ties those maps to the exterior models.
It includes open restrictions and arbitrary nonflat/non-Noetherian base changes.

The item's theorem now binds `(T : TwoTermPerfectDeterminantData) (hT : T.IsCanonical)`
and concludes Nonempty of the same normalization structure. In particular neither T
nor its modelIso/pullbackIso may be chosen after theta in order to force its equations.
For this fixed canonical T, `determinantComparison` still spells out the exterior-model
identification, det(lambda), and determinant pullback inverse. Its overlap equation is
therefore the desired equality of the specified adjunction transitions with intrinsic
determinant transitions. Every other geometric, cotangent, rank and universe binder
is unchanged, including the universal D/F/kappa/E/K data checked in the return.

Additional edge checks: the cone sign is the existing repaired
`(-1)^(a*(b+1))`; deletion and insertion of [E --id--> E] give dual-first evaluation.
The identity chain map gives identity on exterior orientations. The rank-zero empty
wedges are included, and the zero ring and empty scheme introduce no positivity
assumption. Exact cones of chain quasi-isomorphisms are locally split exact, so their
basis/lift equations detect the map even over rings with zero divisors. On a basis
open, the pure-wedge pullback formula tests an actual generating section, so it is not
a vacuous compatibility condition. No equality between u and w has been imposed.

Additional searches on this repair: LeanFinder for "Canonical determinant comparison
of two-term perfect complexes normalized by the exact cone determinant and compatible
with pullback of exterior-power generators" returned alternating complex isomorphisms,
ordinary determinant associatedness, exterior-power pairing and derived SES triangles;
none supplies the required comparison. LeanSearch for "A determinant functor on perfect
two-term complexes with canonical exterior-power comparisons and pullback compatible
with the exact cone formula" returned exteriorPower.functor, ordinary determinants and
matrix determinant formulas, not this interface. Mathlib grep for
`IsFlatLCIDeterminantComparison|TwoTermPerfectDeterminantData|canonicalTwoTermPerfectDeterminant`
returned zero hits. Project rg found only the existing generic cone/pure-wedge predicates
and a completed-conormal consumer, not an IsCanonical predicate for these data. Those
predicates and the original determinant data were reused, not copied. No new definition
node is introduced: all helpers refine the determinant node's own canonical comparison.
The local sources Perfect Complexes 0FJX/0FJY and More on Algebra's determinant good-diagram
construction were read again, alongside all four recorded proof dependency interfaces.

## Dependency modules

`lem-trf-two-term-perfect-determinant`: the old recorded theorem gives the Tor-window
equivalence and existence of an unconstrained determinant datum; its modelIso is only
constrained on identity complexes, so it fails to express the node's canonical exterior
model comparisons. The module Sheaf.TraceFormula.CanonicalTwoTermPerfectDeterminant
publicly reuses those original data and defines their IsCanonical predicate by the
shared exact-cone and pure-wedge predicates. Its theorem
`exists_canonicalTwoTermPerfectDeterminantData` states the original full Tor-window
equivalence and existence of a datum satisfying this predicate, with a four-step source
proof docstring and sorry proof. Only this dependency node's lean field changes. The
algebraic predicates live in FlatLCICanonicalAdjunction, which is imported for those
definitions, not for any adjunction construction or theorem; the existence statement
and predicate mention no K or adjunction data. The consumer compiles against this new
interface, providing the requested consumer validation. There are two named theorems
with sorry in the packet, one for each delivered DAG node, and no sorry in any definition.

## Second reading by Q116

A separate self-review pass compared the two modules with both node statements and the
return. No additional agent was started, as the dispatcher forbids it; the maintainer's
independent review remains external to this pass. The only returned defect was H3,
and the check found and removed the existential choice of T, added an independent
canonicity condition for every chain quasi-isomorphism and every termwise pullback,
and supplied the matching canonical existence statement as a lean-only dependency
repair. The exact-cone condition uses the actual degree maps and the derived q; the
pullback condition uses the actual tensor term maps and K-flat counit. The two clauses
mention no theta or K, so they cannot merely assume the consumer's conclusion.

Hypothesis and clause check: the original Noetherian/flat/finite-presentation/pure-fibre
and regular-chart binders are identical to the saved packet and adjunction node;
D/F/kappa/E with Properties and K with IsNormalized stay universally quantified.
The only added representation hypothesis is canonicity for the universally fixed T,
now furnished by the repaired determinant node. The perfectness, chart, theta,
normalization, overlap, square, change_hom and arbitrary-base-change clauses are
unchanged. All nine source proof steps remain in the consumer docstring. The dependency
keeps the full perfect/Tor equivalence, invertibility, core functor laws, evaluation,
zero and natural identity/composition-compatible pullback data via the original record,
and adds exactly their missing canonical model interpretation. This repairs an unusable
record, not the natural-language statement; no statement_change is needed.
