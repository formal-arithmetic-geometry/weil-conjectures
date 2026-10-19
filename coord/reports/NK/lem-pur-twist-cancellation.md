## Worker report

Repair of return L at immutable head 03e2c2053bd7 (H3/H5 and H8).
The initial saved-packet dry run passed at bcb6f9ba94. Reading the actual
normalizations against the return nevertheless reproduced the mathematical defects,
so this packet repairs the maps, rather than re-pushing that mechanically valid packet.
The saved returned source is retained only in scratchpad/Returned.lean, outside delivery.
The current shared node was compared without git; only lean and the explicitly allowed
additional landed stmt_deps differ.

The theorem is `AlgebraicGeometry.ProEtale.purity_twist_cancellation`, in
`Sheaf.Paper.PurityTwistCancellation`. It still has exactly one sorry. Its source is
blueprint main-20261015, sk-thm-regular.proof.md Step 2 and the displayed Phi formula
of pur9-rg-def-phi. The theorem's hypotheses and five conjuncts retain the previous
signature verbatim. No source-statement correction is needed.

Repair of H3/H5, signed contraction:

- `PurityCancellationFrame` gives bases of the actual intrinsic signed lines on a
  trivializing pro-etale object. `zero` sets the zero-degree basis vector to 1;
  `positive` sets the positive vectors to the actual sheaf pure tensors;
  `negative` makes each dual basis vector evaluate to 1 on the positive vector.
  Thus these are coherent powers of one generator, including the dual basis.
- `purityCancellationSection` maps fixed-scalar sections to those intrinsic lines
  by the actual realization's sheafification unit and equivalence counit. It is a
  construction, not a free section identification.
- `PurityCancellationContractions.line_add` now has a determining equation:
  `section_normalized` sends the pure tensor of local signed basis vectors to the
  basis vector of the summed degree. The equation explicitly applies line_add.hom.
  Local lifting along realization supplies these sections after a cover; intrinsic
  module linearity and the basis property determine the map on that cover, hence
  globally. Changing the first generator by u changes both sides by u^(r+s).
- `purityCancellationSingleProduct` constructs the actual canonical morphism in a
  general coefficient category: the published DerivedCategory.shiftTensorShiftIso,
  shifted cupSingleTensorMap, and the single functor applied to line_add.hom,
  followed by 2r+2s=2(r+s). `purityCancellationProductNormalized` is literally HEq
  with this constructed morphism. `derived_normalized` applies that determining
  equation to derived.hom; hence derived is not free. `Contractions.product` reads
  the uniquely determined isomorphism. This same-site heterogeneous equation
  bridges definitionally equal presentations of derived tensor; neither endpoint
  changes its scheme. Stating the equation before specialization avoids the kernel
  timeout from separately checking the expanded specialized morphism type. The
  generic construction binds all categorical instances explicitly.
  `purityCancellationZero` uses the fixed realization inverse of the normalized
  coefficient-unit comparison, the equivalence unit, constant comparison and zero
  shift, with no supplied unit map.
- `Contractions.unit` is the inverse of product(m,-m) followed by the zero
  identification. `Comparisons.unitCancel` is DEFINED from contractionsZ.unit.
  `Comparisons.addCancel` is DEFINED from contractionsX.product(N,-m), followed by
  the dimension equation. Neither unitCancel nor addCancel is a free field.
  Crucially these use separate records on Z and X. Nothing equates types of
  isomorphisms on different schemes.

Repair of H3/H5, pullback:

- `PurityCancellationFiniteComparison` is the exact SpSignedComparison type at
  P.level-1 and the prescribed annihilating coefficient map.
  `Comparisons.root_normalized` is the root-tensor adjunct equation from
  spFiniteTwists_cartesian at that level, fixing signed degree one. Its existing
  zero/positive/negative equations then fix the signed family in all degrees.
- `PurityCancellationSheafPullback.normalized` requires equality between the
  adjunct of its fixed-scalar sheaf comparison, transported through the specified
  realization section maps, and the actual adjunct of B.signed. This equation
  refers to BOTH maps and determines the sheaf comparison; it is not an existence
  property of its endpoints.
- `SheafPullback.transport` is defined using the derived pullback commutation with
  shifts, its exact-functor comparison, its canonical single comparison, and the
  single functor applied to the normalized sheaf map. `pullbackTransport` and
  `pullback` are definitions from it. No free derived pullback family remains.
- The coprojection witness, its inverse projection/counit characterization and its
  same-endpoint HEq normalization are retained unchanged. Both uses of HEq in
  the module stay on one scheme; the other compares the derived product with a
  constructed morphism, never with another unconstrained comparison field.

H8: all helpers, including purityCancellationFiniteLine,
PurityCancellationFiniteComparison and PurityCancellationContractions, have proper
source/blueprint docstrings. The new declarations are all listed in lean.declarations.

Hypothesis-by-hypothesis correspondence:

- P : PurityFiniteSetting retains k, ell different from characteristic, its fixed
  coefficient closure, finite extension E, positive level n and Lambda=O_E/varpi^n.
  The actual coefficient is P.Coefficient, the prescribed size lift. The default
  Kummer annihilator is ell^n; no ramification divisibility is imposed.
- Z and X : Scheme.{u}, their Over instances and the six LocallyOfFiniteType,
  QuasiCompact and IsSeparated instances give separated finite-type k-schemes.
  i, i.IsOver and IsClosedImmersion are precisely the closed immersion over k.
- N m c : Nat and _hN : N=m+c give the dimensions, retaining zero cases.
  Negative twists and shifts use integer negation after coercion.
- omegaX and omegaZ are the actual unbounded pro-etale derived objects; _hX and
  _hZ use purityCoprojectionConstructible via the canonical intrinsic realization
  and impose their stated bounded constructibility.
- piX and piZ are exactly the two specified orientations to T_X(N), T_Z(m).
  b is exactly omegaZ isomorphic to Ri!omegaX. No regularity, frame-class or
  orientation normalization condition is added to any of them.

Clause-by-clause correspondence:

- purityCancellationLine is the specified finite root line's signed tensor/dual
  power through the inverse of finiteCoefficientIntrinsicRealization. No new
  coefficient line is chosen. purityCancellationTate puts it in degree zero and
  shifts by 2r; purityCancellationTwist uses the recorded derived tensor functor.
- The first conjunct Nonempty(PurityCancellationComparisons ...) supplies the
  normalized structural identifications as a CONCLUSION. In particular no
  infrastructure-existence assumption is imposed on the specified inputs.
- The second conjunct asserts IsIso of the displayed composite for every such
  package. Its successive factors are: the derived unit cancellation on Z;
  F_Z(-m).map piZ.inv; F_Z(-m).map b.hom; F_Z(-m).map (Ri!.map piX.hom);
  inverse normalized root pullback; inverse specified coprojection; and Ri!.map
  addCancel.hom. The last three together are exactly the displayed last arrow.
  Unit/add/pullback now denote the section-normalized constructions described
  above, rather than arbitrary endpoint identifications.
- The third conjunct Nonempty(Ri!Lambda_X isomorphic to T_Z(-c)) is the untwisted
  Lambda_Z(-c)[-2c] conclusion.
- The fourth conjunct identifies H^0(Ri!T_X(c)) with P.constant Z. The fifth says
  IsZero of every H^q for q unequal to zero. Together they express the degree-zero
  sheaf conclusion without strengthening it to a stalk/frame normalization.

Dependency declarations read and used:

- Sheaf.Paper.PurityConventions: defaultAnnihilator and the coefficient datum;
  its public PurityFiniteSetting gives Coefficient and constant.
- Sheaf.Paper.ProEtaleTateTwistsOfUniverses: spComplexTwistOfUniverses and the
  public signed coefficientTwistLine/powers and finite-root construction.
- Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients: the recorded System
  and RingSystem.finiteRight, publicly retaining sfFiniteExceptionalAt and the
  finite-stage rightDerivedUpperShriek used in the coprojection declaration.
- Sheaf.Paper.PurityCoprojection: purityCoprojectionConstructible,
  purityCoprojectionProperty and purity_coprojection. Its property fixes the
  coprojection by the projection/counit equation in the same fixed-scalar category.
- Sheaf.Paper.TateTwistLocallyFree: tateFiniteCoefficient, tateFiniteLine,
  tateFiniteTensor and tateTwist_locallyFree, for the actual finite signed line.
- Sheaf.Paper.CartesianCoefficientTwists: SpSignedComparison and the precise
  spFiniteTwists_cartesian root adjunct formula, read including its full signature.
- Sheaf.Paper.SupportedCup: cupSingleTensorMap and cupConstantIso. These are the
  existing canonical localization tensorator and constant comparison, not copies.
- Sheaf.AlgebraicGeometry.ProEtaleConstantModuleUnit:
  proEtaleConstantModuleUnit, whose generator equation determines the unit map.
  Its public SfIntrinsicRealizationTransport gives sfIntrinsicRealizationUnit and
  sfIntrinsicModuleEquivalence, built from finiteCoefficientIntrinsicRealization.
- The finite-coefficient Derived.UpperLowerStar exactness comparison
  leftDerivedUpperStarIsoMapDerivedCategory, followed by the generic exact
  functor's mapDerivedCategory commShiftIso and mapDerivedCategorySingleFunctor.
  Current finite-coefficient sources were read using scompile.py --source.
  The older general Derived.Shift import collided with its finite-coefficient
  owners, so the transport uses the existing exact-functor comparisons directly;
  neither version of that extra shift module is needed.

The additional landed nodes def-pur-supported-cup, def-pur-proetale-constant-module-unit,
and def-weil-proetale-inverse-image remain statement dependencies. The theorem nodes
det-def-sp-tate-twist-locally-free and det-prop-sfb-cartesian-coefficients-twists remain
proof dependencies only. The new statement dependencies
def-pur-finite-tate-line-signed-comparison and def-pur-signed-comparison-interface expose
the five plain declarations used by the Lean statement: tateFiniteCoefficient,
tateFiniteScalar, tateFiniteLine, tateFiniteTensor, and SpSignedComparison. Both are
existing:true definition records; no module is copied and no dependency theorem is edited.

Edge cases read against the repaired definitions: N=m=c=0; c=0 and N=m;
m=0 and N=c; identity immersion; empty X; and particularly Z empty with X
nonempty. The contractionsZ and contractionsX have separate types, and the only
relations between them are the correctly typed pullback comparisons. On the empty
scheme, all module sections are the zero ring/module, so a basis indexed by Fin 1
is still valid over that zero ring and the normalization equations hold uniquely.
No false equality of Hom/isomorphism TYPES across Z and X remains. The theorem
still concludes comparison existence, so the IsIso conclusion is not vacuous.
These are mathematical edge-case checks, not a claimed stage-3 existence proof.
All positive coefficient levels, including ramified E with e not dividing n, remain.
The sites retain object universe u+1 and morphism universe u, and the intrinsic
module category is transported at the sheaf level before localization; no new
universe equality is imposed.

Searches retained from the original packet: msearch leanfinder for exceptional
Tate cancellation gave eight unrelated triangle/shift hits; loogle
CategoryTheory.TwistShiftData gave only generic shift data; msearch grep
TateTwist|tateObject|coprojection in CategoryTheory found only categorical
coprojections; leansearch for derived exceptional cancellation found only generic
shift/triangle lemmas. Exact node/name searches in the upstream source, lean/Sheaf
and dag/lean_names_upstream.json found no existing statement of this composite.
The blueprint Step 2, definition of Phi and unit statement were read.

Repair searches on 2026-10-18: msearch grep
signed.*[Cc]ontract|[Cc]ontract.*[Ss]igned in CategoryTheory returned zero hits;
leanfinder for canonical signed tensor product of a rank-one sheaf normalized
by local basis and dual evaluation gave eight generic free-sheaf/tensor/Picard
hits, none this normalization. Loogle for the expected derived single/shift helper
names gave zero Mathlib matches (the shift helper is upstream, not Mathlib).
rg in lean/Sheaf located cupSingleTensorMap, cupConstantIso, the specified
realization unit and proEtaleConstantModuleUnit; these are reused. rg found the
canonical DerivedCategory.shiftTensorShiftIso in the upstream generic monoidal
shift module. Exact new-helper-name searches across upstream, lean/Sheaf and the
upstream name map found no collisions. Searches are recorded in searches.jsonl.

No STATEMENT-DISPUTED fault is asserted. The node's six-step proof remains the
single theorem docstring: local signed contraction; root pullback; functoriality
of the three orientation arrows; coprojection and dimension arithmetic; second
coprojection and untwisting; and application of cohomology to the resulting Phi.

## New nodes

def-pur-finite-tate-line-signed-comparison records the four existing canonical finite Tate
coefficient, scalar, line, and normalized tensor declarations in
Sheaf.Paper.TateTwistLocallyFree. Its source is the finite-coefficient calculation in
Step 2. LeanSearch, LeanFinder, Loogle, and grep searches found no Mathlib or upstream
definition; grep of lean/Sheaf located the four declarations, so no copy is made.
The existing:true record imports the owner module and lists all four declarations.

def-pur-signed-comparison-interface records the existing SpSignedComparison structure in
Sheaf.Paper.CartesianCoefficientTwists. Its source is the signed comparison used by the
root pullback calculation in Step 2. LeanSearch, LeanFinder, Loogle, and grep searches
found no Mathlib or upstream match, while grep of lean/Sheaf located the exact structure.
The existing:true record lists that structure and introduces no duplicate or choice.
Together these two definition nodes expose the five plain declarations that had
previously been carried only by the two theorem nodes; those theorem nodes remain in
proof_deps.

## Repair self-check by NK

The return was read against the returned file and the new source with the node
open. The old line-only existence fields did not determine any arrow; they were
removed. The cross-scheme unit HEq was ill-typed mathematically; it was removed
and unitCancel now uses only Z. The free pullbackTransport did not use the finite
comparison; it is now a definition whose underlying sheaf map satisfies the actual
adjunct equation against B.signed. The theorem signature and the inverse
projection/counit coprojection normalization were preserved. No independent agent
was started, as required by this dispatcher brief; the maintainer performs the
independent delivery review.

Validation: an earlier repaired version compiled in 10.8 seconds at the sandbox
path and 12.1 seconds at the library path. The final source also passed scompile.py
server confirmation and deliver2.py preflight and compilation (dry-run c5bdcf70c4).
All accepted compiles are clean; only the expected sorry warning is permitted. The final source contains exactly one sorry; the theorem
signature matches the returned signature byte-for-byte, and lean.statement is
extracted verbatim from it. No global build was run.

The constructed single/shift product ends with an explicit `eqToHom (congrArg ...)` for
the 2*r + 2*s endpoint equality, and the normalized equation is stated before coefficient
specialization. The successful scompile and deliver2 compiles are evidence that these
endpoint types elaborate within the 60-second limit.

The failed experiments in scratchpad isolate why the equation is packaged before
specialization: a concrete application of the generic shift/tensor map caused a
kernel timeout, even with no explicit result annotation. The abstract construction
and the final determining-equation interface compile within the limit. No timeout
limit, tool, live source or compiler option was changed to hide a failure.


Final controls were run individually through scompile.py on copies of the final
source, retained only under scratchpad (not delivered):

- NegativeControl.lean exited 1 in 11.7 seconds. negContractionCtl simultaneously
  negates line_add and derived, as in the returned sign-flip control; the copied
  section_normalized proof fails at line 523 because the actual product map has
  changed. negDerivedCtl negates only the derived product; derived_normalized fails
  at line 530 against the constructed single/even-shift map. negPullbackCtl negates
  the sheaf comparison; normalized fails at line 537 against the unchanged B.signed
  adjunct. These are the three intended dependent-equation type mismatches, not
  import, syntax, or Neg-instance failures.
- PositiveControl.lean compiled cleanly in 11.5 seconds at its sandbox path and
  13.6 seconds at its check-module path. unitOnZCtl gives exactly
  Unit(P,Z) isomorphic to Tensor_Z(Tate_Z(m),Tate_Z(-m)), for independent arbitrary
  Z and X, with no equality assumption between them. This directly checks the
  endpoint error from return L; the empty-Z inhabitability argument is given in
  the edge-case paragraph above.

Concurrent library refresh briefly left compiled dependency artifacts missing on
this machine. The prescribed wrapper's server confirmation resolved that issue;
no tool or shared file was modified. The final dry run is repeated after this
validation report is recorded, then the packet is pushed by deliver2.py.

## Repair of return L at 0f2443e44472 (R1)

The saved packet was retained and its first dry run was run before edits. All
compilation checks passed, including the five existing declarations; preflight
rejected the missing source record of def-pur-signed-comparison-interface and
reported the two incomplete existing declaration signatures. This retry supplies
that source and records both signatures verbatim up to their declaration bodies.
Self-check also made the new nodes precise: the finite level is natural, and the
signed comparison has f:X to Y, with source lines on Y and target lines on X.
The latter now explicitly cites the existing signed-power definition node.

R1 is addressed by the two existing:true definition records, one for the four
Scheme.tateFiniteCoefficient/tateFiniteScalar/tateFiniteLine/tateFiniteTensor
declarations and one for ProEtale.SpSignedComparison. Their source modules were
opened and their full signatures and defining bodies/fields read. No declaration
is moved, copied, or chosen from a theorem. The item cites both definition nodes
and keeps det-def-sp-tate-twist-locally-free and
det-prop-sfb-cartesian-coefficients-twists in proof_deps only. The Lean module is
unchanged from the returned, substantively accepted delivery. Its theorem record
matches the signature (excluding the := delimiter); it has exactly one sorry,
and its helpers are listed in lean.declarations. The current main node differs
only in lean and the authorized additional statement dependencies.

For advisory A1, current published source was read through scompile.py --source:
ProEtale.FiniteCoefficient.Derived.Tensor defines derivedTensor as curriedTensor.
The accepted Lean retains the explicit eqToHom for the even-shift endpoint. The
successful module compiles establish elaboration, not an independent proof of
the expanded HEq endpoint type equality; the earlier report's compile-evidence
claim should be read with that limitation. No new equality proof or change to
the accepted Lean is claimed.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
