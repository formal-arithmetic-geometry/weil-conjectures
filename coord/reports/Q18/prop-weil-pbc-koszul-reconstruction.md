## Worker report

`Sheaf.Paper.KoszulReconstruction` states
`AlgebraicGeometry.Scheme.koszulReconstruction`. No proof is supplied: every theorem
introduced in this packet has proof `by sorry`. Definitions contain actual constructions,
or select the entire universal derived pair / a uniquely characterized map. The target
node's statement is unchanged. Its statement dependencies gain the existing nodes for
intrinsic completion, derived inverse limits, finite coefficient sheaves, and the
independent-universe K-flat and scalar-extension interfaces supplied in this packet.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `T : Scheme.{t}` is the arbitrary scheme. Its site is exactly `T.ProEt`, with topology
  `ProEt.topology T`; object universe t+1 and morphism universe t stay distinct.
- `A : Type (t + 1)` and `[CommRing A]` are the commutative coefficient ring in the site
  size convention. `d : AdicCoefficientDatum A` includes `IsNoetherianRing A`, finite
  generation of `d.ideal`, additive torsion of `A ⧸ d.ideal`, and finiteness and
  degree-zero perfectness of `A ⧸ d.ideal ^ (n+1)` for every `n : ℕ`.
- `r : ℕ`, `a : Fin r → A`, and `_ha : Ideal.span (Set.range a) = d.ideal` are precisely
  the finite generating list and its ideal. No regular-sequence or nonempty-list
  assumption is present. `_ha` remains a genuine hypothesis despite the underscore.
- `reductionCoefficient T d.ideal n` is the sheafification of continuous component
  functions with values in the discrete quotient, retaining commutativity.
  `completedReductionCoefficient T d.ideal` is the actual inverse limit of this
  quotient-coefficient system with canonical projections. Its module and derived
  categories are `reductionModules` and `reductionDerivedCategory`; no constant
  coefficient derived category is substituted for the completed one.
- `completedReductionTower T d.ideal` is the universal left derived functor of the
  actual strict reduction construction. Its K-flat counit fixes every level and
  transition. `ReductionTowerDerivedPair.computes` ensures use of a single K-flat
  complex for the entire strict quotient tower, with all quotient actions retained.
- `completedKoszulFactor` is `[A_T --a^(m+1)--> A_T]` in degrees -1 and 0.
  `completedKoszulTower` takes its ordered total tensor, with the Mathlib signed
  total differential. Index `m : ℕ` represents positive exponent m+1.
- `completedKoszulFactorStepF` multiplies by a in degree -1, is identity in degree
  zero, and is zero elsewhere. The strict factor tower and recursive total tensor
  give the stipulated tensor transitions, including composites.
- For `r=0`, the recursive tower is the constant `completedKoszulRingComplex`, namely
  A_T[0]. No positive-degree term or extra summand is introduced in this case.
- `completedKoszulTensorTower` is C tensor Q_m using the actual total sheaf tensor
  bifunctor. `completedKoszulStrictTower` transposes that diagram to a complex of
  strict towers. The explicit fiber `completedKoszulFiber` computes its sequential
  derived inverse limit: exact pro-etale countable products and the derived-product
  comparison are used by its named derived-limit statement. Thus the descended
  `completedKoszulDerivedFunctor` is the requested Koszul completion functor.
- `completedKoszulUnitZero`, `completedKoszulTensorUnit`, and
  `completedKoszulFiberUnit` implement the degree-zero inclusions, tensor with the
  identity, then the map c to (u_C(c),0) into the fiber. Localization gives the actual
  natural transformation `completedKoszulDerivedUnit`, the map kappa_K.
- `reconstructionLimit` is the ordinary strict inverse-limit functor.
  `reconstructionRlim` is its total right derived functor, constructed using the
  Grothendieck strict tower category and its K-injective resolutions. The universal
  comparison `reconstructionRlimComparison` records how it acts on a tower complex.
  It is a functor on D(Tow), not a nonfunctorial choice of a Roos triangle.
- `reconstructionOrdinaryUnit_exists` characterizes the map into the ordinary limit
  by x mapping to 1 tensor x at every quotient projection and every site section.
  `reconstructionUnitOnKFlat` composes this map with the actual total-right-derived
  comparison and the inverse universal K-flat reduction-tower counit.
  `reconstructionCompletionUnit_exists` uniquely characterizes the resulting natural
  transformation on D(Mod(A_T)) by this formula on ALL K-flat representatives.
  `reconstructionCompletionUnit` is therefore exactly comp_K, independently of any
  isomorphism supplied by the target theorem.
- Derived I-completeness is rendered directly by `IsIso` of kappa_K in the final
  implication, using the existing Koszul unit without introducing a second predicate.
- The existential `c` is a natural isomorphism
  `completedKoszulDerivedFunctor ≅ completedReductionTower ⋙ reconstructionRlim`.
  Its component is the stated c_K, and naturality is part of the natural isomorphism
  structure for every derived morphism, not just maps of chosen representatives.
- The first conjunct is `kappa_K ≫ c.hom.app K = comp_K` for every K. This is the
  source equation c_K composed after kappa_K, in Lean's left-to-right composition.
- The second conjunct says `IsIso (kappa_K) → IsIso (comp_K)` for
  every K, including arbitrary unbounded objects. No completeness assumption is used
  in the comparison's existence or its unit equation.

Dependency declarations read and used:

- `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`,
  `completedReductionCoefficient`, `completedReductionProjection`, `reductionModules`,
  `reductionDerivedCategory`, `completedReductionTower`, its universal counit and
  `completedReductionTowerComplexCounit`, normalization and evaluation comparisons.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  its functorial interface `Functor.map₂CochainComplex` implements the tensor tower.
- `Sheaf.Paper.IntrinsicCompletion`: actual factors, strict tensor tower, explicit fiber,
  `completedKoszulDerivedFunctor`, and `completedKoszulDerivedUnit`.
- `Sheaf.Paper.CompletedDerivedInverseLimit`: `completedTowerDerivedSequence`,
  `completedTowerDerivedStep`, `CompletedDerivedInverseLimit`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`:
  `CategoryTheory.ringedStrictTowerHomotopyLimit`, whose universal right-derived pair
  is the stated strict-limit convention. Its recorded small-category interface is
  imported as a proof tool; the construction here uses the genuine unequal-size
  pro-etale site and the canonical Grothendieck K-injective derived functor directly.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`:
  `SheafOfModules.site_derived_tensor_descent`, imported for representative descent.
  K-flatness and coefficient change in the actual construction use the recorded
  independent-universe `CochainComplex.IsKFlat` and
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients` interfaces.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`:
  `Functor.rightDerivedFunctor`, its universal unit, and triangulated derived functor
  framework; `GrothendieckAbelian.KInjectiveResolution` supplies the canonical
  derivability structure from the delivered tower Grothendieck theorem.

Proof-only nodes `lem-weil-pbc-completed-constant-sheaf-reduction` and
`lem-weil-pbc-constant-completion-equivalence` have no recorded Lean modules on the
base; their imports therefore remain for the maintainer when those nodes are stated.
Their full proof plan is retained in the theorem docstring. They are not necessary
as statement dependencies or as data defining either completion or either unit.

Edge cases checked: empty scheme, zero ring, I the unit ideal, I=0, empty generating
list, repeated or zero generators, m=1, all unbounded K (including zero). For r=0
I=0, the constant degree-zero Koszul tower and identity quotient tower give the same
completion. For I=A the completed ring and module category are zero; the statement
has the intended zero-object interpretation. Positive powers are indexed bijectively
by n+1, so no quotient A/I^0 is silently added and no positive quotient is omitted.
No flatness of a quotient or exactness of general site products is assumed.

Searches:

- msearch LeanFinder: `derived completion identifies Koszul completion with the derived
  inverse limit of quotient towers`: eight ordinary AdicCompletion hits; none states
  this completed-sheaf derived comparison.
- msearch Loogle: `DerivedCategory, Koszul`: zero hits, unknown identifier Koszul.
- msearch grep: `koszul.*completion|koszulReconstruction|adicCoefficientDatum`: no hit
  in Mathlib. Ordinary completion and local cohomology do not give this statement.
- rg of upstream WeilConjectures for the node id and Koszul reconstruction: no hit.
- rg of lean/Sheaf found IntrinsicKoszulCompletion and KoszulQuotientLimit: those use
  the constant coefficient ring and CompleteCoefficientDatum, not this completed
  coefficient category. Their full signatures and relevant docstrings were read.
  RingedKoszulSystem is a generic small equal-size site interface; its finite tensor
  construction was inspected, while the existing intrinsic-completion node supplies
  this actual pro-etale specialization and the precise negative-degree factors.
- Live scompile --source: AdicCoefficientDatum and ProEtaleDiscreteCoefficients were
  unavailable. Read-only server delivery-ref searches found no delivered module for
  this datum. The unfinished Q02 draft was read and reused, with repairs compiled in
  this delivery; it is not treated as a landed declaration or a mathematical proof.
- Sources read: [Stacks 099M](https://stacks.math.columbia.edu/tag/099M),
  [091Z](https://stacks.math.columbia.edu/tag/091Z), and
  [0A0E](https://stacks.math.columbia.edu/tag/0A0E), alongside the full reviewed DAG
  statement and proof. 099M concerns constant coefficients; the proof plan expressly
  uses the completed-coefficient comparison node and does not equate ambient categories.

No new DAG node and no statement correction. No `STATEMENT-DISPUTED` fault found.
The independent second reading is left to the second worker.

## Dependency modules

`def-weil-pbc-adic-coefficient-datum`: this genuine prerequisite has no recorded Lean
module. The delivered full module constructs the actual inverse-limit coefficient
sheaf, projections, strict ordinary reduction functor and its universal left derived
pair, quotient objects, evaluation comparisons, and balancing normalization with
naturality and cocycle. The datum includes every Noetherian, finite, torsion and
perfectness hypothesis. Universal scalar extension is packaged in an opaque structure
with the original universal counit and K-flat computation, preventing repeated
unfolding of nested existential witnesses during elaboration. The pure-tensor section
uses local transparency for the underlying module action; this changes no definition.

`def-weil-pbc-intrinsic-completion`: genuine existing node, previously without a Lean
record. Its entire specified complex model is supplied, including multiplication by
compatible residues, negative-degree factors, (a,1) transitions, total tensor, empty
unit, the signed mapping fiber, its unit, functorial maps, localization descent and
relation to the derived-limit predicate. This is precisely the notion required by the
target, not a new definition with different coefficient category or signs.

`def-weil-pbc-derived-inverse-limit`: genuine prerequisite of intrinsic completion,
previously without a Lean record. The delivered module supplies exact derived tower
evaluations and transitions and defines an object with its distinguished Roos triangle.
It selects neither an arbitrary inverse-limit functor nor an unnormalized completion map.

`def-weil-pbc-proetale-modules`: the recorded RingCat-valued finite coefficient interface
forgets the commutative structure needed for these tensors. Its original full module is
imported unchanged. The enhancement retains CommRingCat sheafification and natural
coefficient maps; its uniquely characterized forgetful comparison identifies this with
the original continuous-functions coefficient sheaf, including on section generators.

`def-pc-kflat-complex`: paired-source repair of the published artifact, which does not
accept the current recorded three independent universe arguments. The recorded current
source is recompiled, preserving site object t+1, morphism t and coefficient t+1 sizes.
No private K-flat predicate is introduced.

`lem-pc-kflat-resolution`: recompile the current recorded source against that KFlat
interface, with all flat-term, quasi-isomorphism and degreewise epimorphism clauses.

`lem-pur-derived-change-of-rings`: recompile its current recorded source against the same
paired KFlat interface, retaining the uniquely specified ordinary functor on objects
and maps, universal derived counit, and all K-flat computations.

All dependency DAG statements and other fields are unchanged. Every attached module is
compiled separately by scompile in dependency order with two threads and 60 seconds.

Validation evidence: the full eight-module scompile packet compiled cleanly in
`compile2.log`: KFlat 2.3 s, K-flat resolution 1.2 s, derived change of rings 1.4 s,
coefficient enhancement 2.2 s, adic coefficient datum 27.2 s, derived-limit predicate
2.0 s, intrinsic completion 5.4 s, and Koszul reconstruction 2.6 s. The final statement
renders completeness directly as invertibility of the existing Koszul unit. The dry-run
wrapper recompiles that final packet. Its first attempt encountered a server temporary
filesystem ENOSPC tool crash; a retry was started after a read-only check showed space
available. No server cleanup or modification of project tools was performed.

The original blueprint body at order 1248 was also read from the server's literature
copy. Its two displayed isomorphisms and the unit-compatibility sentence correspond
exactly to the natural-isomorphism conclusion, first conjunct, and final implication.

Final dry-run result: BLOCKED by an actual compiler-tool crash. Both
`deliver2.py Q18 prop-weil-pbc-koszul-reconstruction --no-push` attempts failed inside
server `tools/nt_compile.py`, `own_directory`, while creating a symlink in its private
`/tmp/nt-stage2-…/objects/Sheaf/AlgebraicGeometry/` directory:
`OSError: [Errno 28] No space left on device`. The retry failed identically after the
read-only space check. No preflight result or OK was produced, and nothing was pushed.
The complete packet, its previous clean per-file compilation, and both crash logs are
preserved in this sandbox for retry once the tool's temporary-filesystem issue is fixed.

## Retry on 2026-10-15 UTC

The complete eight-module packet again compiled cleanly with scompile.py (all invocations
under 60 seconds, no diagnostics). The former ENOSPC crash did not recur. The first
retry reached preflight and identified a truncated lean.statement for the independent
K-flat resolution. This signature is now refreshed verbatim with the preflight's
bracket-aware declaration reader; all other primary signatures were checked likewise.

Preflight also refuses the two genuine existing unstated dependencies
`def-weil-pbc-intrinsic-completion` and `def-weil-pbc-derived-inverse-limit`: they were
not on the base item's direct dependency list and had no landed Lean record. The
human's 2026-10-16 instruction explicitly requires stating these in the same delivery
and citing them. No source-based mathematical statement correction is warranted: the
item statement already defines the Koszul complex and its completion correctly.
A second dry run is required after the signature repair to confirm this tool refusal.

## Confirmed tool refusal after metadata repair

The second current dry run completed its clean packet compilation and reached server
preflight. The repaired K-flat-resolution signature is accepted. The exact output is
preserved in `dryrun-current.log`. Preflight now reports six findings:

- It refuses `def-weil-pbc-derived-inverse-limit` and
  `def-weil-pbc-intrinsic-completion` because they are existing nodes not on the
  base item's direct dependency list and have no landed Lean record.
- It refuses adding those same two unstated prerequisite nodes to `stmt_deps`.
- As a consequence it does not recognize their delivered modules as owned by nodes.
- It asks for the independent second reading, which is intentionally left for the
  second worker. This alone would be accepted by the dry-run wrapper.

The first five findings implement an older restriction and contradict the prompt's
2026-10-16 human instruction: “If the needed object is a genuine DAG node with no
usable recorded declaration or Mathlib match, state that node yourself in this delivery
(its own module and node record, under §1(A)), cite it in stmt_deps, and state your item
on top of it.” Both genuine dependencies are fully supplied here. Their source-based
statements and the target statement are unchanged. Fabricating a mathematical
statement_change merely to bypass this check would be inappropriate. No project tool
was edited and nothing was pushed. The delivery is BLOCKED by this reproducible
preflight refusal after the metadata repair; the eight clean modules remain ready
for the independent reader once the tool supports the authorized dependency packet.

## Current retry of the retained packet

Re-read the standing stage-2 brief, stage rules, section H, worker role, setup,
goal, state and tools instructions, and compared the retained item and dependency
records with the current shared DAG. Re-read the actual blueprint order 1248 from
the server literature copy: the two displayed isomorphisms and the intervening
unit-compatibility sentence agree with the retained theorem. No source-based
statement correction is warranted.

Repeated the prescribed LeanFinder, Loogle and Mathlib grep queries recorded above:
LeanFinder again returned eight ordinary adic-completion declarations, Loogle
returned zero hits with unknown identifier Koszul, and grep returned zero hits.
Repeated the source/project searches: no upstream target declaration; the
constant-coefficient KoszulQuotientLimit and IntrinsicKoszulCompletion remain
different ambient categories. Live `scompile.py --source` confirms that
IntrinsicCompletion and AdicCoefficientDatum still have no published source.
The published KFlat source still has the same three independent universes as
the paired source in this packet. Its source/artifact synchronization repair
therefore remains in the delivery.

All eight modules explicitly disable autoImplicit and have no lines over 100
characters. No mathematical declaration, hypothesis, unit, transition, or
coefficient category was changed in this retry. The current mandatory
`deliver2.py --no-push` run printed OK for commit `488e1bdd4e`: all modules
compile and preflight passes except for the independent second reading, which
the wrapper explicitly accepts for a worker dry run. The previous prerequisite
refusal no longer occurs. This result supersedes the historical BLOCKED results
above. Full output is in `dryrun-repair.log`. Nothing was pushed, and no
second-reading section was written by this worker.

## Earlier second reading (a previous round; superseded)

The final delivery consists of one module, `Sheaf.Paper.KoszulReconstruction`, and
its item record. The eight-module packet described in the retained Worker report
has been superseded: the shared DAG now has landed coefficient, derived-limit and
intrinsic-completion interfaces. I removed all seven copied dependency records
and their modules from the delivery, instead using the current declarations.
This resolves an H4/H13 mismatch that appeared after the first worker's packet:
its private `AdicCoefficientDatum` conflicted with the now-landed declaration of
the same full name, and it replaced usable recorded dependencies with earlier
copies. The originals are retained only under `scratchpad` for audit.

I read the blueprint file at order 1248 from the server literature copy, not just
the imported node. Its two displayed isomorphisms and intervening sentence are
the comparison, unit equation, and completeness consequence below. I also read
proetale.tex, section-derived-completion-noetherian (099L), including the standing
Noetherian and completed-constant-sheaf hypotheses and lemma-naive-completion
(099M), and algebraization.tex, lemma-derived-completion-koszul (0A0E), including
the general ringed-site and global-generator hypotheses. The target's existing
proof explicitly passes through its completed-coefficient comparison nodes;
it does not identify the whole constant and completed module categories. No
mathematical statement change, target-unit change, or new DAG node is needed.

The following is my object, hypothesis and conclusion inventory, matched against
the final Lean file and the dependency declarations I opened:

- Arbitrary scheme T: `(T : Scheme.{t})`, and its actual small pro-etale site in
  every imported module. Pass. No separation, Noetherianity of T, characteristic
  or nonemptiness assumption is added.
- Commutative Noetherian A, ideal I, additive torsion A/I, and finite perfect
  positive quotients: `{A : Type t} [CommRing A] (d : AdicCoefficientDatum A)`.
  I read `CompletedAdicCoefficientDatum.AdicCoefficientDatum`, which extends
  `CompleteCoefficientDatum`, and the latter's fields and perfectness predicate:
  the inherited fields are ideal, Noetherianity, finite generation, additive
  torsion and positive-power perfectness; `quotientFinite` adds precisely set
  finiteness of each positive quotient. Pass.
- Finite ordered generating list with ideal I: `(r : ℕ) (a : Fin r → A)` and
  `_ha : Ideal.span (Set.range a) = d.ideal`. Pass; the underscore does not
  discard this genuine hypothesis. No regular-sequence assumption is present.
- Finite quotient sheaves and completed A_T: the recorded `completedAdicFiniteRing`,
  `completedAdicRingSystem`, actual limit `completedAdicRing`, its projections,
  and `completedAdicCommRing`. I opened their formulas: quotient transitions are
  sheafified postcomposition on continuous component functions; commutativity
  retains the same underlying limit-ring data. Pass.
- Modules and derived category over that completed sheaf: `CompletedAdicModules`
  and `DerivedCategory (CompletedAdicModules T d)`. Pass; these are actual left
  module sheaves over A_T, with Mathlib's abelian structure and standard derived
  localization. No constant-coefficient category is substituted.
- Strict derived quotient tower: the recorded `completedAdicOrdinaryTower` and
  `completedAdicReduction`. I read their tensor factors, quotient transitions,
  universal counit and K-flat computation in `completedAdicReduction_exists`.
  `reconstructionReductionComplexCounit` uses that same witness with the
  canonical complex/homotopy localization factors. Pass: every quotient level
  uses a single representative and retains its completed scalar action.
- Koszul factors, degrees, powers and transitions: the recorded
  `completedAdicKoszul`, `completedAdicKoszulStep`, and
  `completedAdicKoszulTensor`. I followed these through scalar extension to
  `koszulPowerSheaf`, `koszulPower`, and `koszulPowerTransition` in the constant
  intrinsic-completion module. The exterior complex is the ordered finite
  Koszul tensor, supported in [-r,0]; its chain-to-cochain embedding places the
  degree-one generators in degree -1, and the diagonal generator map multiplies
  by a_j. Pass. Every index m denotes exponent m+1.
- Koszul derived inverse limit: `completedAdicKoszulProduct`,
  `completedAdicKoszulOneSubShift`, and `completedAdicKoszulFibre` are the
  already-landed explicit product/mapping-fibre model. The new
  `reconstructionKoszulProductMap` and `reconstructionKoszulFiberMap` merely
  extend it on maps by tensor, products, the canonical map of mapping cones,
  and shift. Their functor and localization lift render functoriality on all
  derived morphisms. Pass. No second Koszul object or coefficient construction
  is defined.
- Koszul unit: the recorded `completedAdicKoszulUnitComplex` is c mapped to
  (u_C(c),0). `reconstructionKoszulComplexUnit` assembles these maps and
  `reconstructionKoszulDerivedUnit` localizes them. The named
  `reconstructionKoszulIntrinsicComparison` explicitly identifies this functor's
  object and unit with `completedAdicIntrinsicCompletion` and
  `completedAdicIntrinsicUnit`. Pass; this is the node's κ_K, including its
  normalization, rather than an arbitrary map into an isomorphic object.
- Functorial total right derived inverse limit on strict towers:
  `reconstructionLimit := lim` and `reconstructionRlim :=
  (reconstructionLimit T d).rightDerivedFunctor`. The Grothendieck tower theorem
  supplies K-injective resolutions without an added assumption on T or K.
  The comparison is the universal right-derived unit with the standard
  localization isomorphisms. Pass. The recorded general strict-tower theorem
  has an equal-size small-site interface; the construction uses the generic
  right-derived API on the genuine pro-etale tower category, preserving its
  distinct site universes, rather than imposing a new equality on them.
- Quotient completion map: `reconstructionQuotientUnit_exists` uniquely fixes
  the module map by its value one on all sections. The uniquely normalized
  `reconstructionOrdinaryUnit` has n-th projection rho-inverse followed by
  tensoring with that residue map. `reconstructionUnitOnKFlat` composes its
  localization with the right-derived comparison and inverse reduction
  counit. Finally `reconstructionCompletionUnit_exists` fixes the natural
  transformation on ALL K-flat representatives. Pass: comp_K is constructed
  independently of the reconstruction isomorphism; no arbitrary choice or
  circular identification defines it.
- Functorial isomorphism for every K, without completeness assumed: existential
  natural isomorphism `c : reconstructionKoszulDerivedFunctor T d r a ≅
  completedAdicReduction T d ⋙ reconstructionRlim T d`. Pass. Naturality is a
  field of the natural isomorphism on the actual derived category.
- Canonical unit equality: first conjunct, for all K,
  `(reconstructionKoszulDerivedUnit T d r a).app K ≫ c.hom.app K =
  (reconstructionCompletionUnit T d).app K`. Pass: Lean's composition order
  renders exactly c_K composed after κ_K.
- Derived-complete consequence: second conjunct, for every unbounded K,
  `IsIso (κ_K) → IsIso (comp_K)`. Pass. This is exactly the node's definition
  of derived completeness; the intrinsic comparison above verifies agreement
  with the recorded completeness predicate. No separate hypothesis is imposed
  on the comparison isomorphism's existence.

Edge cases: r=0 is permitted and the recorded exterior degree-zero Koszul object
is the coefficient unit; I=0 then gives the constant quotient tower and the
identity completion. With redundant zero generators the negative summands have
zero transition and disappear in the derived limit. The zero complex, empty
scheme, zero ring, unit ideal and all characteristics remain admitted. No n=0
quotient is included: n : ℕ always denotes n+1, and all positive exponents occur.
The site keeps object universe t+1 and morphism universe t, while coefficient
and module sheaves live in t+1. The underlying A and scheme use the common
universe of the recorded size convention, with quotients lifted by ULift;
no new equality between site object and morphism universes is assumed.

Independent searches: I ran msearch LeanFinder for “Koszul derived completion of
sheaves is the derived inverse limit of reductions with compatible units” (eight
hits: ordinary local cohomology, differentials, sheaf limits and period rings),
Loogle for quoted completion (twelve editor-completion hits), and Mathlib grep
for `koszul.*completion|derivedCompletion|reconstructionLimit` (zero hits).
I also searched the exact upstream and project trees with Koszul, strict tower,
derived completion, reconstructionCompletionUnit and koszulReconstruction.
The related constant-coefficient `IntrinsicKoszulCompletion` and
`KoszulQuotientLimit` differ in ambient coefficients; the landed
`CompletedAdicIntrinsicCompletion` supplies the object but no functorial
reconstruction theorem. Thus no existing declaration states this result.
There is no new definition node: all substantive objects already have recorded
nodes, and the extra maps are canonical interfaces of the owning item.

Other mismatches repaired: the first packet's dependency records and declaration
list were stale, so I reduced stmt_deps to the original dependencies plus the
landed intrinsic-completion node and removed all dependency overrides. The
Lean statement record is refreshed verbatim from the final theorem signature.
All definitions contain real constructions or choices uniquely fixed by their
universal property or section formulas; every postponed theorem is named,
recorded in lean.declarations, and has a source/blueprint and full proof plan.
All theorem proofs remain `by sorry`. No local notation, private definition,
file-local instance or unbound variable is introduced.

Validation: the final one-module packet compiled cleanly through `scompile.py`:
sandbox import check 36.5 seconds, library-module check 31.4 seconds, both
with two threads, nice 19, the unchanged 60-second per-file limit, and no
diagnostics. Signature equality and 100-column checks pass. A current-tree
search found no collision for any of the module's 28 declarations. The
namespace ambiguity in the product-map helper was repaired with the fully
qualified `Limits.Pi.map`; explicit tensor zero-preservation instances and
typed coefficient-unit sections resolve the remaining elaboration interfaces.

The required final dry run printed `OK (dry run)` at commit `b326c26cf0`:
the complete one-module packet compiles and passes current server preflight.
Only the item node, its module and this report are staged. The Lean record's
date uses the actual UTC date at delivery; the theorem signature and all
mathematical fields are unchanged after the successful compile and dry run.


### Immutable maintainer review correction (2026-10-16)

The independent immutable review at 6b96c6c3c816d09b018efbfceb244f01fc9d3d69
found one mechanical H6 issue in the final one-module packet: the mapping-cone
index witness in `reconstructionKoszulFiberMap` proved `(j - 1) + 1 = j`
inline using `change` and `omega`. The replacement module uses the existing
Mathlib theorem `sub_add_cancel j 1` directly. This removes the local proof
without adding a declaration or changing any definition's mathematical data,
the main signature, hypotheses, conclusions, or dependency records. All 13
introduced theorems still have exactly `by sorry` proofs. The retained earlier
worker history is superseded by the final one-module second reading above.

The immutable original was independently reproduced using scompile.py with
the local side overlay: sandbox check 39.6 seconds and library-module check
33.7 seconds, exit 0 and no diagnostics. The full replacement module also passed scompile.py with exit 0 and no
diagnostics: sandbox check 33.2 seconds and library-module check 35.0 seconds.
The complete independent compiler evidence is recorded in review.md.

## Second reading by Q18

I read the item record, the order-1248 blueprint source, and the external source
places before checking the Lean declaration. The blueprint states a functorial
isomorphism from the Koszul derived completion to the derived limit of the strict
quotient tower, compatibility of the two canonical units, and the derived-complete
consequence. Stacks 099M gives the quotient-tower formula in the Noetherian case;
Stacks 0A0E gives the Koszul formula, and the blueprint explicitly distinguishes the
Koszul tower from the quotient tower.

The item inventory and Lean rendering are as follows.

- The scheme, coefficient datum, ideal generators, and generator equation are
  rendered by `(T : Scheme.{t})`, `{A : Type t} [CommRing A]`,
  `d : AdicCoefficientDatum A`, `(r : ℕ)`, `(a : Fin r → A)`, and
  `_ha : Ideal.span (Set.range a) = d.ideal`. The datum supplies commutative
  Noetherian A, additive torsion of A/I, finite positive quotients, perfectness,
  the actual completed sheaf, and its projections. No extra Noetherianity,
  separatedness, characteristic, or nonemptiness assumption is added.
- The completed coefficient modules and their derived category are
  `CompletedAdicModules T d` and `DerivedCategory (CompletedAdicModules T d)`.
  The imported declaration is the sheaf of left modules over the actual inverse
  limit ring `completedAdicRing T d`; no constant-coefficient category is used.
- The strict quotient tower is the recorded
  `completedAdicReduction T d`, whose K-flat representative computation is fixed
  by `completedAdicReduction_exists`. Its values use the canonical quotient maps
  `completedAdicFiniteModuleStep`, so the tower retains all transitions.
- The Koszul terms and transitions are the recorded
  `completedAdicKoszul`, `completedAdicKoszulStep`, and
  `completedAdicKoszulTensor`. They are the ordered tensor of the two-term
  complexes with multiplication by `a j ^ (m+1)`, in cohomological degrees
  `[-r,0]`; the transition has multiplication by `a j` in degree -1 and identity
  in degree 0. The index is `m : ℕ`, hence positive powers are `m+1`, as in the
  datum convention. For `r = 0` the imported tensor is the unit complex.
- The Koszul derived limit is rendered by
  `completedAdicKoszulProduct`, `completedAdicKoszulOneSubShift`,
  `completedAdicKoszulFibre`, and the functorial maps
  `reconstructionKoszulProductMap` and `reconstructionKoszulFiberMap`.
  `reconstructionKoszulFiberFunctor_inverts` and
  `reconstructionKoszulDerivedFunctor` descend this explicit mapping-fibre model
  through quasi-isomorphisms, so this is a derived functor on the full unbounded
  derived category.
- The completion unit κ is the localization of the degree-zero inclusion
  `completedAdicKoszulUnitComplex`, via
  `reconstructionKoszulComplexUnit` and `reconstructionKoszulDerivedUnit`.
  The unit-compatible comparison
  `reconstructionKoszulIntrinsicComparison` identifies this model with the
  recorded `completedAdicIntrinsicCompletion` and
  `completedAdicIntrinsicUnit`; it is not an arbitrary map into an isomorphic
  object.
- The functorial right-derived inverse limit is
  `reconstructionLimit := lim` and
  `reconstructionRlim := (reconstructionLimit T d).rightDerivedFunctor`.
  `reconstructionRlimComparison` supplies the standard localization comparison,
  while `reconstructionCompletionUnit` is independently normalized from the
  quotient maps on every K-flat representative. Thus the quotient unit is not
  defined by first choosing the desired comparison isomorphism.
- The final declaration
  `AlgebraicGeometry.Scheme.koszulReconstruction` gives an existential natural
  isomorphism `c : reconstructionKoszulDerivedFunctor T d r a ≅
  completedAdicReduction T d ⋙ reconstructionRlim T d`. Its first conjunct is,
  for every derived object K,
  `κ_K ≫ c.hom.app K = (reconstructionCompletionUnit T d).app K`, exactly the
  unit compatibility in the node. Its second conjunct is
  `IsIso κ_K → IsIso comp_K`, exactly the stated derived-complete consequence.
  The natural-isomorphism field supplies invertibility of `c` without an extra
  hypothesis.

Edge cases were checked against the definitions: `r = 0` gives the degree-zero
unit Koszul complex; zero or redundant generators, the zero complex, the zero
ring, the unit ideal, and an empty scheme remain admissible. The tower uses only
positive powers (`m+1`), matching the datum's `n+1` indexing. No characteristic,
separatedness, or nonempty-index hypothesis is introduced. Site object and morphism
universes remain those of the imported pro-etale modules (`t+1` and `t`); no
universe equality is imposed.

For H4 searches I ran the prescribed LeanFinder and Loogle queries for Koszul
derived completion and quotient-tower reconstruction, plus `rg` searches through
Mathlib, the upstream `WeilConjectures` tree, and the project declarations. The
only hits were ordinary `AdicCompletion`, local cohomology, or unrelated Koszul
material. No existing declaration states this completed-coefficient reconstruction.

The worker packet's only mechanical repair was retained: the mapping-cone index
witness in `reconstructionKoszulFiberMap` now uses Mathlib's
`sub_add_cancel j 1`, removing an inline `change`/`omega` proof. No mathematical
statement, hypothesis, conclusion, dependency, or definition was changed in this
second reading. All helper definitions have real constructions or uniquely
characterized choices; postponed results are named theorems with `by sorry`, source
places, and `(blueprint: prop-weil-pbc-koszul-reconstruction)` documentation.

The required `scompile.py` invocation compiled the module cleanly with no
diagnostics. The retained dry run reports `OK (dry run)` after current preflight.
