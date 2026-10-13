## What changed

Applied reviewer point C1. The tensor stalk comparison node's second proof step now explicitly transports the square to the chosen pullback and invokes `lem-pc-pullback-stalk-tensor-flat`; that node is included in the step `uses` and `proof_deps`. The corresponding module docstring was updated to the same argument. No Lean declaration or theorem statement changed.

Corrected the intermediate statement
AlgebraicGeometry.singleComplexInheritedTensorCondition to the canonical pullback
tensor comparison of Stacks Tag 0DJA(1), explicitly pinned by
IsCanonicalPullbackTensorComparison. The theorem now returns a canonical core-monoidal model, its defining predicate,
and inheritance for every E. This includes monoidal existence and fixes the map
used in the source. Existing canonical comparison existence and monoidal
realization theorems supply the model without a new hole. The canonical
inheritance clause has a complete Lean proof: transfer invertibility through the
original coordinate square, apply the ring inheritance theorem, and cancel the
vertical isomorphisms in the tensor square.

The two new modules from the earlier attempt remain, but the geometric bridge is
corrected to canonical comparisons. It no longer asserts transport for arbitrary
monoidal structures. Removed its public import of the ring inheritance theorem;
its statement uses only the cohomology model, tensor infrastructure, and flatness.
The primary module imports the ring inheritance theorem directly, as a proof import.

Adapted the proofs of SingleComplexBaseChangeCriterion and
TorIndependentPerfectTensorBaseChange because their old calls fail against the
corrected interface. Every declaration signature and visibility in these modules
stays unchanged. No Challenge target or existing definition changes.

## Proved and sorry left

The corrected canonical declaration
AlgebraicGeometry.singleComplexInheritedTensorCondition has no sorry in its proof.
This is a decomposition: one canonical inheritance obligation is reduced to two
strictly smaller obligations. It is NOT a proof of the retired, stronger assertion
about every unrelated monoidal structure, and is NOT a sorry-free mathematical proof.
The change record and statement_change document that source correction separately.

Exactly two new holes remain:
- ModuleCat.localizedTensorComparison_inheritance,
  lem-pc-localized-tensor-comparison-inheritance: the mixed-ring K-flat tensor and
  flat-cohomology inheritance argument, with no schemes or coordinate presentations.
- AlgebraicGeometry.exists_tensorStalkComparison_squares,
  lem-pc-tensor-stalk-comparison-squares: flatness and simultaneous canonical
  coordinate squares, with no h_stalk hypothesis and no horizontal invertibility.

The two adapted caller modules have no sorry. No hole is placed in a definition,
private declaration, or partial proof. The ring and geometric holes have exactly
:= by sorry, sources, complete proof plans in docstrings, and matching nodes.

## No longer needed

Removed the primary module's proof import
Sheaf.Algebra.Homology.DerivedTensorTransitivity and direct proof dependency
lem-pc-derived-tensor-transitivity. Its Lean signature gives an associator with a
True side condition, not the flat cohomology inheritance clause described by the
old DAG proof. The new ring lemma uses lem-pc-kflat-derived-tensor-associator and
lem-pc-derived-module-free-generation instead. Other citers may still reach that
wrapper; pruning here is relative to this proof. The forced criterion adaptation
no longer uses lem-pc-canonical-pullback-tensor-monoidal-realization in its proof
route, and its node is updated accordingly. Its unused proof import
Sheaf.AlgebraicGeometry.CanonicalPullbackTensorMonoidalRealization is removed.

Removed the bridge's public import
Sheaf.Algebra.Homology.LocalizedTensorComparisonInheritance: the bridge does not
use that theorem or its module in its signature. The primary proof imports it
directly. Removed def-pc-derived-pullback-monoidal-model from the bridge proof
route; its canonical equation now comes from
 def-pc-derived-pullback-tensor-comparison. The canonical comparison existence theorem still reaches the monoidal-model
node transitively; the primary proof directly uses canonical comparison existence
and monoidal realization. No unit statement or realized step is bypassed:
sk-thm-picard-semicon has empty realized statement and step lists.

## Where the brief, the DAG or earlier work was wrong

The prior second reading was correct to refuse arbitrary-monoidal transport:
coordinate invariance is about the SAME derived morphism, and a comparison of
pullback tensorators supplies no square for the localized base-derived source.
The previous proof paragraph claimed such a square without constructing it.
The current delivery removes that claim instead of hiding it in a new theorem.

The original Lean universal quantifier does not specify the source's canonical
induced map. Tag 0DJA(1) uses the canonical transitivity map; the existing canonical
comparison predicate pins exactly that map to the shared counit. The stronger
all-monoidal assertion has not been disproved, and no counterexample is claimed.
Its truth would require additional theory beyond the cited source.

The earlier plan also used a flat inheritance clause absent from the current
DerivedTensorTransitivity signature. The new ring-level lemma states that missing
argument separately. It is strictly part of the argument and is not a renamed
copy of the scheme theorem.

Searches in this session: LeanFinder for uniqueness of strong monoidal structures
on derived scalar extension; Loogle for Functor.Monoidal; launcher grep for the
projection formula; rg across Sheaf, WeilConjectures, and Mathlib for tensorator
transport, coordinate invariance, and monoidal uniqueness. Read the canonical
comparison and realization proofs, the stalk-source transport and naturality
proofs, and QCqsDerivedProjectionMate. The latter gives invertibility of a supplied
mate; it alone does not supply the required source-compatible stalk square.
Read Stacks Tags 0DJA and 08EU online. Earlier logged searches, including the
unavailable LeanSearch response, remain recorded in both new nodes.

Edge cases: the canonical condition still covers arbitrary unbounded E and K,
all integer degrees, all coordinates, zero complexes, and empty schemes. The ring
lemma allows zero rings. Flatness is over A tensor_R B, never over R. The canonical
coordinate predicate imposes no new geometric flatness, boundedness, or finiteness
assumption; it characterizes the specific morphism in the source.

## New nodes

lem-pc-localized-tensor-comparison-inheritance is the ring-level obligation in
Sheaf.Algebra.Homology.LocalizedTensorComparisonInheritance.

lem-pc-tensor-stalk-comparison-squares is the canonical-coordinate obligation in
Sheaf.AlgebraicGeometry.TensorStalkComparisonSquares, now bound to the specified
canonical tensor comparison rather than an arbitrary monoidal instance.

Change record: coord/changes/single-complex-inheritance-canonical-comparison.md.
Both new nodes remain in sec-picard-framework and sk-thm-picard-semicon.

## Statement corrected

The old Lean conclusion quantified over every Functor.Monoidal on derivedPullback.
The corrected conclusion returns a core-monoidal model m whose inverse tensorator
satisfies IsCanonicalPullbackTensorComparison, and inheritance for every E using
that map. Canonical comparison uniqueness identifies it with any other canonical
family tau, so it says exactly the source's induced map.
The DAG statement makes that normalization explicit, and its statement_change
preserves the old statement, dependency lists, proof, source, and both citers.
This is an intermediate statement correction under stage 3 section 3; the five
Challenge statements and all definitions used by them remain untouched.

Both citers still hold: lem-pc-rf-base-change-single-complex-criterion already binds
tau and its canonical predicate, and identifies the returned model with tau by
canonical comparison uniqueness;
lem-pc-tor-independent-perfect-tensor-base-change uses the returned canonical core-monoidal model to cancel its invertible
direct image. Their Lean
statements are unchanged.

## Forced adaptations

Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion (unclaimed): the original
proof against the corrected canonical interface fails because it projects .2 as
if the result were the former conjunction. It now receives m, its canonical
predicate, and inheritance from the corrected theorem. The equation comparing its
inverse tensorator with the already bound tau comes from canonical-comparison
uniqueness. The existing rewrite and induction call remain. No other proof or
signature is changed.

Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange (unclaimed): the
original proof against the corrected interface incorrectly destructures its result
as the former conjunction and then destructures the alleged Nonempty monoidal
instance. The forced edits receive m, discard its canonical predicate, and use
m.toMonoidal. The tensor map, its isomorphism proof, inheritance application,
induction, cancellation, and braiding argument are unchanged. No new import, helper, signature, or visibility change is made in this caller.
The installed monoidal instance has an explicit type annotation; the original
private helpers stay byte-identical.

The final dry run checks the original callers against the compiled baseline and
against the changed dependencies, then checks every adapted signature.

Counterfactual diagnostics collected in this session using lcompile.py against
this sandbox's compiled dependencies (both exited 1):

- Original SingleComplexBaseChangeCriterion.lean:112:20: `Function expected at
  (singleComplexInheritedTensorCondition ... h_stalk).2`; the term has type
  `IsCanonicalPullbackTensorComparison ... ∧ ∀ E, StalkCondition ...`.
  Changed proof lines 110–122 destructure the returned model, canonical predicate,
  and inheritance, then use canonical-comparison uniqueness instead of the old
  realization equation. This is required to recover the caller's already fixed τ.
- Original TorIndependentPerfectTensorBaseChange.lean:223:12:
  `failed to synthesize instance of type class (derivedPullback g').Monoidal`.
  The old nested destructuring extracts the unit isomorphism from the new core
  model. Changed lines 221–223 retain that model and install `m.toMonoidal`;
  the tensorator elaborates against the existing comparison expression. No private
  helper changes.

Validation: deliver3.py --no-push printed OK for commit a5b2c50eb9: all five
delivered modules compiled, the original callers compiled against the baseline
and failed against the changed dependencies, and preflight passed except for the
second reading, which the second reader writes. Nothing was pushed. Completed
axiom probes found no forbidden axiom. The TorIndependentPerfectTensorBaseChange
probe alone reached its 60-second timeout; the delivery tool reported this
explicitly and proceeded to preflight. That caller's ordinary compilation passed.
This is a validation limitation, not a claim that its axiom probe passed. The
earlier compiler-slot blockage was overcome without changing launcher tools or
bypassing their slot limits. A final dry run checks the updated report.

## Earlier second reading (a previous round; superseded)

1. Interface and scope: compared all three existing delivered modules with the
repository by diff. The only changed signature is the declared canonical-comparison
correction of singleComplexInheritedTensorCondition, with its change record and
statement_change. Both caller signatures and all their private helpers are unchanged.
Read Stacks Tags 0DJA(1) and 0BYJ independently: the source uses the induced map,
not every possible monoidal structure. The correction is justified as an intermediate
source correction, not a proof of the former universal assertion. No definition or
Challenge statement is changed. Caller adaptations destructure the new existential
and use canonical uniqueness or its toMonoidal instance; they are necessary.

2. Proof and trust: read the entire five-module delivery. The primary reduction
transfers h_stalk through the first square, cancels b, applies ring inheritance,
and transfers through the second square, cancelling aU. The cancellation directions
and degree quantifiers are correct. The only textual holes are the two reported
public named theorems, each with the entire proof `:= by sorry`. There are no hollow
new definitions, forbidden declarations, or arbitrary witnesses used to define data.
The existential ring representatives are eliminated only inside a proposition proof.
Local compilation and the delivery's all-declaration probes are recorded below.

3. Split statements: checked both signatures against their docstring arguments and
nodes. The ring theorem is a true localizing-subcategory argument on D(A), with
C flat over A tensor_R B; K-flatness is over A, not incorrectly assumed over R.
The geometry theorem constructs simultaneous coordinate squares for the same
canonical map and asserts no horizontal invertibility. K-flat representatives,
a K-injective target, the shared counit, and tensor/stalk naturality give its map.
Identity base change, the tensor unit, zero complexes, zero coefficient ring, and
the empty scheme cause no exceptional assumptions. The ring unit case reduces to
the assumed comparison (up to unit isomorphisms); the zero case is automatic.
Both statements are strictly smaller parts, not renamed copies of the scheme result.
Independent searches used different queries: LeanFinder for derived scalar-extension
comparison and localizing subcategories, and for stalk/pullback/counit commuting
squares; Loogle for IsIso (only generic isomorphism infrastructure); launcher grep
for localizedComparison/cohomologyIso_smul, and rg on both source roots for
inheritance and tensor comparisons. Read BaseDerivedTensorLocalizedNaturality,
DerivedTensorLocalizationCohomology, FlatBaseDerivedTensorComparison, the mixed
K-flat associator and derivedModuleFreeGeneration. None supplies either full new
statement: flat-base comparison requires R-K-flatness, and localization/naturality
does not supply tensor inheritance or both geometric squares. No short closure
of either hole was found.

4. Route and pruning: the primary proof uses existing canonical comparison existence
and monoidal realization before the two split obligations. Its removed old dependency
is exactly lem-pc-derived-tensor-transitivity; the wrapper only returns an associator
and True, so cannot supply inheritance. The criterion's removed proof dependency is
exactly lem-pc-canonical-pullback-tensor-monoidal-realization. Both are listed under
No longer needed. The other caller drops no old proof dependency. The criterion's
unused proof import is removed; the primary new proof imports are private. The new
public imports support
symbols or instances in the new signatures, rather than a proof alone. Read the unit
record: its realized statement and sole step list are empty, so no realized unit
statement or step has been bypassed. Verdict: valid decomposition, no claim of net
sorry reduction (one corrected upper hole replaced by two lower holes).

5. DAG: compared existing node fields, read each proof step and dependency union,
and checked both new lean.statement records against their actual declarations.
The main node records canonical realization, geometric coordinates, ring inheritance,
and cancellation, matching Lean. Caller nodes record their adapted routes. New nodes
have sources, searches, status split, creation metadata, blueprint origin, chapter,
unit and Lean records. The main statement_change records the retired statement and
its citers. Verdict: consistent.

Second reader changes: added this independent review and scratch axiom checks; no
Lean proof, signature, definition, import, or DAG change was necessary.

Second-reader validation: `lcompile.py --all` compiled all five modules with exit
code 0 and no warnings. The scratch `#print axioms` check compiled with exit code
0 and checked singleComplexInheritedTensorCondition,
localizedTensorComparison_inheritance, exists_tensorStalkComparison_squares,
singleComplexBaseChangeCriterion and torIndependent_perfect_tensor_baseChange.
Every output lists only propext, Classical.choice, Quot.sound and sorryAx from the
open dependencies. In particular the adapted Tor-independent caller's direct
axiom check completed, resolving the earlier report's probe limitation for that
public declaration. Logs are in scratchpad/second-reading-compile.log and
scratchpad/second-reading-axioms.log. No mathematical hole was closed by this
second reading, and no new hole was added.

The second-reader dry run printed OK at 958deec2e6: all delivered modules compiled,
the original caller counterfactuals confirmed both adaptations, all-declaration
axiom probes completed without a forbidden axiom, and preflight passed. Review
class is CODEX because of the declared intermediate statement correction, new
nodes/modules and forced adaptations. Delivery follows through deliver3.py.

## Forced adaptations

### Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion
Original against changed dependencies failed:
```
ment
  ⟨E, hE⟩
/tmp/forced-adaptation-s_fraba2/lean/Sheaf/AlgebraicGeometry/SingleComplexBaseChangeCriterion.lean:94:63: error: unsolved goals
inst✝² : (Y : Scheme) → HasDerivedCategory (SheafOfModules (moduleRings Y.toRingedSpace))
X X' S S' : Scheme
f : X ⟶ S
f' : X' ⟶ S'
g : S' ⟶ S
g' : X' ⟶ X
sq : IsPullback g' f' f g
inst✝¹ : QuasiCompact f
inst✝ : QuasiSeparated f
E : schemeDerivedCategory X
hE : schemeDerivedQCohProperty X E
G : CochainComplex (SheafOfModules (moduleRings X.toRingedSpace)) ℤ
hG_qcoh : ∀ (i : ℤ), (G.X i).IsQuasicoherent
h_stalk :
  SingleComplexBaseChange.StalkCondition f f' g g' sq (DerivedCategory.Q.obj G)
    (DerivedCategory.Q.obj (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (ComplexShape.up ℤ)).obj G))
    ((SingleComplexBaseChange.counit g').app
      ((HomotopyCategory.quotient (SheafOfModules (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)).obj G))
τ :
  (A B : schemeDerivedCategory X) →
    (derivedPullback g').obj (A ⊗ B) ⟶ (derivedPullback g').obj A ⊗ (derivedPullback g').obj B
hτ : IsCanonicalPullbackTensorComparison g' τ
b : ℤ
hb x✝ : G.IsStrictlyLE b
hG : schemeDerivedQCohProperty X (DerivedCategory.Q.obj G)
G' : HomologicalComplex X'.Modules (ComplexShape.up ℤ) :=
  ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (ComplexShape.up ℤ)).obj G
hG' : schemeDerivedQCohProperty X' (DerivedCategory.Q.obj G')
m : (derivedPullback g').CoreMonoidal
hm : ∀ (A B : schemeDerivedCategory X), (m.μIso A B).inv = τ A B
this : (derivedPullback g').Monoidal := m.toMonoidal
⊢ IsIso
    (schemeDerivedBaseChangeMap f f' g g' ⋯ (E ⊗ DerivedCategory.Q.obj G) ≫
      (schemeDerivedDirectImage f').map
        (τ E (DerivedCategory.Q.obj G) ≫
          (derivedPullback g').obj E ◁
            (SingleComplexBaseChange.counit g').app
              ((HomotopyCategory.quotient (SheafOfModules (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)).obj G)))

(with the modules compiled into /tmp/forced-adaptation-s_fraba2/.lbuild) [12.3 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange
Original against changed dependencies failed:
```
llback g').obj X_1) ((derivedPullback g').obj Y) ((derivedPullback g').obj Z)).hom ≫
        (derivedPullback g').obj X_1 ◁ (μIso✝ Y Z).hom ≫ (μIso✝ X_1 (Y ⊗ Z)).hom
left_unitality✝ :
  ∀ (X_1 : schemeDerivedCategory X),
    (λ_ ((derivedPullback g').obj X_1)).hom =
      mon.hom ▷ (derivedPullback g').obj X_1 ≫
        (μIso✝ (𝟙_ (schemeDerivedCategory X)) X_1).hom ≫ (derivedPullback g').map (λ_ X_1).hom
right_unitality✝ :
  ∀ (X_1 : schemeDerivedCategory X),
    (ρ_ ((derivedPullback g').obj X_1)).hom =
      (derivedPullback g').obj X_1 ◁ mon.hom ≫
        (μIso✝ X_1 (𝟙_ (schemeDerivedCategory X))).hom ≫ (derivedPullback g').map (ρ_ X_1).hom
hinherit :
  (IsCanonicalPullbackTensorComparison g' fun A B ↦
      ({ εIso := mon, μIso := μIso✝, μIso_hom_natural_left := μIso_hom_natural_left✝,
              μIso_hom_natural_right := μIso_hom_natural_right✝, associativity := associativity✝,
              left_unitality := left_unitality✝, right_unitality := right_unitality✝ }.μIso
          A B).inv) ∧
    ∀ (E : schemeDerivedQCohCategory X),
      SingleComplexBaseChange.StalkCondition f f' g g' sq (E.obj ⊗ { obj := P, property := hPq }.obj)
        ((derivedPullback g').obj E.obj ⊗ { obj := (derivedPullback g').obj P, property := hP'q }.obj)
        (({ εIso := mon, μIso := μIso✝, μIso_hom_natural_left := μIso_hom_natural_left✝,
                  μIso_hom_natural_right := μIso_hom_natural_right✝, associativity := associativity✝,
                  left_unitality := left_unitality✝, right_unitality := right_unitality✝ }.μIso
              E.obj { obj := P, property := hPq }.obj).inv ≫
          (derivedPullback g').obj E.obj ◁ 𝟙 ((derivedPullback g').obj { obj := P, property := hPq }.obj))
this : 𝟙_ (schemeDerivedCategory (pullback f g)) ≅ (derivedPullback g').obj (𝟙_ (schemeDerivedCategory X)) := mon
⊢ IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g) ⋯ (P ⊗ K))

(with the modules compiled into /tmp/forced-adaptation-yilbt3g3/.lbuild) [29.2 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Earlier second reading (a previous round; superseded)

1. Compared all three existing modules with the repository using diff. The only
signature change is the explicitly recorded correction of
AlgebraicGeometry.singleComplexInheritedTensorCondition to a canonical comparison.
The change record and node statement_change disclose the retired universal assertion;
this delivery does not prove it. Both callers preserve every signature and private
helper. Their small proof edits are forced by the corrected existential interface.
No target or definition changes. Verdict: declared intermediate correction only.

2. Read the five delivered modules. The original square transfers invertibility,
then cancellation removes its target isomorphism. Ring inheritance supplies the
tensor comparison; the second square and source cancellation give the conclusion.
All quantifiers and cancellation directions agree. Only the two reported named
public theorems contain sorry. There are no forbidden declarations, hollow definitions,
or data definitions choosing an arbitrary existence witness. Verdict: genuine
reduction, conditional on its two stated lower obligations and existing dependencies.
Fresh compilation and all-declaration axiom checks are required below.

3. Read both split signatures, their complete docstring arguments, and their nodes.
Flatness is over A tensor_R B, while K-flatness is over A; extension of a K-flat
A-complex to C remains K-flat over C. Thus N needs no K-flatness assumption.
For U equal to the tensor unit the ring conclusion is the hypothesis up to unit
isomorphisms; zero U and zero rings are harmless. The geometric bridge asserts only
coordinate squares, without assuming horizontal invertibility, and uses the same
canonical derived morphism. Empty schemes give no point z. Both obligations are
strict parts of the argument. Independently read Stacks Tags 0DJA and 0BYJ online.
New LeanFinder search for preservation of quasi-isomorphisms by K-flat tensor,
Loogle search for Module.Flat, and grep for tensor/localization found generic
exactness infrastructure, not either full obligation. The model equations pin its
maps; arbitrary model choices do not introduce arbitrary comparison maps.
Verdict: true obligations; neither has a short complete proof available here.

4. Checked primary imports and both caller diffs. The primary proof privately imports
the two split obligations and monoidal realization; its canonical-comparison public
import is needed in its new signature. Removed dependencies are documented in
No longer needed: derived-tensor-transitivity for the primary node and canonical
monoidal realization for the criterion. The old transitivity wrapper supplies no
inheritance conclusion. The unit realized record is empty, so this reduction does
not bypass a realized unit step. Verdict: appropriate pruning and an honest
decomposition, with two holes added and no proof of the retired statement claimed.

5. Checked the proof-step dependency unions, sources, creation metadata, blueprint,
chapter, unit and Lean records of both new nodes. The primary node follows canonical
existence, realization, coordinate transport, inheritance and cancellation; caller
nodes follow their adapted proofs. New Lean signature records match the files.
Verdict: DAG agrees with the delivered reduction.

This second reading added this fresh review and independent searches. No Lean or
DAG repair was necessary; no additional mathematical hole was closed or added.

Fresh second-reader axiom validation: the scratch Review.lean compiled through
lcompile.py with exit code 0. All five public declarations printed only propext,
Classical.choice, Quot.sound and sorryAx from open dependencies. This includes
both adapted callers. Log: scratchpad/current-second-reading-axioms.log.

Fresh dry run: deliver3.py --no-push printed OK at 66667dce92. All five
modules compiled, forced caller adaptations passed their counterfactual checks,
and preflight passed with review class CODEX. No axiom-probe limitation was
reported by this run. This remains a decomposition and intermediate statement
correction, with two lower holes, rather than a proof of the retired assertion.

## Forced adaptations

### Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion
Original against changed dependencies failed:
```
ment
  ⟨E, hE⟩
/tmp/forced-adaptation-378chez_/lean/Sheaf/AlgebraicGeometry/SingleComplexBaseChangeCriterion.lean:94:63: error: unsolved goals
inst✝² : (Y : Scheme) → HasDerivedCategory (SheafOfModules (moduleRings Y.toRingedSpace))
X X' S S' : Scheme
f : X ⟶ S
f' : X' ⟶ S'
g : S' ⟶ S
g' : X' ⟶ X
sq : IsPullback g' f' f g
inst✝¹ : QuasiCompact f
inst✝ : QuasiSeparated f
E : schemeDerivedCategory X
hE : schemeDerivedQCohProperty X E
G : CochainComplex (SheafOfModules (moduleRings X.toRingedSpace)) ℤ
hG_qcoh : ∀ (i : ℤ), (G.X i).IsQuasicoherent
h_stalk :
  SingleComplexBaseChange.StalkCondition f f' g g' sq (DerivedCategory.Q.obj G)
    (DerivedCategory.Q.obj (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (ComplexShape.up ℤ)).obj G))
    ((SingleComplexBaseChange.counit g').app
      ((HomotopyCategory.quotient (SheafOfModules (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)).obj G))
τ :
  (A B : schemeDerivedCategory X) →
    (derivedPullback g').obj (A ⊗ B) ⟶ (derivedPullback g').obj A ⊗ (derivedPullback g').obj B
hτ : IsCanonicalPullbackTensorComparison g' τ
b : ℤ
hb x✝ : G.IsStrictlyLE b
hG : schemeDerivedQCohProperty X (DerivedCategory.Q.obj G)
G' : HomologicalComplex X'.Modules (ComplexShape.up ℤ) :=
  ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (ComplexShape.up ℤ)).obj G
hG' : schemeDerivedQCohProperty X' (DerivedCategory.Q.obj G')
m : (derivedPullback g').CoreMonoidal
hm : ∀ (A B : schemeDerivedCategory X), (m.μIso A B).inv = τ A B
this : (derivedPullback g').Monoidal := m.toMonoidal
⊢ IsIso
    (schemeDerivedBaseChangeMap f f' g g' ⋯ (E ⊗ DerivedCategory.Q.obj G) ≫
      (schemeDerivedDirectImage f').map
        (τ E (DerivedCategory.Q.obj G) ≫
          (derivedPullback g').obj E ◁
            (SingleComplexBaseChange.counit g').app
              ((HomotopyCategory.quotient (SheafOfModules (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)).obj G)))

(with the modules compiled into /tmp/forced-adaptation-378chez_/.lbuild) [14.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange
Original against changed dependencies failed:
```
llback g').obj X_1) ((derivedPullback g').obj Y) ((derivedPullback g').obj Z)).hom ≫
        (derivedPullback g').obj X_1 ◁ (μIso✝ Y Z).hom ≫ (μIso✝ X_1 (Y ⊗ Z)).hom
left_unitality✝ :
  ∀ (X_1 : schemeDerivedCategory X),
    (λ_ ((derivedPullback g').obj X_1)).hom =
      mon.hom ▷ (derivedPullback g').obj X_1 ≫
        (μIso✝ (𝟙_ (schemeDerivedCategory X)) X_1).hom ≫ (derivedPullback g').map (λ_ X_1).hom
right_unitality✝ :
  ∀ (X_1 : schemeDerivedCategory X),
    (ρ_ ((derivedPullback g').obj X_1)).hom =
      (derivedPullback g').obj X_1 ◁ mon.hom ≫
        (μIso✝ X_1 (𝟙_ (schemeDerivedCategory X))).hom ≫ (derivedPullback g').map (ρ_ X_1).hom
hinherit :
  (IsCanonicalPullbackTensorComparison g' fun A B ↦
      ({ εIso := mon, μIso := μIso✝, μIso_hom_natural_left := μIso_hom_natural_left✝,
              μIso_hom_natural_right := μIso_hom_natural_right✝, associativity := associativity✝,
              left_unitality := left_unitality✝, right_unitality := right_unitality✝ }.μIso
          A B).inv) ∧
    ∀ (E : schemeDerivedQCohCategory X),
      SingleComplexBaseChange.StalkCondition f f' g g' sq (E.obj ⊗ { obj := P, property := hPq }.obj)
        ((derivedPullback g').obj E.obj ⊗ { obj := (derivedPullback g').obj P, property := hP'q }.obj)
        (({ εIso := mon, μIso := μIso✝, μIso_hom_natural_left := μIso_hom_natural_left✝,
                  μIso_hom_natural_right := μIso_hom_natural_right✝, associativity := associativity✝,
                  left_unitality := left_unitality✝, right_unitality := right_unitality✝ }.μIso
              E.obj { obj := P, property := hPq }.obj).inv ≫
          (derivedPullback g').obj E.obj ◁ 𝟙 ((derivedPullback g').obj { obj := P, property := hPq }.obj))
this : 𝟙_ (schemeDerivedCategory (pullback f g)) ≅ (derivedPullback g').obj (𝟙_ (schemeDerivedCategory X)) := mon
⊢ IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g) ⋯ (P ⊗ K))

(with the modules compiled into /tmp/forced-adaptation-d4o4qhrg/.lbuild) [28.2 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by F4

1. Compared all five delivery modules with the repository (three existing, two new).
   The sole changed existing signature is the declared canonical-comparison correction
   of AlgebraicGeometry.singleComplexInheritedTensorCondition. Its change record and
   statement_change disclose the former universal assertion. Both caller signatures,
   visibility and private helpers are unchanged. The caller diffs only adapt the
   existential interface and remove the criterion's unnecessary realization import.
   No target or definition changes. Verdict: correctly declared intermediate correction,
   not a proof of the retired assertion.

2. Read the entire reduction and both caller proofs. The first commuting square
   transfers h_stalk, target cancellation gives the original ring comparison, ring
   inheritance supplies its tensor analogue, and source cancellation in the second
   square gives the required stalk comparison. The degree and coordinate quantifiers
   are preserved. Fresh lcompile.py --all compiled all five modules with exit code 0
   and no warnings. Exactly the two listed public named theorems have := by sorry;
   no forbidden declaration, hollow definition, or data chosen from mere existence
   is introduced. Existential coordinate representatives are used only in proofs.
   Verdict: genuine reduction conditional on the reported lower obligations.

3. Independently checked both new signatures against their word proofs and nodes.
   Ring flatness is over A tensor_R B, and K-flatness of U,Q is over A. The ring
   assertion follows by mixed derived associativity and exact flat extension, or
   the documented localizing-subcategory argument. The geometry statement gives
   squares for the same canonical map without any horizontal invertibility claim.
   The K-flat/shared-counit equation supplies the required tensor compatibility.
   Unit U reduces to the assumed comparison, zero complexes and zero rings are
   harmless, identity base change specializes correctly, and empty schemes supply
   no stalk point. Read Stacks Tags 0DJA and 0BYJ independently online. Fresh
   LeanFinder search for preservation of a derived base-change comparison under
   K-flat tensor found generic flat exactness only; launcher grep with
   cohomologyIso_smul/localized_eq/stalk tensor and rg over both source roots found
   localization/naturality infrastructure, not either new conclusion. Loogle's
   tensorator and IsIso queries returned unknown-identifier diagnostics, not usable
   matches. Read FlatBaseDerivedTensorComparison, the mixed K-flat associator,
   DerivedModuleFreeGeneration and canonical-comparison equations: the flat-base
   result requires K-flatness over R, stronger than available here. Neither new
   theorem is a renamed copy of the scheme inheritance result, and neither has
   a short closure from those declarations. Verdict: true, needed, strictly smaller
   obligations with complete sourced docstring arguments.

4. Checked imports and old proof_deps against the actual route. The main node
   drops lem-pc-derived-tensor-transitivity; its wrapper returns an associator
   and True, not the needed inheritance conclusion. The criterion drops
   lem-pc-canonical-pullback-tensor-monoidal-realization. Both are reported under
   No longer needed; the other caller drops no old proof dependency. New primary
   proof imports are private, and the canonical-comparison public import supplies
   its signature. New public imports supply statement symbols or required tensor
   instances. The unit sk-thm-picard-semicon has empty realized statement/step
   attachments, so none is bypassed. Verdict: appropriate pruning; decomposition
   with two lower holes, not claimed net sorry reduction.

5. Checked all five node records and dependency unions against their proof steps.
   Both new Lean statement records and the corrected primary record agree verbatim
   with Lean. The new nodes carry sources, searches, split status, creation metadata,
   blueprint origin, chapter, unit and Lean records. In particular C1 is satisfied:
   the geometric proof step explicitly transports to the chosen pullback, invokes
   lem-pc-pullback-stalk-tensor-flat and includes it in proof_deps; the docstring
   records the same argument. Verdict: Lean and DAG agree.

This second reading added a fresh independent review and searches. No Lean or DAG
change was necessary. No additional mathematical hole was closed or added.

Fresh axiom check: the scratch Review.lean imports this sandbox's compiled modules
through its .lbuild link. Its five #print axioms commands compiled with exit code 0;
the primary declaration, both split theorems and both adapted public callers use
only propext, Classical.choice, Quot.sound and sorryAx from open obligations.

This second-reader dry run printed OK at 4082e62131. The delivered modules compiled,
original caller counterfactuals established both forced adaptations, all-declaration
axiom probes completed without a reported limitation or forbidden axiom, and
preflight passed with review class CODEX. C1's geometric flatness dependency is
explicit in both proof_deps and the word proof. Delivery follows via deliver3.py.

## Forced adaptations

### Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion
Original against changed dependencies failed:
```
ment
  ⟨E, hE⟩
/tmp/forced-adaptation-79eo21di/lean/Sheaf/AlgebraicGeometry/SingleComplexBaseChangeCriterion.lean:94:63: error: unsolved goals
inst✝² : (Y : Scheme) → HasDerivedCategory (SheafOfModules (moduleRings Y.toRingedSpace))
X X' S S' : Scheme
f : X ⟶ S
f' : X' ⟶ S'
g : S' ⟶ S
g' : X' ⟶ X
sq : IsPullback g' f' f g
inst✝¹ : QuasiCompact f
inst✝ : QuasiSeparated f
E : schemeDerivedCategory X
hE : schemeDerivedQCohProperty X E
G : CochainComplex (SheafOfModules (moduleRings X.toRingedSpace)) ℤ
hG_qcoh : ∀ (i : ℤ), (G.X i).IsQuasicoherent
h_stalk :
  SingleComplexBaseChange.StalkCondition f f' g g' sq (DerivedCategory.Q.obj G)
    (DerivedCategory.Q.obj (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (ComplexShape.up ℤ)).obj G))
    ((SingleComplexBaseChange.counit g').app
      ((HomotopyCategory.quotient (SheafOfModules (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)).obj G))
τ :
  (A B : schemeDerivedCategory X) →
    (derivedPullback g').obj (A ⊗ B) ⟶ (derivedPullback g').obj A ⊗ (derivedPullback g').obj B
hτ : IsCanonicalPullbackTensorComparison g' τ
b : ℤ
hb x✝ : G.IsStrictlyLE b
hG : schemeDerivedQCohProperty X (DerivedCategory.Q.obj G)
G' : HomologicalComplex X'.Modules (ComplexShape.up ℤ) :=
  ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (ComplexShape.up ℤ)).obj G
hG' : schemeDerivedQCohProperty X' (DerivedCategory.Q.obj G')
m : (derivedPullback g').CoreMonoidal
hm : ∀ (A B : schemeDerivedCategory X), (m.μIso A B).inv = τ A B
this : (derivedPullback g').Monoidal := m.toMonoidal
⊢ IsIso
    (schemeDerivedBaseChangeMap f f' g g' ⋯ (E ⊗ DerivedCategory.Q.obj G) ≫
      (schemeDerivedDirectImage f').map
        (τ E (DerivedCategory.Q.obj G) ≫
          (derivedPullback g').obj E ◁
            (SingleComplexBaseChange.counit g').app
              ((HomotopyCategory.quotient (SheafOfModules (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)).obj G)))

(with the modules compiled into /tmp/forced-adaptation-79eo21di/.lbuild) [11.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange
Original against changed dependencies failed:
```
llback g').obj X_1) ((derivedPullback g').obj Y) ((derivedPullback g').obj Z)).hom ≫
        (derivedPullback g').obj X_1 ◁ (μIso✝ Y Z).hom ≫ (μIso✝ X_1 (Y ⊗ Z)).hom
left_unitality✝ :
  ∀ (X_1 : schemeDerivedCategory X),
    (λ_ ((derivedPullback g').obj X_1)).hom =
      mon.hom ▷ (derivedPullback g').obj X_1 ≫
        (μIso✝ (𝟙_ (schemeDerivedCategory X)) X_1).hom ≫ (derivedPullback g').map (λ_ X_1).hom
right_unitality✝ :
  ∀ (X_1 : schemeDerivedCategory X),
    (ρ_ ((derivedPullback g').obj X_1)).hom =
      (derivedPullback g').obj X_1 ◁ mon.hom ≫
        (μIso✝ X_1 (𝟙_ (schemeDerivedCategory X))).hom ≫ (derivedPullback g').map (ρ_ X_1).hom
hinherit :
  (IsCanonicalPullbackTensorComparison g' fun A B ↦
      ({ εIso := mon, μIso := μIso✝, μIso_hom_natural_left := μIso_hom_natural_left✝,
              μIso_hom_natural_right := μIso_hom_natural_right✝, associativity := associativity✝,
              left_unitality := left_unitality✝, right_unitality := right_unitality✝ }.μIso
          A B).inv) ∧
    ∀ (E : schemeDerivedQCohCategory X),
      SingleComplexBaseChange.StalkCondition f f' g g' sq (E.obj ⊗ { obj := P, property := hPq }.obj)
        ((derivedPullback g').obj E.obj ⊗ { obj := (derivedPullback g').obj P, property := hP'q }.obj)
        (({ εIso := mon, μIso := μIso✝, μIso_hom_natural_left := μIso_hom_natural_left✝,
                  μIso_hom_natural_right := μIso_hom_natural_right✝, associativity := associativity✝,
                  left_unitality := left_unitality✝, right_unitality := right_unitality✝ }.μIso
              E.obj { obj := P, property := hPq }.obj).inv ≫
          (derivedPullback g').obj E.obj ◁ 𝟙 ((derivedPullback g').obj { obj := P, property := hPq }.obj))
this : 𝟙_ (schemeDerivedCategory (pullback f g)) ≅ (derivedPullback g').obj (𝟙_ (schemeDerivedCategory X)) := mon
⊢ IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g) ⋯ (P ⊗ K))

(with the modules compiled into /tmp/forced-adaptation-bj7eedwj/.lbuild) [29.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
