## Worker report

The module `Sheaf.Algebra.Homology.OneKFlatChainTranspose` states
`WeilConjectures.oneKFlatChainTranspose`, with its entire proof `sorry`.
`OneKFlatChainTransposeData` packages precisely the simultaneous comparison and
representative equations asserted by the node; the theorem asserts that this
package exists. It is a conclusion, not a hypothesis supplied by the caller.
There are no definitions containing postponed data and no theorem proofs supplied.

Hypothesis and clause correspondence:

- The site is `C : Type c`, `[Category.{v} C]`, `J : GrothendieckTopology C`.
  Its module universe is `max c v u`, independently of both site universes.
  `HasSheafify` and `WEqualsLocallyBijective` are the standard sheafification
  interfaces for the small-site module category, not additional geometric
  conditions. All site objects and arrows fit in this module universe.
- The coefficient sheaf is `R : Sheaf J CommRingCat.{max c v u}`.
  Every module category is written directly as `SheafOfModules` over the
  underlying ring sheaf, with universe `max c v u`.
  `HasDerivedCategory.{w}` supplies the localization, with arbitrary Hom universe w.
- All complexes are `CochainComplex (PodModules ... J R) ℤ`. There is no truncation,
  boundedness, termwise injectivity, or K-flatness assumption on the first factor A.
- P's K-flatness is the recorded `IsKFlatIndependentCoefficients (R := R) P`.
  Its flat terms are `∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)`.
  E's sole resolution condition is `hE : E.IsKInjective`, using Mathlib's predicate.
- `S : CoefficientClosedStructure (derivedInternalHomOfUniverses ... J R)` and
  `T : CoefficientTensorModels ... J R S` are the given normalized derived
  tensor-Hom structure. They are precisely the data the statement says to use.
  Neither an arbitrary new adjunction nor an unspecified tensor is chosen.
- `comparison` supplies `Q(Tot(A,P)) ≅ S.tensor.obj (QA,QP)`.
  `comparison_normalization` identifies its restriction to K-flat A with
  `T.iso J R S A P hA hP`. That hA occurs only inside this normalization law,
  never as a premise of the theorem or of the arbitrary-A comparison.
  `comparison_naturality` gives the actual simultaneous square for maps in A,P.
  Normalization and naturality determine this comparison uniquely: evaluate
  the naturality square at any flat-term K-flat resolution F→A and cancel its
  localized tensor isomorphism. Thus the existence package specifies the
  canonical comparison rather than an unrelated object isomorphism.
- `uncurry` supplies a chain map `Tot(A,P) ⟶ E` for each f.
  `uncurry_pure` evaluates it on `coefficientTensorGenerator` and equates it to
  the actual product projection `coefficientHomComponent`, applied to f(x),
  then evaluated at `op (Over.mk (𝟙 U.unop))` on y. This is exactly f(a)(p),
  with no sign. It states a formula only on the actual sheafified summand
  generators; it does not claim every global tensor section is pure.
  These formulas determine the chain map uniquely by sheafification and direct sums.
- `transpose_eq` states `c.hom ≫ transpose.symm(h) = Q(uncurry f)` for the
  GIVEN adjunction. Here h is literally Qf followed by Q of the EXISTING
  covariant `homComplexFunctor` map of
  `CategoryTheory.coefficientHomAugmentation` and the inverse
  `coefficientHomResolutionIso`. The augmentation is Hom(P,E→I(E))
  for the very same fixed replacement used
  by `coefficientHomResolution`. `hom_comparison_isIso` asserts that this
  exact identification is invertible when E is K-injective.
- `uncurry_naturality` renders the node's simultaneous a:A'→A, b:P'→P,
  e:E→E' equation. The new f is `a ≫ f ≫ Hom(b,E) ≫ Hom(P',e)`;
  the new uncurrying is `(a tensor b) ≫ uncurry(f) ≫ e`.
  Derived naturality follows by localizing this equality, the comparison
  square and the already fixed natural Hom factorization and adjunction.
- `tensor_inverts` says that quasi-isomorphisms in either representative tensor
  argument give an isomorphism after Q, even when A and A' are not K-flat.
  `hom_inverts` does the same for the actual contravariant/covariant Hom map
  between K-injective targets. Together with the naturality equalities, these
  state agreement with inversion: solve the same squares for any such
  isomorphism's inverse. No new inverse-dependent comparison is chosen.
- `interchange_sign` is the existing `RingedDerivedNative.symmetryPure`.
  Its full definition was read: the ACTUAL native complex braiding maps the
  generator in degrees n,m to `(n*m).negOnePow` times the reversed generator,
  for all integer degrees and every compatible total-degree equality.
  Its source uses exactly `coefficientTotalTensor`'s tensor and generators.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  this is the same Mathlib `SheafOfModules` used by `PodModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, its localization and quasi-iso instance.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` (public through tensor-model import).
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective` (the recorded Mathlib match).
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  the existing `coefficientTotalTensor` is its same uncurry bifunctor.
- `WeilConjectures.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex`,
  `homComplexFunctor`; components from its existing `HomComplexComponents` API.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`: `CoefficientClosedStructure`,
  `.tensor`, `.transpose`, `CoefficientTensorModels`, `.iso`,
  `coefficientTotalTensor`, `coefficientTensorGenerator`.
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`:
  `coefficientHomComponent`, `coefficientHomResolutionIso`, and the fixed
  resolution/factorization read in full.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `def-sfb-ringed-slice-comparison-model`, with the existing declaration
  `CategoryTheory.coefficientHomAugmentation` in
  `Sheaf.Algebra.Homology.RingedSliceEvaluationModels`. Its signature takes
  any unbounded complex E and gives E→I(E), using exactly the fixed resolution
  and its Grothendieck-abelian instance. Applying the covariant
  `homComplexFunctor` gives the same map formerly spelled `podHomAugmentation`.
  Neither the slice-comparison data nor a theorem about them is a premise.
- `def-sfb-tensor-symmetry-pure-equation`, with the existing declaration in
  `Sheaf.Algebra.Homology.RingedTensorComplexConstraints`: `symmetryPure`.
  This is the predicate defining the symmetry clause, not the theorem asserting
  all four complex constraints.
- Proof-only imports retain the recorded K-flat tensor quasi-iso preservation,
  site tensor descent, K-flat resolution, and Hom quasi-iso tools.
  The localization universal-property Mathlib match is already imported transitively.
  The fixed functorial K-injective resolution dependency is likewise already public.

Searches (all performed before writing):

- msearch LeanFinder, “Derived tensor Hom adjunction with arbitrary unbounded
  first complex and K-flat second factor represented by chain evaluation”:
  eight hits, including HasGoodTensor₁₂, HasTensor, HasGoodTensor₂₃ and Tor;
  none gives the normalized one-sided representative statement.
- msearch Loogle, `HomologicalComplex.tensorHom, homTensorCurryEquiv`:
  zero hits; homTensorCurryEquiv is not an identifier.
- msearch grep, `homTensor|tensorHom|KFlat`, Algebra/Homology:
  five hits for tensorHom in Mathlib's Monoidal file, no derived transpose theorem.
- msearch LeanSearch, “K-flat second factor and K-injective target compute derived
  tensor Hom transposition on arbitrary complexes”: eight hits including tensorObj,
  tensorHom, mapBifunctorFlipIso and K-injective transport, no exact statement.
- rg in `lean/WeilConjectures` and `lean/Sheaf`,
  `homTensor|chain.*[Tt]ranspos|oneKFlat|one.*KFlat|coefficient.*[Ss]ymmetr`:
  found ordinary Hom-tensor currying, KFlatRHomCurrying and the coefficient model;
  inspected the HomTensorDegreewiseEquation API and the fixed normalization.
  The former is a complex-valued double-Hom currying assertion, not this extension
  to the fixed derived closed transposition on arbitrary A.
- grep of the item ID in `lean/WeilConjectures` returned no existing statement.
- Further source search found the exact fixed augmentation and Koszul-sign
  predicate used here, so neither is defined again. Checked DAG reachability
  for the original carrier modules; the repaired definition nodes depend only
  on the existing definitions listed below and do not depend on this item.

Edge cases checked against the source and the written type:
zero A, P or E; zero coefficient ring; empty site; degree-zero complexes (ordinary
unsigned evaluation); odd/odd degrees (minus on interchange); characteristic two
(where minus becomes plus); negative degrees (integer negOnePow); arbitrary
non-flat A and complexes unbounded in both directions. No nonempty, nonzero,
characteristic, termwise injectivity, or boundedness restriction is present.
Site and coefficient universes remain independent with the stated maximum convention.

Source read: the local Stacks `sites-cohomology.tex` proof of lemma-internal-hom
(Tag 08J9), explicitly taking any first complex and a K-flat second complex;
the node's seven-step refinement, including the actual-generator calculation,
normalization/cancellation argument, and representative-inversion square.
No statement correction or mathematical dispute is needed.

## New nodes

`def-sfb-tensor-symmetry-pure-equation` registers the existing
`CategoryTheory.RingedDerivedNative.symmetryPure` in
`Sheaf.Algebra.Homology.RingedTensorComplexConstraints` (lines 31–38).
It defines the proposition that the actual braiding takes the actual
(p,q)-generator to `(p*q).negOnePow` times the swapped generator. It asserts
no theorem and duplicates no construction. Its source is Stacks 06YU and
the subsequent commutativity display, reread locally.

The retained search log records LeanSearch with the full homogeneous-sign
query (eight hits including graded tensor swaps and mapBifunctorFlipIso),
LeanFinder for Koszul braiding on pure tensor generators (eight hits starting
with HomologicalComplex.ιTensorObj), and Mathlib grep
`ι_braiding_hom|braiding.*negOnePow` (zero hits). DAG search for
`PodModules|podHomAugmentation|symmetryPure` found theorem carriers but no
owner for this predicate. Blueprint searches for pure tensor symmetry gave
zero matches and Koszul symmetry found only the unrelated supertrace node.
The recorded blueprint ancestor is lem-sfb-dc-hom-preserves via this item and
lem-sfb-dc-hom-filtered-colimit. All original search records are retained.

The formerly proposed `def-sfb-hom-resolution-augmentation` is removed:
the existing definition node `def-sfb-ringed-slice-comparison-model` already
owns the exact fixed augmentation needed here. No dependency module is added.

## Returned-head repair

The returned immutable head was c2bcee5fc184; its return reported missing
published Mathlib artifacts. The required first saved-packet dry run on
2026-10-21 advanced beyond that problem but failed inside the imported
Sheaf.CategoryTheory.RingedSiteDualityMaps at lines 795 and 828 with type
mismatches involving Hom projection evaluation. A separate prescribed
scompile.py reproduced both diagnostics. Neither reached this item's type.

Read-only import-graph inspection identified the path:
DerivedAutomorphismHomEvaluation → RingedInternalHomShiftOfUniverses →
RingedSiteDualityMaps. The ordinary ringed-site augmentation was the only
construction used from that broad automorphism module. Existing
CategoryTheory.coefficientHomAugmentation in RingedSliceEvaluationModels
is the very same toKInjectiveResolution map, using the same instance and
replacement as coefficientHomResolution. Its module has no import path to
the failing dependency. The item now imports this smaller existing module,
maps that augmentation by the existing Hom functor, and writes the module
category directly instead of using the PodModules alias. This is a change
of expression of definitionally identical data, not a new mathematical
statement or a new hypothesis. The unused new augmentation-owner node is
removed and the item cites the already landed definition owner instead.
No library source or launcher tool was edited.

## Second reading by Q05

This dispatcher worker performed the second reading; no second agent was
started. The independent maintainer review remains separate. I reopened
the item, the rewritten module, the retained symmetry node, and the actual
existing augmentation source and its owner record.

The site universes c,v and coefficient parameter u remain independent;
all module sizes are max c v u, with independent derived Hom universe w.
A is still arbitrary and unbounded, P is K-flat with flat terms, E is only
K-injective, and S,T are the given normalized structure and model. Every
field of the conclusion is unchanged: normalized comparison, simultaneous
naturality, unsigned chain evaluation, transpose for the fixed adjunction,
fixed Hom comparison, inverse squares and actual Koszul sign. The Hom
augmentation still goes from Hom(P,E) to Hom(P,I(E)); the existing source
shows it uses precisely the same toKInjectiveResolution and instance as
the old expression. No slice object or slice comparison is required.

The retained edge-case check includes zero complexes and ring, empty site,
arbitrary non-flat A, unbounded complexes, negative degrees, odd/odd sign,
and characteristic two. The theorem signature matches lean.statement
verbatim and its only postponed proof is the named final theorem.

Validation: the prescribed scompile.py type-checked both the sandbox and
library paths (26.9 s and 26.5 s); it flagged only one overlong line. That
line was wrapped. The subsequent deliver2.py --no-push recompiled the final
packet and printed OK at dry-run commit 89c7b68154d: preflight and compiles
passed with no remaining warnings. The final self-check found one sorry,
maximum line length 89, and exact theorem-header/lean.statement agreement.
Only lean and stmt_deps differ from current main. Delivery contains this
module, its node, one existing-definition owner node, and this report.

## Timeout repair of cd2471432eb0

The required first saved-packet dry run reproduced the returned 60-second
file-only timeout, both preliminarily and in the server confirmation. It was
not a stale-base issue. A diagnostic-only profiler run showed that the large
structure field types were being repeated in generated recursors, constructor
injectivity lemmas, projections and size declarations. The profiler setting
has been removed from the delivery.

The module now names the existing field types and propositions as ten public
helper definitions in the same owning module. This is definition factoring,
not splitting the file or increasing the limit. Each helper is the old field
expression with its free comparison/uncurry data bound explicitly; no theorem
or data construction was replaced, and no mathematical hypothesis or equation
changed. Explicit universe arguments pin K-flatness, flatness and Hom to their
already intended site/coefficient universes. The existing eleven structure
fields and final theorem header remain.

## Second reading by Q05

For this repair I reopened the entire item, all statement-dependency records,
their relevant source declarations, the new helper definitions and structure,
and Stacks 08J9 and 06YT. No other agent was started, as the dispatcher requires.
The site/category/coefficient binders and independent c,v,u,w sizes are the
same. The allowed P is still K-flat with flat terms; E is K-injective; A is
arbitrary, unbounded, and may have non-flat terms. S and T are the same fixed
normalized closed structure and its representative model.

The field-to-helper correspondence is exhaustive:

- comparison: OneKFlatChainComparison, the same arbitrary-A tensor isomorphisms.
- comparison_normalization: OneKFlatChainComparisonNormalization, equality with
  the same T.iso for K-flat A, without assuming A K-flat elsewhere.
- comparison_naturality: OneKFlatChainComparisonNaturality, the identical
  simultaneous square for a:A→A' and b:P→P'.
- uncurry: OneKFlatChainUncurry, the same chain-map-valued family for every f.
- uncurry_pure: OneKFlatChainUncurryPure, actual tensor generators and Hom
  product projection evaluated at the identity slice object, unsigned.
- transpose_eq: OneKFlatChainTransposeEquation, the same given adjunction,
  same fixed Hom augmentation, same resolution-factorization inverse.
- uncurry_naturality: OneKFlatChainUncurryNaturality, the same contravariant b
  and covariant e composites, with a:A'→A.
- tensor_inverts: OneKFlatChainTensorInverts, the same localized tensor maps
  for quasi-isomorphisms a,b and the same allowed P,P'.
- hom_inverts: OneKFlatChainHomInverts, the same actual Hom functor maps for
  quasi-isomorphisms b,e between the stated representatives.
- hom_comparison_isIso: OneKFlatChainHomComparisonIsIso, invertibility of the
  exact Hom identification used in transpose_eq.
- interchange_sign remains the existing symmetryPure, with no new definition.

Every helper has a source/blueprint docstring and is registered under the
item's lean.declarations. They only name the item's clauses, so require no
independent definition node. There is still exactly one postponed theorem,
oneKFlatChainTranspose. The original pure-sign definition-owner node is
unchanged. No statement correction is needed. The earlier edge-case checks
remain valid: empty site, zero ring/complexes, degree zero, odd/odd interchange,
negative degrees, characteristic two, and non-flat unbounded A. Searching the
current Sheaf and WeilConjectures sources for the ten helper names found no
existing declaration. Comparing the item JSON with the read-only main copy
found only lean and the already authorized stmt_deps additions changed.

Validation of this repair: the prescribed scompile.py compiled the complete
single file cleanly as Sheaf.Stage2.Sandbox0 in 22.8 seconds and at its library
path in 21.2 seconds, both below the unchanged 60-second limit. The final
self-check confirmed eleven conclusion fields, ten real helper definitions,
exact lean.statement/theorem-header equality, one sorry, maximum line length
98, no profiler setting, and no mathematical node-field changes.

## Reachability repair of fb99135d5498

The required first saved-packet dry run passed on 2026-10-21 at dabe120488d:
preflight and both server file checks passed. The independent immutable-head
return nevertheless identifies a separate DAG defect: the newly introduced
`def-sfb-tensor-symmetry-pure-equation` is not on a target reach and lacks the
required flag. Reading the current configured targets in coord/new-targets.txt
and following statement/proof edges, including merged-node resolution and
former targets, confirms that neither this item nor the new definition is
currently reached. The item still directly cites the definition in stmt_deps.

The repair adds only `import_flags: ["unreachable"]` to that new definition
node, exactly the missing flag identified by the return. Its statement,
dependencies, source, existing Lean attachment and searches are retained.
No existing node's non-Lean fields or Lean source are changed by this repair.
No artificial target dependency or mathematical hypothesis is added.

## Second reading by Q05

For this reachability repair I read the saved node, the full Lean module,
the new definition node and their report against the current main files.
The item still differs from main only in lean and its existing stmt_deps
additions. Its eleven conclusion fields retain arbitrary unbounded A,
flat-term K-flat P, K-injective E, the given S and T, normalized and natural
comparison, unsigned generator evaluation, the fixed derived transpose,
simultaneous chain naturality, representative-inversion clauses, the exact
Hom comparison and the actual Koszul braiding equation. The ten helper
definitions still contain real expressions and the sole postponed proof
is oneKFlatChainTranspose. The theorem signature equals lean.statement,
all universes are bound explicitly and every line has at most 100 characters.
The edge cases and mathematical correspondence recorded above are unchanged.
The sole repair is the new definition's reachability metadata.

## Delivery-tool conflict

The repaired-packet deliver2.py --no-push ran both server file checks and
then refused the metadata repair with this exact server-preflight error:

    (b) new node def-sfb-tensor-symmetry-pure-equation: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

This conflicts with the independent return of fb99135d5498, which requires
this currently unreached new node to be flagged unreachable. The initial
saved packet without the flag passed deliver2.py --no-push but had exactly
the defect cited by that independent return. The sandbox retains the real
repair (the flag) and the saved Lean module; nothing was pushed. Under the
launcher's explicit rule for a wrong gate refusal, no launcher script or
project tool was edited, copied, patched or bypassed. The maintainer needs
to permit or set this reachability field when merging this new definition.

## Saved-packet retry after the dispatcher tool-failure return

On 2026-10-21 this repair worker reopened the retained report, new definition
node, item record and Lean module, and ran the required first saved-packet
command `deliver2.py Q05 lem-sfb-hom-kflat-chain-transpose --no-push`.
It again exited 1 after the server checks and staged-packet preparation,
with exactly one preflight reason:

    (b) new node def-sfb-tensor-symmetry-pure-equation: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

The sandbox retains `import_flags: ["unreachable"]`, the concrete repair of
the immutable-head fb99135d5498 return. Removing it would restore that
reported DAG defect. The item still differs from the current read clone
only in lean and the authorized stmt_deps additions; the recorded signature
is verbatim in the retained Lean file. No source, statement, tool or launcher
script was changed, and nothing was pushed. This is the same wrong gate
refusal, requiring the maintainer to permit or supply the flag at merge.

## Saved-packet retry, dispatcher attempt 4

On 2026-10-21 the required first saved-packet dry run again ran the two
server Lean file checks and reached server preflight, then exited 1 with
exactly the same single refusal:

    (b) new node def-sfb-tensor-symmetry-pure-equation: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

The retained new node still carries `import_flags: ["unreachable"]`, which
repairs the independent return for immutable head fb99135d5498. Removing
this flag would restore the returned reachability defect. The current read
clone has no such new definition node; comparison of the item with that clone
shows only lean and the authorized stmt_deps additions changed. The retained
Lean signature matches its node record verbatim, with one sorry and maximum
line length 98. No Lean or node content needed a new change on this retry.
No tools were modified or bypassed, and nothing was pushed. The delivery
gate must permit the required flag, or the maintainer must supply it at merge.


## Saved-packet retry, dispatcher attempt 5

On 2026-10-21 this worker ran the prescribed first saved-packet dry run,
`deliver2.py Q05 lem-sfb-hom-kflat-chain-transpose --no-push`.
It performed the server file checks and staged the retained packet, then
exited 1 at stage-2 preflight with the same single diagnostic:

    (b) new node def-sfb-tensor-symmetry-pure-equation: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

The retained `import_flags: ["unreachable"]` is the repair specifically
required by the immutable-head fb99135d5498 return. This remains an actual
wrong gate refusal: the required flag cannot pass the prescribed delivery
wrapper. Per the launcher's explicit tool-failure rule, no tool was patched
or bypassed and the flag was retained. Nothing was pushed.

The read-clone comparison again found only lean and the authorized stmt_deps
additions different in the item; the new definition is absent from that clone.
The recorded theorem signature is verbatim in the module, which retains one
sorry and maximum line length 98. No mathematical or Lean change is needed
to resolve this metadata-gate conflict. The maintainer must permit the flag
in the new-node gate or provide the flag during the merge.

## Saved-packet retry, current dispatcher repair

On 2026-10-21 the required saved-packet dry run again completed its
server file checks and staged the packet, then exited 1 at preflight:

    (b) new node def-sfb-tensor-symmetry-pure-equation: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

The saved reachability repair remains `import_flags: ["unreachable"]`.
Removing it would reintroduce the explicit immutable-head fb99135d5498
return. The current read-clone comparison found only lean and stmt_deps
changed in the item, with the new definition still absent upstream. The
recorded theorem signature matches its source verbatim; the module has
one sorry, explicit autoImplicit false, and maximum line length 98.
No tool was edited or bypassed and nothing was pushed. The prescribed
wrapper must permit the required flag or the maintainer must supply it.

## Saved-packet retry, 2026-10-21 final gate confirmation

The required first dry run again completed both server Lean file checks, then
failed preflight with exactly one reason:

    (b) new node def-sfb-tensor-symmetry-pure-equation: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Read-only inspection confirms the conflict: tools/check_dag.py requires
`unreachable` in import_flags for a node outside the target/former-target
closure; brief-stage2 section 5 and server preflight forbid that field on
a new definition node. The retained flag repairs the immutable-head return.
Removing it would repeat the returned defect. No mathematical correction,
artificial target dependency, tool modification or bypass is appropriate.
The new node and module are retained unchanged; the item's differences from
the read clone remain lean and authorized stmt_deps additions only. The
recorded signature matches the Lean source, with one sorry and maximum line
length 98. Nothing was pushed. The maintainer must permit this field in the
gate or supply it during merge before this packet can be delivered.

## Saved-packet retry, current server-gate verification

The required first dry run completed its two server Lean file checks and
failed preflight with one reason:

    (b) new node def-sfb-tensor-symmetry-pure-equation: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

The server checked delivery base fd1f7e596 and accepted the item's landed
statement-dependency addition. The retained unreachable flag is precisely
the reachability repair requested at immutable head fb99135d5498. Read-only
inspection of check_dag.py and the stage-2 field contract confirms that
removing the flag would restore the returned defect. The read-clone
comparison shows only lean and stmt_deps differ in the item; the symmetry
node is new. The theorem signature remains verbatim, with one sorry and
maximum line width 98. No source, DAG statement or launcher tool was changed;
no gate was bypassed and nothing was pushed. This remains a tool refusal
requiring maintainer resolution of the contradictory metadata gates.

## Saved-packet retry, 2026-10-21 dispatcher verification

The prescribed first saved-packet dry run completed the server Lean file
checks, staged the retained packet, and failed stage-2 preflight with one
reason:

    (b) new node def-sfb-tensor-symmetry-pure-equation: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Read-only verification of tools/check_dag.py, lines 131–135, confirms that
the immutable-head return requires exactly the retained unreachable flag.
The stage-2 preflight contract treats import_flags as a maintainer field,
and the live wrapper still refuses it on this new definition. Removing the
flag would restore the reported defect; no tool was edited or bypassed.
The current read-clone comparison and signature checks are unchanged:
only lean and stmt_deps differ in the item, its recorded signature occurs
verbatim, and its module has one sorry and maximum line length 98.
No mathematical or Lean change resolves this contradictory gate. Nothing
was pushed; delivery requires the gate to accept the requested flag or
the maintainer to supply it at merge.


## Saved-packet retry against base 937ccdd5c

On 2026-10-21 the required first saved-packet dry run completed the server
Lean checks and exited 1 at stage-2 preflight with exactly one refusal:

    (b) new node def-sfb-tensor-symmetry-pure-equation: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

The wrapper checked base 937ccdd5c and accepted the added landed statement
dependency. The retained import_flags: ["unreachable"] repairs the independent
return of fb99135d5498; removing it restores that return's defect. Read-only
inspection of tools/check_dag.py confirms that an unreached node requires
this flag, while brief-stage2 section 5 forbids additional new-node fields.
No authorized packet change resolves these contradictory requirements.
The launcher explicitly forbids patching or bypassing a wrong delivery gate.

The self-check confirmed that only lean and stmt_deps differ in the item
from the current read clone, its recorded signature is verbatim in the file,
and the Lean module retains one sorry, explicit autoImplicit false and
maximum line width 98. The required flag and Lean source remain unchanged.
Nothing was pushed. The gate must allow the repair, or the maintainer must
apply the required reachability metadata at merge.


## Saved-packet retry against base a1c8ee208

On 2026-10-21 this dispatcher worker inspected the retained report and ran
the required first saved-packet dry run. The server Lean checks completed;
stage-2 preflight then exited 1 with exactly one refusal:

    (b) new node def-sfb-tensor-symmetry-pure-equation: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

The wrapper checked base a1c8ee208 and accepted the added landed statement
dependency. The retained unreachable flag repairs the immutable-head
fb99135d5498 return. Read-only inspection of tools/check_dag.py confirms
that an unreached node without that flag fails DAG validation. Removing
the flag would therefore restore the returned defect. The launcher forbids
patching or bypassing this wrong gate refusal; no tool was modified.

The self-check confirmed that only lean and stmt_deps differ in the item
from the current read clone, its recorded signature is verbatim in the
module, and the module retains one sorry, explicit autoImplicit false,
and maximum line width 98. No mathematical or Lean change is needed for
this metadata conflict. The repaired packet remains in the sandbox and
nothing was pushed. The gate must permit the flag, or the maintainer must
supply the required reachability metadata at merge.


## Reachability repair on the current base, 2026-10-21

The mandatory first saved-packet dry run reproduced the rejection of
`import_flags` as a maintainer-only field after its server Lean checks.
Unlike the earlier retries, the current configured DAG now reaches the
item AND its new symmetry definition. This was checked read-only with
`dag_queue.Dag._graph` and `distances_from`, using the configured ten target
roots, the former target root, and the packet node overlay. The traversal
uses the project's unsplit-node and merged-node rules. Both nodes occur
in its result. Consequently the historical unreachable flag is now wrong:
check_dag.py would reject it as flagged unreachable but reached.

Removed only `import_flags` from the new definition node. This resolves
both the stage-2 field refusal and the returned reachability defect on
the current base. The old report's statements that removal necessarily
restores the defect describe the old bases and are superseded by this
current reachability check. No artificial dependency, statement change,
Lean source change, or tool modification was made.

The saved module was reopened and its recorded theorem signature is still
verbatim. The module has one sorry, explicit `autoImplicit false`, and a
maximum line width of 98. Only `lean` and the authorized `stmt_deps`
additions differ in the item from the current read clone. The first dry
run compiled the saved Lean packet; the final dry run below checks it
again against the current server base before delivery.


## Final current-server validation

The final saved-packet dry run printed:

    OK (dry run): commit a6ff3b55c72 passes the preflight and compiles; nothing pushed

The refreshed server base now already contains
`def-sfb-tensor-symmetry-pure-equation`. It is therefore no longer a new
node in this delivery. The wrapper explicitly preserved its maintainer
`import_flags` metadata and staged only the item node, its Lean module,
and this report. Thus the earlier read-clone overlay reachability check
is not a request to overwrite server metadata: the server's prescribed
preflight validated the effective landing delta against its authoritative
branch and passed. The retained definition node copy merely registers the
existing declaration and contributes no new-node metadata delta.

The read-clone overlay witness is
`nt-target-poincare-isiso → sk-def-sfb-dc-restricted-functors →
lem-sfb-dc-hom-preserves → lem-sfb-dc-hom-small-coefficients →
lem-sfb-qlbar-internal-hom-coefficient-comparison →
lem-sfb-dc-hom-filtered-colimit → lem-sfb-hom-kflat-chain-transpose →
def-sfb-tensor-symmetry-pure-equation`.
The authoritative server preflight, rather than this clone witness, is
the final check of the server's configured reachability and metadata.
No library or tool was edited. The module and theorem statement are
unchanged from the saved packet, and all per-file server checks passed.
