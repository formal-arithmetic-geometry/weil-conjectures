## Worker report

The delivery states lem-sfb-adic-stratum-completion-unit in
`Sheaf.Paper.AdicStratumCompletionUnit`. There are two postponed theorems:
`AlgebraicGeometry.Scheme.SfbAdicRestriction.adicStratumCompletionUnit` (restriction)
and `adicStratumCompletionUnit_detection` (detection). Both have source citations
and full natural-language proofs following the five DAG proof steps. The other
declarations have actual data. No statement, dependency list or proof was changed.
No new nodes or dependency modules are required.

Hypothesis and conclusion correspondence:

- A scheme and its finite Noetherian affine cover are `X : Scheme.{u}` and
  `[IsNoetherian X]`, Mathlib's Noetherian-scheme predicate. The coefficient
  hypotheses are `A : Type (u + 1)`, `[CommRing A]`, `[IsNoetherianRing A]`,
  `I : Ideal A`, `r : ℕ`, `a : Fin r → A`, and
  `ha : Ideal.span (Set.range a) = I`. The finite enumeration includes zero
  generators and repeated generators. There is no regular-sequence hypothesis.
- The small pro-etale site is the recorded `Scheme.ProEt`, with topology
  `ProEt.topology`. We use its recorded equivalent `proEtaleSiteModel` and
  `proEtaleModelTopology` to apply the small-category coefficient framework.
  `modelEquivalence` is explicitly made from AsSmall.up/down sheaf pushforward.
  This transports the site; it does not identify the original site's object
  universe u+1 with its morphism universe u. Coefficients use the framework's
  ambient u+1 universe, and derived categories use its standard localization.
- `ConstantCompletion.completed J A I` is exactly B_T, the limit of the constant
  A/I^(n+1) sheaves. Thus index n=0 means the first quotient A/I, not A/I^0.
  We reuse the dependency's `constant`, `finite`, `projection` and `completed`;
  no completion object or notion of constant sheaf is redefined here.
- A locally closed immersion is `i : S ⟶ X` with `[IsImmersion i]`.
  `inverse i` and `direct i` transport the recorded actual sheaf inverse/direct
  image, with the transported `proEtaleSheafAdjunction`. The finite-limit
  instance is inherited from the immersion-limit-preservation dependency.
  `F : ConstantCompletion.InverseImageData (inverse i)` supplies the algebraic
  realization of this *fixed* geometric functor. It does not permit a different
  map or a different inverse image. Such data exist by the dependency's
  `inverseImageData_exists`; the theorem holds for every realization.
- The first conjunct of `UnitRestriction` is
  `IsIso (ConstantCompletion.completedMap F A I)`. That map is the dependency's
  limit lift of the finite projections, using its constant-section comparisons.
  This is the specified canonical i^-1 B_X → B_S, not an arbitrary isomorphism.
- Slice restriction is `sliceAlgebra J U`. Its ring and set functors are exactly
  `J.overPullback`, and its module functor is exactly
  `SheafOfModules.overFunctor (siteModuleRings O) U`, with identity underlying
  comparisons. All ring and module operations are explicitly evaluated on the
  underlying object of the slice. `sliceDirect` and `sliceAdjunction` use the
  canonical cocontinuous localization adjunction for `Over.forget U`.
- `completedPull` is the dependency's universal derived module pullback along
  `completedMap`. In the slice case it derives precisely the overFunctor just
  specified, followed by the canonical coefficient identification. The second
  conjunct of `UnitRestriction` asserts that its comparison on *every* complex
  is invertible, so this is the exact termwise restriction, with no boundedness
  or K-flat restriction imposed on the object M. This is the derived slice
  functor of the recorded restriction node, expressed through the normalized
  universal pullback interface rather than a new localization choice.
- The third conjunct quantifies over the dependency's actual
  `KoszulPresentation J A I true r a` and the corresponding target presentation.
  It supplies a natural completion comparison e and explicitly asserts
  `completedPull.map (koszulUnit ... M) ≫ e.hom.app M = koszulUnit ... (FM)`.
  These are the dependency's actual strict augmented Koszul completion units.
  This is a statement about the units themselves, not only their target objects.
  The dependency supplies the presentations under the displayed hypotheses.
- `finiteComparison` is a concrete composite of `finiteDerivedComparison` and
  `completedFinitePull_existsUnique`, in the actual A/I^(n+1) coefficient
  categories. The latter is uniquely normalized on K-flat representatives;
  it is not an arbitrary selected isomorphism. The fourth conjunct of
  `UnitRestriction` gives the equation relating this comparison to the
  dependency's `finitePull` and `derivedPullComparison`. Those maps retain
  their scalar-insertion/representative normalization. This expresses
  commutation with the canonical finite derived reductions for every n≥1.
- The final conjunct of `UnitRestriction` preserves
  `ConstantCompletion.IsComplete (projection J A I 0) M`. This abbreviation
  uses the recorded `IsLocallyDerivedRingedIdealComplete`, with the kernel of
  B→constant(A/I). By `flat_and_quotients` this kernel is the ideal IB in the
  node. No alternative global or cohomological completeness predicate is used.
- `adicStratumCompletionUnit` asserts `UnitRestriction` for every immersion
  and every further slice object. Composing these two clauses gives M|_U.
- The detection theorem uses the recorded
  `Scheme.FiniteLocallyClosedStratification X`, with its actual domains,
  immersion morphisms, disjointness and covering conditions. A chosen cover
  on each stratum is `V α`, a sieve on the terminal object, with `hV` asserting
  membership in `proEtaleModelTopology`. Any chosen pro-etale covering family
  gives its generated covering sieve. Testing the sieve is equivalent to
  testing that family: further restrictions preserve completeness by the
  first theorem, and the generators themselves lie in the generated sieve.
  The conclusion is precisely the iff between completeness of arbitrary M
  and completeness on every `stratumSlicePull` indexed by an arrow in V α.
  `stratumSlicePull` is the explicit composite immersion/slice restriction.

Dependency declarations read and used (module; declaration):

- Mathlib.AlgebraicGeometry.Scheme; `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Noetherian and Mathlib.RingTheory.Noetherian.Defs;
  `AlgebraicGeometry.IsNoetherian`, `IsNoetherianRing`.
- Mathlib.AlgebraicGeometry.Sites.Proetale; `Scheme.ProEt`, `ProEt.topology`.
- Mathlib.CategoryTheory.Sites.ConstantSheaf; `CategoryTheory.constantSheaf`,
  used by the ConstantCompletion definitions and the slice constant comparison.
- Sheaf.CategoryTheory.RingedSiteModules; `CategoryTheory.ringedSiteModules`,
  used by `ConstantCompletion.Mod` and the actual `SheafOfModules.overFunctor`.
- Mathlib.Algebra.Homology.DerivedCategory.Basic; `DerivedCategory`,
  `HasDerivedCategory`, via the recorded `ConstantCompletion.D` and `Q`.
- Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete;
  `CategoryTheory.IsLocallyDerivedRingedIdealComplete`, via `IsComplete`.
- Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral;
  `ringedDerivedRestrictionGeneral` and `ringedOverFunctor_exactGeneral`:
  exact derived localization of the same overFunctor used in `sliceAlgebra`.
- Sheaf.Paper.ConstantCompletionEquivalence;
  `CategoryTheory.ConstantCompletion.equivalence` and its recorded canonical
  coefficient, pullback, finite comparison, Koszul and completeness interfaces
  named above. All finite comparisons are the existing normalized comparisons.
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel;
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`, the universal
  derived extension interface underlying the recorded change-of-ring functors.
- Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification;
  `Scheme.FiniteLocallyClosedStratification`.
- Sheaf.AlgebraicGeometry.ProEtaleInverseImage;
  `Scheme.proEtaleSheafInverseImage`, `proEtaleSheafDirectImage`,
  `proEtaleSheafAdjunction`, `proEtaleSiteModel`, `proEtaleModelTopology`.

The proof-tool modules for immersion limits, weakly-etale localization, the
object inverse-image/slice comparison, normalized strict Roos, additive Roos,
exact products, canonical tensor pullback and Noetherian stratum detection
are imported. The docstrings specify how their statements prove each clause.

Edge cases checked against the formulas and the source: empty X, empty strata,
the zero ring, I=0, no generators r=0, I=A, redundant or repeated generators,
finite quotients with infinite projective dimension, and unbounded M. No
nonemptiness, constructibility, perfectness, boundedness, principal-ideal,
regularity or finite-coefficient hypothesis has been added. Empty cases are
handled by the empty-cover sheaf axiom; r=0 uses the empty Koszul tensor.

Sources read: the node and all its statement dependencies with their recorded
Lean signatures/docstrings; Bhatt--Scholze Lemma 6.5.8, Remark 6.5.10 and
Proposition 6.6.11; local Stacks proetale.tex Tags 099L/099M and algebraization.tex
Tag 0A0E. The blueprint provenance and the node's full five-step proof were
checked. There is no STATEMENT-DISPUTED finding.

Searches made before introducing helpers:

- msearch.py leanfinder: "Restriction to locally closed pro etale strata
  commutes with the Koszul completion unit and finite reductions". Eight
  ordinary scheme restriction/adic-completion hits; no matching theorem.
- msearch.py loogle: "SheafOfModules, IsAdicComplete". Zero hits.
- msearch.py grep:
  "(strat|immersion).*(complet|koszul)|(complet|koszul).*(strat|immersion)".
  Zero Mathlib hits.
- Local rg in lean/WeilConjectures and lean/Sheaf for stratum/immersion,
  completion, Koszul and the exact item id; exact-id grep in WeilConjectures.
  No exact statement. The existing ConstantCompletion interfaces supply the
  notions. CompletedExchange treats a different fixed coefficient situation;
  AdicStratifiedPerfect is downstream and is not imported.
- DAG search found the analogous unsupplied
  lem-weil-pbc-stratum-completion-unit-restriction, not an existing Lean
  declaration. No new independent mathematical notion was needed. The helpers
  in this module construct the item's canonical maps and package its clauses.

Validation: scompile.py compiled the complete module against the live published
library, with no errors or unexpected warnings. Every universe and variable is
explicitly bound (`autoImplicit false`).

## Second reading by Q33

I reread the final node and module together. This is a self-review: the dispatch
explicitly prohibits starting other agents; the maintainer's independent review
follows delivery. The coefficient map is the finite-projection map, the Koszul
unit equation has the correct direction, finite exponent indexing is n+1, and
the last theorem tests actual composite restrictions rather than arbitrary
functors. I checked that no proof has silently replaced the actual unit with
an unspecified map. During elaboration I removed a redundant attempted second
derived-localization presentation of slice restriction: its instance-dependent
category types did not identify definitionally with the recorded completion
framework. The final file uses the existing universal derived pullback of the
actual overFunctor and states invertibility on every complex. It thereby
retains precisely exact slice restriction and its canonical coefficient map.
The theorem statements and the source hypotheses agree clause by clause as
listed above; no node correction was required.

## Delivery tool failure

The prescribed `deliver2.py ... --no-push` was run twice. Both attempts failed
before module/preflight review while compiling the overlay dependency
`Sheaf.CategoryTheory.RingedSiteModules`: `unknown module prefix 'Mathlib'`.
The printed search path contained only the live project's build directory and
the Lean toolchain, with no Mathlib directory. The automatic server confirmation
then reported `Live published library is unavailable`. Nothing was pushed.
The earlier direct scompile.py run of this module completed successfully
(13.8 seconds for the library module). No launcher scripts or upstream files
were edited to work around the unavailable compilation environment.

## Retry validation on 2026-10-21

Retained the saved packet and began with the required `deliver2.py Q33
lem-sfb-adic-stratum-completion-unit --no-push`. It exited 1 before checking the
item: the overlay dependency `Sheaf.CategoryTheory.RingedSiteModules` failed at
line 6 with `unknown module prefix 'Mathlib'`. The compiler search path listed
only the live project's build directory and the Lean toolchain. Its automatic
server confirmation reported `Live published library is unavailable`.

A separate prescribed `scompile.py Q33 lem-sfb-adic-stratum-completion-unit`
invocation on `lean/Sheaf/Paper/AdicStratumCompletionUnit.lean` reproduced the same
missing-Mathlib error and unavailable-library server confirmation, exiting 1.
This is an environment/tool failure before the item's elaboration, rather than
a diagnostic repairable in the packet. No Lean or node files, shared sources,
launcher scripts or compiler settings were changed; nothing was pushed.

## Further retry validation on 2026-10-21

Started with the retained packet and the required `deliver2.py Q33
lem-sfb-adic-stratum-completion-unit --no-push`. It exited 1 while compiling
the overlay prerequisite `Sheaf.CategoryTheory.RingedSiteModules`, before
elaborating this item's module. The diagnostic now identifies a missing
published Mathlib artifact rather than an unknown prefix:
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Abelian.olean` does not exist under
`/home/ubuntu/weil-conjectures-sheaf/lean/.lake/packages/mathlib/.lake/build/lib/lean/`.
The wrapper's server confirmation again reported
`Live published library is unavailable`.

The prescribed direct `scompile.py Q33 lem-sfb-adic-stratum-completion-unit`
on the retained `lean/Sheaf/Paper/AdicStratumCompletionUnit.lean` reproduced
the identical missing-artifact diagnostic and server confirmation, exiting 1.
This is a published-build/tool failure before the packet is checked; changing
the statement or its imports cannot supply that required Mathlib artifact.
The Lean module and node packet are retained unchanged. No live files,
launcher scripts, compiler settings or published artifacts were modified;
nothing was pushed.

## Dispatcher retry validation on 2026-10-21

Retained the saved packet and read the report before running the required
`deliver2.py Q33 lem-sfb-adic-stratum-completion-unit --no-push`.
The dry run exited 1 in the prerequisite `Sheaf.CategoryTheory.RingedSiteModules`
at line 6, before this item's elaboration: the published artifact
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Abelian.olean` does not exist.
The automatic server confirmation reported `Live published library is unavailable`.
A direct prescribed `scompile.py` invocation on the saved
`lean/Sheaf/Paper/AdicStratumCompletionUnit.lean` independently reproduced that
same missing-artifact diagnostic and unavailable-library confirmation (exit 1).
The dependency's required published Mathlib artifact cannot be repaired in this
packet. The Lean module and node remain unchanged; no shared source, launcher
script or published artifact was modified, and nothing was pushed.

## Final dispatcher retry on 2026-10-21

Read the retained report and ran the required dry run first:
`deliver2.py Q33 lem-sfb-adic-stratum-completion-unit --no-push`.
The wrapper waited for concurrent dependency compiles, then reported a 60-second
timeout in `WeilConjectures.Algebra.Homology.HomComplexSectionsCochains`.
Its automatic server confirmation failed earlier in the prerequisite
`Sheaf.CategoryTheory.RingedIdealGenerators` at line 6: the published object file
`/home/ubuntu/weil-conjectures-sheaf/lean/.lake/build/lib/lean/WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean`
does not exist.

Ran the prescribed direct `scompile.py Q33
lem-sfb-adic-stratum-completion-unit` on the retained
`lean/Sheaf/Paper/AdicStratumCompletionUnit.lean`. Both its local overlay compile
and automatic server confirmation reproduced the identical missing-object-file
error in `RingedIdealGenerators`, exiting 1 before this item's elaboration.
The missing published prerequisite is a compilation-environment failure; no
statement or import repair in this packet can supply that artifact. No timeout
limit, launcher script, published artifact or shared source was changed.
Nothing was pushed.

The saved Lean module is retained unchanged. Self-check confirmed its recorded
main signature matches verbatim, every line is within 100 characters, and the
two postponed theorem proofs remain `sorry`. Refreshed the sandbox node's
unchanged metadata from the current read-only node, retaining the saved `lean`
record; the sandbox node now differs from that current node only in `lean`.

## Retained-packet retry on 2026-10-21

Read the retained report and ran the required `deliver2.py Q33
lem-sfb-adic-stratum-completion-unit --no-push` before making changes.
It exited 1 in the prerequisite `Sheaf.CategoryTheory.RingedIdealGenerators`,
line 6, before elaborating the item: the published object file
`WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean` is missing.
The wrapper's automatic server confirmation reproduced the same diagnostic.
A separate prescribed `scompile.py` invocation on the retained module also
exited 1 with the identical missing-artifact error, confirmed on the server.
This is the same published-build failure recorded by the previous attempt;
there is no packet elaboration diagnostic to repair. The module and node are
retained unchanged, and nothing was pushed. No shared sources, launcher scripts,
compiler limits or published artifacts were modified.

## Successful retained-packet validation on 2026-10-21

The required initial `deliver2.py Q33 lem-sfb-adic-stratum-completion-unit --no-push` completed successfully: its current-server confirmation compiled the retained module and the preflight printed `OK (dry run)`, commit `8fa7604f38b`. The local overlay had reported a missing `Sheaf.Paper.RingedTopoiDerivedPullback.olean`; the prescribed automatic server confirmation resolved that local failure.

Retained the Lean module unchanged. Reread the complete module against the current node: the canonical coefficient map, actual Koszul-unit equation, finite derived reductions, completeness preservation, and finite-stratum cover detection remain as mapped above. The node differs from the current read-only source only in `lean`; its signature is verbatim, JSON formatting is canonical, all Lean lines are at most 100 characters, and the two theorem proofs remain `sorry`. No new nodes, dependency repairs, or statement correction were necessary.

## Return L: compilation timeout repair on 2026-10-21

The required first dry run of the saved packet reproduced the return: both the
sandbox compile and current-server confirmation timed out after 60 seconds.
A temporary profiler run then completed, showing substantial type-checking and
linting costs (sandbox: 29.3 seconds cumulative type checking and 27.6 seconds
cumulative linting; wall time 48.3 seconds). The profiler option was removed.

The repair gives explicit source/target functor types to `inverse`, `direct`,
`completedPull`, `stratumPull`, and `stratumSlicePull`. The last three now use
regular definitions instead of reducible abbreviations. Their bodies are unchanged.
The module also makes `ConstantCompletion.completed` and
`ConstantCompletion.derivedPull` locally irreducible, following the dependency
module's own unfolding controls. In particular the immersion instance remains
inside the body of `stratumPull`, rather than its inferred public result type.
No timeout, coefficient universe, canonical map, theorem signature, mathematical
hypothesis or conclusion was changed. No new theorem, node or import was added.

Self-review of the patch against the retained module confirms that these are
only explicit type annotations and unfolding controls. The coefficient map
remains the finite-projection lift; the Koszul-unit equation and normalized
finite-reduction equation are unchanged; completeness still means the recorded
local internal-Hom predicate; detection still tests all arrows in the chosen
covering sieves on the actual finite strata. Empty strata, zero generators and
unbounded complexes remain included. The two theorem proofs remain `sorry`.

The first explicit-type patch still timed out in the library-form check. The
final repair additionally controls local unfolding of `HasDerivedCategory.standard`,
`modelEquivalence`, `inverse`, `direct`, `adjunction`, `sliceAlgebra`,
`sliceAdjunction`, `completedPull`, `finiteComparison`, `stratumPull`, and
`stratumSlicePull`. These local attributes do not change any definition body
or exported mathematical statement. The prescribed `scompile.py` then passed
both the sandbox form (34.3 seconds) and library form (34.8 seconds), with no
errors or warnings. Both theorem signatures are textually identical to the
retained signatures, the node differs from the current read-only source only
in `lean`, JSON formatting is canonical, and every Lean line is within 100
characters. No profiler or diagnostic command remains in the module.
