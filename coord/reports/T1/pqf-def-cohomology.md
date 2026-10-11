## Worker report

The module defines `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages` for a scheme. Its first conjunct expresses that the cohomology functors are the right derived global-sections functors and form a universal cohomological delta-functor, which supplies the long exact sequence for short exact sequences. The second conjunct identifies the derived direct image with the right-derived functor of module direct image for every ringed-space target and morphism from the scheme's underlying ringed space; the required derived-category instances are explicit binders.

The scheme hypothesis is the explicit `(X : Scheme.{u})`. The cohomology category is `SheafOfModules (moduleRings X.toRingedSpace)`, and the target is `ModuleCat ((moduleRings X.toRingedSpace).obj.obj (op ⊤))`. The right-derived family is `(RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerived`. Universality is `G.IsUniversal`. Higher direct images are rendered by `RingedSpace.derivedModuleDirectImage g = (RingedSpace.moduleDirectImage g).rightDerivedFunctor`.

Dependencies used: `Sheaf.Topology.RingedSpaceModuleCohomology` (`AlgebraicGeometry.RingedSpace.moduleCohomology`, `globalSectionsFunctor`), `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage` (`moduleDirectImage`, `derivedModuleDirectImage`), and `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor` (`Functor.exists_universal_rightDerived_deltaFunctor` and `CohomologicalDeltaFunctor`). The enough-injectives declaration is `AlgebraicGeometry.RingedSpace.moduleSheaves_abelian_enoughInjectives`.

Edge cases checked: arbitrary universe `u`, degree zero included by `ℕ`, and no nonemptiness or separatedness assumptions on the scheme.

Searches: `msearch.py leanfinder "sheaf cohomology right derived global sections higher direct images"` found only generic `Sheaf.H`; `msearch.py loogle "Functor.rightDerived, Sheaf.H, higherDirectImage"` had no exact hit; `rg` over Mathlib and `WeilConjectures` found no exact combined declaration. Existing ringed-space cohomology and derived-direct-image declarations were reused.

## Earlier second reading (a previous round; superseded)

Read the node and module line by line. The Lean binders match the scheme object, right-derived global-sections clause, universal delta-functor/long-exact clause, and higher-direct-image right-derived clause. No hypotheses are omitted from the source; derived-category instances are made explicit where required for the higher-direct-image expression.

## Second reading by T1

I independently read the node, all six statement-dependency nodes, their recorded
source declarations, the item module, and the source paragraphs. The Worker report
and earlier reading above describe the old draft; the final delivery is the theorem
below, not the unasserted proposition described there.

Source checked: the repository does not contain the downloaded Stacks tree, so I read
its local copy at `/home/ubuntu/c1-stacks-review/cohomology.tex`, lines 32–165 and
6550–6630, and its `tags/tags` mapping. Tag 01DZ is `section-cohomology-sheaves`;
the module paragraphs define both H^p and R^p f_* by injective resolutions, with
module-valued cohomology and no geometric hypotheses. The unbounded construction
preceding Tag 079W computes Rf_* by K-injective resolutions. Tags 01EO and 01EY
are respectively Čech comparison and Leray, not the definitions. I corrected the
module/declaration references to 01DZ and the construction preceding 079W. The
node's mathematical statement is sound and unchanged; its inherited parenthetical
bibliography is inaccurate, as its existing lead_note already records. Its unit
is proper-and-quasi-finite implies finite, and no unit statement is changed.

Clause-by-clause inventory and verdict:

1. Object X is an arbitrary scheme: `(X : Scheme.{u})`. Verdict: exact; no
   properness, Noetherian, separation, quasi-coherence or field hypothesis.
2. O_X-modules are `SheafOfModules.{u} (moduleRings X.toRingedSpace)`, precisely
   the module category used by def-sc-ringed-space-module-cohomology and
   lem-sc-ringed-space-module-sheaves-enough-injectives. Verdict: same objects,
   not their underlying abelian sheaves.
3. Global sections is `RingedSpace.globalSectionsFunctor X.toRingedSpace`,
   evaluation at `op ⊤`, with values in modules over O_X(X). H^p is the recorded
   `RingedSpace.moduleCohomology X.toRingedSpace p`. The first conjunct asserts,
   for every `p : ℕ`, equality with `Functor.rightDerived` of global sections.
   Verdict: exact right-derived identification, including all functor maps.
   The explicit `InjectiveResolution.instHasInjectiveResolutions` argument is
   built from `moduleSheaves_abelian_enoughInjectives X.toRingedSpace |>.2`;
   enough injectives is supplied, not assumed of X. No inline `let` or private
   cohomology definition is needed.
4. Each short exact sequence gives its long exact cohomology sequence: the
   second conjunct provides `G : CohomologicalDeltaFunctor` with
   `G.F = RingedSpace.moduleCohomology X.toRingedSpace`. I opened DeltaFunctor:
   its delta, mono_zero, exact_middle, exact_right, exact_left and naturality
   fields express all positions of the long exact sequence, including its
   initial zero and the connecting maps. Verdict: all clauses covered.
   The old extra `G.IsUniversal` conclusion is removed; the universal theorem
   remains the proof dependency giving these connecting maps.
5. The morphism f:X→S is `(S : Scheme.{u}) (f : X ⟶ S)`, and its underlying
   ringed-space morphism is `f.toLRSHom.toShHom`. Verdict: the node's scheme
   morphism, replacing the draft's more general arbitrary ringed-space target.
6. Higher direct images in every nonnegative degree are computed by f_*:
   for each `p : ℕ`, the last conjunct is a natural functor isomorphism between
   `singleFunctor ... 0 ⋙ derivedModuleDirectImage f.toLRSHom.toShHom ⋙
   homologyFunctor ... (p : ℤ)` and the ordinary p-th `Functor.rightDerived`
   of `moduleDirectImage f.toLRSHom.toShHom`. It states
   H^p(Rf_*(F[0])) ≅ R^p f_*(F), on objects and maps, not merely an equality
   between two names for unbounded Rf_*. Verdict: the missing degree-p clause
   is now present. The two HasDerivedCategory binders are choices of the
   localization infrastructure required by the dependency declaration, not
   geometric assumptions; their size universes wX and wS are independent and
   arbitrary, rather than fixed to u as in the draft.

Dependency reading: RingedSpaceModuleCohomology defines exactly module-valued
right-derived sections and records resolution comparison and independence.
RingedSpaceDerivedDirectImage defines the module pushforward with scalar action
via g-sharp, and unbounded derived pushforward computed by K-injectives.
RightDerivedUniversalDeltaFunctor supplies long exact sequences for an additive
left exact functor with enough injectives. Mathlib's
`CochainComplex.isKInjective_of_injective` accepts a strictly bounded-below
complex and injective terms, as an injective resolution supplies. The enough
injectives theorem supplies the needed resolution instance explicitly.
GlobalSectionsLeftExact is about additive-group-valued scheme global sections,
not module-valued RingedSpace.globalSectionsFunctor: I did not identify those
functors. The docstring explains why sectionwise kernels and finite products
prove the corresponding left exactness for module-valued sections. This does
not require a replacement definition or dependency module: both recorded
notions are usable as stated, and there is no left-exactness assumption in the
final theorem. All three original proof steps and their dependencies are
included in the theorem docstring.

Edge cases: degree zero is included in both `∀ p : ℕ` clauses; delta-functor
mono_zero covers the start of the long exact sequence. Zero module sheaves and
short exact sequences with zero terms are unrestricted. Empty schemes and the
empty target are not excluded; the theorem covers every existing scheme
morphism (it does not postulate a morphism to the empty scheme). No index set,
nonemptiness or characteristic assumption occurs. The object universe u is
arbitrary; both schemes can always be placed in a common universe, and wX/wS
retain all choices of derived-category sizes. No unbound variables remain.

Independent searches (2026-10-11):

- `msearch.py T1 pqf-def-cohomology leanfinder "cohomological delta functor of
  modules on ringed spaces long exact sequence"`: eight generic group-cohomology,
  short-complex and derived-category hits, no exact combined scheme statement.
- `msearch.py T1 pqf-def-cohomology loogle "CategoryTheory.Functor.rightDerived"`:
  twelve generic right-derived definitions and degree-zero/vanishing/map lemmas;
  no exact item declaration.
- `rg` with `longExact`, `long_exact`, `CohomologicalDeltaFunctor`,
  `moduleCohomology`, `single.*rightDerived`, and `higherDirectImage` on Mathlib's
  Abelian and AlgebraicGeometry/RingedSpace directories, source
  WeilConjectures/AlgebraicGeometry/Cohomology and CategoryTheory/DerivedCategory,
  and the project's lean/Sheaf: found the recorded moduleCohomology and generic
  delta-functor infrastructure, plus upstream Scheme.Modules.higherDirectImage
  (DirectImage.lean:170), which is already defined as rightDerived of scheme
  module pushforward. No combined declaration asserts all three clauses.
  Upstream Scheme.Modules.H is underlying abelian-sheaf cohomology, requiring
  a comparison theorem with moduleCohomology; it is not substituted here.
  `dag/lean_names_upstream.json` has no pqf-def-cohomology declaration.

Mismatches repaired: an unasserted Prop definition became a theorem with `sorry`;
cohomology is tied to the existing moduleCohomology declaration; the extra
universality conclusion was removed; the unbounded definitional equality was
replaced by the missing degree-p natural comparison; targets are schemes;
derived-category size universes were generalized; source tags, header and
step-by-step proof docstring were repaired. The mathematical node statement
and dependency list are unchanged, and no new definition nodes or dependency
modules are delivered. The only proof is the named theorem's `sorry`; no data
definition contains a hole. Server compilation with scompile.py passed cleanly
in 3.0 seconds, without errors or warnings. The lean.statement was read from
the final file with tools/stage2_delivery.py signature and recorded verbatim.
