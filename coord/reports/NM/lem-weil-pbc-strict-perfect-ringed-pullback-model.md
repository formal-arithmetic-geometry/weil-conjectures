## Worker report

This packet states `lem-weil-pbc-strict-perfect-ringed-pullback-model` in
`Sheaf.Paper.StrictPerfectRingedPullbackModel`. All new theorems have `sorry`
proofs. Definitions contain actual tensor/sheafification or categorical data;
the finite-free isomorphism is selected from a theorem asserting uniqueness
under its complete local pure-tensor coordinate characterization.

Hypotheses and clauses are rendered as follows.

- The two sites have independent object universes `uC`, `uD`, independent hom
  universes `vC`, `vD`, and `EssentiallySmall.{r}` hypotheses. Coefficients and
  module sheaves live in `r`, and derived-category morphisms in `w`. This is
  the chosen-small-site size convention, without equating site universes.
- `R`, `RI`, `S : Sheaf ... CommRingCat.{r}` are the ring sheaves. `uInv`,
  `uPush`, `adj`, and `PreservesFiniteLimits uInv` present the geometric
  morphism. `I : AlgebraicInverseImage uInv R RI` fixes the transported
  algebraic structures and `c : RI ⟶ S` is the coefficient map.
- `uStar`, `hobj`, `hmap` identify ordinary pullback on both objects and maps
  with `changeOfRings c (I.modules.obj M)`, rather than an arbitrary functor.
  Its `Additive` instance is an encoding of this additive construction; it
  imposes no exactness or flatness of the coefficient morphism.
- `LF`, `epsilon`, and `LF.IsLeftDerivedFunctor epsilon ...` name the derived
  functor and its canonical comparison by its universal property. The
  supplied universal property fixes this input. Invertibility on strict-perfect
  models is concluded, not assumed as an additional computation hypothesis.
- `F`, `package : StrictPerfectCoefficientPackageOnSite _ F`, `a`, `b`,
  `hbounded` are exactly the specified complex, finite ranks, degreewise
  finite-free splittings and common interval. No chain-map condition is placed
  on the splittings. The original, already recorded general-site package is
  reused through `StrictPerfectCoefficientPackageOfUniverses`.
- The first two conjuncts of `strictPerfectRingedPullbackModel` say every
  source term is `IsFlatOnSite` and the complex is
  `IsKFlatIndependentCoefficients`.
- Its next conjunct says the mapped complex is zero outside exactly `[a,b]`.
- `ringedPullbackTensorSection` is the actual local tensor generator, passed
  through the module-sheafification unit and the specified `hobj` transport.
  `IsRingedPullbackFiniteFreeComparison` imposes the formula
  `(s ⊗ (a_j)) ↦ (s c(a_j))` in every coordinate, on every object of the
  target site and every section of the inverse-image tuple sheaf.
  `existsUnique_ringedPullbackFiniteFreeIso` asserts existence and uniqueness
  with this characterization. `ringedPullbackFiniteFreeIso` chooses that
  uniquely determined isomorphism, never an arbitrary `Nonempty` witness.
- `ringedPullback_strictPerfect_splitting` states the transported splitting
  equation. `ringedPullbackStrictPerfectPackage` has real fields `N :=
  package.N`, `i := uStar.map package.i ≫ gamma.hom`, and `p := gamma.inv ≫
  uStar.map package.p`; its proof field refers to the named splitting theorem.
  Thus the same ranks and specified maps form the requested pulled package.
- The next two main conjuncts say the mapped terms are flat and the mapped
  complex is K-flat, using exactly the recorded independent predicates.
- `ringedPullbackComplexComparison` transports the given `epsilon` from the
  homotopy category to complexes using `quotientCompQhIso` and
  `mapHomotopyCategoryFactors`. It does not choose a replacement comparison.
  `IsIso (... .app F)` states that the canonical comparison is invertible.
- The `∀ P e` clause says precisely that `LF.map e.inv ≫ epsilon_F` is an
  isomorphism from `LF(P)` to the localized specified termwise model.
- The final clause quantifies over any other bounded packaged complex `G`
  and any chain map `v`. In diagrammatic Lean composition order it states
  `epsilon_F ≫ Q_S(uStar(v)) = LF(Q_R(v)) ≫ epsilon_G`, which is exactly the
  node's naturality equation.

Dependency declarations read and used:

- `CategoryTheory.ringedSiteModules`,
  `Sheaf.CategoryTheory.RingedSiteModules`: the exact Mathlib module-sheaf
  category, not a new category.
- `DerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Qh`,
  `DerivedCategory.quotientCompQhIso`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: derived localizations and
  canonical quotient comparison.
- `SheafOfModules.ringedTopoiDerivedPullback`,
  `Sheaf.Paper.RingedTopoiDerivedPullback`: original proved derived pullback and
  resolution comparison, imported directly. Its module and node record are
  unchanged. The item takes `LF`, `epsilon`, and their universal property as
  inputs, without calling a generalized existence theorem.
- `SheafOfModules.StrictPerfectCoefficientPackageOnSite`,
  `Sheaf.Paper.StrictPerfectPackageOnSite`, publicly imported by recorded
  `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`: degreewise chosen
  ranks/inclusions/projections with the splitting equation. The representation
  wrapper itself is not substituted for the degreewise package.
- `SheafOfModules.IsFlatOnSite`,
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: exactness of the
  sheafified tensor functor.
- `CochainComplex.IsKFlatIndependentCoefficients`,
  `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: acyclicity of the
  total tensor with every acyclic complex.
- `SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite`,
  `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`: the stated
  proof dependency for both applications of bounded-flat K-flatness.
- `SheafOfModules.changeOfRings`, `changeOfRingsPresheaf`,
  `changeOfRingsHom`,
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`: actual
  sheafified scalar extension; the recorded tensor node's additional
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` is imported
  for the proof's independent-universe tensor structures.
- `SheafOfModules.AlgebraicInverseImage`,
  `Sheaf.CategoryTheory.AlgebraicInverseImage`: the same-coefficient/module
  universe algebraic lift, already allowing all four site universes to differ.
  The recorded `Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses` is
  additionally imported as a proof dependency. No new algebraic lift is defined.
- The size-convention node is metatheoretic and has no declaration to import;
  its universe bounds and relative smallness are explicit above.

Sources read: Stacks `sites-cohomology.tex`, lemma-strictly-perfect-pullback
(Tag 08H3), and section-derived-pullback including lemma-pullback-K-flat;
the node's five-step proof and its bounded-flat dependency's proof/signature.
The full source signature and docstring of each recorded interface were read.
The compact-object example in `lean/Sheaf` is now withdrawn; its node records
`WeilConjectures.CategoryTheory.CompactObject` as the replacement.

Edge cases checked: zero ring, zero complex, empty site, rank zero, interval
`a = b`, and `a > b` (forcing the zero complex) are not excluded. Bounds are
arbitrary integers and can change for the second complex. Splittings remain
only degreewise. The identity ring map and nonflat maps such as Z → Z/2 are
included. No assumption of global categorical projectivity, exactness of
`uStar`, coefficient-map flatness, or equality of site universes is introduced.
The pure-tensor characterization uses all local inverse-image sections, not
merely images of original sections or global sections.

Searches performed through the prescribed `msearch.py`:

- LeanFinder, “Derived inverse image of a bounded complex of finite free
  retract sheaves is the termwise pullback, with canonical K-flat comparison
  natural in chain maps”: eight hits, principally `pullbackObjFreeIso`,
  `freeFunctorCompPullbackIso`, and `mapDerivedCategoryFactorsh`; no match for
  the arbitrary-topos specified strict-perfect/K-flat/naturality package.
- Loogle, `SheafOfModules.pullbackObjFreeIso`: five hits, all ordinary free
  pullback statements for a site functor. Their full signatures require a
  continuous final site functor; this node allows an arbitrary geometric
  morphism with its algebraic inverse-image presentation.
- grep, `KFlat|[Ss]trict[Pp]erfect` in
  `Algebra/Category/ModuleCat/Sheaf`: zero hits.
- LeanSearch, “A bounded complex of finite projective sheaves is K-flat and
  its derived inverse image is its termwise pullback”: eight hits including
  `Module.Flat.of_projective`, categorical K-projectives, and ordinary sheaf
  pullback; none is the node's statement.
- `rg` in project `WeilConjectures/` and `Sheaf/` found
  `LocalizedPullbackPerfectModel` and `LocalKFlatPullbackModel`; the former
  concerns schemes/open localization and only an object isomorphism, rather
  than this arbitrary-topos natural comparison and transported chosen package.
  An identifier search found none of the new names in those sources, Mathlib,
  or `dag/lean_names_upstream.json`. The exact node-id search found no existing
  Lean statement. Search output is also in sandbox `searches.jsonl`.

No statement correction, new definition node, or mathematical dispute is needed.

## Dependency modules

None in the repaired packet. Following the H13 return's expressly permitted
alternative, removed `RingedTopoiDerivedPullbackOfUniverses.lean` and the copy
of `lem-weil-pbc-ringed-topoi-derived-pullback.json`. The original NG declaration
and K4 proof remain owned by the unchanged original dependency node. The main
module imports `Sheaf.Paper.RingedTopoiDerivedPullback` directly and explicitly
imports the existing independent flatness and K-flatness interfaces used in its
signature. All six independent universes remain unchanged. The item assumes the
specified left derived functor and its universal-property comparison; stating
this conditional computation theorem does not require a separate generalized
existence theorem. No use of the removed declaration occurs in the main module.

## Second reading by NM

In-thread rereading (no other agents were started, as instructed): compared each
of the seven statement dependencies and every clause of the item against the
module. In particular checked composition direction for i/p and for the derived
model, local pure-tensor rather than arbitrary isomorphism normalization, the
same finite ranks and both interval endpoints, and use of the supplied epsilon
rather than an unrelated isomorphism. Repaired initial elaboration problems by
explicitly typing the inverse-image module section and fixing the scalar-extension
sheafification universe. The maintainer performs the independent delivery review.

## Validation

The independent-universe dependency module compiled successfully through
`scompile.py` (14 s). The initial main-module compile exposed elaboration issues,
which were edited. Subsequent wrapper attempts failed before checking the edited
main module: its overlay compilation could not find the `Mathlib` prefix, and
server confirmation reported `Live published library is unavailable`. No tool
or live source was edited. Final compile/dry-run status is recorded below.

Final validation outcome: repeated `scompile.py` attempts and the prescribed
`deliver2.py ... --no-push` dry run all fail in the wrapper's prerequisite overlay
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic`, line 6, before
checking the edited main module: `unknown module prefix 'Mathlib'`. The displayed
search path has only the live project's build directory and Lean's toolchain;
server confirmation says `Live published library is unavailable`. The dry run
reported `COMPILE FAILED on the server, nothing pushed`. This is a tool/build
availability failure, not an accepted source compile. The packet remains an
unverified draft in the sandbox and was not delivered.

## Retry validation, 2026-10-21

Retained the saved packet and ran the required `deliver2.py NM
lem-weil-pbc-strict-perfect-ringed-pullback-model --no-push` first. It failed
before compiling either packet file: the prerequisite overlay
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic` imports
`Mathlib.LinearAlgebra.TensorProduct.Basic`, whose published `.olean` is missing
at `/home/ubuntu/weil-conjectures-sheaf/lean/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/LinearAlgebra/TensorProduct/Basic.olean`.
The wrapper's server confirmation again reported `Live published library is
unavailable`. A direct prescribed `scompile.py` retry passing both packet modules
reproduced the same missing-object-file error and server confirmation (exit 1).
This is not a busy-server exit 124 or a diagnostic in the delivered source.
No source change can restore the read-only published Mathlib build; no live file
or launcher tool was modified. The saved packet remains unverified and unpushed.

## Saved-packet retry, 2026-10-21 (third attempt)

Inspected the retained report and ran the required dry run first. `deliver2.py
NM lem-weil-pbc-strict-perfect-ringed-pullback-model --no-push` exited 1
before checking either packet module: prerequisite overlay
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic` could not import
`Mathlib.LinearAlgebra.TensorProduct.Basic` because its published `.olean`
does not exist. The wrapper's server confirmation reported
`Live published library is unavailable`.

Retried through prescribed `scompile.py`, supplying both saved Lean modules
in dependency order. It also exited 1 before packet compilation: prerequisite
`WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom` could not
import the missing published
`Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.olean`. Server confirmation
again reported `Live published library is unavailable`. Neither attempt was
a busy-server timeout (124). These failures concern the read-only published
Mathlib build, not a diagnostic repairable in the packet. No Lean, node, live
repository, or launcher-tool source was changed. The saved packet remains
unverified and unpushed.

## Saved-packet self-check, 2026-10-21 (fourth attempt)

Started with the prescribed dry run on the retained packet. Reread both saved
modules, the current item and its seven statement dependencies, the recorded
module-sheaf, derived-category, strict-perfect package, flatness and K-flatness
interfaces, the original ringed-topos derived-pullback theorem, the algebraic
inverse-image structure, and Stacks `lemma-strictly-perfect-pullback` and
`lemma-pullback-K-flat`. No semantic change was needed. The same bounds and
ranks, degreewise transported splitting equation, flatness and K-flatness on
both sides, supplied canonical comparison, arbitrary derived isomorphism and
chain-map naturality are all represented. Rank zero and reversed interval
bounds remain included. Both files explicitly disable auto-implicit variables.
The dependency repair still is necessary: the original theorem fixes both site
object and morphism universes to the coefficient universe. A fresh name search
in the current `lean/WeilConjectures` and `lean/Sheaf` sources found no competing
saved declaration. Refreshed the two sandbox node copies from current metadata,
retaining their `lean` records, so all other fields remain unchanged.
The current compile/delivery result will be recorded below.

### Fourth-attempt validation outcome

The required dry run failed (exit 1), with nothing pushed. Its private-overlay
compile successfully checked `RingedTopoiDerivedPullbackOfUniverses` in 10.8 s.
Before checking the main file, an unrelated imported prerequisite,
`WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`, timed out
at 60 s. The automatic server confirmation then failed in
`Sheaf/Paper/KFlatRingedToposPullback.lean:6:0`: published object file
`/home/ubuntu/weil-conjectures-sheaf/lean/.lake/build/lib/lean/WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean`
does not exist.

Retried with the prescribed `scompile.py`, passing both saved files in dependency
order. This retry failed immediately (exit 1) in that same prerequisite, with
exactly the missing `WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic`
object-file diagnostic in both local compilation and automatic server
confirmation. This is not the busy-server message or a diagnostic in a packet
file. Repairing the read-only published library or launcher cache is outside
worker authorization; removing the required derived-pullback dependency would
not faithfully encode the node. No live source or launcher tool was changed.
The main module remains unverified, and the packet has not been delivered.

## Saved-packet retry, 2026-10-21 (fifth attempt)

Inspected the retained report and ran the prescribed `deliver2.py NM
lem-weil-pbc-strict-perfect-ringed-pullback-model --no-push` on the saved
packet. It exited 1 before checking either packet module. Private overlay
`Sheaf.Paper.KFlatRingedToposPullback` failed at line 6 with:

```
object file '/home/ubuntu/weil-conjectures-sheaf/lean/.lake/build/lib/lean/WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean' of module WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic does not exist
```

The wrapper's automatic server confirmation reproduced the same error. Retried
using `scompile.py NM lem-weil-pbc-strict-perfect-ringed-pullback-model` with
both saved modules in dependency order. It exited 1 with the same missing
published object-file diagnostic, again confirmed on the server. Neither
attempt returned the busy-server timeout (124).

Compared both saved node copies against current shared metadata: there is no
non-`lean` delta. Read the current prerequisite source and the upstream tensor
helper source: the latter exists as Lean source, but the wrappers cannot load
its published artifact. The required prerequisite import is retained; no live
source, artifact, launcher script, or saved Lean declaration was modified.
The main module remains unverified and nothing was pushed. Restoring the
published build or repairing wrapper artifact resolution requires the
maintainer/launcher; it cannot be repaired within this worker's sandbox.

## Saved-packet repair and self-check, 2026-10-21 (sixth attempt)

Read the retained report and ran the prescribed dry run first. The old tensor
artifact failure was cleared, and the dependency module compiled in 10.2 s.
The dry run then failed in imported upstream modules owing to unavailable
published artifacts (`UpperLowerStar.Defs`, and `Topology.Stratification` on
server confirmation), before compiling the main packet file. A prescribed
`scompile.py` retry subsequently resolved those prerequisites through the
wrapper and reached the main file.

The main file exposed an underconstrained universe application in the
sheafification unit. After reading the current server tensor-product source
with `scompile.py --source`, supplied all four universes explicitly as
`sheafificationAdjunction.{r, vD, r, uD}` and all three as
`changeOfRingsPresheaf.{vD, uD, r}`. No equation between site and coefficient
universes was introduced. Marked `ringedPullbackComplexComparison`
`noncomputable` because its existing abelian-category construction is
noncomputable; its data and signature are unchanged.

Reread the item and its seven statement-dependency records, both saved
modules, the recorded ringed-site module, derived-category, package, flatness
and K-flatness declarations and their docstrings, the original derived
pullback theorem, and Stacks strictly-perfect pullback and K-flat pullback.
The source and target flatness/K-flatness, original bounds and ranks,
transported splitting equation, specified epsilon, arbitrary derived
isomorphism and chain-map naturality still match clause by clause. No
mathematical correction is needed. Both node copies still differ from the
current shared nodes only in `lean`; the stored main signatures are verbatim.
Both modules disable auto-implicit variables, have no overlong lines, and
leave `sorry` only as the complete proofs of the four named theorems.
The current source-name search found no competing declaration. No live
source, published artifact or launcher script was modified.

Validation: prescribed `scompile.py` compiled each file separately in dependency
order with exit 0 and no warnings or errors. The dependency module took 10.5 s
and the main module took 42.9 s under its final library module name (sandbox
check 42.7 s), within the unchanged 60 s limit.

The final prescribed `deliver2.py ... --no-push` returned exit 0:
`OK (dry run): commit 4c9c36f13cb passes the preflight and compiles; nothing pushed`.
The retained packet is ready for the required normal delivery.

## Returned timeout repair, 2026-10-21

Reproduced the immutable-head return with the required saved-packet dry run.
The dependency module completed in 10.5 seconds locally (50.4 seconds in the
server confirmation), but the main module exceeded 60 seconds on both paths.
A temporary sandbox-only profiler copy identified repeated elaboration of
`sheafCompose` as the cost: the high-priority generic multicospan instance
searched for irrelevant countable/finite category structures on section types
at each occurrence, before using the small-site transport.

In `StrictPerfectRingedPullbackModel.lean`, prioritize Mathlib's existing
`hasSheafCompose_of_preservesLimitsOfSize` (12000) and
`hasSheafComposeEssentiallySmallSite` (11000) over the generic multicospan
instance. The first handles genuinely size-bounded limits; the second
transports an essentially small site to its small model. This adds no
instance, hypothesis, definition, universe equality, theorem, or mathematical
assumption. These are existing canonical proofs of the same proposition, so
proof irrelevance preserves the mathematical interfaces and all signatures.
The timeout limit remains 60 seconds; neither module was split.

The experimental file without profiling output compiled cleanly via the
prescribed `scompile.py`: 21.6 seconds as a sandbox module and 13.2 seconds
under the final check-module name. The dependency module completed each of
its checks in 10.5–10.6 seconds. Final delivery-name validation follows below.

Self-check: reread both packet modules, the item and all seven statement
nodes, their recorded declarations and docstrings, Stacks strictly-perfect
pullback and K-flat pullback, and the item's five-step proof. The transported
splitting remains `uStar.map i ≫ gamma.hom` followed by
`gamma.inv ≫ uStar.map p`; the concrete package preserves `package.N`.
Flatness and K-flatness on both sites, the common interval, arbitrary derived
isomorphisms and naturality of the supplied epsilon are all retained.
Rank zero, zero rings, the zero complex, reversed interval bounds and nonflat
coefficient maps are still covered. There is no semantic statement change.
Compared each saved node with current shared metadata: only `lean` differs.
All original search records are retained; no new notion required searching
or a new DAG node. No shared source, artifact or launcher file was modified.

Final prescribed `scompile.py` on both delivery files completed with exit 0:
the independent-universe dependency took 10.5–10.6 seconds, and the main
module took 29.6 seconds as a sandbox and 29.9 seconds as
`Sheaf.Paper.StrictPerfectRingedPullbackModel`. No warning or error was emitted.
The return's timeout is therefore repaired by an actual source change, with
all mathematical declaration signatures retained verbatim.

The required final dry run passed with exit 0:
`OK (dry run): commit 5b2584d8651 passes the preflight and compiles; nothing pushed`.
This checks the actual delivery-name modules and the packet's node/report shape.

## H13 and H9 returned-delivery repair, 2026-10-21

Inspected the saved packet and ran the prescribed dry run first; it passed as
commit `493750f1555`. This mechanical pass did not discharge the return.
Repaired both independently reviewed issues:

- H13: chose the reviewer's explicit “drop the dependency node file and new
  module” alternative. Removed both from the sandbox packet, preserved the
  proved original dependency and its record, and imported its original module
  directly. The only additional imports are the already existing independent
  flatness and K-flatness interfaces previously re-exported by the removed
  module. No generalized theorem is called by the item or its definitions.
- H9: changed both priority attributes to `attribute [local instance ...]`.
  Their elaboration optimization is confined to this module and no longer
  changes instance priorities for importers.

Compared the saved item node with the current shared node: every non-`lean`
field is identical. All eight item declaration signatures and all construction
data are unchanged from the independently accepted returned statement. Rechecked
zero rank, zero complex, reversed interval bounds and nonflat coefficient maps;
none is excluded. No statement correction, new node, or dependency-record
replacement remains. Earlier validation sections above describe historical
attempts; this section describes the repaired packet.

Repaired-packet validation: `scompile.py` completed with exit 0 and no compiler
warning or error. The one remaining module compiled in 28.1 seconds as
`Sheaf.Stage2.Sandbox0` and 25.8 seconds as
`Sheaf.Paper.StrictPerfectRingedPullbackModel`, under the unchanged 60-second
limit. The node's recorded signature matches the file verbatim and every Lean
line is at most 100 characters. Both instance priorities are local, and no
dependency node file or dependency module remains in the packet.

The repaired packet's prescribed dry run passed with exit 0:
`OK (dry run): commit 9bdd9a57e65 passes the preflight and compiles; nothing pushed`.
The staged files were exactly the item module, item node and worker report.
Both H13 and H9 are repaired by source/packet changes, not an unchanged re-push.
