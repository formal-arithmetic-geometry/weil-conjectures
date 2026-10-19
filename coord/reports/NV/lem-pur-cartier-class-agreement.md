## Worker report

The delivery states `WeilConjectures.PurityFiniteSetting.cartier_class_agreement`
in `Sheaf.Paper.CartierClassAgreement`. Its two conclusions are equality of the
specified general relative divisor class with the supported Cartier Kummer map,
in the latter's canonical finite-root coordinates, and Cartier-preserving pullback
of that class. Every theorem proof is `sorry`.

Hypothesis and clause correspondence:

- The finite coefficients, field, extension and arbitrary positive level are
  `P : PurityFiniteSetting.{u}`. `P.Coefficient` is the standard size lift of
  O_E/(varpi^n). `P.level_pos` is n>=1. There is no ramification-divisibility
  hypothesis. The actual exponent is `P.diagonalExponent = ell^P.level`.
- The separated finite-type k-scheme T is `(a : T ⟶ Spec (.of P.field.k))`
  with `[IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]`.
- The effective Cartier divisor is `(i : D ⟶ T) [IsClosedImmersion i]`
  and `(hI : i.ker.IsInvertible)`, precisely the recorded Cartier ideal notion.
- The class constructed in the second paragraph of lem-pur-divisor-class is
  `P.generalDivisorClass a i hI`. It applies the existing `divisorProEtale`
  to the unique `DivisorEtaleNormalized` family. That predicate uses the existing
  `SupportedKummerBoundary`, which retains the dual ideal's frame torsor and the
  canonical frame off D, rather than an arbitrary lift of the ordinary Chern class.
- `FunctorialCupH true i 2 1` is the recorded supported-Hom realization of
  H^2_D(T,A(1)), via `supported_cohomology_hom`. In these coordinates the
  identification with Hom has already been applied; no arbitrary supported-Hom
  isomorphism is a binder.
- The named Cartier morphism is `P.agreementCartierMap a i hI`, expressed in its
  etale-origin root chart. `agreementCartierEtale` selects **the existing** etale
  component of `(Etale.cartier_kummer_map ell E).2.exists.choose`, at coefficient
  predecessor n-1 and Kummer predecessor n-1. A direct successor case split on the positive level makes both indices
  definitionally exact; it does not choose a class. `agreementCartierMap` then applies
  the existing `functorialCupCompare`. The existing `CartierKummerRealization`
  property identifies exactly this arrow with `cartierKummerMap` under the
  constant-quotient source and projection-normalized target comparisons. Thus
  this uses the original A(1) through its canonical root chart, not a replacement
  twist or an arbitrary isomorphism. The source's final etale-witness clause
  explicitly supplies this presentation.
- The first conjunct is `generalDivisorClass ... = agreementCartierMap ...`.
  The relative Kummer/scalar-unit normalization is part of the selected
  `CartierEtaleKummerNormalization` system, not an added hypothesis. Its
  scalar map sends v to v tensor 1 and the projection chart is theta from
  def-pur-frame-class.
- The second conjunct universally quantifies T', D', a', h and w. The three
  scheme-property instances on a' say that T' is also separated finite type.
  `h ≫ a = a'` says h is a k-morphism. `ChosenCartesianSquare w i' i h`
  says D' is the scheme-theoretic pullback. `[IsClosedImmersion i']` and
  `hI' : i'.ker.IsInvertible` say it is again Cartier. The equation is precisely
  `functorialCupPullback true ... (generalDivisorClass ...) = generalDivisorClass ...`.
- No smoothness is assumed for any of T, D, T', D', and h need not be flat.

Dependencies read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, `Coefficient`,
  `constantEtale`, `constant`; the recorded finite datum is retained.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: recorded intrinsic
  signed twists; the finite root presentation comes from the dependency's
  imported positive-twist interface, as used already in the frame and cup modules.
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`:
  `Scheme.IdealSheafData.IsInvertible.isInvertible_dual_toModules` and
  `Scheme.Modules.dual`; no second Cartier or line-bundle definition.
- `Sheaf.AlgebraicGeometry.SupportCohomology`:
  `ProEtale.derivedSupportSections` and support cohomology are reexported by
  `Sheaf.Paper.SupportedCohomologyHom`, whose
  `ProEtale.supported_cohomology_hom` gives the Hom realization used here.
- `Sheaf.Paper.PurityDivisorClass`: `DivisorEtaleClasses`,
  `DivisorEtaleNormalized`, `divisorProEtale`, and the original `divisor_class`.
- `Sheaf.AlgebraicGeometry.CartierKummerMap`: `Etale.cartier_kummer_map`,
  `CartierEtaleKummerFamily`, `CartierEtaleKummerNormalization`,
  `CartierKummerRealization`, `CartierKummerBaseChange`, and `cartierKummerMap`.
- `Sheaf.Paper.SupportedCupFunctoriality`: `FunctorialCupH`,
  `functorialCupCompare`, `functorialCupPullback`, with their canonical source
  and finite-root twist comparisons.
- `Sheaf.AlgebraicGeometry.ClosedSupportHom`: `Etale.closedSupportHom`, the
  normalized relative cone realization in the proof plan.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`, with its scalar-unit
  and transpose formulas, used in the proof plan.
- `Sheaf.Paper.PurityFrameClass`: `frameClass`, `frameBoundaryProduct` and
  the imported `frameTwistEtale` / `frameTwist` arbitrary-positive-level root
  prescription. No frame-existence or purity theorem is imposed as a hypothesis.

All already-stated proof dependency modules are imported. Imports needed only
for the eventual proof are ordinary imports. In particular this includes the
relative cone, underlying-module comparison, finite direct-image exactness,
ordinary supported Kummer construction, finite-root flatness, K-flatness, and
supported-Hom pullback modules. The seven DAG proof steps are reproduced in
the theorem docstring. The divisor-class dependency repair retains the entire previous module and appends
three declarations, so its public interface and smooth-pair theorem remain available.

Edge cases checked: empty D and empty T are allowed (invertible unit ideal and
all unit formulas remain meaningful on the zero global ring); empty T' and the
identity square are included; nonreduced Cartier divisors and singular T are
allowed; n=1 gives predecessor zero in the published indexing; arbitrary positive
n, including n not divisible by the ramification index, uses ell^n; arbitrary
nonflat and ramified morphisms are included precisely when the pullback ideal
is still Cartier. A morphism factoring through nonempty D is appropriately
excluded when its pulled-back zero ideal is not Cartier. The source normalization
is the Yoneda relative-torsor normalization already fixed by the DAG and dependency;
no claim identifying it with the positive rank-one frame boundary is introduced.

Searches for an existing statement:

- `msearch.py ... leanfinder "The supported Kummer class of a Cartier divisor equals
  its derived supported morphism and commutes with pullback"`: eight generic
  scheme-section and restriction results; none states this comparison.
- `msearch.py ... loogle '"Cartier", "Kummer"'`: zero hits.
- `msearch.py ... grep 'Cartier|supported.*Kummer' AlgebraicGeometry`: zero hits.
- `rg -n 'cartier.class.agreement|CartierKummer|SupportedKummerBoundary|divisor_class'`
  in both the upstream WeilConjectures tree and shared lean/Sheaf: no upstream
  Cartier/Kummer comparison; existing side modules supply the two constructions,
  normalization and scalar interfaces, not their agreement with divisor_class.
- `grep -rn 'lem-pur-cartier-class-agreement'` in the upstream tree: no hits.
- `rg` of `dag/lean_names_upstream.json` for the Cartier comparison and new
  accessor names: no matching upstream declaration.
  Source declarations and their docstrings were inspected, including the full
  Cartier realization/base-change system and general divisor normalization.

No new mathematical notion or definition node is needed. No statement correction
and no disputed statement are introduced. The dependency interface and compile-cost defects are repaired below.

## Dependency modules

`lem-pur-divisor-class`: its landed record and owning module
`Sheaf.Paper.PurityDivisorClass` are retained. Although `DivisorEtaleClasses`
and its normalization quantify over all Cartier immersions, the landed existence
theorem is stated for the smooth setup. This delivery appends the general
unique-family interface in the same module: `existsUnique_generalDivisorEtaleClasses`
exposes the general construction from the node's second paragraph on a
separated finite-type k-scheme, `generalDivisorEtaleClasses` selects that unique
family, and `generalDivisorClass` applies the existing `divisorProEtale`. The
definition's data is fixed by the uniqueness theorem, with no mere existence
choice. The dependency's `lean` record remains headed by
`Sheaf.Paper.PurityDivisorClass.divisor_class` and appends these three names with
a note explaining the same-module superset; no replacement module is delivered.

`def-pur-frame-class`: the existing `Sheaf.Paper.PurityFrameClass` timed out
at 60 s in both overlay and server confirmation. An isolated profiling check
completed in 57.2 s and identified expensive generated recursive-fold wrappers
and a 51.2 s private-module linter pass. The sandbox replacement changes only
`frameBoundaryProduct` from equation-compiler recursion to the identical dependent
`Nat.rec` left fold. The empty-tuple value and successor step are unchanged,
as are every public signature, source, target, comparison, and class. This avoids
the generated recursion wrappers; it adds no assumptions or new notion. The
node changes only in `lean`, with the required explanation. This dependency is
compiled as a separate delivered file, in dependency order before both consumers.

`def-weil-derived-pullback-tensor-hom`: the retained packet also contains an
interface-preserving compilation repair of this transitive prerequisite. Its
published module repeatedly exceeded the 60-second limit. The delivered
`Sheaf.Paper.DerivedPullbackTensorHom` is the complete live module with only
`set_option backward.isDefEq.respectTransparency false` added after the existing
explicit-variable setting. All declarations, signatures, definitions, imports,
and docstrings are unchanged; the node changes only in `lean`, with `lean.note`
explaining this repair. The initial dry run compiled this private overlay in
54.4 seconds. This is a compilation repair, with no new mathematical notion.

## Second reading by NV

The dispatcher requires direct delivery and explicitly forbids starting other
agents. This section records the author's rereading; it does not claim an
independent review. The maintainer supplies that independent review after delivery.
I reread the node against the final signature and all three modules. The smooth-only
existence interface was the mismatch found, and is repaired by the general
unique-family interface. The check also confirmed that n-1 is used for both
published positive indices, that the comparison retains the canonical relative
trivialization, and that the universal pullback clause uses a cartesian square
and an actual k-morphism, with all three finite-type/separated hypotheses on T'.

Compilation feedback: the first check exposed dependent-type simplification failures
in predecessor reindexing. A direct successor split on the positive level replaces
those casts, preserving every positive level and the same selected witness.

Recovery self-check (2026-10-18): retained the saved packet and ran its required dry
run first. The frame-class and same-module divisor files compiled cleanly. The final
Cartier-agreement module exposed an implicit constructor argument in the current
`PurityFiniteSetting.mk`; the successor-level accessor now uses the explicit
`@mk` case pattern to bind the finite-extension instance. This changes no public
signature, coefficient index, or mathematical hypothesis. All three node copies
still change only `lean`; their recorded signatures, dates, explicit-variable
settings, and 100-column limit were checked against the delivered files.
The reconstructed positive-level setting likewise uses `@PurityFiniteSetting.mk`
so that the instance is supplied in its correct implicit position. After these
two elaboration repairs, the prescribed three-file `scompile.py` check passed
cleanly for every delivered file, in both sandbox and library-module form;
`CartierClassAgreement` took 11.0 s and 11.2 s respectively. No theorem was proved,
no signature changed, and no extra assumption was introduced.

Return repair (2026-10-18): the returned H13/H4 point required preserving the
landed `lem-pur-divisor-class` owner. I therefore removed the replacement
`PurityDivisorClassGeneral` module, copied the landed `PurityDivisorClass` source,
and appended `existsUnique_generalDivisorEtaleClasses`,
`generalDivisorEtaleClasses`, and `generalDivisorClass` inside the existing
namespace. The dependency node's `lean` record still declares
`divisor_class` and the original seven declarations, appending exactly those
three names with a same-module-superset note. The Cartier module now imports
`Sheaf.Paper.PurityDivisorClass` directly. A subsequent dry run reached the
server preflight; its reported failure was a 60-second timeout in the unrelated
imported `Sheaf/AlgebraicGeometry/OrdinaryFiniteP1Decomposition.lean` while the
shared compile queue was loaded, so I reran the prescribed wrapper.

Final repair self-check (2026-10-18): compared all saved node fields and both
modified dependency modules with the current shared source. The divisor-class
file now preserves the entire current module, including its four newly landed
public imports, and appends only the three requested declarations. Corrected its
lean.statement to the verbatim divisor_class signature, matching lean.declaration;
the original seven names remain first in lean.declarations. The extra replacement
module is absent. All three node copies still differ only in lean.

Current validation (2026-10-18): the required initial dry run compiled the
frame-class overlay on the server in 51.8 s, then stopped in the imported
SupportedCupFunctoriality module at its unchanged 60 s limit. It did not reach
the two downstream delivered files. The prescribed three-file scompile check
is being rerun on the finalized same-module packet.

Repair continuation (2026-10-18): the required first dry run was started on the
saved packet before any edits. The comparison with current live source found one
subsequently landed public import, `Sheaf.CategoryTheory.Sites.TorsorWithSection`,
missing from the saved divisor module; it is now retained as well. The delivered
module is consequently the entire live module plus exactly the three requested
declarations. The original seven names and `divisor_class` signature remain
unchanged, and the replacement module remains absent.

Recovery check (2026-10-18, current attempt): verified that the delivered divisor
module is the current live module verbatim up to its namespace end, followed by
exactly the three requested declarations. The original seven recorded names remain
first, `divisor_class` remains the primary declaration, all three node copies differ
only in `lean`, each recorded signature occurs verbatim in its module, and no
`PurityDivisorClassGeneral` module remains. The author reread the current node,
final agreement signature, normalization accessor, and canonical pullback formula;
no mathematical change or additional hypothesis was found.

The required initial dry run stopped before the delivered-file checks: the overlay
`DerivedPullbackTensorHom` timed out at 60 seconds; server confirmation instead
timed out in `IntegralOperationsScalarComparisons`. A prescribed three-file
`scompile.py` retry again timed out in the same overlay module; confirmation then
reached the live `PurityFrameClass` and timed out there. The saved packet is
retained unchanged; another ordinary dry run is in progress with the shared
dependency cache populated by these checks. No launcher script, timeout, or live
source has been modified.

Final packet self-check (2026-10-18, resumed repair): all four saved node copies
were compared with the current shared DAG and differ only in `lean`. All recorded
signatures occur verbatim in their modules; variables and universes are explicitly
bound and no Lean line exceeds 100 characters. The divisor module preserves the
complete current live source and appends exactly the three requested declarations;
`divisor_class` remains primary and its original seven declarations remain first.
`CartierClassAgreement` imports this owning module and the removed
`PurityDivisorClassGeneral` module is absent. The agreement and Cartier-preserving
pullback signature remain exactly the version found mathematically correct in the
return. This is an author self-check, not an independent second reading. The
required dry run is checking the complete four-file packet.

Validation completed (2026-10-18, current repair): the required initial
deliver2.py --no-push run returned OK at temporary commit 162d07e10d;
preflight passed and all four delivered Lean files compiled. The final author
self-check reopened the item and source, matched both conclusion clauses and
all hypotheses with the unchanged signature, verified the live divisor module
is preserved with exactly three appended declarations, and checked primary
ownership, signatures, explicit variables, and line widths. Refreshed the
dependency copy’s maintainer metadata from the live DAG; every node differs
only in lean. No additional mathematical repair was required.
