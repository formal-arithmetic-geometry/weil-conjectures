## Worker report

The module `Sheaf.Paper.OpenLocalizedCounitComparison` states
`AlgebraicGeometry.Scheme.cbcOpenLocalizedCounitComparison`, with one `sorry` and
no other postponed theorem. Its helper definitions construct the canonical maps
and their coordinates from published definitions; they have real data. The node
is unchanged outside `lean`. No new nodes or dependency repairs are needed.

The source read is Stacks `sites-modules.tex`, lemma-extension-by-zero (03DI,
lines 2058 onward, including both Hom transpositions), lemma-restrict-back (0F6Z,
line 2338 onward), and lemma-localize-morphism-ringed-sites (04J0, line 2369
onward, including its displayed restricted ring map). The statement follows the
five proof steps in the node, including the specified normalization of alpha.

Hypothesis and clause correspondence:

- `X Y : Scheme.{u}` and `g : X ⟶ Y` are the schemes T', T and their arbitrary
  scheme morphism. There is no properness, flatness or nonemptiness assumption.
- `U : Y.ProEt` with `[IsOpenImmersion U.hom]` represents the arbitrary open
  immersion j, including a non-chosen presentation of its open subscheme. The
  target object is `(proEtaleModelBaseChange g).obj (AsSmall.up.obj U)`, whose
  underlying scheme is the chosen cartesian pullback of U along g. This is j'.
  The slice functor is `Over.post (proEtaleModelBaseChange g)` at this object.
  Via `ProEt.sliceEquiv` this is g_U on the localized sites, with the standard
  associativity identification of the two iterated fibre products.
- `B : Type (u + 1)` with `[CommRing B] [Finite B]` is the finite commutative
  coefficient ring. No topology is an added hypothesis: constant sheaves are
  used directly. The published finite coefficient comparison identifies these
  with the discrete coefficient sheaves while preserving constants.
- Sites use the already published `proEtaleSiteModel` and
  `proEtaleModelTopology`. This is `AsSmall.{u+1} X.ProEt`: every original object
  is retained and only Hom is enlarged from u to u+1. This is an equivalent site,
  not an extra assumption equating the original object and Hom universes.
  Its Over categories give exactly the localized sites allowed in the node.
- `cbcOpenModelCoefficient` is precomposition of the existing constant sheaf
  with AsSmall.down. `cbcOpenModelCoefficientMap` is precomposition of the actual
  `proEtaleConstantDirectImageMap`. Thus its adjunct is precisely c_g, with each
  constant b sent to the same constant b. Restriction of this map is
  `sliceModuleRingMap`, so the localized coefficient action is the one specified
  by 04J0, not an arbitrary ringed structure.
- `cbcOpenFinitePullback` is Mathlib's `SheafOfModules.pullback` along this
  structural map. This is the ordinary module tensor pullback: `pullbackIso`
  identifies it with presheaf module pullback followed by module sheafification.
  Equivalently it is inverse image followed by extension of scalars along c_g;
  these are coordinates of the recorded pro-etale module pullback on the small
  model, not a private replacement construction of inverse image or tensor.
- The source restriction directly uses the published
  `SheafOfModules.localizedSystemRestriction`; `cbcOpenTargetRestriction`
  specializes the same declaration. Both are the sectionwise `overFunctor`.
- `cbcOpenExtension` is the recorded `localizedSystemExtension`: literally
  `extensionByZeroPresheaf ⋙ PresheafOfModules.sheafification (𝟙 _)`. Thus it is
  exactly j_!F = P_F^#, not an arbitrarily selected left adjoint.
- The adjunction directly uses the recorded
  `SheafOfModules.localizedSystemAdjunction`. Its unique
  summand-insertion unit fixes its normalization. No arbitrary adjunction
  variable, unit or counit is assumed.
- `cbcOpenLocalizedPullback` is j_! followed by g_B^* followed by j'^*, i.e. H.
- `cbcOpenLocalizedCounit` is literally whiskering the actual adjunction counit
  with g_B^* followed by j'^*. The associator and unitor only fix parentheses.
  The first conjunct says `IsIso (cbcOpenLocalizedCounit g B U)`.
- `cbcOpenSlicePullback` is the actual localized pullback along the restricted
  canonical ring map. `cbcOpenSliceComparison` is the published
  `sliceModulePullbackMap`, the inverse mate of the identity-on-sections direct
  image square. This is the canonical lambda in the node, not an arbitrary iso.
  Its `IsIso` is the second conjunct.
- The existential natural isomorphism `alpha : H ≅ cbcOpenSlicePullback ...`
  is fixed by `alpha.inv.app F = g_U^*(eta_F) ≫ lambda_(j_!F)`. This is precisely
  the inverse of alpha in node proof Step 5, written without a premature
  instance for invertibility of eta. The next clause is
  `beta_M = alpha_(j^*M) ≫ lambda_M`, i.e. the claimed exact identification of
  beta with the canonical localized pullback comparison.
- `cbcOpenExtensionGenerator` is the module sheafification unit on P_F.
  The next clause says the actual unit at a section s over W is that
  sheafification unit applied to `DirectSum.lof ... W.hom s`.
- The following clause says the actual counit sends that same generator, for
  F = j^*M, to s in M(W.left). Thus both final adjunction formulas in the node
  are sectionwise equalities of the actual specified transformations.
- The last clause is the explicit generator formula for beta.
  `cbcOpenPullbackGenerator ... V W psi s b` means `[V,psi,s] tensor b`:
  apply the actual module pullback unit at V, restrict along psi, then multiply
  by b in the target coefficient sheaf. In that clause phi indexes the
  extension summand and psi is a morphism in the target slice, so it satisfies
  the required compatibility over the inverse-image open. The formula sends
  `[V,psi,iota_phi(s)] tensor b` to `[V,psi,s] tensor b`. Neither this clause nor
  the helper assumes all sheaf sections are global presheaf generators.

Dependencies read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleBaseChange`, `proEtaleSiteModel`, `proEtaleModelTopology`,
  `proEtaleModelBaseChange`, `proEtaleConstantDirectImageMap`, and the module
  inverse-image and coefficient tensor-pullback declarations and docstrings.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `Scheme.ProEt.weaklyEtale_localization`, `sliceEquiv`, `sliceTo`, `sliceFrom`;
  these give the interpretation of the slice sites, rings and module categories.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  `ProEtale.finiteCoefficientInverseImageMap_isIso`,
  `finiteCoefficientConstantComparison_isIso`, and
  `finiteCoefficientInverseImageMap_constant`. These identify the constant-ring
  coordinates with the node's canonical finite coefficient maps.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and its public
  tensor imports supply the recorded independent-universe tensor interface.
  The actual module pullback uses Mathlib's existing pullback construction.
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`:
  `SheafOfModules.extensionByZeroPresheaf`, `extensionByZeroPresheafObj`, and
  their direct-sum and restriction definitions (publicly imported through the
  localized module interface).
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification` and `sheafificationAdjunction`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`:
  `SheafOfModules.localizedSystemExtension`, `localizedSystemRestriction`,
  `localizedSystemAdjunction`, `localizedSystemAdjunction_existsUnique`.
- `Mathlib.CategoryTheory.Sites.CoverLifting`:
  `Functor.pushforwardContinuousSheafificationCompatibility` and
  `toSheafify_pullbackSheafificationCompatibility`, specializing to Over.forget
  and abelian-group values. This dependency is a Mathlib match, not an unstated
  node requiring a new record.
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`:
  `SheafOfModules.localize_ringed_site_morphism_general`,
  `ringedSiteModuleMap`, `localizedRingedSiteMap`.
  Its published comparison helpers are imported directly from
  `Sheaf.CategoryTheory.Sites.LocalizedModulePullbackComparison`:
  `sliceModuleRingMap` and `sliceModulePullbackMap`.
  `overPost_isContinuous` from `LocalizedSheavesOverRepresentable` supplies the
  continuity instance without introducing a postponed claim.

Edge cases checked mathematically: g = identity; U = Y; U empty; inverse-image
open empty even when U is nonempty; X empty; the zero coefficient ring; zero
module sheaves; objects admitting no arrow to U (zero direct sum). No Nontrivial,
Nonempty or nonzero condition is imposed. Over an object of the open slice the
summand is unique by openness. In the tensor generator clause b is a section of
B_X(W), not incorrectly an element of the abstract ring B. Ring sheaf sections
are never assumed globally constant. All variables and the universe are explicit;
`open Classical in` supplies only decidable equality for direct sums.

Searches actually run with msearch.py, NE and this item:

- leanfinder: "The pullback of extension by zero counit restricted to a cartesian
  open is the canonical localized module pullback comparison". Eight hits,
  including pullback_map_ιFree_comp_pullbackObjFreeIso_hom, pullbackObjUnitToUnit,
  pullbackObjFreeIso, pullbackComp and pullbackIso. None states this node.
- loogle: "SheafOfModules.overFunctor, CategoryTheory.Adjunction.counit".
  Successful search, zero hits.
- grep: "extensionByZero.*[Cc]ounit|localized.*[Cc]ounit|[Cc]ounit.*extensionByZero".
  Successful Mathlib search, zero hits.
- rg in both project roots for localized/open counit, extension counit and the
  item id: existing `AdicPullbackPresentationTransport` gives only the special
  reduction-ring comparison-isIso and no full finite-ring canonical comparison
  or unit/counit/generator statement. Ordinary scheme module and derived
  localized counit lemmas concern different sites and maps. The exact proposed
  declaration names and item id have no declaration match in the source roots
  or `dag/lean_names_upstream.json`.

No statement fault or mathematical dispute was found. In particular alpha is
normalized using both lambda and the actual unit, as the node proof specifies;
the attribution of alpha solely to ringed localization is understood with this
explicit normalization. Stage 2 leaves the one named theorem's proof as `sorry`.


## Return repair

The return at immutable head `ebdeae754d6f` reports two colliding helper names:
`AlgebraicGeometry.Scheme.cbcOpenRestriction` and
`AlgebraicGeometry.Scheme.cbcOpenAdjunction`. I read the declarations and docstrings
in `Sheaf.Paper.CompletedExtensionZeroComparison` (restriction at line 342,
adjunction at line 380). They take an `AdicCoefficientDatum`, an open scheme
morphism and its openness witness, and operate on completed adic module sheaves
on the scheme sites. This item instead takes an arbitrary finite commutative
ring and uses literal slices of the small site model. Replacing the finite
coefficient objects by those completed objects would change the statement.

Both colliding aliases have been deleted, rather than renamed. Every occurrence
now applies the existing `SheafOfModules.localizedSystemRestriction` or
`SheafOfModules.localizedSystemAdjunction` from the already imported dependency
`Sheaf.CategoryTheory.LocalizedModuleExactForSystems` directly, at exactly the
arguments formerly in the aliases. Their entries have also been removed from
`lean.declarations`. No completed coefficient declaration is copied or renamed.
No import of the downstream completed comparison is needed. These substitutions
are expansions of the deleted abbreviations, so all hypotheses, the actual
unit/counit, alpha normalization, and generator equations are unchanged.

The current shared node still has no `lean` field. Its other fields agree with
the retained packet. The delivery wrapper is responsible for rebasing onto the
current server branch; no direct Git operation is performed in the shared clone.

## Second reading by NE

Read the retained node and repaired source together. The schemes and arbitrary
morphism, finite coefficient ring and open object binders are unchanged. The two
isomorphism assertions, inverse-alpha normalization, identification of beta,
unit summand insertion, counit summand evaluation and pulled-back generator
formula are unchanged after expanding the former aliases. Both removed names
are absent from declaration commands and the delivered declaration list. The
reused generic adjunction is the same uniquely normalized choice as before.
The empty-open, identity-map and zero-ring cases retain the same types. There
is still exactly one postponed theorem and no postponed definition data.


Validation in this repair session: the initial saved-packet dry run and the
post-repair explicit `scompile.py` invocation both failed before checking this
module. The local overlay dependency
`WeilConjectures.Mathlib.CategoryTheory.NatIso` cannot resolve module prefix
`Mathlib`; server confirmation reports `Live published library is unavailable`.
This is an environment/tool failure, not an elaboration diagnostic for this file.
The packet self-check verifies the 100-character limit, exactly one `sorry`,
complete declaration list, verbatim stored signature, absence of the colliding
declarations, and equality of every non-`lean` node field with the current clone.
This section records the same worker's renewed reading; no second agent was
started, as the dispatcher explicitly forbids it. Independent stage-2 review
remains the maintainer's responsibility.

The final repaired-packet `deliver2.py --no-push` retry also failed before this
module was compiled. Its refreshed overlay now finds Mathlib's prefix but lacks
`Mathlib/CategoryTheory/Functor/Category.olean`; server confirmation again says
`Live published library is unavailable`. No files were pushed. The repaired
packet is retained for compilation and delivery after the published build is
restored. No launcher tool, shared source, or compiled library was modified.

## Retained-packet retry, 2026-10-21

As instructed, this retry first read the saved report and ran
`deliver2.py NE lem-cbc-open-localized-counit-comparison --no-push`. It failed
before compiling this item: overlay `WeilConjectures.Mathlib.CategoryTheory.NatIso`
cannot load `Mathlib/CategoryTheory/Functor/Category.olean`. Server confirmation
reports `Live published library is unavailable`. An explicit `scompile.py` of
the retained module subsequently produced the identical failure and confirmation.
This is neither a timeout nor a duplicate-declaration diagnostic.

I re-read the removed-name usages in the repaired module and the completed
coefficient declarations in `CompletedExtensionZeroComparison`. The saved repair
already deletes both colliding aliases and uses the published generic restriction
and adjunction directly. A fresh self-check confirms that both names are absent
from the delivered module, all 13 declarations match `lean.declarations`, the
stored theorem signature is verbatim, every non-lean node field matches the
current shared clone, all lines fit 100 characters, and there is exactly one
`sorry`. The saved source and node are retained unchanged. No push was attempted
because both prescribed validation tools stop at unavailable build artifacts.

## Latest retained-packet repair retry, 2026-10-21

The required initial saved-packet dry run and explicit `scompile.py` both stop
before compiling this item. Overlay module
`WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Preserves` cannot load
`Mathlib/CategoryTheory/Abelian/GrothendieckAxioms/Basic.olean`. Each prescribed
wrapper confirms against the server and reports
`Live published library is unavailable`. This is a missing published build
artifact, not an item elaboration error or a busy-server timeout.

The current clone changed only `lean_audit` from null to an empty object since
the saved packet. Rebased the node copy onto that current record, retaining only
the packet's `lean` field as this delivery's delta. No mathematical statement,
Lean source or signature changed. Re-read both completed-coefficient declarations
and the saved direct generic adjunction/restriction usages: neither colliding
name is declared or renamed in this module. The mechanical self-check passes:
all 13 declarations match the record, the stored signature is verbatim, lines
fit 100 characters, and the only `sorry` is the named theorem's entire proof.
No second agent was started. Compilation and delivery remain unverified while
the published library is unavailable; no push is attempted.

The post-rebase dry run likewise fails in the same overlay before reaching the
item, now on missing `Mathlib/CategoryTheory/Preadditive/Injective/Basic.olean`.
Server confirmation still reports `Live published library is unavailable`.
The duplicate-alias repair and rebased packet are retained; nothing was pushed.


## Current saved-packet self-check, 2026-10-21

Started by reading this saved report and running the prescribed `deliver2.py
--no-push`, before any packet changes. The retained alias repair is substantive
relative to the returned immutable head: both colliding declarations are deleted,
and their uses expand directly to the published `localizedSystemRestriction` and
`localizedSystemAdjunction`. Re-read their complete signatures and normalization
in `LocalizedModuleExactForSystems`, and the completed-coefficient declarations
in `CompletedExtensionZeroComparison`; the latter have different coefficient and
site arguments and are not substituted for this finite-coefficient statement.

The node copy agrees with the current shared node in every field except `lean`.
The mechanical self-check passes for all 13 declaration names, the verbatim
stored signature, removal of both colliding names, the 100-character line limit,
explicit universe and variable binding, indent-1 JSON with a final newline, and
exactly one `sorry`, the named theorem's proof. The theorem still asserts the
counit and slice-comparison isomorphisms, the unit-normalized alpha, beta's
identification with lambda, and all three generator formulas. Identity maps,
empty opens and schemes, and zero coefficients remain included. No mathematical
statement, helper definition, dependency, or Lean source changed in this retry.

The initial dry run compiled several overlay prerequisites, then stopped before
item compilation on
`WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`, with a
60-second dependency timeout. Its server confirmation reports
`Live published library is unavailable`. An explicit prescribed `scompile.py`
check follows to distinguish this environment failure from item elaboration.

The explicit `scompile.py` check reproduced the same prerequisite timeout at
`WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` before
reaching this module. Server confirmation again reports
`Live published library is unavailable`. Both authorized validation routes fail
outside the packet, so no item elaboration result or successful preflight can
be claimed. The repaired source and node remain intact; nothing was pushed.
No shared source, launcher tool, or published build was modified.

## Import-artifact repair retry, 2026-10-21

Started with the retained packet and the prescribed `deliver2.py --no-push`.
The concrete failure has changed: both the overlay and server confirmation stop
at the import header of `Sheaf.CategoryTheory.SiteInverseImageTensor`, in
0.5--0.6 seconds, because the published object file for
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings` does not exist.
Neither reaches this item or the previously timed-out SheafCohomology.Basic.

To test an authorized repair through the compiler wrapper, supplied the read-only
`ChangeOfRings.lean` source together with this item's source to `scompile.py`.
Server confirmation compiled ChangeOfRings in 2.2 seconds, then stopped at the
same import header because the published object file for
`WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering` does not exist. Read its
current server source with `scompile.py --source`. A subsequent ordinary
single-file `scompile.py` call again fails on the missing ChangeOfRings object
file in both overlay and server confirmation. Explicit source compilation thus
does not restore the published prerequisite for subsequent delivery checks.
These are missing import artifacts, not 60-second definition elaboration limits.
No definition change can be validated while compilation stops before elaboration.
No compiler tool, shared source, or published library has been modified.

Re-read the completed-coefficient `cbcOpenRestriction` and `cbcOpenAdjunction`
signatures and the generic localized restriction/adjunction declarations used by
the packet. The retained repair deletes both colliding aliases and applies the
published generic declarations directly, with no renamed duplicate. The packet
self-check confirms: no non-lean field differs from the current shared node;
all 13 declarations match the record; the theorem signature is verbatim;
no line exceeds 100 characters; JSON uses indent 1 and a final newline;
autoImplicit is false; and the only sorry is the named theorem's entire proof.
The mathematical statement and its empty-open, empty-scheme, identity-morphism
and zero-ring cases are unchanged. No push or successful compile is claimed.

The final dry run still fails before reaching this item. Its overlay retains the
missing ChangeOfRings import diagnostic; current server confirmation now gets
past SiteInverseImageTensor using its cache and fails at the import header of
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage` on missing published
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic.olean`, in 0.6 seconds.
Thus the current blocker remains unavailable prerequisite artifacts, with no
60-second timeout and no item elaboration diagnostic. Nothing was pushed.

## Dispatcher retry validation, 2026-10-21

Started with the saved packet: read this report and ran the prescribed
`deliver2.py NE lem-cbc-open-localized-counit-comparison --no-push` before edits.
Its local compile failed on missing published
`WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients.olean`;
server confirmation stopped at the import header of ProEtaleInverseImage on
missing `WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic.olean`, in
0.5 seconds. It did not compile this item's module.

The subsequent explicit `scompile.py` of this item's retained module failed in
both local compilation and server confirmation at the import header of
LocalizedModuleAdjunctionExact: published
`WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous.olean` does not exist
(0.4 seconds). Neither failure is a busy-server timeout or an elaboration error
in the delivered definition. The wrappers cannot validate the packet against
the published prerequisites. The earlier source-supplying attempt recorded above
also did not restore prerequisite availability for delivery validation.

Re-read the completed-coefficient restriction and adjunction signatures, and the
published generic localized restriction and uniquely normalized adjunction used
by the repair. The retained source deletes both colliding aliases and applies
the generic declarations directly. No alias was renamed or reintroduced.
A fresh mechanical self-check passes: every non-lean node field agrees with
the current shared clone; all 13 declarations equal lean.declarations; the
stored theorem signature is verbatim; no line exceeds 100 characters; exactly
one sorry remains, as the named theorem's proof; autoImplicit is false; the JSON
has indent 1 and a final newline. The source, node, hypotheses and clauses are
retained unchanged. No second agent, shared-source edit, tool modification or
push was performed. Delivery remains blocked by missing published prerequisites.

## Saved-packet validation retry, 2026-10-21

Read the saved report and ran the required initial `deliver2.py NE
lem-cbc-open-localized-counit-comparison --no-push` before changing the packet.
Both local compilation and server confirmation stopped before this item's
module: the import header of
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleObject` could not load
published `WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients.olean`
(0.4--0.5 seconds). The subsequent explicit prescribed `scompile.py` invocation
likewise stopped at that prerequisite's import header, in both execution paths,
on missing published
`WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf.olean`
(0.4 seconds). These are missing published artifacts, not item elaboration
failures or busy-server timeouts. No successful compile or preflight is claimed.

Re-read this node's statement and proof, the complete retained module, the
completed-coefficient restriction/adjunction declarations in
`CompletedExtensionZeroComparison`, and the generic restriction and normalized
adjunction signatures in `LocalizedModuleExactForSystems`. The saved repair
removes both colliding aliases and applies the generic declarations directly;
it neither renames them nor copies completed-coefficient constructions. The
finite coefficient binders, open object, actual counit, canonical slice map,
unit-normalized alpha, beta identification, and unit/counit/pullback generator
clauses remain as recorded. Empty opens and schemes, identity morphisms and
zero coefficient rings remain included.

A fresh mechanical check finds no non-lean field difference against the current
shared node. All 13 declarations match `lean.declarations`, the stored theorem
signature is verbatim, both colliding names are absent from the source, every
line fits 100 characters, `autoImplicit` is false, and the only sorry is the
named theorem's proof. JSON has indent 1 and a final newline. The substantive
alias repair is retained unchanged. No shared source, launcher tool, published
build, or Git state was modified directly; no second agent or push was used.


## Current prerequisite-artifact retry, 2026-10-21

As required, read the saved report and ran the initial prescribed
`deliver2.py NE lem-cbc-open-localized-counit-comparison --no-push` before
changing the packet. It stops before item compilation: the overlay cannot load
published `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs.olean`.
Its server-source confirmation proceeds further but fails on missing published
`WeilConjectures.Topology.Stratification.olean` while importing
`Sheaf.CategoryTheory.ModuleInverseImageAdjunction` (0.4 seconds).

The separate prescribed `scompile.py` invocation likewise fails on the same
Etale prerequisite in the overlay. Its server-source confirmation proceeds
through cached prerequisite overrides, then fails at the import header of
`Sheaf.AlgebraicGeometry.ProEtaleOperations` on missing published
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs.olean`
(0.1 seconds). Neither failure is a busy-server timeout or an elaboration error
in the delivered item. Neither validation route reaches this module.

Re-read both completed-coefficient declarations and the generic localized
restriction, normalized adjunction, and uniqueness theorem used by the retained
repair. The two colliding aliases remain deleted, not renamed. A fresh
mechanical check confirms no non-lean field differences against the shared
node, all 13 declarations matching the record, a verbatim stored signature,
100-character lines, one sorry in the named theorem's proof, indent-1 JSON,
and a final newline. The retained module and node are unchanged. No shared
source, compiled library, launcher tool, direct Git state, or second agent
was used to repair the prerequisite environment. No successful compile,
preflight, or delivery is claimed, and nothing was pushed.
