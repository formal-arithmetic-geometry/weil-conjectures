## Worker report

Q87 states `lem-sfb-dg-finite-principal-hom-descent` in
`Sheaf.CategoryTheory.DgFinitePrincipalHomDescent`, with the single theorem
`CategoryTheory.SheafDg.PrincipalHom.finite_principal_hom_descent` left `sorry`.
The auxiliary module `Sheaf.CategoryTheory.DgPrincipalHomModels` contains real definitions
and coordinate specifications, with no postponed proofs or chosen data. No source statement
is changed. The existential model data are conclusions of the theorem; none are assumptions
on the input algebra or modules. In particular the theorem does not assume that an
augmentation, localized Hom diagram, projective resolution, or derived Hom functor exists.

Sources read: the full node statement and its nine proof steps; its two statement-dependency
nodes and their recorded declarations; Stacks `perfect.tex`, label
`lemma-alternating-cech-complex-complex-computes-cohomology` (08D2), including the immediately
preceding total-sign discussion; the current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
and its direct-images proof. The dg refinement is explicitly agent-formulated in the node,
not a verbatim assertion of 08D2. The code follows the node's explicit refinement.

Clause-by-clause correspondence:

- A commutative ring is `{S : Type u} [CommRing S]`. The structural binder
  `[HasDerivedCategory.{u + 1} (ModuleCat.{u} S)]` chooses the ordinary coefficient
  localization in its standard morphism universe; `HasDerivedCategory.standard` always
  supplies it. This is no restriction on S. Every universe and variable is explicit.
- `A : PrincipalHom.Algebra S` abbreviates the RECORDED
  `SheafDg.Algebra (singletonRingSheaf S)`. It is a unital associative monoid in the
  S-linear total-tensor category of complexes. Thus the S-action is central in degree zero
  and the differential is S-linear; no graded commutativity is imposed. The existing
  punctual site identifies this with an ordinary S-dg algebra. `LeftModule`, `GradedMap`,
  `Derived`, `moduleQ` and `derivedShift` are the original dependency declarations.
- `r : ℕ`, `hr : 1 ≤ r`, `f : Fin r → S`, and
  `hf : Ideal.span (Set.range f) = ⊤` are exactly the finite nonempty unit-ideal cover.
  `Fin r` uses zero-based labels; its order supplies the same alternating signs.
- Every principal localization is asserted in the first conjunct
  `∀ g : S, Nonempty (LocalizationModel A g)`. The dg algebra map is degreewise an
  `IsLocalizedModule (Submonoid.powers g)` map. This is the module-localization universal
  property, including surjectivity by fractions, invertible denominators and the equality
  criterion, not just an invertibility test. Therefore its degree-n target is canonically
  `(S_g) ⊗[S] C^n`, and the chain-map and multiplicativity equations fix its differential
  and product. We keep the S-coefficient presentation, which is the restriction to S of
  the unique S_g-action; this is precisely the coefficient convention on the theorem's
  right side. There is no arbitrary algebra map standing in for localization.
- `LocalizationModel.map` uses the original `SheafDg.extension`, the balanced tensor
  coequalizer, and the original `restrictScalars`. `counit_normalization` equates its
  adjunction counit to the original `actionCounit` (b tensor n ↦ bn). This pins the
  ordinary unit to x ↦ 1 tensor x. `module_localized` says that very unit, in each degree,
  is the module localization, hence is x ↦ x/1. `exact_extension` and
  `exact_restriction` preserve arbitrary quasi-isomorphisms. The termwise localization
  property also implies ordinary exactness via `IsLocalizedModule.map_exact`.
  `derivedExtension`, `derivedRestriction`, their comparison isomorphisms,
  `derivedAdjunction`, and `unit_normalization` express the exact derived adjunction.
- `Intersections r` is all nonempty finite subsets. `product f J` is the actual finite
  product of the f_j. `Index r p` specifies `J.card = p+1`, with nonemptiness. The local
  algebra and module in `LocalDiagram` are precisely those at `product f J`.
- `HomModel.coordinate`, `injective` and `range` identify the ENTIRE term of degree q
  with the recorded signed `GradedMap` space, after punctual evaluation. In particular
  h(cx)=(-1)^(q|c|)c h(x), and there are no additional cochains or missing maps.
  `differential` is Mathlib `HomComplex.δ`, namely d_N h-(-1)^q h d_P.
  Its S-linear coordinates retain the coefficient-module structure.
- Arbitrary `M,N : Derived A` range over the pair Z in the final `∀ Z`.
  `DerivedHomModel.functor` is the derived bifunctor. `resolution`, `resolutionMap`,
  `resolution_quasiIso` give an actual quasi-isomorphism P→M's canonical word-object
  representative; `resolution_projective` gives acyclic Hom(P,L) for every acyclic L.
  `compute` computes RHom by the strict Hom complex for EVERY such P and every N, not
  just the selected resolution; `compute_natural` normalizes its maps. Its `cohomology`
  is an additive equivalence H^q RHom(M,N) ≃+ Hom_D(C)(M,N[q]) for every integer q.
  The additive structure on D(C) is required to make `moduleQ` additive, so it agrees
  with the underlying chain-map addition.
- Canonical independence is the final `∀ H' R', ∃! e, IsCanonicalHomComparison ... e`.
  The property pins the strict comparison to identical homogeneous cochains and pins
  the derived comparison on every projective computation. Thus it specifies the canonical
  natural isomorphism, not an unnormalized equivalence between arbitrary objects.
- `LocalDiagram.toLocal_fraction` fixes the canonical Hom restriction by its value on
  every x/1; `change_unit` fixes all further module localizations and
  `transition_fraction` fixes the corresponding Hom transitions. Generation by fractions
  makes those equations determining. `DescentData.localized_projective` ensures that
  P_fJ computes each local RHom, with `localDerivedHom` supplying the normalized derived
  models. All local Hom complexes are S-complexes, as required after restriction.
- `CechModel.coordinate` gives exactly the product indexed by |J|=p+1 in each bidegree;
  `vertical` gives the Hom differential and `horizontal` gives the alternating deletion
  sum with sign (-1)^(number of smaller indices). The condition is stated on each
  coordinate generator; finite linearity determines the entire map. `naturality` fixes
  its action on both module variables. Empty coordinate products are zero modules, so
  the double complex has precisely the columns 0,...,r-1.
- `HomologicalComplex₂.totalFunctor` on up/up integer complexes uses horizontal sign 1
  and vertical sign `p.negOnePow` (`ComplexShapeSigns.lean`, TensorSigns and its induced
  TotalComplexShape instance). Hence its total differential is exactly
  delta+(-1)^p d_Hom. Although Mathlib uses a general direct-sum total, only the specified
  finite set of columns is nonzero in every total degree.
- `CechModel.augmentation_formula` says the strict comparison is the singleton
  restrictions followed by the column-zero total inclusion, with every other component
  zero. `DescentData.compute`, `compute_natural` descend the WHOLE strict finite diagram
  on projective resolutions to its derived total; the local Hom objects are not totaled
  independently in a triangulated category. `comparison_formula` transports exactly that
  augmentation to `comparison : derivedHom.functor ⟶ total`. The main conclusion
  `∀ Z, IsIso (d.comparison.app Z)` is the stated isomorphism in D(S), naturally in both
  derived variables. It is not only a cohomology-level assertion.
- No compactness, boundedness, flatness, Noetherian or finite generation hypotheses occur
  anywhere on S, A, P, N or M. The only finite index is the specified principal cover.

Recorded dependency declarations used:

- `Sheaf.CategoryTheory.SheafDgModuleLocalization`: `CategoryTheory.SheafDg.Algebra`,
  `LeftModule`, `GradedMap`, `Derived`, `moduleQ`, `derivedShift`, `quasiIsomorphisms`,
  `extension`, `restrictScalars`, `actionCounit` (their full signatures and docstrings read).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`; coefficient cohomology is the
  `DerivedCategory.homologyFunctor` in its HomologySequence module.
- `Sheaf.ProperBaseChange.SingletonSiteModuleComparison`: `singletonRingSheaf`,
  `singletonEvaluation`, its additive instance and the existing punctual-site comparison.
  No duplicate punctual site or ordinary module category is defined.
- The proof imports all currently recorded proof-dependency modules: the upstream affine
  Čech theorem `Scheme.Modules.exactAt_cechComplex_basicOpen`, upstream
  `HomologicalComplex₂.quasiIso_of_finite_strip_row_augmentation`, and
  `CategoryTheory.DgAlgebra.homotopy_acyclic_localization`. The Mathlib match for
  `lem-weil-pbc-localization-module-exact` is imported privately as
  `Mathlib.Algebra.Module.LocalizedModule.Exact` (`LocalizedModule.map_exact`).
  The other four dg proof nodes have no recorded Lean declaration, so they have no
  import yet; their arguments are retained by name in the nine-step theorem docstring.

Edge cases checked before writing and on the second pass:

- r=1: the sole generator is a unit; there is one column, its augmentation is the
  ordinary localization Hom map, and it becomes the identity under the canonical
  localization identification. The horizontal face target is empty.
- Zero ring, zero algebra and zero modules are allowed: no nontriviality or faithful
  action is assumed. Localizing at zero or a nilpotent gives zero coordinates, which
  all the model specifications permit. A unit in the cover also gives the usual
  redundant-coordinate Čech resolution.
- `Index r p` is empty for p<0 and p≥r, but all internal degrees and all source-module
  degrees remain arbitrary integers. Finite regrouping across these columns does not
  require boundedness or compactness of the source.
- The empty cover is excluded exactly by `hr`, including over the zero ring, as in
  the node. Empty intersections do not introduce an extra augmentation column.
- The Hom sign, signed left shift, total sign and deletion order were checked
  against the recorded dependency and Mathlib's actual definitions.

Searches (actual wrapper records are in searches.jsonl and copied verbatim into the new
node's mathlib_searches):

- LeanFinder: "Derived Hom over a differential graded algebra satisfies finite principal
  localization Cech descent" returned eight ordinary derived-localization/fraction results,
  none the requested statement.
- Loogle: `"Cech", "Localization"` returned zero matches.
- Mathlib grep: `dgHom|dg.*Cech|Dg.*Cech|[Hh]omotopically[Pp]rojective` returned zero matches.
- LeanSearch: "Hom complexes for left differential graded modules with signed graded
  linearity" found the existing ordinary cochain and Hom differential definitions used
  here, but no dg-linear subcomplex/localization diagram.
- LeanFinder: "Strict homogeneous Hom model and finite alternating principal localization
  Cech double complex for left differential graded modules over a central commutative
  coefficient ring" returned standard representation resolutions, tensor and bicomplex
  constructions, with no matching model.
- Mathlib CategoryTheory grep: `GradedLinear|HomModel|LocalizationModel|CechModel` returned
  zero matches.
- Project `rg` and the requested node-id search in WeilConjectures found no existing
  finite-principal dg-Hom descent theorem. Sheaf search found the recorded sheaf-dg
  definitions and `DgBimoduleModels.BimoduleHomModel`: the latter is for right modules
  over integer dg algebras and has precomposition action, so it is not this left
  S-linear, signed, scalar-localization interface. Its source was read, not duplicated.
- DAG `blueprint_refs.py search 'dg Hom'` returned no blueprint-node matches;
  `search 'principal localization'` returned four unrelated scheme/ordinary-algebra
  nodes. Node text searches found the assigned theorem and existing ordinary coefficient
  Hom models, but no existing node for these strict left-dg principal Hom coordinates.

Validation: both delivered modules compiled separately, in dependency order, using
scompile.py against the live server publication. The expected one `sorry` is the entire
proof of the named main theorem. An initial server confirmation compiled both modules successfully. After the counit
normalization was added, the server overlay began failing on the pre-existing
SheafDgModuleLocalization dependency with ENOSPC (error code 28). Both scompile.py and
the required deliver2.py dry run have reproduced that infrastructure failure.
No statement dispute, dependency-record repair, or statement correction is needed.

## New nodes

`def-sfb-dg-principal-hom-models` introduces the strict dg-linear Hom, universal principal
localization, fraction-normalized diagram and finite alternating total specifications.
Its own module has no theorem or `sorry`. The source is Stacks 09LN/08D2 with the explicit
left-module refinement already written in this item's proof. This is the missing interface,
not a new dg algebra/module/derived-category definition: those are aliases of the recorded
sheaf-dg declarations, specialized using the existing punctual ring sheaf and evaluation.
The ordinary Hom cochains and total complex are Mathlib's. The searches listed above show
why the combined strict localization-and-Hom interface is new. The new node cites exactly
the sheaf-dg, punctual comparison and abstract-derived dependency nodes it uses. Its
blueprint ancestor and via are inherited from the assigned item as returned by
`blueprint_refs.py ancestor`; it asserts no additional existence or descent theorem.

## Second reading by Q87

The dispatcher forbids starting another agent. This section records a separate rereading
by the same worker; the maintainer supplies the independent review of this delivery.
I reopened the original node, both module files and the recorded dependency declarations.
The clause correspondence above was checked against the actual fields, especially the
localization units, signed graded-linearity range condition, finite index set, total signs
and derived augmentation normalization.

The first pass specified a localization adjunction unit only by its localization universal
property. That leaves a scaled unit possible, which would not name the canonical fraction
map relative to the chosen balanced tensor quotient. I added `counit_normalization` against
the dependency's action counit, fixing b tensor n ↦ bn and hence fixing x ↦ 1 tensor x.
I also included existence of localization data for every g in S, independently of which
products occur in the finite cover. The only compiler repair was to publicly import
`Mathlib.RingTheory.Ideal.Span`, because the theorem's unit-ideal predicate is public.
No hypotheses were added to the original mathematical input and no conclusion was removed.

## Retry on 2026-10-24

Retained the saved packet and first ran the prescribed `deliver2.py Q87
lem-sfb-dg-finite-principal-hom-descent --no-push`. It exited 1 after 22 seconds:
`COMPILE FAILED on the server, nothing pushed`, followed by
`overlay Sheaf.CategoryTheory.SheafDgModuleLocalization` and
`resource exhausted (error code: 28, no space left on device)`.
Confirmed with `scompile.py` on both saved module files, in dependency order;
it exited 1 after 22 seconds with the identical overlay dependency and ENOSPC error.
Both delivered files already use module mode. The failure occurs in the existing
server dependency overlay before either delivered file is compiled. No Lean or
node changes were made, and nothing was pushed. Server storage and launcher scripts
are outside this worker's authorized repair scope; the complete packet is retained.

## Dispatcher retry confirmation on 2026-10-24

Read the retained report and ran the required dry run before any packet changes.
`deliver2.py Q87 lem-sfb-dg-finite-principal-hom-descent --no-push` again exited 1
after 22 seconds, reporting `COMPILE FAILED on the server, nothing pushed`,
`overlay Sheaf.CategoryTheory.SheafDgModuleLocalization`, and
`resource exhausted (error code: 28, no space left on device)`.
Then ran `scompile.py Q87 lem-sfb-dg-finite-principal-hom-descent` with both saved
modules, `DgPrincipalHomModels.lean` followed by `DgFinitePrincipalHomDescent.lean`.
It also exited 1 after 22 seconds with the identical existing-dependency ENOSPC
diagnostic. Reopened both module headers: both begin with `module`, with public
statement imports and private proof imports as required. There is no Lean
elaboration diagnostic to repair; compilation fails in the existing dependency
overlay before checking the delivery. Retained both modules and both node records
unchanged. No push was attempted. The remaining fault is server storage, outside
the sandbox-only write authorization.

## Dispatcher retry at 2026-10-24 10:43 UTC

Inspected the retained report and first ran the required saved-packet dry run:
`deliver2.py Q87 lem-sfb-dg-finite-principal-hom-descent --no-push`.
It exited 1 after 22 seconds with `COMPILE FAILED on the server, nothing pushed`,
`overlay Sheaf.CategoryTheory.SheafDgModuleLocalization`, and
`resource exhausted (error code: 28, no space left on device)`.
Confirmed using the prescribed `scompile.py` with both retained modules in
 dependency order; it also exited 1 after 22 seconds with the identical existing
server-dependency ENOSPC failure. Both delivered modules begin with `module`.
There is no delivered-file elaboration diagnostic to repair. Retained both Lean
files and both node records unchanged; no push attempted. Repairing server storage
is outside the sandbox-only write scope, and launcher tools must not be modified.

## Dispatcher retry at 2026-10-24 10:46 UTC

Inspected the saved report and ran the prescribed saved-packet dry run first.
`deliver2.py Q87 lem-sfb-dg-finite-principal-hom-descent --no-push` exited 1
with `COMPILE FAILED on the server, nothing pushed`, followed by
`overlay Sheaf.CategoryTheory.SheafDgModuleLocalization` and
`resource exhausted (error code: 28, no space left on device)` after 22 seconds.
Confirmed using `scompile.py` with both retained modules in dependency order;
it exited 1 after 22 seconds with the same dependency overlay and ENOSPC error.
Both retained module headers use module mode and public statement imports.
The failure precedes checking either delivered file, so there is no new Lean
diagnostic to repair. Retained both modules and both node records unchanged.
No push attempted. Server storage is outside this worker's sandbox-only write
scope; launcher scripts are also explicitly excluded from modification.

## Dispatcher retry at 2026-10-24 10:49 UTC

Read the retained report and first ran the prescribed saved-packet dry run.
`deliver2.py Q87 lem-sfb-dg-finite-principal-hom-descent --no-push` exited 1
with `COMPILE FAILED on the server, nothing pushed`, followed by
`overlay Sheaf.CategoryTheory.SheafDgModuleLocalization` and
`resource exhausted (error code: 28, no space left on device)` after 22 seconds.
Confirmed with `scompile.py` on both retained modules, in dependency order;
it also exited 1 after 22 seconds with the identical existing-dependency ENOSPC
failure. Both delivered files begin with `module` and use public statement imports.
The tools fail before checking either delivered file; there is no new Lean diagnostic
to repair. Retained both modules and both node records unchanged. No push attempted.
Server storage is outside the sandbox-only write authorization, and launcher scripts
are explicitly excluded from modification.

## Dispatcher retry at 2026-10-24 10:55 UTC

Read the saved report and ran the prescribed saved-packet dry run first.
`deliver2.py Q87 lem-sfb-dg-finite-principal-hom-descent --no-push` exited 1
after 22 seconds with `COMPILE FAILED on the server, nothing pushed`,
`overlay Sheaf.CategoryTheory.SheafDgModuleLocalization`, and
`resource exhausted (error code: 28, no space left on device)`.
Confirmed with `scompile.py` on both retained modules in dependency order;
it exited 1 after 22 seconds with the identical dependency-overlay error.
Reopened both module headers: both use module mode. The failure occurs
before checking either delivered file and supplies no Lean diagnostic to repair.
Retained both modules and both node records unchanged; nothing was pushed.
Server storage is outside the sandbox-only write authorization, and launcher
scripts must not be modified or worked around.


## Dispatcher retry at 2026-10-24 11:05 UTC

Inspected the retained packet and ran the prescribed saved-packet dry run first.
Both that dry run and a second dry run after a short wait exited 1 with
`COMPILE FAILED on the server, nothing pushed`,
`overlay Sheaf.CategoryTheory.SheafDgModuleLocalization`, and
`resource exhausted (error code: 28, no space left on device)`.
Confirmed with `scompile.py` on both retained modules in dependency order;
it exited 1 with the identical existing-dependency overlay failure.
The failure precedes compilation of the delivered files. Both module headers
use module mode. No Lean file or node record was changed; no push was attempted.
Server/compiler storage repair is outside the sandbox-only write scope.

## Dispatcher retry at 2026-10-24 11:08 UTC

Read the saved report and first ran the required saved-packet dry run.
`deliver2.py Q87 lem-sfb-dg-finite-principal-hom-descent --no-push` exited 1
with `COMPILE FAILED on the server, nothing pushed`, followed by
`overlay Sheaf.CategoryTheory.SheafDgModuleLocalization` and
`resource exhausted (error code: 28, no space left on device)` after 22 seconds.
Confirmed using the prescribed `scompile.py` with both retained modules in
 dependency order; it exited 1 after 22 seconds with the identical existing
server-dependency ENOSPC failure. Reopened both module headers: both use module
mode, public statement imports, and `autoImplicit false`. The failure precedes
checking either delivery file and supplies no Lean diagnostic to repair.
Retained both Lean files and both node records unchanged; nothing was pushed.
Server storage repair is outside the sandbox-only write authorization, and
launcher scripts must not be modified or worked around.


## Dispatcher retry at 2026-10-24 11:11 UTC

Inspected the saved report and ran the prescribed saved-packet dry run first.
`deliver2.py Q87 lem-sfb-dg-finite-principal-hom-descent --no-push` exited 1
with `COMPILE FAILED on the server, nothing pushed`, followed by
`overlay Sheaf.CategoryTheory.SheafDgModuleLocalization` and
`resource exhausted (error code: 28, no space left on device)` after 22 seconds.
Confirmed with `scompile.py` on both retained modules in dependency order;
it also exited 1 after 22 seconds with the identical existing-dependency ENOSPC
failure. Reopened both module headers: both use module mode, public statement
imports and explicit variable binding. The failure precedes checking either
delivered file, so it supplies no Lean diagnostic to repair. Retained both Lean
files and both node records unchanged; no push attempted. Server storage is
outside the sandbox-only write authorization, and launcher scripts must not
be modified.

## Saved-packet repair on 2026-10-24

The required initial dry run now compiled both delivered modules and the private
overlay successfully. Server storage no longer blocks this packet. Its concrete
preflight diagnostic was an erroneous metadata entry:
`lean.declarations` named `CategoryTheory.SheafDg.PrincipalHom.and`, which is not
a declaration. Removed that entry and checked every remaining declaration against
the two retained modules. Recorded both primary signatures verbatim, preserving
their line breaks. No Lean source or mathematical statement changed.

Reread both retained modules, the current item, its statement-dependency records
and source declarations, and the saved clause correspondence. The localization
counit normalization, signed GradedMap coordinates, fraction transitions, finite
Cech total and augmentation match the report. Both modules use `autoImplicit false`;
the sole postponed proof is the named main theorem. The item differs from its
current base only in `lean` and the addition of the delivered definition node to
`stmt_deps`. No statement correction or dependency module is introduced.

Validation after repair: `deliver2.py Q87 lem-sfb-dg-finite-principal-hom-descent
--no-push` printed `OK (dry run)`; both modules compile and server preflight passes.
The earlier ENOSPC entries above are historical retry records, now resolved.
