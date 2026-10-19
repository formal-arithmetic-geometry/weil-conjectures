## Worker report

The delivery states `lem-pur-flag-localized-product` in
`Sheaf.Paper.LocalizedFlagProduct`, namespace
`WeilConjectures.PurityFiniteSetting`. It retains the node's statement and proof plan.
No proofs are supplied: all theorems have proof `sorry`; definitions contain actual
maps, composites, canonical comparison maps, or choice from a uniquely normalized
universal property.

Clause-by-clause reading:

* Finite coefficients are the binder `P : PurityFiniteSetting.{u}`. Its field datum,
  coefficient extension, positive level, ring and fixed size lift are the recorded
  conventions. The auxiliary Kummer exponent is `P.diagonalExponent`; it kills the
  coefficient ring at every positive level, without a ramification divisibility hypothesis.
* The separated finite-type k-scheme is `S`, its structure map `aS`, and the three
  instances `IsSeparated aS`, `LocallyOfFiniteType aS`, `QuasiCompact aS`.
* `LocalizedFlagFiltration S r` packages the given arbitrary filtration: `H` gives its
  levels, with ambient module `H (Fin.last r)`; `step` and `mono` give the successive
  monomorphisms; `zero` says F_0=0; and `line` says each actual sheaf cokernel Q_j
  is invertible. Local lifts of the line quotients give adapted frames, so every
  level and every ambient quotient is locally free; these equivalent properties
  need no additional input fields. It does not require the
  filtration to be the universal one or to split globally. The module reuses the
  dependency's meanings of vector subbundle and invertible quotient.
* `localizedFlagDualRank` supplies the rank i of the coordinate dual, using adapted
  local frames. `localizedFlagBundle` is the recorded `PurityVectorBundle` with its
  coordinate module literally `Scheme.Modules.dual (D.H i)`, chosen total space
  `VectorBundleZeroSection.scheme`, projection `π`, identity comparison `phi`, and
  the recorded augmentation zero section. This is Spec Sym(F_i dual), not Spec Sym(F_i).
* `localizedFlagAlgebraMap` is Sym of the actual transpose inclusion: its degree-one
  map is `Scheme.Modules.dualMap d` followed by the symmetric-algebra inclusion.
  `localizedFlagTotalMap` applies the existing relative-Spec anti-equivalence.
  `localizedFlagInclusion` therefore gives the actual nested total-space map.
* `LocalizedFlagGeometry` records smoothness of all projections, closedness of all
  zero sections, the rank-zero zero-section isomorphism, and for each successive
  inclusion: closedness, invertibility of its kernel ideal, compatibility with the
  projections and zeros, and an isomorphism of its ideal module with the dual of
  pi_j*Q_j. The last clause says its Cartier divisor line is pi_j*Q_j. Polynomial
  charts in its proof identify its equation with the quotient of the tautological
  vector. No smoothness of S is imposed.
* `localizedFlagCartierClass` and `localizedFlagCartierRaw` use the existing ordinary
  supported Kummer class with its unique relative-boundary normalization. It is the ordinary representative
  of the recorded pro-etale supported Cartier class, by `CartierKummerRealization`.
* `localizedFlagProjectionRaw` is the actual adjoint of the tensor of the counit and
  the normalized root-line pullback comparison. Its derived version uses the
  canonical flat degree-zero tensor and exact direct-image comparisons. Its inverse
  is justified by a named theorem; no unspecified isomorphism is assumed.
* `localizedFlagTensorCartierRaw` tensors the actual Cartier map with the previous
  twist and uses the standard tensor/shift and root multiplication identifications.
  `localizedFlagCompose` applies the actual exact closed direct image to the preceding
  class, uses the closed-direct-image composition and shift comparisons, then the
  inverse projection map and this tensored Cartier map. This is exactly the nested
  recursion in the node. All shifts involved are even, so the two standard ordering
  conventions for tensor/shift comparison give the same map here.
* `localizedFlagTheta` selects the uniquely recursively normalized family. Its base
  is inverse restriction of constants along the rank-zero isomorphism, followed by the zero-shift comparison;
  under E_0=S it is the identity. Its step is the specified composite transported
  along the proved zero-section composition equality. There is no arbitrary step map
  or unconstrained initial class.
* `localizedFlagForgotten` precomposes Theta with the actual restriction of constant
  coefficients, changes to the existing positive Tate power coordinates using
  `localizedFlagPowerComparison`, and applies the exact canonical site comparison.
  Thus it lies in the existing `ordinaryFiniteCohomology` group on the pro-etale site.
* For every `i : Fin (r+1)`, the theorem equates that class to the actual pullback
  `ordinaryFiniteCohomologyPullback` of `ordinaryFiniteFlagTopProduct` of the family
  `localizedFlagRoots`. This family restricts `ordinaryFiniteFlagRoot` to the first
  i quotients with `Fin.castLE`. The empty product is the recorded unit. It does not
  use the full r-fold product for intermediate i.
* The theorem also returns `LocalizedFlagGeometry`, so the geometric assertions in
  the node appear in the main statement, and not merely in explanatory comments.

Dependency declarations read and used:

* `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and its
  actual coefficient ring, constant coefficients and field datum.
* `Sheaf.AlgebraicGeometry.CompleteFlagBundle`: `CompleteFlagBundleData` and the
  meanings and properties of subbundles, successive inclusions and cokernel quotients.
  The statement concerns any supplied filtration, not just `completeFlagBundle`.
* `Sheaf.Paper.PurityVectorBundleZeroSection`: `AlgebraicGeometry.PurityVectorBundle`,
  `PurityVectorBundle.zeroSection`, `zeroSection_spec`; its imported canonical
  `VectorBundleZeroSection` symmetric algebra, augmentation and relative Spec.
* `Sheaf.AlgebraicGeometry.CartierKummerMap`: `cartier_kummer_map`,
  `CartierKummerRealization` and the normalized `cartierKummerMap`.
* `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`:
  `AlgebraicGeometry.Etale.ordinary_supported_kummer`, including uniqueness of its
  supported Ext class with the specified relative boundary. This already landed
  owning node is added to stmt_deps.
* The finite part of `def-coefficient-twists-detailed` is the recorded
  `Scheme.finiteEtaleTateSheaf`, already imported by `PurityFiniteSetting` and the
  supported-cup dependencies. The unused all-coefficient twist import is omitted.
* `Sheaf.Paper.KummerAdditivity`: `Etale.kummerFirstChern`,
  `ProEtale.kummerFirstChern`, `kummer_additivity`, with their canonical comparison.
* `Sheaf.Paper.SupportedCup` and `SupportedCupFunctoriality`: the supported-Hom model,
  actual restriction of constants, normalized twist product and exact site comparison.
  The landed definition node `def-pur-supported-class-operations` owns the reused
  `functorialCupTwistProductGeneral`; it replaces the theorem-node dependency.
* `Sheaf.Paper.ChernFlagFormula`: `ordinaryFiniteFlagRoot` and
  `ordinaryFiniteFlagTopProduct`, reused for the ordered product. The new definition
  node `def-pur-ordinary-finite-flag-products` owns these existing declarations,
  together with `ordinaryFiniteFlagProductCoefficient`; no Lean source is added.
* `Sheaf.AlgebraicGeometry.ProjectiveLineTrace`: `Etale.projectiveLineTraceTransport`,
  the canonical transport used by the existing ordinary finite cohomology pullback;
  its owning definition node is added to stmt_deps.
* `WeilConjectures.AlgebraicGeometry.Modules.Dual`: the actual `Scheme.Modules.dual`
  and `dualMap`.
* The statement file imports only modules needed to elaborate its definitions. The recorded
  proof-dependency modules are proof-origin references; importing the finite compact
  projection module here would pull a known duplicate upstream comparison owner, so it
  is intentionally omitted from this stage-2 statement module.

Edge cases checked mathematically before writing: rank zero, i=0 within an arbitrary
rank, i=1, i=r, empty base, a singular/nonreduced base, a locally but not globally
split flag, and every positive finite coefficient level. The polynomial coordinate
is a nonzerodivisor over any coefficient ring; no regularity of S is used. A global
splitting and arbitrary choices of maps are not hypotheses. Universes are bound
explicitly, and site module values retain the usual u+1 lift.

Searches:

* `msearch.py ... leanfinder "Forgetting support of nested Cartier divisor classes for
  a filtered vector bundle is the product of first Chern classes"`: eight hits about
  affine-open section calculations and ideal-sheaf chart constructions; no match.
* `msearch.py ... loogle '"Gysin"'`: only the unrelated
  `CategoryTheory.Sheaf.finestTopologySingle`; no match.
* `msearch.py ... grep 'Gysin|Cartier.*cohomology|firstChern|chernClass'`: three
  incidental hits in `Mathlib/CategoryTheory/Sites/Canonical.lean`; no match.
* `msearch.py ... leansearch "Forgetting support of nested subbundle divisor classes
  is the product of first Chern classes"`: differential-geometric vector bundles and
  meromorphic-divisor arithmetic; no match.
* `rg -n 'localized.flag|flag.*product|subbundle.*divisor'` in the upstream
  `WeilConjectures` and side `lean/Sheaf` trees, and the prescribed node-id grep
  in upstream: no existing instance of this supported-composite formula. The side
  Chern flag formula supplies the root product and is reused.

The retained attempt had an arbitrary composition map, an unconstrained base class,
no dual-coordinate relationship for the total spaces, and the full r-fold product
at all indices. These defects are removed. No natural-language node correction is
needed, and no statement is disputed.

## Second reading by NN

Author's second reading; the independent maintainer review follows delivery. I reread
the full node and source Steps 2 and 4 against the file, including all helper data.
The current blueprint proof's wording about quotient sections on arbitrary singular
zero loci is precisely what this node replaces by nested subbundle Cartier maps.
The four retained-attempt mismatches listed above are repaired explicitly. The rank-zero
class is canonically normalized; the partial-root family has length i; all vector
bundle coordinates are duals; and the step is an exact direct-image/projection/tensor
composite. No independent reviewer or proof completion is claimed in this report.

## Resumed validation, 2026-10-19

The saved packet was retained. The initial required full dry run completed with
an item-module timeout and explicitly reported that nothing was pushed. Diagnostic
probes isolated the expensive term: keeping the concrete finite projection in the
composition normalization timed out, while abstracting that argument alone made the
prefix compile. The finite projection now has its explicit expected derived Hom
result type. This exposes the same source and target without forcing consumers to
normalize its inferred implementation type. The map's body, counit normalization,
root pullback comparison and invertibility theorem are unchanged.

The composition normalization accepts its preceding class through an explicit
heterogeneous parameter. Its characterization still requires HEq to the typed class
in the exact-image model, so it fixes the identical morphism and endpoints. Both this
parameter and the output are explicitly bound in the purity specialization. No
categorical instance, universe, mathematical hypothesis or node statement changes.
Elaboration runs sequentially with `Elab.async false`; the time limit stays 60 seconds.
All diagnostic options and checkpoint commands remain only in scratchpad.

The full repaired source compiled cleanly through scompile.py, in 38.1 seconds for
the sandbox and 35.0 seconds for the library check. Only the one owning item module
is delivered; the previously attempted dependency repair was superseded by the
published SupportedCupFunctoriality module and is retained only in scratchpad.

The resumed second reading checked the actual current definitions, correcting the
older report's description of the filtration fields: its ambient module is the final
level, and consecutive monomorphisms with invertible cokernels give adapted frames
and the vector-subbundle condition. At every i the geometry uses Spec Sym(H_i dual),
not Sym(H_i); the inclusion is induced by the transpose of step. The kernel ideal is
the dual of the pulled-back actual line quotient. The normalized initial class is
inverse constant restriction at rank zero; the successor is the exact closed-image,
inverse counit projection and Cartier tensor composite, with every input fixed.
The final equality uses exactly the first i quotient roots, including the empty
product. The finite setting, separated finite-type base, singular and empty cases,
and arbitrary nonsplit filtration remain as in the DAG statement. Every declaration
is now listed in lean.declarations, and lean.statement is verbatim from the module.

The final import-repaired full dry run passed preflight and compilation:
`OK (dry run): commit ecf0e0ca13 passes the preflight and compiles; nothing pushed`.
The ensuing delivery invocation performs the final submission checks.

### Preflight import repair

The first repaired full dry run passed compilation, then rejected the direct
KummerAdditivity import because that module is also recorded for the dropped
route node def-per-ordinary-kummer-first-chern. The module's declarations are already
publicly available through ChernFlagFormula and SupportedCupFunctoriality. Removed
only the redundant direct import, preserving the finite Kummer definitions and
all map expressions. That earlier packet added lem-asd-ordinary-supported-kummer,
lem-pur-supported-cup-functoriality, lem-pur-chern-flag-formula, and def-amb-p1-trace.
The independent review returned the middle two ownership citations as H2; the
repair below replaces them with their definition-node owners.

### Final self-check

The source contains 58 recorded declarations and 11 named sorry theorems, each with
its source and proof docstring. No definition contains sorry data. The module has
no diagnostic options, checkpoint commands or lines over 100 characters. Both
implicit-variable options are disabled; every universe is explicitly declared.
The item differs from the shared node only in lean and four added statement
dependencies (including the new existing-declaration definition node). The main signature is verbatim, the natural-language
statement is unchanged, and the packet now includes the existing-declaration definition node described
below. There are no dependency modules. The report's second reading is the author's; independent review remains
the maintainer's responsibility.


## New nodes

`def-pur-ordinary-finite-flag-products` owns the already published
`ordinaryFiniteFlagRoot`, `ordinaryFiniteFlagProductCoefficient` and
`ordinaryFiniteFlagTopProduct` in `Sheaf.Paper.ChernFlagFormula`, using
`existing: true`. The source is localized-top-Chern proof Steps 2 and 4 and Stacks
Tag 0FI5's product of total line classes. The root is the actual Kummer Chern morphism
with the fixed finite exponent. The coefficient recurrence appends a last factor
on the right, with zero-family coefficients (1,0,...) and constant coefficient 1.
The top-product recurrence starts with 1 and appends the last root on the right.
The family input consists of arbitrary degree-two ordinary etale morphisms; the
root definition specializes these to invertible modules. Both recurrences use the
existing exact comparison and cup step from `def-pur-chern-classes`.

The saved searches were supplemented with LeanSearch and LeanFinder queries for
ordered Kummer-root products and polynomial coefficients: the eight hits each
concern unrelated formally etale algebras, root systems, Witt polynomials or elliptic
curves. The Mathlib grep for the exact three names and Chern/cup patterns returned
zero hits. Upstream `WeilConjectures` grep returned no definitions. Project grep
found exactly the three definitions in ChernFlagFormula (lines 52, 67, 86). DAG grep
found their names only in the theorem node lem-pur-chern-flag-formula, with no
owning definition node. `blueprint_refs.py search flag` found only the unrelated
invariant-linear-flag node p-linear-triangular. The new node records those searches
and reuses the declarations; it does not define another root or product.

## Returned delivery repair, 2026-10-19

The initial required saved-packet dry run passed at 939be36c82. It was retained as
the starting point; passing that mechanical check did not discharge the independent
return on immutable head 0ce4f388ae2e. Both numbered H2 points are repaired:

1. Replaced stmt_deps citation lem-pur-chern-flag-formula by the new definition node
   def-pur-ordinary-finite-flag-products. That node owns all three existing plain
   definitions in ChernFlagFormula, not its filtered-bundle theorem.
2. Replaced stmt_deps citation lem-pur-supported-cup-functoriality by the landed
   def-pur-supported-class-operations, whose lean.declarations explicitly includes
   functorialCupTwistProductGeneral. The functoriality theorem remains in proof_deps
   for its actual proof use; it is not a statement dependency for the plain map.

The accepted lem-asd-ordinary-supported-kummer dependency remains: the class used
is the witness of its uniquely normalized boundary theorem. The Lean file, main
signature, natural-language statement, proof and proof_deps are unchanged.

### Repair second reading by NN

I read the three existing declarations, their complete signatures and docstrings,
PurityChernClasses' actual unit/cup step, the new node and the item against the
return. The new root binder accepts any k-scheme and invertible module without
an extra separatedness assumption; the product binders accept any scheme and an
ordered finite family of the same etale Hom type. The recurrence for b_(i+1)
uses the previous b_(i+1) plus b_i cup the last root; t appends the last root.
The root exponent, target Tate line, exact comparison, right order and empty
unit are the recorded definitions. No property of Chern classes of a filtered
bundle is smuggled into the new definition. The owning supported-operations node
contains the exact general twist product used by the item. Both return points
are changes to node ownership only; the maintainer's accepted mathematical
statement and all previously checked edge cases are preserved. This is the
author's second reading, with independent review left to the maintainer.


### Repair validation

`scompile.py NN lem-pur-flag-localized-product` compiled the unchanged item in
34.7 seconds for each sandbox/library check with no messages. The self-check
confirmed the exact main signature, existing-root signature, new-node citation
set, unique new id, JSON layout, line width and explicit-variable settings.
Against current main, only lean and stmt_deps differ: the item adds the new
flag-products definition node, landed supported-class operations, the accepted
ordinary supported Kummer witness and the trace-transport definition. No original
statement dependency is removed. The two returned theorem-node additions are
absent from stmt_deps, while the genuine functoriality proof dependency remains.

The repaired full dry run passed: `OK (dry run): commit 5a576c15db passes the
preflight and compiles; nothing pushed`. The wrapper also compiled the existing
ChernFlagFormula reference, so both recorded module interfaces were checked.
