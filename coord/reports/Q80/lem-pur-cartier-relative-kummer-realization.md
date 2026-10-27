## Worker report

The module states `lem-pur-cartier-relative-kummer-realization` in three main realization declarations,
all over the recorded `PurityFiniteSetting`, and keeps the source statement unchanged.
No proof of the item is supplied. Every theorem has `sorry`; every definition has real data.
The statement dependencies cite definition ownership for the canonical constant site-exchange
map, the exact-functor transport of derived arrows, the existing supported class operations,
and ordinary supported scalar extension. Two new existing:true definition nodes register
previously unowned plain definitions. No dependency module is changed. The canonical
reindexing transport helper required by the failed compiler gate is documented below.

Clause-by-clause rendering:

- The finite-field datum, prime distinct from its characteristic, chosen finite coefficient
  extension, uniformizer quotient and positive integer n are exactly `P : PurityFiniteSetting`.
  `P.Coefficient` is the recorded size lift of O_E/(varpi^n), with n=P.level. There is no
  ramification-index divisibility hypothesis. `P.diagonalExponent` is ell^n.
- R=Z/N is `relativeCartierRootRing`, the standard universe lift of ZMod N.
  `relativeCartierRootZero` states its defining zero relation. `relativeCartierScalar`
  is the existing quotient scalar map, composed with the inverse size lift.
- For EVERY k-scheme S, including non-finite-type S, `relativeCartierRoots_realization`
  takes `S` and its structure morphism `a`. Its first conjunct is NA=0. Its second
  conjunct is `ObjectProperty.flat (P.relativeCartierRoots S)`.
  The roots are expressed using the recorded `finiteEtaleTateLine` with coefficient R:
  R tensor_(Z/N) mu_N, canonically mu_N by r tensor z -> r z. This reuses the original
  roots presheaf and its unique exponent action; it is not a new roots construction.
- L_S=mu_N tensor_R^L A is specified by `SupportedDerivedScalarUnit`: the normalized
  scalar unit exhibits the degree-zero ordinary tensor `P.frameTwistEtale S 1` as
  derived scalar extension on ALL unbounded derived test objects. The equation on
  `finiteEtaleTateOneGenerator` fixes the scalar map on every local pure tensor.
  The final clause displays the actual derived isomorphism from every representation
  `(L, etaL)` of that derived extension to the degree-zero tensor, with its unit
  compatibility. Thus the concentration and comparison are asserted in the derived
  category, not just degree by degree. This is the universal-arrow encoding already
  used by `Sheaf.IsDerivedBaseChange` and ordinary supported Kummer scalar change.
  The K-flat construction of def-kun-derived-tensor represents that same universal
  derived extension; resolving the flat root factor by itself gives this ordinary
  tensor. No flatness of the quotient coefficient ring is assumed.
- The original pro-etale A(1) is `relativeCartierProLine`, exactly the existing
  `Scheme.finiteTateProSheaf` at predecessor n-1. Its definition eliminates the impossible
  level-zero branch and otherwise returns that existing object. `relativeCartierTwist_realization`
  asserts a unique q from the etale-root inverse image to that specified original twist.
  `RelativeCartierRootNormalized` is exactly the existing `IsFiniteTateSiteComparison`
  at quotient predecessor n-1, root predecessor n-1, and power 1, including the local
  root-limit section formula on arbitrary pro-etale tests. Composing with the first
  theorem's derived-to-degree-zero comparison gives theta_S for C_S L_S.
- The main theorem has `b : B -> Spec k` and separated, locally finite type,
  quasi-compact instances, and the same three conditions on `v >> b` for T.
  These are precisely separated finite-type k-schemes. `SmoothOfRelativeDimension d v`
  renders T/B smooth of dimension d. `IsClosedImmersion i` and `hI : i.ker.IsInvertible`
  render the effective Cartier divisor; `Smooth (i >> v)` renders D/B smooth.
  `_hcodim` is the recorded equality of stalk Krull dimensions for pure codimension one.
- c^e is the existing `agreementCartierEtale (v >> b) i hI`, realized by `.hom`.
  Its first conjunct explicitly states the full `SupportedKummerBoundary` predicate:
  frame torsor of O(D), section one on support, prescribed canonical frame off D
  mapping to zero, and the relative Yoneda normalization. The complement and its frame
  are retained inside that existing predicate, rather than arbitrary additional data.
- The second conjunct supplies the R-boundary kappaR with the same full normalization
  and `SupportedKummerScalar` to c^e. That predicate includes the actual unbounded
  derived scalar units on the supported source and roots target, their generator
  normalizations, and the Ext square. Both derived morphisms therefore have the
  stipulated common roots-boundary construction.
- c^p is `relativeCartierProMap`, which realizes the EXISTING published Ext class with the same `Ext.hom` as
  `Etale.cartierKummerMap`, at positive level n. `relativeCartierProExt` takes that
  exact class from the very same unique pair of `cartier_kummer_map`; it avoids an
  expensive comparison of the private Shrink instances captured by the old arrow. Its definition supplies the source-implied
  unit hypothesis on ell from `diagonalExponent_isUnit`, with no extra assumption.
- Epsilon is `SupportedConstantNormalization.gamma P.Coefficient i`, the canonical
  site-exchange mate with the constant-unit normalization. The main third conjunct
  asserts its invertibility and the actual derived-arrow equality
  `functorialCupExactHom C 2 ce.hom >> single(q.hom)[2] = single(gamma) >> cp`.
  `functorialCupExactHom` includes the exact inverse image's canonical single and
  shift comparisons, so both sides have exactly the same objects. This is precisely
  theta[2] C(ce) = cp epsilon in the degree-zero representatives; it is not an equality
  only after forgetting support or composing with the constant restriction.
- The fourth conjunct is `generalDivisorClass = agreementCartierMap` in the recorded
  supported-Hom realization. The latter definition is the canonical supported comparison
  of this very ce. Together with the previous canonical-source/target equation, this
  says cl(D)=cp under supported Hom with the requested agreement-map normalization.
- The last clause quantifies over EVERY etale principal presentation U,e,f,t,sq. The
  chosen Cartesian square says scheme-theoretically D_U=V(f). Its conclusion is the
  actual canonical supported pullback of the global divisor class, `HEq` to
  `-(P.frameBoundary U (e >> v >> b) f)`. The existing frame boundary is +partial kappa(f),
  so this retains the requested negative Yoneda sign. HEq only accommodates the two
  recorded supported-Hom instance presentations, not different cohomological classes.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `Coefficient`,
  `constantEtale`, `constant`; the actual finite-field and quotient datum.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: recorded intrinsic twist interface,
  reexported finite line; `Sheaf.Paper.FixedFinitePositiveCoefficientTwist` supplies
  `diagonalExponent`, annihilation and invertibility at every positive level.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`: `siteComparisonDerivedPullbackPlus`;
  the unbounded exact functor used here is the same `comparisonUpperStar.mapDerivedCategory`.
- `Sheaf.Paper.PurityFrameClass`, via `PurityFrameKummer` and `PurityFramePrincipalBoundary`:
  `frameTwistEtale`, `frameTwist`, `frameBoundary` with the existing coefficient maps and sign.
- `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`: `ordinary_supported_kummer`
  and its unique-boundary interface; `OrdinarySupportedKummerBoundary`: `SupportedKummerBoundary`;
  `OrdinarySupportedKummerScalar`: `SupportedKummerScalar`, `SupportedDerivedScalarUnit`.
- `Sheaf.AlgebraicGeometry.CartierKummerMap`: `cartierKummerMap` and `cartier_kummer_map`;
  `CartierKummerData`: the normalized realization predicate.
- `Sheaf.Paper.SupportedCohomologyHom`: `ProEtale.supported_cohomology_hom`;
  `Sheaf.Paper.PurityDivisorClass`: `generalDivisorClass`, `generalDivisorEtaleClasses`,
  `divisor_class`; `Sheaf.Paper.CartierClassAgreement`: `agreementCartierEtale`,
  `agreementCartierMap`, `cartier_class_agreement`.
- `Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization`: canonical `gamma`;
  `Sheaf.Paper.SupportedCupFunctoriality`: `functorialCupExactHom`, `functorialCupPullback`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: fixed-ring module derived categories;
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: original continuous-function coefficient
  sheaf module category and its existing fixed-ring realization, not a different site.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `SmoothOfRelativeDimension`, `Etale`;
  `WeilConjectures.AlgebraicGeometry.EffectiveCartier`: invertible Cartier kernel and its dual;
  `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: existing K-flat derived tensor.
- Root normalization reuses `Scheme.finiteTateProSheaf`, `IsFiniteTateSiteComparison`
  from `Sheaf.Paper.FiniteTateSiteDescent`, not an arbitrary isomorphism of lines.

The source read was the current blueprint's rank-one Thom proof, Step 1; the live
node's expanded seven-step realization proof; the relative Cartier Kummer-map and
divisor-class source statements and their recorded Lean declarations/docstrings.
The proof-dependency modules already recorded are imported without public unless
also needed in the statement. The proof dependency supported-root-scalar-site-comparison
has no recorded module; its assertion is not assumed as new data or used as a hidden
construction. The existing scalar universal and canonical source interfaces suffice
to state this item and its complete proof plan cites that node.

Edge cases checked: n=1 uses the predecessor-zero branch; all n>=1 are covered.
Ramified extensions with n not divisible by e remain allowed, and A need not be flat
as an R-module. Empty S, T, B and D are allowed; the zero scheme's unit conditions use
the ordinary IsUnit convention and the roots and constants on the empty site vanish.
D empty is an invertible Cartier ideal and no nonempty-support assumption is introduced.
An etale neighbourhood need not be affine; the quantified equation is a global section
on any such U. Relative dimension d=0 is retained (nonempty codimension-one smooth
Cartier families then cannot occur, but the empty divisor still can). Scheme objects
retain universe u with site objects u+1 and morphisms u; coefficients use u+1.

Searches actually made in this session:

1. msearch.py, leanfinder, "The relative supported Cartier Kummer class agrees under
   etale to proetale comparison with the roots of unity derived scalar extension":
   eight hits on StandardEtalePair presentations and Algebra.etaleLocus_eq_compl_support;
   none is a supported sheaf Kummer comparison.
2. msearch.py, loogle, `"Kummer", "Sheaf"`: zero hits.
3. msearch.py, grep, `Kummer|Cartier.*realization`, subdirectory AlgebraicGeometry:
   zero Mathlib hits.
4. rg on `lean/WeilConjectures` and `lean/Sheaf` for relative Kummer, Cartier realization,
   root flatness and Cartier Kummer classes: existing roots, Kummer, scalar and divisor
   constructions listed above; no declaration with the complete node statement.
5. rg for the exact item id in both source roots: no match before writing this module.
6. rg for the new `relativeCartier`/`RelativeCartier` declaration names in both source roots:
   no existing declaration. A filename `ValuationZeroSectionRelativeCartier` is unrelated.

No statement dispute, no source correction, and no private copy of an existing construction.
The repair adds ownership nodes for two existing constructions, with no new mathematical notion. The root/scalar aliases and positive-level transports
are helpers for this node and are all listed in `lean.declarations`.

Validation: the prescribed scompile.py and deliver2.py checks are run on this module.

Further search: msearch.py LeanSearch, "Finite roots of unity sheaf is flat over Z modulo N and its derived extension of coefficients is the ordinary tensor with A": eight hits on rootsOfUnity and cyclotomic field extensions; none concerns flat sheaves or derived scalar extension.

Prior-delivery compiler validation: scompile.py compiled the returned module in sandbox and library names with no errors or warnings, in 57.0 s and 49.3 s respectively, under the unchanged 60 s per-file limit. Explicit unfolding of the existing positive-level coefficient wrappers avoids the earlier instance comparison failure.


## Returned-delivery repair

Repaired H2 from the independent review of immutable head dbeda4e3df3a. The saved
Lean module before the dry-run compilation repair had SHA256
`a96ca362d7c716533cf215ae302301c27e695a64fc770d874cb70de735e6bd80`. The
item and its Lean clauses retain the mathematics accepted by that review. The two
theorem-only stmt_deps are replaced by the two definition nodes below and the already
landed `def-pur-supported-class-operations`. The theorem
`lem-pur-supported-constant-exchange-normalization` remains in proof_deps. The
original proof_deps are unchanged; the cup-functoriality theorem had been added
only to stmt_deps for its plain definitions, and that addition is removed.
Neither plain map is selected by `.choose` from its former theorem owner.
`functorialCupPullback` remains owned by `def-pur-supported-class-operations`; that
node is neither delivered nor edited. No source statement or theorem signature changes.
The packet was compared with the current shared node: only lean and stmt_deps
differ; proof_deps are unchanged. The prescribed delivery wrapper rebases
the packet on the current live branch.

## New nodes

`def-pur-supported-constant-exchange-maps` records, with existing:true,
`AlgebraicGeometry.SupportedConstantNormalization.gamma` in
`Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization`, and the plain
site, fixed-module, constant, inverse/direct-image, adjunction, restriction and
comparison components used by its formula. For arbitrary A and scheme morphism i,
gamma is the transpose of inverse coherent pullback comparison, the image of the
etale counit, and the constant-unit comparison. This is the source's actual
adjunction-mate construction, including closed i; invertibility stays a theorem.
Its object and morphism universes are u+1 and u for the sites and u+1 for coefficients.
The TeX statement matches gamma and each listed component read in the existing
module. No closedness, finiteness, nonemptiness or field hypothesis is added to gamma.
LeanSearch and LeanFinder returned general constant-sheaf adjunctions, Mathlib grep
returned no specialized map, upstream grep no duplicate, DAG inspection only theorem
ownership, and blueprint search no definition node. The new record reuses the existing
declaration; its source is Stacks 03S6/095L's adjunction construction, specialized to
the site comparison in the rank-one Thom proof Step 1.

`def-pur-exact-derived-hom-map` records, with existing:true,
`WeilConjectures.PurityFiniteSetting.functorialCupExactHom` in
`Sheaf.Paper.SupportedCupFunctoriality`. The statement binds abelian B,D, their
chosen derived-category sizes, exact additive F, S,T, every integer a and the actual
derived morphism alpha. It defines exactly the composite of inverse single
comparison, the derived image of alpha, shift comparison and shifted forward single
comparison. This is the existing definition's entire signature and body, with no
functoriality assertion; arbitrary a, a=0, negative a, zero objects and zero alpha
remain allowed. The source is the termwise exact-functor construction of Stacks 015F
and its site application 099W, used in the rank-one Thom realization Step 1.
LeanSearch/LeanFinder identify the single comparison and Ext analogues; Mathlib grep
confirms those constituent maps, not an identical named operation on arbitrary
integer-shifted derived arrows. Source and DAG searches find the exact existing
Sheaf definition, previously attached only to a theorem. The existing supported
class operations node does not own it and is preserved. Full search results and
digests for both new nodes are recorded in their mathlib_searches.

Repair validation: the dedicated module-mode ExistingChecks probe checked every
registered declaration of both new nodes on the server, in sandbox and library
names, with no errors or warnings. The import-only probe also passed (20.6/24.0 s).
The returned module encountered repeated 60 s timeouts during the prescribed
dry run. Scratch-only probes isolated the coefficient conversion issue described
below without weakening any statement.

Self-check: the two theorem stmt_deps are absent; their definition owners and
`def-pur-supported-class-operations` are present; the constant-exchange theorem remains in proof_deps;
all current-base statement and proof dependencies remain; no other node is edited;
both new existing:true signatures are verbatim from their owning modules.


## Compile repair required by the dry run

The requested H2 repair initially left Lean byte-for-byte unchanged. The required
first dry run and subsequent confirmations repeatedly timed out at 60 s, so the
packet could not reach preflight. An import-only probe passed; a profiling probe
located the cost in dependent coefficient conversion in relativeCartierProExt.
The reduced diagnostic displayed Nat.casesAuxOn with equality transports from
relativeCartierProLine's tactic case split. A direct pattern-match version passed
in 58.8/46.8 s, but further actual-module compiles still hit the limit. The final
repair therefore names the canonical presentation equality explicitly.

relativeCartierProLine uses a direct dependent pattern match instead of two tactic
case splits. Its level-zero branch still eliminates Nat.not_succ_le_zero 0 hlevel,
and the positive-level branch returns exactly Scheme.finiteTateProSheaf C.l E n T 1
with the same hE instance. Its signature, quotient, predecessor and actual sheaf
are unchanged.

The new named theorem relativeCartierProExt_type identifies the Ext type built
from Etale.cartierSupported and the original finite Tate sheaf at predecessor
P.level-1 with the existing Ext type using P.Coefficient and relativeCartierProLine.
It is a presentation helper of this node, recorded in lean.declarations; its proof
is sorry, with the complete proof in its docstring: use positivity to write the
level as m+1, expand the coefficient quotient and size lifts and the positive
Tate-sheaf branch, and apply reflexivity to the identical standard Ext types.
There is no new mathematical hypothesis. The positive case m=0 covers n=1.

relativeCartierProExt now applies this fixed type equality to the SAME published
cartier_kummer_map .choose.2 class at predecessor P.level-1. It obtains ell's unit
proof from diagonalExponent_isUnit just as before, using P.level_pos directly.
Thus the definition contains real data and a specified equality transport, not an
arbitrary existence choice or an assumed comparison arrow. An equality proof fixes
the transport uniquely by proof irrelevance. The three realization theorem
signatures and all their clauses are unchanged, and no other source declaration
body changes. The helper statement merely records the canonical coefficient and
index identification implicit in this node's prescribed original Tate sheaf.

The final full source compiled through scompile.py in sandbox and library modes
in 42.3 s and 42.9 s, cleanly under the unchanged 60 s limit. Its SHA256 is
`926fa04c25a3933311e48dbe4614cb2b0f8202d9f5b5b43c7cfe044815c92e3d`.
The main statement signature and both new definition-node signatures remain
verbatim, and the new helper has the same source/blueprint ownership and a complete
natural-language proof as required for a postponed construction proof.

Preflight repair: bracket citations in the constant-exchange definition are
individual [id] references, as required by the checker. An unnecessary additional
cup-functoriality proof_dep was removed after preflight rejected it; the item's
proof_deps are now exactly the base's. The constant-exchange theorem is retained
there, as requested by the return. No statement_change is needed or introduced.
The full delivered source cleared the wrapper's server compilation confirmation
before the preflight field diagnostics were issued.

## Second reading by Q80

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
