## Worker report

The delivery states the live node in
`Sheaf.Paper.CartierRelativeBoundaryRealization`, declaration
`WeilConjectures.PurityFiniteSetting.cartier_relative_boundary_realization`.
The node was already split and reviewed under N0; that work is retained verbatim.
The prior attempt's split-refusal diagnostic does not authorize another split and
none is attempted here. This is a stage-2 Lean statement, with one postponed theorem.
All definitions contain real constructions; the canonical reduced classes reuse
the existing uniquely normalized construction, rather than choosing arbitrary classes.

Clause-by-clause correspondence:

1. The fixed field, distinct coefficient prime, finite subextension E and positive
   coefficient level are `P : PurityFiniteSetting.{u}`. The ring A is precisely
   `P.Coefficient`, the common-universe lift of the existing quotient. The structure
   map `a : T ⟶ Spec (.of P.field.k)` and instances `IsSeparated a`,
   `LocallyOfFiniteType a`, `QuasiCompact a` render separated finite type over k.
   The closed immersion is `i`; `hI : i.ker.IsInvertible` is the published Cartier
   ideal interface. No smoothness of T or D is present.
2. N is `P.diagonalExponent = P.coefficients.l ^ P.level`; R is the existing
   `ProEtale.cartierResidueRing P.coefficients.l P.level`, namely lifted ZMod N.
   `P.diagonalExponent_isUnit a` and `P.diagonalExponent_annihilates` supply the
   source's invertibility and annihilation, without adding hypotheses. The root
   sheaf is `T.rootsOfUnitySheaf P.diagonalExponent`. The module model uses the
   published `finiteEtaleTateLine T N R hR`, canonically roots tensor R. The theorem
   explicitly asserts `IsIso (ordinaryFiniteRootMap R N hR T)`, fixing the identity
   coefficient root chart, rather than assuming or choosing an isomorphism.
3. The line bundle, frame torsor and specified complement section are retained by
   the existing `Etale.cartierPoleBoundary i hI`. Its specifying predicate
   `CartierPoleBoundarySpec` uses the actual dual ideal, `etaleIsoTorsor`,
   `supportedDivisorSectionPullback`, the supported integral generator +1, and
   the requirement that the specified frame maps to zero. This is the supported
   integral Ext presentation of the entire relative H1 class alpha_D. It does
   not remember only the underlying Picard class. The helper
   `cartierRelativeBoundary` composes this exact class with the actual short-exact
   Kummer extension, with degree equation `1 + 1 = 2`; it is beta_D in the same
   supported integral Ext presentation. In particular it does not use the raw
   `relativeTorsorEquiv`, whose sign differs from the canonical Ext normalization.
4. The first conjunct quantifies over arbitrary injective module resolutions I
   and arbitrary injective abelian resolutions J of the same underlying root
   line. `cartierUnderlyingResolution` applies the existing exact coefficient
   forgetful functor termwise. Existence of q with
   `(RawModuleScalarComparison.forget _ T).map (I.ι.f 0) ≫ q.f 0 = J.ι.f 0`
   requires an identity-augmented comparison, not an unconstrained chain map.
   The source of the existential `iso` in `CartierRelativeConeComparison` is the underlying module
   relative derived section cone; its target is the abelian injective-resolution
   section cone. The source is written by taking underlying groups before the
   section cone: evaluation, finite direct sums and shift commute with forgetting
   module structures, so this gives exactly the same complex. The isomorphism
   lives in `DerivedCategory AddCommGrpCat`, before taking any cohomology.
   The first equality fixes its morphism to `DerivedCategory.Q.map (relativeSectionMap … q)`.
   There is no arbitrary triangulated cone isomorphism. The final universal clause
   on q' states independence of the augmented lift in that derived category.
5. The projection conjunct is the explicit equation for the two actual maps to
   absolute sections, with `relativeForgetComplex` and the evaluated lift.
   The boundary conjunct compares the actual shifted-cone inclusions, which are
   `(0,-b)` in the signed coordinates. The two `CartierKernelNormalization` conjuncts impose both coordinate equations from the published
   kernel/cone theorem: zero open coordinate and original closed kernel inclusion.
   In signed coordinates this is precisely k mapping to (k,0), with differential
   `(da,res(a)-db)`. Both inclusions are required quasi-isomorphisms. The induced
   kernel map is uniquely constrained by its composite with the monic kernel
   inclusion, and the final equality gives the actual commuting support square.
6. `cartierRelativeModuleBoundary` is the existing canonical reduced R-module
   Ext class. Its `.hom` is the required arrow from i_*R_D to M[2], using the
   canonical roots-tensor-R identification just stated. The
   `SupportedKummerBoundary R …` conjunct retains the precise frame torsor and
   section. The following explicit Ext equality evaluates exact scalar forgetting
   on the supported integral generator and identifies the result with beta_D
   followed by the canonical root chart. This is an equality on i_*Z_D, before
   any precomposition by the absolute unit or loss of relative trivialization.
   Thus it specifies the whole underlying relative class and its sign.
7. `cartierRelativeCoefficientBoundary` is the normalized A-adjunct of the SAME
   beta_D. The next explicit Ext equality uses exactly
   `ordinaryFiniteRootMap P.Coefficient P.diagonalExponent … T` on its target.
   This map sends roots to the tensor with coefficient one. The comparison
   `P.functorialCupCompare i 2 1` is the published etale/pro-etale inverse image
   with supported-source and twist comparisons. Together these are sigma rho in
   the roots-projection chart of `def-pur-frame-class`. The last equality is
   `P.generalDivisorClass a i hI = P.functorialCupCompare …
   (P.cartierRelativeCoefficientBoundary a i hI).hom`, exactly the asserted global
   class identity. It is not a collection of local equations or an equality only
   after forgetting support.

The mathematical relative group is represented here by its normalized supported
integral Ext model. This is the existing representation already used by
`PurityDivisorClass.DivisorEtaleNormalized`, `SupportedKummerBoundary` and
`CartierPoleBoundarySpec`. No second relative-cohomology definition, torsor
classification, divisor section, root line, tensor or site comparison is introduced.
The new helpers only name this node's composites, evaluated lift, and the explicitly
specified comparison diagram. Every helper belongs to the item and is listed in
`lean.declarations`; no new node or dependency replacement is needed.

Recorded dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, its
  existing coefficient quotient and exponent/invertibility interfaces.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the recorded intrinsic
  twist family; its finite chart is `frameTwistEtale` / `frameTwist`, used by the
  divisor and supported-Hom interfaces. The full recorded rational/Qbar declaration
  is retained via its module, without imposing rational hypotheses on this finite result.
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`:
  `Scheme.IdealSheafData.IsInvertible.isInvertible_dual_toModules`.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`:
  `Scheme.kummerSequence_shortExact`, `rootsOfUnitySheaf`, `kummerSequence`.
- `Sheaf.AlgebraicGeometry.RelativeTorsorCohomology`:
  `Etale.relative_torsor_cohomology`, `relativeSectionComplex`,
  `relativeSectionMap`, `relativeConnecting` and its short-exact-sequence model.
  The recorded canonical classification has the negative of the raw lifting-class
  convention; the delivery uses the equivalent normalized extension model.
- `WeilConjectures.AlgebraicGeometry.Sites.GmPicard`:
  `Scheme.nonempty_equiv_quotient_torsor`; its frame-torsor construction is
  `Scheme.Modules.etaleIsoTorsor` in the existing EtalePicard interface.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule`, ordinary unbounded module derived categories.
- `Sheaf.AlgebraicGeometry.PurityRelativeCone`:
  `Etale.relativeConeSupportComparison`, `RelativeCone.Realization`,
  `RelativeCone.projection`, `RelativeCone.boundary`, and signed normalization.
- `Sheaf.AlgebraicGeometry.ClosedSupportHom`: `Etale.closedSupportHom`, the
  ordinary derived Hom/relative cone isomorphism, with arbitrary coefficient ring.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, its finite-limit assertion and module variant.
- `Sheaf.Paper.PurityFrameClass` and its public `PurityFrameKummer` interface:
  `WeilConjectures.PurityFiniteSetting.frameClass`, `frameTwistEtale`,
  `frameTwist`, the fixed ell^n root chart and canonical root coefficient map.
- `Sheaf.Paper.PurityDivisorClass`: `divisor_class`,
  `existsUnique_generalDivisorEtaleClasses`, `generalDivisorEtaleClasses`,
  `generalDivisorClass`, `DivisorEtaleNormalized`, `divisorProEtale`.
- `Sheaf.AlgebraicGeometry.CartierPoleBoundary`:
  `Etale.CartierPoleBoundarySpec`; `CartierReductionData`:
  `Etale.cartierPoleBoundary`, `ProEtale.cartierReducedEtale`,
  `cartierResidueRing`, `cartierResidue_cast`, `cartierResidue_finite`.
- `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary`:
  `Etale.SupportedKummerBoundary`, `supportedIntegralGenerator`, divisor section.
- `Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison`:
  `Etale.RawModuleScalarComparison.forget`, with its additive and exact instances.
- `Sheaf.AlgebraicGeometry.RelativeEtaleCohomology`: `relativeSections`,
  `relativeSectionRestriction`, `relativeSectionComplex`, `relativeForgetComplex`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`: `Scheme.finiteEtaleTateLine`.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer`: `Etale.ordinaryFiniteRootMap`.
- `Sheaf.Paper.SupportedCupFunctoriality`: `PurityFiniteSetting.functorialCupCompare`,
  owned by `def-pur-supported-hom-site-comparison`; `functorialCupSource` and
  `functorialCupTwist`, owned by `def-pur-supported-class-operations`. The comparison
  uses `functorialCupComparisonSource_existsUnique`, not the node theorem
  `supportedCupFunctoriality`.

The Cartier reduction, pole boundary and supported Kummer definition nodes, together
with the scalar-forgetting, relative-cohomology, finite twist and finite root-map owner
nodes, are already landed and appear in the item's statement dependencies under
brief-stage2 section 5. The supported cup comparison owner is also cited. Their
existing records are unchanged; the unused derived-module comparison theorem is removed. Proof imports retain the recorded restriction-kernel
comparison, injective resolution definition, finite-root-line lemma, normalized
supported Hom comparison, raw-torsor sign normalization, and kernel/cone theorem.

Edge cases: an empty D gives the globally trivial framed pair and zero supported
class; empty T gives zero section/cohomology objects. A whole nonempty T with zero
ideal is not Cartier. Disconnected, singular and nonreduced T are allowed: none of
the constructions requires local smooth coordinates. Positive level one and ramified
E are included; ell^n kills A since ell lies in the uniformizer ideal. No divisibility
of n by the ramification index or flatness of A over R is assumed. Nontrivial line
bundles are included globally, with their actual section on the entire complement.
Arbitrary I and J and all identity-augmented lifts are included, with derived lift
independence; forgetting injectives is not assumed to preserve injectivity.

Searches performed with the prescribed msearch wrapper:

- LeanFinder: `Relative Kummer boundary of Cartier frame torsor with complement
  section compared to supported module derived morphism`. Eight hits concerned
  cotangent localization sections, submersive presentation bases and differential
  presentations. None states this comparison or Cartier class identity.
- Loogle: `"Kummer", "Sheaf"`. Available, zero hits.
- Mathlib grep: `relative.*Kummer|Kummer.*relative|CartierDivisor|EffectiveCartier`.
  Available, zero hits.
- Project rg over both `lean/WeilConjectures` and `lean/Sheaf` for
  `cartier.*relative|Cartier.*Relative|cartier_relative|boundary_realization|` the
  exact item id. The results include Cartier-class agreement, line-zero realization,
  relative effective Cartier constructions and reduction comparison, but no declaration
  of this complete signed relative-cone comparison. Those existing canonical
  constructions are reused rather than duplicated. The exact item-id search in the
  upstream library has no declaration for the item.

Source read: current blueprint `lem-amb-cartier-kummer-map.proof.md`, paragraphs
1--3 and the coefficient paragraph. The integral supported extension model fixes
the local quotient of the dual frame to +1 and kills the canonical complementary
frame; this is the same global relative input as the source. No statement correction,
unit change or mathematical dispute is asserted.

Validation of the original packet: the required server wrapper compiled both the sandbox and library module
cleanly on the first corrected pass (21.2 s and 16.3 s). The original pass exposed
the incorrect accessor `l_prime`; it was corrected to the actual recorded primality
fact `prime.out`. The final root-chart isomorphism assertion and explicit proof
imports are also checked by the final prescribed dry run before delivery.


## Repair of return L, immutable head 9df586b0fc6c

The saved packet was retained and first dry-run unchanged. That dry run passed
(commit b1637e5465d), but the independent review's H2/H4 findings still required
repair. Comparing the saved packet with current main showed only the four previous
statement-dependency additions and the Lean record as non-source differences.
The mathematical statement, proof and proof dependencies remain verbatim.

1. Replace the duplicate `moduleUnderlyingSheaf` name by the existing owner
   `RawModuleScalarComparison.forget` in `cartierUnderlyingResolution`, the J binder,
   and both augmentation equations. The Ext equalities already used that owner.
   Its declaration and exactness instances were read in
   `Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison`. Remove the public
   import of `DerivedModuleUnderlyingComparison` and remove
   `lem-weil-pbc-derived-module-underlying-comparison` from the added dependencies.
   Add `def-sbc-raw-module-scalar-pullback-comparison`. This uses one canonical
   scalar-forgetting construction throughout and changes no resolution or map.
2. Add the missing owner statement dependencies
   `def-amb-relative-etale-cohomology`, `def-asd-finite-etale-tate-twist`, and
   `def-asd-ordinary-finite-p1-kummer-class`, and explicitly import their modules.
   Their actual declarations supply the relative section cone and projection,
   `finiteEtaleTateLine`, and `ordinaryFiniteRootMap`, respectively.
   Also explicitly cite/import `lem-pur-supported-cup-functoriality` for
   `functorialCupCompare`; its uniquely normalized chosen comparison is permitted
   by the return. No theorem is cited merely for a duplicate plain abbreviation.
3. Self-check with the source, node and Lean open: the coefficient setting,
   separated finite-type hypotheses, Cartier pair and full complementary section,
   Yoneda Kummer composite, arbitrary augmented resolutions and lift independence,
   derived cone isomorphism, projection, signed boundary and both normalized kernel
   maps, underlying supported Ext equalities, and global divisor-class equality
   are retained exactly. There is still one theorem with proof `sorry`, no hollow
   definition, no new node, and no statement correction. This is the full stage-2
   re-delivery requested by the return, not a Lean-only FIX with changed dependencies.

The compile initially passed current-source confirmation in 47.0 s, but a following
dry run timed out. Profiling isolated repeated instance-proof checking and generated
record/derived-Hom conversions. The repaired module registers the existing owner
proofs `cartierEtaleAbSheafify`, `cartierEtaleModuleSheafify`, `cartierEtaleAbHasExt`,
and `cartierEtaleModuleHasExt` as instances. These are propositions already proved
in the cited `def-sfb-cartier-reduction-data` module; no file-local instance, new
notion, assumption or proof is introduced. The coefficient-boundary definition now
has an explicit result type using the identical `functorialCupSource` and
`functorialCupTwist` interfaces, retaining the same `cartierReducedEtale` body.

`CartierRelativeConeComparison` is now the existential predicate spelling out the
same record's fields, rather than a structure requiring generated recursors. Its
witnesses are exactly the derived isomorphism, both normalized kernel inclusions,
and the induced kernel map. Its conjuncts are exactly the fixed localized map,
projection equation, signed boundary equation, both normalization conditions, both
quasi-isomorphism assertions, kernel-inclusion equation, and supported square.
The main theorem asserts this predicate directly in place of `Nonempty` of that
record. These are equivalent presentations of the same comparison; no clause is
removed or weakened. No record projections are promised to downstream users.
The theorem signature in the node record is regenerated verbatim.

Final prescribed `scompile.py` validation passed both the sandbox module (32.9 s)
and library module (33.7 s), with no errors or unexpected warnings and the unchanged
60-second limit. All profiling options were removed. The final dry run follows.


## Repair of return L, immutable head b381a1ace9c9

The retained packet was first dry-run unchanged: commit d2ef1c3739e passed
preflight and both per-file compiles. The mandatory H2 repair replaces
`lem-pur-supported-cup-functoriality` in `stmt_deps` with the two landed
definition owners `def-pur-supported-hom-site-comparison` and
`def-pur-supported-class-operations`. Their current records and the full
source signatures and docstrings were read in
`Sheaf.Paper.SupportedCupFunctoriality`: the former owns `functorialCupCompare`,
and the latter owns `functorialCupSource` and `functorialCupTwist`. The comparison's
`.choose` is from `functorialCupComparisonSource_existsUnique`, which uniquely
determines the normalized closed-source isomorphism; it is not a choice from
the supported-cup functoriality node theorem. The previous return section above
records the historical permission that this return explicitly withdraws.

The Lean module is byte-identical to the retained reviewed packet, including
the same public import. No mathematical statement, proof step, proof dependency,
helper declaration or edge case changes. Relative to current main, the node
changes only `stmt_deps` and `lean`; all original statement dependencies remain.
The advisory about the four global instance attributes is recorded; they are
retained with the accepted Lean file. No new definition or dependency module
is introduced. The Lean record date is refreshed for this re-delivery.

Self-check with the node and Lean open retained all seven clauses: finite
coefficient and Cartier hypotheses; the actual Kummer and root charts; the
complete frame torsor with complement section; arbitrary identity-augmented
resolutions and derived lift independence; projection, signed boundary and
normalized kernel square; the full supported integral Ext equality over R;
and the A-adjunct and global supported divisor-class equality. Empty support,
empty base, nonsmooth and nonreduced pairs, and ramified coefficients are
still included. The existing worker report above supplies the clause-by-clause
mapping and prior searches. No statement correction is needed.

Repaired-packet validation: `scompile.py` compiled the sandbox and library
module in 18.5 s and 20.4 s, respectively, with no errors or unexpected
warnings. The self-check verified only `lean`/`stmt_deps` differ from main,
all original dependencies are retained, the two correct owners are cited,
the public import remains, the recorded theorem signature matches verbatim,
and the file has one postponed theorem, explicit implicits and 100-column
lines. JSON format is one-space indentation with a final newline.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
