## Worker report

This repairs the returned immutable delivery `d22a5c0338c1`, retaining the earlier statement repairs. The natural-language
statement, its hypotheses and its proof route are retained. The module is
`Sheaf.Paper.RelativeSupportBottomDescent`, with main declaration
`AlgebraicGeometry.Etale.relative_support_bottom_descent`. All proofs in the main statement module remain
`sorry`; every construction has real data. Existing proved declarations in the imported
coefficient-comparison module are preserved during the definition extraction. The helper proof obligations are named,
documented, and listed in the owning node's `lean.declarations`.

The statement now cites three definition nodes for the support kernel, module-to-abelian
forgetting, and Grothendieck edge maps. The three theorem nodes identified by the return
are proof dependencies only. `lem-pur-support-site-comparison` remains a statement
dependency because its unique map construction is used. See the new-node and dependency
sections below. All six clauses and every mathematical hypothesis are unchanged.

Hypothesis-by-hypothesis matching:

- `P : WeilConjectures.PurityFiniteSetting.{u}` is the finite datum k, ell, E, n, A;
  `P.level_pos` retains every positive level, including ramified levels. The signed
  finite Tate coefficient uses `ringChar P.Coefficient`, so no divisibility of the
  level by the ramification index is added.
- `b : B ⟶ Spec (.of P.field.k)` gives the base k-scheme. `v : V ⟶ B` with
  `[SmoothOfRelativeDimension d v]` is smooth of fixed finite relative dimension d.
  The k-structure maps on V, Z and U are the indicated composites.
- `i : Z ⟶ V` and `[IsClosedImmersion i]` give the closed subscheme;
  `[Smooth (i ≫ v)]` gives smoothness of Z over B.
- `c : ℕ` allows c=0. `hcodim` is exactly the local-ring Krull-dimension equation
  at every z in Z, using `ringKrullDim` in `WithBot ℕ∞`; no finite-dimensional-base
  condition is introduced.
- `e : U ⟶ V` and `[Etale e]` give the arbitrary etale localization.
- `f : Fin c → Γ(U, ⊤)`, `toZ`, and `hframe : IsPullback ... i e` say that the
  zero-locus subscheme cut out by these c functions is Z times_V U. This is the
  scheme-theoretic generating condition from the frame definition, with no
  regular-sequence, choice of orientation, or frame-class assumption.
- `r : ℤ` retains positive, zero and negative twists. The coefficient on a test
  W is restriction of the same sheaf A(r) on U, using the existing
  `Etale.localizationRestriction`; it is not an independently chosen coefficient
  sheaf on each W. Module restriction followed by scalar forgetting is the
  corresponding abelian restriction, sectionwise.

Conclusion-by-conclusion matching:

- The first conjunct quantifies over every integer b' below 2c and asserts
  `IsZero (relativeSupportCohomologySheaf ... b')`. This sheaf is homology of
  the right-derived actual `supportedKernel` on U, not a sheaf on a varying W.
- The second conjunct makes `relativeSupportEdge ... W` invertible for every
  `W : U.Etale`. Its source is literally the recorded
  `Etale.supportCohomology (pullback.snd i_U W.hom) ...` with the restricted
  coefficient. Its target is literally evaluation at W of
  `relativeSupportCohomologySheaf P i_U r ((2*c : ℕ) : ℤ)` on U. Sections of
  the restriction to W are precisely evaluation at W. The explicit cast avoids
  substituting an unproved arithmetic conversion in a type.
- The third conjunct is the commuting edge/restriction square for every pair
  W,W' and every morphism `a : W' ⟶ W`. The supported-class map is
  `relativeSupportClassRestriction`; the target map is the actual restriction
  of the same cohomology sheaf on U.
- The fourth conjunct asserts invertibility of the actual
  `relativeSupportProComparison` and of the resulting `relativeSupportProEdge`
  on every W. The comparison derives the published
  `ProEtale.supportComparisonUnit`, whose kernel-inclusion equation fixes it
  to the adjunction unit on sections. The scalar-forgetting transport is Mathlib's
  `PreservesKernel.iso`, with its kernel-inclusion normalization. `relativeSupportProEdge` is defined by
  the inverse of this specific comparison followed by the etale edge, so its
  target is the same sheaf on U. No bare `Nonempty` group isomorphism remains.
- The fifth conjunct states the same edge/restriction square for the pro-etale
  groups. For these coefficients of etale origin,
  `relativeSupportProRestriction` is the canonical restriction transported
  through the unit-induced supported comparison. Thus it uses the same
  restriction and coefficient transport as the etale side and makes no second
  choice of support maps or injective resolutions. This is the node's
  pro-etale assertion using canonical comparison.
- The final conjunct quantifies over an arbitrary index universe `w`, a family
  `W : ι → U.Etale`, arrows `a` to the terminal U-object, and the actual cover
  condition `Sieve.ofArrows W a ∈ U.smallEtaleTopology ...`. The variables x,y
  belong literally to `Etale.supportCohomology i_U (2*c) A(r)`. Equality is
  required only after their canonical restrictions to the specified cover
  members. The premise does not quantify over all etale objects and does not
  require an identity member. Empty families over the empty scheme are allowed.

Canonical interfaces and deferred proof obligations:

`relativeSupportEvaluationIso_existsUnique` identifies evaluation of the support
kernel with the recorded support functor on W, uniquely by the kernel inclusion.
Deriving it by `Functor.rightDerivedBaseChange`, and using preservation of
injectives by etale restriction, gives `relativeSupportDerivedEvaluation` and its
named invertibility obligation. This relates the actual W-side group to a single
injective calculation on U. `relativeSupportEdge` then uses the existing
`Functor.grothendieckLeftEdgeMap` for the support kernel on U followed by
evaluation at W. Its final factor is
`singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso`, giving the
required natural-number/integer homology comparison. The global support
identification has its own unique kernel normalization, so the cover clause starts
from the recorded global supported group without replacing it by sheaf sections.
Both `Classical.choose` uses choose the unique kernel-normalized isomorphism of
an `∃!` theorem; none chooses an arbitrary class, map or group isomorphism.

The general support comparison helper uses the finite torsion site comparison on
an arbitrary scheme and its complement, followed by the functorial support long
exact sequence. It does not use the finite-type-only invertibility theorem in
`SupportSiteComparison`. Scalar forgetting is compared on acyclic resolutions,
not assumed to preserve injectives of arbitrary module categories. The acyclicity
helper's docstring now cites Stacks 09XP and 09XQ explicitly. The main docstring
carries all nine proof steps: c=0; local coordinates; the rank-one and supported
product calculation for all signed twists; closed-support adjunction; restriction
and injective resolutions; the lowest row edge; cocycle restriction naturality;
unit-induced site comparison; and separation on the specified cover.

Dependencies used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `PurityFiniteSetting.forgetEtale` and the actual coefficient quotient.
- The recorded `Sheaf.Paper.PbcCoefficientTwists` and its finite signed Tate
  reexports: `Scheme.finiteEtaleTateSheaf`.
- `Sheaf.AlgebraicGeometry.SupportCohomology`: `Etale.supportSections`,
  `Etale.supportCohomology`, `ProEtale.supportSections` and
  `ProEtale.supportCohomology`.
- `Sheaf.AlgebraicGeometry.EtaleSupportedKernel`: `Etale.supportedKernel` and
  `Etale.supportedClosedInverseImage`; the adjunction theorem stays in its old module.
- `Sheaf.AlgebraicGeometry.SupportSiteComparison`:
  `ProEtale.etaleSupportKernel`, `supportComparisonUnit_existsUnique`,
  `supportComparisonUnit` and its actual comparison inverse image.
- `Sheaf.AlgebraicGeometry.EtaleModuleAbelianForget`: `Etale.moduleAbelianForget`.
  Its additive and exactness instances remain in the comparison theorem module. The
  support-specific scalar comparison uses Mathlib `PreservesKernel.iso` directly.
- `WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck`:
  `Functor.grothendieckLeftEdgeMap` and the natural-number/integer derived comparison.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange`:
  `Functor.rightDerivedBaseChange`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.localizationRestriction`, canonically inverse image along an etale map.
- Mathlib's `SmoothOfRelativeDimension`, `Smooth`, `Etale`, `IsClosedImmersion`,
  `Scheme.smallEtaleTopology`, `Sieve.ofArrows`, `ringKrullDim`,
  `NatTrans.rightDerived`, and pointwise evaluation. The already stated proof
  dependency modules are imported non-publicly as the stage requires.

Edge cases checked against the final interface: c=0 and its empty tuple; d=0;
empty U and an empty covering family; empty support; negative cohomological
indices; all signed r; arbitrary positive levels including ramification; arbitrary
bases with no finite-type, Noetherian or finite-dimensional assumption; identities
and nonidentity restrictions; covering families without an identity member; and
an arbitrary covering-index universe. The coefficient category remains in u+1,
while the actual small pro-etale site retains its object/morphism universe sizes.
No constant-sheaf identification or orientation is asserted.

Searches: the saved packet recorded LeanFinder, Loogle and Mathlib/project grep
searches with no exact bottom-descent statement. On this repair I reran
`msearch.py ... loogle '\"supportCohomology\"'` (0 hits),
`msearch.py ... grep 'supportCohomology|supportedSectionsFunctor|grothendieckLeftEdgeMap'`
(0 Mathlib hits), and LeanFinder with
`local to global bottom supported etale cohomology edge map natural restriction
 descent on covering families` (8 unrelated Mayer--Vietoris, open-diagram and
presheaf-gluing hits). `rg` for the node id, main theorem name and new normalized
comparison name in upstream, `lean/Sheaf`, and the upstream-name index found only
the frame-independence proof's use of this node. Existing support and comparison
interfaces were read and reused rather than duplicated. Sources reread include
Stacks `etale-cohomology.tex`, section-cohomology-support (09XP),
lemma-sections-with-support-acyclic (09XQ), and `sites-cohomology.tex`,
lemma-cohomology-of-open (03F3), plus the current blueprint frame-independence proof.
The localization reference was checked in the tag index and corrected to 03F3.
The search also found `ModuleRestrictionKernelComparison`: its interface is for
`SheafOfModules` on a common-universe small site. The present scalar comparison
uses the recorded `ModuleCat` sheaves on the actual etale site and directly
specializes Mathlib kernel preservation, rather than making a second module
category or support functor.
There is no statement dispute or change to the natural-language mathematical statement.
A `statement_change` record documents the dependency reclassification and explicit
definition references required by the return, including the two-citer audit.

## Repairs to the returned review

1. H3, supported covering descent: restored the literal global supported group,
   canonical restriction maps, and arbitrary specified covering family.
2. H3, edge target and naturality: one sheaf on U, normalized W-side source
   transport, explicit natural-number/integer comparison, and the full restriction square.
3. H3, pro-etale comparison: actual unit-induced support map, scalar forgetting,
   invertibility, the resulting edge and naturality through canonical comparison.
4. H2: all helpers, including `relativeSupportKernel_additive`, are now listed
   in `lean.declarations`.
5. H8: the main docstring now includes all nine steps; acyclicity has explicit
   source places and its adjunction/injective argument.
6. H6: the two inline over-morphism equation proofs were removed. The cover
   provides its site arrows directly. Every named theorem has only a `sorry`
   proof; required structural identities have named documented proof obligations.

## Second reading by Q72

This is the dispatcher's requested self-check, not a claim of an independent
second worker. No other agent was started; the maintainer supplies the independent
review. I reread the node and the repaired module clause by clause. The saved
packet's last clause was about sections tested on every object, hence included
an identity test; it is now about actual supported classes and a specified cover.
Its edge previously varied the cohomology sheaf with W and omitted naturality;
the new edge evaluates the fixed U-sheaf, explicitly transports the recorded
supported group, and states the restriction square. Its pro-etale clause
previously asserted only existence of an isomorphism; the new arrow derives the
published adjunction-unit map and scalar-forgetting comparison, and its inverse
defines the compared pro-etale edge. The pro-etale restriction square uses this
same canonical comparison. I checked that every hypothesis above is retained,
that the source at each W is A(r) restricted from U, and that empty covers,
negative twists and the c=0 boundary are not excluded. I also checked the
complete helper list, unique normalizations, absence of inline proof terms,
source places and nine-step proof documentation. The old second-reading claims
are replaced by this account of the mismatches actually found and repaired.

## Validation

The final repaired source was compiled with exactly
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q72 lem-pur-relative-support-bottom-descent lean/Sheaf/Paper/RelativeSupportBottomDescent.lean`.
It exited 0 with no Lean diagnostics: sandbox check 9.7 s; library-path check 8.1 s.
The wrapper supplied the private overlay. Earlier diagnostic probes were removed.
The module has no lines over 100 characters, no inline local proofs, and every
postponed theorem is listed among the 36 owning declarations. The recorded main
signature is verbatim from the final source. The original saved packet passed the initial required dry run at `2e8b079d93`.
The ownership repair below is being compiled and preflighted separately.

## New nodes

`def-pur-etale-supported-kernel` records `Sheaf.AlgebraicGeometry.EtaleSupportedKernel`.
It records the identical `supportedKernel` and `supportedClosedInverseImage` definitions
from the adjunction theorem module: kernel of the actual open-adjunction unit, then
composition with closed inverse image. Its source is Stacks 09XP, the supported subsheaf,
and the definition immediately before 09XQ, interpreted on Z using 04CA. The definition
binds arbitrary morphisms; its supported-sheaf interpretation applies to a complementary
closed/open pair. There is no new adjunction or exactness assertion. Edge cases j=id,
j empty, i empty and identity i use the same kernel formula. The original definitions
are removed from the theorem module, which publicly imports this new owner.

`def-pur-etale-module-abelian-forget` records
`Sheaf.AlgebraicGeometry.EtaleModuleAbelianForget`. It extracts exactly the existing
`moduleAbelianForget` abbreviation, whose real data is `sheafCompose` applied to
`forget₂ (ModuleCat Λ) AddCommGrpCat`. The source is the underlying abelian sheaf
in Stacks 03FD, `lemma-cohomology-modules-abelian-agree`. Arbitrary commutative Λ in
Type (u+1), zero coefficients and empty X are retained. The original abbreviation is
removed from the comparison theorem module; that module publicly imports its new owner.
All its existing instances and theorems remain; one stale proof binding is adapted as
documented below.

`def-pur-support-comparison-unit` records the existing `AlgebraicGeometry.ProEtale.supportComparisonUnit` definition in `Sheaf.AlgebraicGeometry.SupportSiteComparison`; it owns the canonical unit notion used by the statement.

`def-pur-grothendieck-edge-maps` records existing upstream definitions
`CategoryTheory.Functor.grothendieckBottomEdgeMap` and
`CategoryTheory.Functor.grothendieckLeftEdgeMap` in
`WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck` (397–425).
It owns no new module. The source is the blueprint edge-map definition and its filtration
composites, as implemented by the canonical spectral-object edges and source/target
transports. The left edge needs G left exact; the bottom needs both F and G left exact;
the recorded signatures retain the upstream acyclicity, additive functors, categories
and universes. Degree zero is included. These natural transformations give precisely
the canonical edge maps used here, with no arbitrary choice of a natural transformation.

Searches for all three new records were repeated on 2026-10-18. `blueprint_refs.py search`
on supportedKernel, moduleAbelianForget and grothendieckLeftEdgeMap returned no blueprint
nodes. `rg` over dag/nodes found mentions in theorem interfaces but no dedicated
definition owner. LeanSearch on "sheaf sections supported closed subset kernel adjunction
unit forget module sheaves abelian sheaves Grothendieck spectral sequence edge maps"
returned eight unrelated sheaf adjunction/sheafification results. LeanFinder on
"kernel functor of sheaves supported on a closed subset and coefficient forgetting module
sheaves and Grothendieck edge maps" returned eight ideal-sheaf, presentation and condensed
module hits; no exact interface. msearch grep for
`supportedKernel|supportedClosedInverseImage|moduleAbelianForget|grothendieckLeftEdgeMap`
returned zero Mathlib hits. Project grep found the two original side definitions and the
upstream edge maps, which were read in full and reused. Each node records the actual
search-log entries, including hit names and digests. No duplicate construction is added.

## Dependency modules

`lem-pur-etale-supported-kernel-adjunction`: its old module owned plain definitions needed
to state the item, forcing an unnecessary theorem-node statement dependency. The module
now imports `EtaleSupportedKernel`; the exact `supportedKernel_closedAdjunction` theorem
and its full proof docstring remain. Only its lean record changes, with the note required
by §1(B); the two extracted definitions are removed from that theorem's declaration list.

`lem-weil-pbc-module-abelian-derived-direct-image-comparison`: its old module owned the
plain coefficient-forgetting abbreviation needed to state the item. It now imports
`EtaleModuleAbelianForget`; the abbreviation has a unique definition in that module.
All existing proved instances, the acyclicity helper and inverse-image comparisons
are retained byte for byte. In the direct-image theorem only the binding of the existing
higher-direct-image comparison changes from destructuring to `let c := ...`: the loaded
API now returns an Iso directly, rather than Nonempty Iso. A wrapper #check confirmed
the direct-Iso signature despite the stale source text returned by --source. The
mathematical proof and all declaration signatures are unchanged. The dependency's node changes only its lean record and note.

## Statement corrected

The hypotheses and conclusions are unchanged from the base node. The text adds explicit
references to the three definition nodes and the sectionwise underlying-abelian-sheaf
convention already used by the support-cohomology interface. The return requests
replacing three added theorem-node statement dependencies by dedicated definition nodes,
and retaining the three theorems as proof dependencies. The `statement_change` field is
metadata for that dependency-only correction, not a change in hypotheses or conclusions;
its `old_statement`, `old_stmt_deps` and `old_proof_deps` are verbatim from the current base.
Source: Stacks 09XP/09XQ for supported sheaves, Stacks 03FD for underlying abelian sheaves,
and the blueprint Grothendieck edge-map definitions. All citers still hold:

- `lem-pur-frame-independence`: holds; the canonical restriction and covering equality
  test, all frame hypotheses and every coefficient degree are unchanged.
- `thm-pur-localized-top-chern`: holds; the vanishing and covering-descent use on the
  smooth zero-section pair remains exactly the same, including singular bases and rank 0.

## Second reading by Q72 — returned ownership repair

I read the three new definition records against the original declaration bodies and
source places. The support definitions and coefficient-forgetting abbreviation are
textually unchanged, apart from ownership docstrings. Each is now defined once and
reexported by its former theorem module. The Grothendieck record points to the existing
upstream natural transformations with the same hypotheses, no copied definition.
The main theorem's signature and the 36 declarations are untouched; only imports change.
A compile and #check found a stale Nonempty-Iso destructuring in the imported comparison
proof; its binding was changed to retain the Iso directly.
The three theorem ids are absent from stmt_deps and present in proof_deps, and the
supportComparisonUnit dependence remains. The two citers listed above were read and
retain their uses. No other agent was started, as instructed; independent review is the
maintainer's. Existing comparison proofs have been preserved, not replaced by sorries.

## Compile compatibility repair

The supplied coefficient-comparison module exposed an existing stale proof binding:
`obtain ⟨c⟩ := higherDirectImageSheafifiedPresheaf ...` destructured the returned Iso
into its hom, so `c.symm` failed. `scompile.py` on a separate #check file confirmed
that the loaded API returns the Iso directly. The sole proof adjustment is
`let c := higherDirectImageSheafifiedPresheaf ...`; the argument and theorem are unchanged.
This keeps the previously proved theorem proved rather than replacing it with a sorry.

## Original statement text

Use the finite datum $k,\ell,E,n,A$ of [def-pur-conventions], for arbitrary $n\geq1$. Let $V\to B$ be a smooth morphism of $k$-schemes, of a fixed finite relative dimension [def-sbc-smooth-morphisms], let $Z\hookrightarrow V$ be a closed immersion [def-weil-closed-immersion] with $Z\to B$ smooth [def-sbc-smooth-morphisms], and let it have pure codimension $c\geq0$ in the sense of [def-pur-frame-class]: $\dim\mathcal O_{V,z}=\dim\mathcal O_{Z,z}+c$ for every $z\in Z$, with Krull dimension the supremum of lengths of strict chains of prime ideals. Let $e:U\to V$ be etale [def-weil-etale-morphism] and suppose the ideal of $Z_U=Z\times_V U$ in $U$ is generated by $c$ global functions, as for a frame in [def-pur-frame-class]. Fix $r\in\mathbf Z$. On the small etale site [def-weil-pbc-etale-site] of $U$, with the twists $A(r)$ of [def-coefficient-twists-detailed], let $\underline\Gamma_{Z_U}$ be the subsheaf-of-sections functor with support and let $R\underline\Gamma_{Z_U}$ be its right derived functor (these sheaves live on $U$ and vanish off $Z_U$). Write $\mathcal H^b_{Z_U}(A(r))$ for its cohomology sheaves. Then
$$\mathcal H^b_{Z_U}(A(r))=0\quad(b<2c).$$
The canonical local-to-global edge map identifies
$$H^{2c}_{Z_U\times_U W}(W,A(r))\xrightarrow{\sim}\Gamma\bigl(W,\mathcal H^{2c}_{Z_U}(A(r))|_W\bigr)$$
for every etale $W\to U$, naturally under further etale restriction. Here the left side is [def-pur-support-cohomology]. The same assertion about the left side holds when it is computed on the small pro-etale site $W_{\mathrm{proet}}$ [def-weil-pbc-proetale-site], using its canonical comparison with ordinary etale supported cohomology. Consequently, if two classes in $H^{2c}_{Z_U}(U,A(r))$ have equal restrictions on every member of an etale covering of $U$, they are equal. No identification of the degree-$2c$ sheaf with a constant or twist sheaf, and no frame class or orientation, is asserted.

## Ownership-repair validation

The explicit five-file `scompile.py Q72 lem-pur-relative-support-bottom-descent` invocation
exited 0 with no Lean diagnostics. It compiled both new definition modules, both adjusted
theorem modules and `RelativeSupportBottomDescent` separately in dependency order, in
both sandbox and library views. Affected imports (ModuleCohomologyConventions,
RelativeSupportCoordinateModel and PurityRankOneLocalCalculation) also recompiled cleanly
in its private overlay. The main theorem's final library-path compile took 13.5 seconds.
Every moved definition occurs exactly once in the packet; all three new definition-node
signatures match their owning sources literally after whitespace normalization. No
mathematical statement, coefficient universe, canonical arrow, hypothesis or conclusion was altered.

## Delivery gate diagnostic

The repaired five-file packet compiled cleanly. The first repaired dry run then reached
the server preflight. Four new-node citation-format diagnostics were repaired by writing
each cited id in its own brackets. Two remaining diagnostics reject the existing proved
coefficient-comparison theorem and its existing private acyclicity helper because their
proofs are not `sorry`. Both proofs were already present on the base; the helper body
was unchanged, and the public theorem has only the loaded-API Iso binding compatibility
adjustment described above. Replacing these established proofs by sorries would lose
completed proof work, while leaving their old defining module imported would duplicate
the extracted coefficient-forgetting declaration. The extraction and all mathematical
interfaces remain in the sandbox for the maintainer; no launcher or gate script was
edited or bypassed. The next dry run checks that only this gate conflict remains.

## Final dry-run result

After fixing all four citation diagnostics, `deliver2.py Q72
lem-pur-relative-support-bottom-descent --no-push` compiled the packet and reached the
server preflight again. Preflight reported exactly two failures, both in the existing
`ModuleAbelianDerivedDirectImageComparison.lean` proofs:

- `AlgebraicGeometry.Etale.isIso_moduleAbelianDerivedLowerStarComparison`:
  "the proof is not `sorry`".
- `AlgebraicGeometry.Etale.moduleAbelianForget_injective_evaluation_acyclic`:
  "the proof is not `sorry`".

All new-node fields, source signatures, dependency changes, citer audit and module
ownership passed. The remaining warning about `lem-pur-support-site-comparison` is an
advisory explicitly allowed by the returned review because its unique canonical map is
used. The delivery tool printed "PREFLIGHT FAILED, nothing pushed". No wrapper or gate
was changed; the complete compiling ownership extraction remains in this sandbox.

## Retried saved-packet dry run — 2026-10-18

As instructed, this retry first inspected the saved report and ran the unchanged
saved packet through `deliver2.py Q72 lem-pur-relative-support-bottom-descent
--no-push`. The wrapper compiled every delivered module (and the saved diagnostic
probe) without a compiler error, rebuilt the packet on current main, and returned
exit 1 at preflight with exactly the same two reasons quoted above: the existing
public comparison theorem and existing private acyclicity helper have proofs
other than `sorry`. No delivery was pushed.

A read-only comparison with current main confirms that both dependency node files
change only `lean`. In `ModuleAbelianDerivedDirectImageComparison`, the only
changes are the requested new-owner import, removal of the extracted abbreviation,
and the documented direct-Iso binding compatibility adjustment. The private helper
proof is unchanged. The three definition nodes remain new, and the main item's
recorded correction still has exactly two citers, both holding. The returned
ownership repair is present; no new mathematical defect or compilation failure
was reported. The launcher-file instruction explicitly forbids patching or working
around a gate that wrongly refuses the packet. The compiling repair and original
proof work are retained for a gate correction; no scripts or live files were edited.

## Saved-packet retry — 2026-10-18, try 3

The required initial `deliver2.py Q72 lem-pur-relative-support-bottom-descent
--no-push` retry compiled the saved packet, refreshed its delivery base through
the authorized wrapper, and returned exit 1 with exactly the same two preflight
failures. The five delivered modules and the retained scratch diagnostic probe
compiled without Lean errors. No delivery was pushed.

Read-only comparison against current shared main again confirms that both
dependency nodes change only `lean`; the coefficient-comparison module retains
its existing proofs, with only the previously documented Iso-binding compatibility
change in the public proof. The support and forgetting definitions occur in their
new owner modules, and their theorem modules import those owners. All three
new definition records remain present, the three old theorem dependencies are
proof-only, and the allowed unique support-comparison dependency remains.

The concrete failure remains the gate's unconditional sorry-only check on
`isIso_moduleAbelianDerivedLowerStarComparison` and
`moduleAbelianForget_injective_evaluation_acyclic`, both already proved on the
base. Read-only inspection of `tools/stage2_delivery.py`, `check_lean_text`,
confirms that it checks all theorem bodies in a changed dependency module without
exempting preserved base proofs. The same dry run otherwise accepts the packet's
ownership records and two-citer audit. No mathematical repair is indicated by
this diagnostic. Existing proofs, live files and all launcher/gate scripts are
retained unchanged; no gate bypass is attempted. The compiling ownership repair
remains in the sandbox for correction of this tool refusal.

## Saved-packet retry — 2026-10-18, try 4

The requested first action after reading this report was the unchanged saved-packet
`deliver2.py Q72 lem-pur-relative-support-bottom-descent --no-push` dry run. All six
checked Lean files (five delivered modules and the retained diagnostic probe) compiled
without compiler errors. The wrapper rebuilt the delivery on its refreshed base and
returned exit 1: `PREFLIGHT FAILED, nothing pushed`, with exactly the same two
`the proof is not sorry` refusals for
`AlgebraicGeometry.Etale.isIso_moduleAbelianDerivedLowerStarComparison` and
`AlgebraicGeometry.Etale.moduleAbelianForget_injective_evaluation_acyclic`.

Read-only comparison against the shared base again confirms the private helper's proof
is unchanged. The public theorem has only the previously documented direct-Iso binding
repair. The remaining module diff is the new-owner import and removal of the extracted
abbreviation. Both dependency nodes change only `lean`; all three requested definition
nodes are present; the three theorem nodes occur only in the item's `proof_deps`.
Preflight accepted these records and the two-citer audit, reporting only those two
proof-body failures. Read-only inspection of `tools/stage2_delivery.py:237` confirms
that the gate checks every theorem body without a preserved-base-proof exemption.
The launcher's explicit prohibition on patching or working around a wrong gate refusal
applies. No source, node, launcher, gate or live-library file was changed in this retry;
only this report records its result. The compiling ownership repair remains saved.


## Saved-packet retry — 2026-10-18, try 5

The required initial saved-packet `deliver2.py Q72
lem-pur-relative-support-bottom-descent --no-push` completed with exit 1 after
compiling all six checked Lean files without compiler errors. The wrapper rebuilt
the packet against its refreshed delivery base. Server preflight accepted the three
new definition records, the two lean-only dependency repairs, and the statement
correction with two citers, both holding. It again reported exactly two failures:

- `AlgebraicGeometry.Etale.isIso_moduleAbelianDerivedLowerStarComparison`:
  “the proof is not `sorry`”.
- `AlgebraicGeometry.Etale.moduleAbelianForget_injective_evaluation_acyclic`:
  “the proof is not `sorry`”.

A read-only comparison against current shared main confirms that the private
acyclicity proof is unchanged, while the public comparison proof contains only
the already documented direct-Iso binding adjustment. The rest of that module's
diff is the requested new-owner import and removal of the extracted abbreviation.
Both dependency nodes still change only `lean`; the three theorem nodes identified
by the return are absent from the item's `stmt_deps` and present in `proof_deps`.
The supportComparisonUnit statement dependence is still the advisory explicitly
allowed by the returned review. Read-only inspection of `tools/stage2_delivery.py`
confirms that `check_lean_text` checks every theorem body in a changed module,
without an exception for preserved base proofs. The tool printed
`PREFLIGHT FAILED, nothing pushed`. No launcher or gate script was patched or
bypassed, no live source or node was edited, and all compiling repair work is retained.

## Repair update for returned delivery 6d66250f64e2

The ownership records for the two published theorem modules and the support comparison unit now use `existing: true` with their exact source signatures; no copied dependency module is delivered. The new definition node `def-pur-support-comparison-unit` has the required search records and cites each notion used in its statement.

The first repair dry run exposed the stage-2 preflight requirement that copied dependency
modules must not replace modules already on the base, and that dependency theorem bodies
must not be delivered with real proofs. I therefore removed the copied
`EtaleSupportedKernelAdjunction` and `ModuleAbelianDerivedDirectImageComparison` modules
from this delivery. Their existing published modules already define
`supportedKernel`, `supportedClosedInverseImage`, and `moduleAbelianForget`; the three
corresponding definition nodes now record those exact existing declarations and the item
imports the published modules. This avoids duplicate declarations and leaves the existing
comparison proofs untouched.

I added the definition node `def-pur-support-comparison-unit`, recording the existing
`AlgebraicGeometry.ProEtale.supportComparisonUnit` in
`Sheaf.AlgebraicGeometry.SupportSiteComparison`. The item now cites this definition node
in `stmt_deps` while retaining `lem-pur-support-site-comparison` in `proof_deps`, so its
statement dependency is a definition rather than a theorem. The item source was compiled
with `scompile.py` after these changes and had no diagnostics.


## Repair of immutable head d22a5c0338c1

The required first saved-packet dry run passed: commit ea3d17dc83, preflight and
per-file compilation clean. The subsequent self-check reproduced the returned
review_split diagnostic: exactly two proof_deps were absent from every step's
uses. This repair retains both dependencies and cites their actual roles.

Step 6 now cites `lem-sp-grothendieck-edge-maps` for the canonical left edge as
the filtration composite with its derived-functor source and target transports.
I read the upstream Grothendieck module's definitions and full edge signatures,
including `grothendieckLeftEdgeMap`. Step 8 now cites
`lem-weil-pbc-module-abelian-derived-direct-image-comparison` for compatibility
of scalar forgetting with derived direct image along the open complement in
the localization comparison. I read that node's full statement and its module's
canonical unit-compatible transformation and invertibility theorem. Its arbitrary
coefficient and arbitrary-morphism hypotheses apply here. These are citations
of existing interfaces; the proof route and all mathematical statements remain.

The main theorem docstring records the same two uses. `statement_change.old_proof`
records the complete original proof from current main, and its explanation names
the returned mismatch and repair. The proof-dependency set now equals exactly
the union of all nine steps' uses; each step remains below 2000 characters.
The two citers remain `lem-pur-frame-independence` and
`thm-pur-localized-top-chern`, both holding because the statement is unchanged.
The obsolete scratch `#check` probe was removed after its successful saved-packet
compile. Only the actual delivered module needs subsequent compilation.

## Second reading by Q72 — dependency-union repair

I checked the node and module together without starting another agent, as the
dispatcher requires. The main Lean signature still matches lean.statement
verbatim. No binder, universe, construction, hypothesis or conclusion changed.
All 36 declarations, the original sorry proofs and the edge cases listed in
the Worker report remain. The only Lean edits are the two proof-docstring
citations. Existing definition-owner records and published dependency modules
are retained from the passing saved packet.
