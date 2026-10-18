## What changed

Implemented the reviewed invertibility repair of
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tateTwistDerived`.
The wrapper now accepts the unit proof, and all six local applications obtain it from
the existing base-field assumptions using the proved `ell_isUnit`. No declaration of
`Challenge.lean` changes. The change record is
`coord/changes/A4-poincare-tate-invertibility.md`.

The corrected theorem is proved for every integer twist and shift. Seven support modules
prove the compatible primitive-root diagram, its free integral-module comparison, the
continuous residue coefficient quotient and inverse limit, arbitrary pullback of a local
basis, and scalar extension. The item proves tensor powers, duals, a one-stratum finite
presentation, and shifted-single constructibility for the actual source construction.

This retry retained the earlier work and completed its remaining geometric theorem.
Over same-universe faithfully flat ind-etale w-contractible ring extensions, sections of
the primitive-root and Kummer covers give compatible units. Residue-field orders imply
invertibility of all power differences. Explicit exponentiation maps are locally
bijective by Lagrange interpolation; sheafification, transition naturality and localization
restriction produce the required isomorphism of actual abelian sheaf diagrams.

The named `poincareProjection` is the existing exceptional projection transformation.
Local transparency annotations and a proved generic projection argument keep the concrete
closed-category conversions within the single-file limit. The original trace-cup and
Poincare-isomorphism results are retained. Public imports of the item are unchanged.

## Proved and sorry left

The original item contains one `sorry`, in
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tateTwistDerived`.
Its corrected, invertibility-aware statement has a complete proof. This is a statement
repair with proof, not a proof of the disputed unrestricted original statement.
Holes removed: that one declaration. Holes added: zero. Split-offs left: zero.
There is no `sorry` in any of the eight delivered Lean modules or in any definition.

New proved public theorems:

- `AlgebraicGeometry.ProEtale.CondensedRing.ell_isUnit`.
- `AlgebraicGeometry.ProEtale.tateResidueModuleCone_isLimit`.
- `AlgebraicGeometry.ProEtale.constantTateResidueSystem_free_iso`.
- `AlgebraicGeometry.ProEtale.exists_compatible_roots_diagram_basis`.
- `AlgebraicGeometry.ProEtale.exists_tateModule_residue_diagram_iso`.
- `AlgebraicGeometry.ProEtale.tateModule_locally_trivial`.
- `AlgebraicGeometry.ProEtale.tateModule_pullback_locally_trivial`.
- `AlgebraicGeometry.ProEtale.tateTwistOne_pullback_locally_trivial`.

All eight modules compiled together against the published build without warnings. The
completed compatible-root module compiled in 14.3 s and the item in 37.9 s in that check.
Fresh `#print axioms` audits of the root-diagram theorem, integral local-basis theorem and
corrected constructibility theorem show exactly `propext`, `Classical.choice` and
`Quot.sound`, with no transitive `sorryAx`. No whole-library build was run.

## No longer needed

No original item import was removed. Its original private zero-twist helper and the
`Sheaf.PoincareDuality.TateTwistLocalLine` import remain for compatibility with the
source declaration inventory; the corrected proof uses the general signed-power route.
The root proof uses the Lagrange API directly and does not import the experimental
`WeilConjectures.AlgebraicGeometry.Sites.Kummer` or
`WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnityConstant` modules.

The old constructibility detour through `def-pur-sheaf-hom`,
`det-def-sfb-constructible-local-model`, and `sk-def-sfb-constructible` is unnecessary.
The actual internal Hom and the upstream cokernel finite-presentation predicate suffice.
The coefficient route through `sk-prop-sfb-qlbar-colimit-x` and
`lem-pur-condensed-zl-reduction-mod-ell-power` is also unnecessary: the actual continuous
coefficient limit and quotient are proved directly.

The broad `lem-pur-twist-sheaf-locally-free` and
`det-def-sp-tate-twist-locally-free` declarations are not imported. The compatible-root
proof now also prunes its former dependencies `lem-asd-finite-etale-twist-line`,
`lem-amb-kummer-any-base`, and
`lem-weil-pbc-proetale-affine-wcontractible-covering-family`: explicit ring covers and
sections give the roots, and retaining the same-universe algebra witnesses gives the
required small cover directly. The field primitive-root argument and weakly etale
localization remain needed. The existing shifted-single module remains needed.
No maintainer `tool_uses` approval was changed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old signature): constructibility was asserted for every scheme,
without the blueprint assumption that the coefficient prime is invertible. On the
characteristic-ell nonreduced group-algebra example recorded in the reviewed node,
compatible roots have unbounded Tate rank. The reviewed DAG had already repaired the
domain. This delivery implements that repair, with no additional finiteness assumption.
The wrapper definition changes, so semantic review of any target using it must reopen.

Some dependency attachments point to files absent from the supplied source snapshot:
`Sheaf.Paper.PurTwistSheafLocallyFree`,
`Sheaf.AlgebraicGeometry.CondensedTateTwists`, and
`Sheaf.Paper.TateTwistLocallyFree`. The actual construction is in
`WeilConjectures.TateTwist.ProEtale`. The final proof uses available, closed source APIs
and explicit comparisons instead. It keeps the Tate unit's integral-root, limit,
scalar-extension, positive-power and dual route.

Edge cases checked by the constructions: empty schemes, zero rings, residue level zero,
twist zero, negative twists, and arbitrary integer shifts. No finite-type,
quasi-compactness or Noetherian hypothesis is added. Every direct use of a changed public
interface is inside the item, as confirmed by `tools/downstream.py --uses` for the
constructibility theorem, wrapper, purity isomorphism, trace, Poincare map and cup product.
Its only downstream importers are `TargetsCheck` and `WeilConjectures`; neither needs a
source adaptation. No module held by another group is adapted.

Delivery-tool failure: the required dry run compiles the completed sandbox but refuses
three changed non-sorry definition bodies: `boundedConstructibleTateTwist`, `poincareMap`
and `cupProduct`. All three full names have explicit entries in
`coord/upstream-statement-exceptions.tsv` (lines 76, 79 and 80). In
`tools/stage3_gate.py`, statement changes and public additions are filtered by that
exception set, but the `body_changed` check at lines 124–126 does not consult it.
Thus the mandatory wrapper repair is rejected even though its declaration is explicitly
excepted. Keeping its old body would call the repaired theorem without the required
unit argument. The other two bodies use the documented definitionally equal projection
interface needed to avoid the concrete category conversion timeout. No tool was edited
or worked around. The report and completed proof remain in the sandbox for the maintainer.

Rechecked 2026-10-18T11:00:43+08:00: the mandatory retained-sandbox dry run completed
all eight module compiles and the axiom-probe phase, then failed preflight for exactly
one reason. The stage3 gate rejects changed non-sorry bodies of
`boundedConstructibleTateTwist`, `poincareMap` and `cupProduct`, despite their explicit
exception entries in `coord/upstream-statement-exceptions.tsv` (lines 76, 79 and 80).
The current `tools/stage3_gate.py` body-change check at lines 124–126 still does not
consult the exception set. The dry run printed `PREFLIGHT FAILED, nothing pushed`.
No tool was edited or bypassed. The complete zero-sorry repair is retained.

Fresh dispatcher retry at 2026-10-18T11:06:06+08:00: ran the required retained-sandbox dry run before
changing any Lean source. It again completed all eight module compiles and the axiom
probes, then printed `PREFLIGHT FAILED, nothing pushed`, with exactly one reason:
the stage3 gate rejects the non-sorry bodies of `boundedConstructibleTateTwist`,
`poincareMap` and `cupProduct`. Current source inspection confirms that all three
are explicitly excepted, but the gate's non-theorem body-change check does not use
that exception set. The corrected wrapper necessarily supplies the newly required
invertibility proof, so retaining its old body cannot implement the assigned repair.
No Lean source, launcher script or repository tool was changed in this retry.
The complete zero-sorry repair is retained pending the gate correction.

Fresh dispatcher retry at 2026-10-18T11:09:59+08:00: the required retained-sandbox dry run
completed the eight-module compilation and axiom-probe phases, then failed preflight
with exactly one reason: stage3_gate.py rejects changed non-sorry bodies of
boundedConstructibleTateTwist, poincareMap and cupProduct. The declarations remain
explicitly excepted at coord/upstream-statement-exceptions.tsv lines 76, 79 and 80,
but the gate's body_changed filter does not consult its exception set. The mandatory
wrapper correction cannot retain the old body, which omits the new unit argument.
The dry run printed PREFLIGHT FAILED, nothing pushed. No Lean source, repository
tool or launcher script was changed. All eight zero-sorry modules are retained.

Fresh dispatcher retry at 2026-10-18T11:14:05+08:00: the required retained-sandbox dry run exited 1
with `PREFLIGHT FAILED, nothing pushed`. Its sole refusal is the stage3 gate's
non-sorry-body check for `boundedConstructibleTateTwist`, `poincareMap`, and
`cupProduct`. The current exception table explicitly lists these declarations, while
`tools/stage3_gate.py` lines 124–126 still do not filter body changes through the
exception set. In this retry compilation was **not run**: the output marks
`IntegralResidueLimit` as `compile+probe: not run` and the other seven modules as
`deferred`. Earlier compile results above are historical, not fresh validation.
No Lean source, repository tool, or launcher script was changed or bypassed.
The eight zero-sorry source modules and all delivery records remain in the sandbox.

Fresh dispatcher retry at 2026-10-18T11:17:47+08:00: ran the required retained-sandbox dry run
before changing Lean source. It exited 1 with `PREFLIGHT FAILED, nothing pushed`.
The sole refusal remains the stage3 gate rejecting changed non-sorry bodies of
`boundedConstructibleTateTwist`, `poincareMap`, and `cupProduct`. All three are
explicitly listed in `coord/upstream-statement-exceptions.tsv` (lines 76, 79, 80),
but `tools/stage3_gate.py` lines 124–126 do not consult those exceptions.
The wrapper body must pass the repaired theorem's invertibility argument.
The delivery script reached preflight after its local compile and axiom-probe
phases; preflight's separate server compile is marked not run/deferred.
No Lean source, repository tool, or launcher script was changed or bypassed.
The complete eight-module zero-sorry repair remains in the sandbox.

Fresh dispatcher retry started 2026-10-18T11:18:31+08:00: the required retained-sandbox
dry run again exited 1 with `PREFLIGHT FAILED, nothing pushed`. Its sole refusal is
the non-sorry definition-body check for `boundedConstructibleTateTwist`,
`poincareMap`, and `cupProduct`. Read-only inspection confirms that the exception
table lists all three full declaration names, but the gate's `body_changed`
filter does not consult those exceptions. The preflight output marks
`IntegralResidueLimit` compile+probe as `not run` and the other modules as
`deferred`; this retry does not claim those as fresh successful checks.
A source scan found no `sorry`, `axiom`, `unsafe`, or `opaque` in the eight
delivered Lean modules. No Lean source, repository tool, or launcher script was
changed or bypassed. The complete repair remains in the sandbox, with zero
remaining holes and zero split-offs, awaiting correction of the delivery gate.

Fresh dispatcher retry at 2026-10-18T11:25:40+08:00: the required
retained-sandbox dry run exited 1 with `PREFLIGHT FAILED, nothing pushed`.
Its sole diagnostic is the stage3 gate rejecting changed non-sorry bodies of
`boundedConstructibleTateTwist`, `poincareMap`, and `cupProduct`. Read-only source
inspection confirms that the exception table explicitly lists all three full
names, while the gate's `body_changed` filter still does not consult the exceptions.
The wrapper cannot retain its old body: that body omits the invertibility argument
required by the repaired theorem. The preflight marks `IntegralResidueLimit`
compile+probe as `not run` and the other seven as `deferred`; those messages are
not fresh compile successes. A fresh source scan found no `sorry`, `axiom`,
`unsafe`, or `opaque` in the eight delivered Lean files. No Lean source, repository
tool or launcher script was changed or bypassed. Zero holes and zero split-offs
remain; the complete repair is retained pending correction of the delivery gate.

## New nodes

`lem-poincare-integral-residue-module-limit`, module
`Sheaf.PoincareDuality.IntegralResidueLimit`: the explicit regular integral coefficient
cone is limiting. All maps, actions, compatibility and the limiting property are proved.

`lem-poincare-integral-residue-free-comparison`, module
`Sheaf.PoincareDuality.IntegralResidueQuotient`: the free module on constant finite
residues is the actual residue diagram, by explicit cokernels and transition identities.

`lem-poincare-compatible-primitive-roots`, module
`Sheaf.PoincareDuality.CompatiblePrimitiveRoots`: the actual abelian root diagram becomes
the constant residue diagram on one small pro-etale cover. This formerly residual
geometric theorem is now fully proved, including local bijectivity and raw inverse image.

`lem-poincare-compatible-integral-root-bases`, module
`Sheaf.PoincareDuality.CompatibleIntegralRootBases`: apply the free-module comparison
to the compatible abelian root bases to identify the two finite integral diagrams.

`lem-poincare-integral-tate-local-basis`, module
`Sheaf.PoincareDuality.IntegralTateBasis`: preserve the inverse limit under weakly etale
restriction, then apply the explicit residue coefficient limit cone.

`lem-poincare-integral-tate-pullback-local-line`, module
`Sheaf.PoincareDuality.IntegralTateLocalLine`: base-change the cover and transport the
basis through the monoidal square, with explicit linearity and coefficient transport.

`lem-poincare-first-twist-pullback-local-line`, module
`Sheaf.PoincareDuality.TateTwistOneLocalLine`: scalar extension commutes with inverse
image and sends the regular integral module to the regular rational module.

`lem-poincare-ell-unit-over-field` is the proved field-to-global-sections unit lemma in
the item. The existing target node records the same integral-to-rational-to-signed-to-
constructible route and its corrected Lean attachment.

All these nodes and modules were retained from the earlier sandbox; no further node
was added by this retry. Their searches and sources remain recorded.
Change record: `coord/changes/A4-poincare-tate-invertibility.md`.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
