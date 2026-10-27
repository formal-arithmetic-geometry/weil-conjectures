## Worker report

Stage 2, group Q98, item lem-sfb-space-relative-flat-closed-kernel-base-change.
Repair of independent review at immutable head dd7b64d89f14. The saved packet's initial
dry run passed at e8fb884b50c, but its two substantive return points still required repair.
The mathematical statement, its theorem signature, and its six proof steps are unchanged.

The main module is Sheaf.AlgebraicGeometry.SpaceRelativeFlatClosedKernelBaseChange.
The theorem is AlgebraicGeometry.AlgebraicSpace.relativeFlatClosedKernel_baseChange.
Its proof is sorry, with all six DAG proof steps in the docstring. Three helper definitions
supply real canonical comparison maps; none selects arbitrary maps or contains sorry.

Hypothesis and clause matching:

- Work over Spec Z: S0 and S are objects of Over (Spec (CommRingCat.of (ULift.{u} ℤ))).
  The ULift merely puts the integer base in the scheme universe. Every scheme has its
  unique integer structure map, so this excludes no scheme or scheme morphism.
- X0,Y0 are algebraic spaces over S0: X0,Y0 are AlgebraicSpace objects over that integer
  base and x0,y0 are their displayed morphisms to schemeSpace S0. These are the existing
  full subcategory of fppf sheaves, not schemes substituted for algebraic spaces.
- Arbitrary scheme morphism a:S→S0: a:S⟶S0 in the over category. There is no property
  binder on a, and being over the integer base is automatic.
- T0=X0×_{S0}Y0: pX,pY and hT0:IsPullback pX pY x0 y0. T0 is any representative
  of the categorical fibre product; the universal property is not an extra geometric
  condition. The full-subcategory inclusion preserves this limit on sheaves.
- T=T0×_{S0}S and q its projection: q,b,hT:IsPullback q b (pX≫x0) (yoneda.map a),
  where ObjectProperty.homMk regards the canonical represented-scheme map as a space map.
- Closed immersion i0: hi0:IsRepresentableWith (fun _ _ c ↦ IsClosedImmersion c.left)
  i0.hom.hom. This is exactly closed immersion on every scheme test, using Mathlib's
  scheme closed-immersion predicate, with no flatness added to i0.
- Flat Y0/S0: hY:MapIsFlat y0; flat W0/X0: hW:MapIsFlat (i0≫pX). MapIsFlat is the
  existing predicate testing Flat on every compatible pair of etale scheme charts.
- W=W0×_{T0}T with r,i: hWsq:IsPullback r i i0 q. The first conclusion states i is
  representable by closed immersions, accounting for the node's description of i.
- Unbounded derived categories and sizes: four separate HasDerivedCategory.{w} instances
  for T0,T,W0,W, with explicit common arbitrary localization universe w. No localization
  is required for X0,Y0, and no relation between site and derived morphism universes is
  imposed. SmallModules is the already existing affine-site model equivalent to Modules.
- Lq*((i0_*O_W0)[0]) ≅ (i_*O_W)[0]: alpha has precisely that type, using the existing
  spaceDerivedPullback, smallModuleDirectImage, SheafOfModules.unit, and
  DerivedCategory.singleFunctor at degree 0. The transported unit is canonically the
  original regular-function structure module via smallModuleUnitIso.
- Identification of closed pushforward with derived pushforward: e0 and ei are the two
  isomorphisms from ordinary pushforward in degree zero to derivedDirectImage of
  derivedStructure. Their homs equal relativeClosedKernelDirectImageComparison,
  constructed from singleMapHomologicalComplex and the universal right-derived unit.
  Thus these are the canonical comparison maps, not unspecified object identifications.
- Lr*O_W0=O_W: er has this isomorphism type and er.hom equals
  relativeClosedKernelDerivedStructureMap r. This map is the adjoint, under the existing
  normalized derived adjunction, of the existing regular-function structure morphism
  followed by the canonical ordinary-to-derived direct-image comparison. On a chart its
  tensor formula is b⊗c ↦ b r♯(c), fixing the multiplication identification.
- The isomorphism is THE derived base-change comparison: the final equation is
  alpha.hom ≫ ei.hom = Lq*(e0.hom) ≫ moduleDerivedExchange(i0,i,q,r)(O_W0) ≫ Ri*(er.hom).
  The existing moduleDerivedExchange is defined as the adjunction mate of the pulled
  counit using spaceDerivedPullbackComp. The equation retains its actual map after all
  three canonical identifications. Since ei is an isomorphism, it uniquely determines
  alpha.hom. This adds no arbitrary comparison as a hypothesis.
- No flatness of a, x0 or i0 and no Noetherian, separatedness, finite-presentation,
  finiteness or properness assumptions appear.

Dependency declarations read and used (all under AlgebraicGeometry.AlgebraicSpace unless
otherwise specified):

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace,
  IsRepresentableWith, Modules, EtaleSite and structureSheaf.
- def-weil-size-convention is metatheoretic; its record explicitly asks consumers to bind
  universes, rather than supplying a declaration to import.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules, the transparent
  existing SheafOfModules specialization underlying Modules.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: HasDerivedCategory, DerivedCategory,
  DerivedCategory.singleFunctor, Q and singleFunctorIsoCompQ.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: moduleDirectImage,
  moduleTensorAdjunction and the compatible-chart moduleDirectImageModel.
- Sheaf.AlgebraicGeometry.SpaceDerivedPullback: spaceDerivedPullback and its counit;
  its normalized composition comparison is used by moduleDerivedExchange.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  fibreProduct_isAlgebraicSpace (the fibre products are supplied by their universal
  properties rather than by introducing another chosen construction).
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: AlgebraicGeometry.IsClosedImmersion;
  Mathlib.AlgebraicGeometry.Morphisms.Flat: AlgebraicGeometry.Flat, with its stalkwise
  characterization Flat.iff_flat_stalkMap.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: MapIsFlat and MapIsLocally.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap: moduleStructureMap, uniquely
  characterized by all regular-function chart projections.
- Sheaf.AlgebraicGeometry.SpaceAffineSectionsCompositors: smallModuleUnitIso and
  fullModuleSection; both retain the fixed restriction equivalence's unit and counit.
- Sheaf.AlgebraicGeometry.SpaceAffineHomComparison: spaceRightDerivedComplexUnit and
  spaceDerivedAdjunction, with its ordinary-unit normalization.
- Sheaf.AlgebraicGeometry.SpaceModuleDerivedExchange: moduleDerivedExchange, the actual
  counit mate, now owned by def-sfb-space-module-derived-exchange. No flat-complex theorem
  is used as a statement dependency.

The four existing owning definition nodes and the new exchange definition node are cited
in stmt_deps. The flat-complex theorem node is removed from that list. Following
the import rule, the already stated proof modules for quasi-coherent modules, affine
higher-image vanishing, K-flat complexes and derived tensor pullback are also imported.
The four proof prerequisites product-tor-independence, affine-locality, closed-immersion-
quasi-coherent-modules and tor-independent-base-change have no recorded module to import;
this delivery only states the item, so their future proof interfaces are not assumed.

Source and edge checks:

Read spaces-more-morphisms.tex lemma-case-of-tor-independence (0CTQ), including its
scheme-chart reduction, and spaces-perfect.tex lemma-compare-base-change (08IR), including
the canonical map in its first proof sentence. Their substitutions are exactly Z'=W0,
X'=X0,Y'=Y0,B'=S0,B=S and f=i0,g=q,f'=i,g'=r. Arbitrary representatives of products and
pullbacks are equivalent to the source's named products. Empty W0, T, X0 or Y0 are allowed;
there is no nonempty-point assumption, and the zero structure module gives the asserted
zero-object identifications. The identity base change and an arbitrary nonflat base change
are included. For example, with S0=Spec Z, X0=S0, Y0=A¹_Z, W0=V(t), changing base to
Spec F_p remains a permitted instance. The flatness condition is substantive: dropping hW allows W0=Spec F_p inside
T0=S0=Spec Z (X0=Y0=S0); base change by Spec F_p has nonzero
Tor_1^Z(F_p,F_p). The independent hY assumption is retained exactly as in 0CTQ.
No n, index-set, field-characteristic or bounded-complex restriction was introduced.
No STATEMENT-DISPUTED issue or source correction was found.

Searches (2026-10-23 UTC):

- msearch.py leanfinder: "Derived pullback of a closed immersion structure sheaf in a
  product with relative flatness is its base changed structure sheaf". Eight results
  concerned scheme flat projections, stability of closed immersions, and affine pullback
  identifications. None states this derived algebraic-space assertion.
- msearch.py leansearch: "Derived base change for the structure sheaf of a closed
  immersion relatively flat over one factor of a product of algebraic spaces".
  Eight results concerned ordinary flat modules/ring maps, regular elements, closed
  immersion stability and Kahler differentials; none matches.
- msearch.py loogle: '"baseChange", "derived"'. Only the two LieAlgebra derived-series
  base-change declarations were returned, unrelated to derived categories.
- msearch.py grep, AlgebraicGeometry: 'TorIndependent|torIndependent|relativeFlatClosed|
  closedKernelBaseChange'. Zero Mathlib results.
- rg in lean/WeilConjectures for the item id: no result. Search for relative-flat closed
  kernel names and TorIndependent found existing scheme-only Tor-independent/flat-complex
  comparisons, including DerivedPullbackTorIndependentFlatComplex and
  TorIndependentPerfectTensorBaseChange. Their scheme objects do not state this item.
- rg in lean/Sheaf for closedKernel/relativeFlatClosed/derived exchange and structure maps
  found the separate pro-etale closed-kernel API, the consumer SpaceDerivedChowNeighbourhood,
  and the canonical moduleDerivedExchange, moduleStructureMap and smallModuleUnitIso used
  here. No existing declaration states the requested relative-flat closed-kernel theorem.
- Read the current server SpaceDerivedPullback with scompile.py --source to diagnose the
  difference between its source and published interface; no blanket replacement was made.

## Repairs

H2: Added def-sfb-space-module-derived-exchange, owning the extracted module
Sheaf.AlgebraicGeometry.SpaceModuleDerivedExchange. moduleDerivedExchange keeps its full
name, type, four independent localization instances, and complete construction verbatim.
The item's stmt_deps now cites this definition node in place of
lem-sfb-space-flat-complex-base-change. The old theorem module publicly imports the new
module and no longer declares the helper, preventing duplicate declarations. Its remaining
coefficient map and theorem are unchanged. The old theorem's lean.declarations no longer
claims ownership of the extracted helper; its dependency record explains the move.

H13: Removed the SpaceDerivedPullback source change and the
def-sfb-space-derived-pullback.json record change from the packet. Byte-identical copies
of the live pullback source and ownership record are supplied only to refresh its private
compilation artifact; they
produce no Git delta. The delivery uses Q72's live module and binders without editing its by,
note, or any other field. The earlier published-olean issue did not justify rewriting
that record; the old report's dependency repair claim is withdrawn.

## New nodes

def-sfb-space-module-derived-exchange records the canonical counit-mate map for any
commuting square of algebraic spaces and any unbounded structure-module derived object.
Its source is Stacks sites-cohomology.tex, 07A6 lemma-adjoint and 07A7
remark-base-change, used in spaces-perfect.tex 08IR's first proof sentence. This is a
construction and asserts no invertibility. The three fresh msearch queries in its
mathlib_searches are recorded in searches.jsonl: LeanSearch returned generic commutative
square adjunction facts, LeanFinder ordinary sheaf/module pullback adjunctions, and
Mathlib grep no derived algebraic-space exchange. Local rg found the exact existing plain
def in SpaceFlatComplexBaseChange, which is moved unchanged, rather than duplicated.
The DAG has no definition node owning it: the other mention in
 def-sfb-space-base-change-comparisons is a historical search-result string, not a
statement or declaration. blueprint_refs.py search 'derived exchange' returned 29
scheme/constant-coefficient/compact-support results, none defining this structure-module
exchange for algebraic spaces; its computed blueprint ancestor is null, as inherited
from the item. The general commuting-square statement includes noncartesian squares,
empty spaces, zero derived objects, identity squares, and nonflat arrows; no assertion of
invertibility fails in those cases. Each source object and hypothesis is explicit in the
new node, and the record cites precisely the definition nodes named in its statement.

## Dependency modules

lem-sfb-space-flat-complex-base-change: the old module mixed the generic exchange helper
with its invertibility theorem, so citing its theorem node for just the helper was H2.
As expressly requested by the return, the plain exchange definition is moved, with its
name and body unchanged, to the new definition module. The old module is delivered with
only that extraction and the public import of its new owner. Its coefficient comparison,
theorem, source, proof docstring, universes and other imports are preserved; only its lean
ownership record changes. No SpaceDerivedPullback dependency module is delivered.

## Self-check by Q98

Re-read the saved theorem and node against 0CTQ and 08IR: a remains arbitrary; hY and hW
are exactly the two flatness assumptions; hi0 and the first conclusion are closed
immersion on scheme tests. T0, T and W retain the three pullback universal properties.
The degree-zero ordinary direct images and derivedStructure objects, the maps e0, ei,
er pinned to their three concrete canonical comparisons, and alpha's final exchange
equation are unchanged. The four HasDerivedCategory instances remain separate and no
all-spaces localization assumption is added. For the new node, the signature of
moduleDerivedExchange exactly accepts the square's four arrows, equality and A; its
source and target are Lg*Rf*A and Rf'*Lh*A. The body takes homEquiv under the normalized
f' adjunction after the inverse g,f' composition, the square transport, the f,h
composition, and pulled f counit. These are exactly the new definition's clauses.
The only mismatches found were those in H2/H13 above; the mathematical theorem has no
new mismatch and no STATEMENT-DISPUTED issue. This is the worker's self-check, not a
claim of an independent second reader; the maintainer independently reviews delivery.

Validation: every delivered module is compiled separately with scompile.py. The repaired
packet is then checked with deliver2.py --no-push before pushing.

## Validation outcome

scompile.py passed every delivered module, one file at a time: the new exchange owner,
the old flat-complex module after extraction, and the item's module. The byte-identical
live pullback source was compiled privately to avoid the published-olean lag; the dry
run's staged-file list confirms that neither its module nor its record is changed.

The repaired dry run rejected the requested ownership extraction: after removing the
flat-complex theorem from stmt_deps, preflight excludes that theorem node's lean-only
ownership repair from the item's prerequisite closure, then reports that the changed
SpaceFlatComplexBaseChange.lean has no owning node in the delivery. The old module must
be changed to remove the moved declaration, otherwise importing both modules duplicates
moduleDerivedExchange. The missing import_flags field was repaired with an empty list;
the final dry run is repeated to isolate the remaining gate failure. No mathematical
dependency is invented to force the ownership-only edit into the graph.

Final repeat: preflight FAILED (stage 2), exactly 1 reason: (c)
lean/Sheaf/AlgebraicGeometry/SpaceFlatComplexBaseChange.lean: no node of the delivery
has it as lean.file (every module is the module of the item, of a new definition node
or of a dependency node). Its owning node file is present in the staged list, but
preflight excludes it as outside the prerequisite closure after the mandated H2
replacement. This is a delivery-gate refusal of the explicitly authorized extraction.
Both return points are repaired in the retained sandbox; nothing is pushed.

## Saved-packet retry

2026-10-23 22:30 UTC: Read the retained report and ran the prescribed initial
`deliver2.py Q98 lem-sfb-space-relative-flat-closed-kernel-base-change --no-push`
on the unchanged repaired packet. All four supplied Lean files passed the server
compilation phase. Preflight again failed for exactly one reason, (c):
`lean/Sheaf/AlgebraicGeometry/SpaceFlatComplexBaseChange.lean: no node of the delivery
has it as lean.file`. The staged list includes its owning theorem-node JSON;
preflight treats that node as outside the prerequisite closure after the H2-mandated
replacement. No changes were pushed. The explicitly requested extraction cannot
pass this gate without a tool correction; launcher/preflight scripts were not edited
or bypassed, and no artificial mathematical dependency was added.

## Saved-packet retry, 2026-10-23 22:34 UTC

The required initial dry run on the retained packet again passed its four-file
server compilation phase and failed preflight for exactly the same ownership
reason (c): `SpaceFlatComplexBaseChange.lean: no node of the delivery has it as
lean.file`. The staged-file list includes both that module and its owning
`lem-sfb-space-flat-complex-base-change.json` record.

Read-only inspection of `tools/stage2_delivery.py`, dependency classification at
lines 953–957 and module ownership at lines 1231–1235, confirms the cause: it
discards the supplied owner as outside the item's prerequisite closure before
checking ownership. The item's live statement and proof dependencies do not
include the flat-complex theorem; H2 expressly requires replacing its previous
statement-dependency citation with the new definition node. The extraction
updates a consumer of that definition, rather than a mathematical prerequisite
of this item. Adding an artificial theorem dependency would contradict H2.
Keeping the old definition while defining the same name in the new module would
leave two library declarations of one name. Neither is a valid repair.

H13 is still satisfied: the supplied pullback source and node record are
byte-identical to live and absent from the staged changes. H2's new owning
definition node and the unchanged-name extraction are retained. No tool was
modified, no direct Git command was run, and nothing was pushed. The remaining
failure is the delivery gate's refusal of the requested ownership extraction.

## Saved-packet retry, 2026-10-23 22:41 UTC

Ran the prescribed initial deliver2.py --no-push on the retained packet. The
four-file server compilation phase completed, followed by preflight failure for
exactly one reason: (c) lean/Sheaf/AlgebraicGeometry/SpaceFlatComplexBaseChange.lean:
no node of the delivery has it as lean.file. The staged list explicitly includes
its owner lem-sfb-space-flat-complex-base-change.json. Nothing was pushed.

Compared the retained files directly with current shared sources without Git
commands: both SpaceDerivedPullback.lean and def-sfb-space-derived-pullback.json
are byte-identical to live (H13). SpaceFlatComplexBaseChange.lean differs only
by extracting moduleDerivedExchange and publicly importing its new owner; the
original coefficient comparison and theorem are unchanged (H2). The extracted
definition keeps its name, type and body. Its new definition node is cited in
the item's stmt_deps; the theorem is not cited for a plain definition.

Read-only inspection of tools/stage2_delivery.py confirms that its prerequisite
classification skips the supplied theorem owner before module ownership is
checked, causing this refusal. Restoring an artificial theorem dependency would
contradict H2; omitting the old-module extraction would duplicate the declaration
when the old and new modules are imported together. The gate needs to admit the
explicitly requested extraction and associated ownership-only node repair. No
launcher or project tools were modified or bypassed. All repaired work remains
in the sandbox.

## Saved-packet retry, 2026-10-23 22:44 UTC

Ran the prescribed initial deliver2.py --no-push against the retained packet.
Its four-file server compilation phase passed. Preflight failed with exactly
one enforced reason (c): lean/Sheaf/AlgebraicGeometry/SpaceFlatComplexBaseChange.lean
has no owning node in the delivery. Its supplied owner JSON appears in the
staged list, but prerequisite classification excludes it (advisory b), causing
the enforced module-ownership rejection. Nothing was pushed.

Rechecked current shared sources without Git commands: both supplied
SpaceDerivedPullback.lean and def-sfb-space-derived-pullback.json are byte-identical
to live. The flat-complex module diff is exactly the public import of the new
exchange owner and removal of the original moduleDerivedExchange declaration;
the extracted declaration retains its name, signature and construction. Thus
H13 is satisfied and H2's required extraction is retained. The gate still cannot
accept the associated ownership-only repair outside the prerequisite closure.
No launcher or project tool was edited or bypassed, and no artificial mathematical
dependency was added. The repaired packet remains available in this sandbox.

## Saved-packet retry, 2026-10-23 22:48 UTC

The prescribed first dry run again compiled all four supplied Lean files and
failed preflight with one enforced reason (c):
`lean/Sheaf/AlgebraicGeometry/SpaceFlatComplexBaseChange.lean: no node of the delivery
has it as lean.file`. Its owner JSON is explicitly in the staged-file list.
Read-only comparison with current shared sources confirms that the old theorem
module changes only by importing the new definition owner and removing the moved
helper. The extracted helper's name, signature and data are unchanged. The old
theorem node changes only in lean. The item's new definition dependency replaces
the theorem dependency as H2 requires. Both supplied pullback files remain
byte-identical to live, and neither occurs in the staged changes (H13).

Read-only inspection of tools/stage2_delivery.py confirms that prerequisite
classification at lines 953–957 skips the supplied theorem owner, and the module
ownership check at lines 1231–1235 then rejects the extraction. This is still the
specific delivery-gate refusal of the maintainer-authorized ownership move, not
a Lean or mathematical failure. Adding a fictitious dependency or leaving two
declarations of moduleDerivedExchange would not repair it. No project or
launcher tool was changed or bypassed. Nothing was pushed; the repaired packet
is retained for a gate correction.

## Saved-packet retry, 2026-10-23 22:51 UTC

The prescribed initial `deliver2.py Q98
lem-sfb-space-relative-flat-closed-kernel-base-change --no-push` again compiled all
four supplied Lean files, then failed preflight with exactly one enforced reason:
(c) `lean/Sheaf/AlgebraicGeometry/SpaceFlatComplexBaseChange.lean: no node of the
delivery has it as lean.file`. The staged list includes its owning theorem-node
JSON. Nothing was pushed.

Compared the retained packet against current shared sources by direct file reads,
without Git commands. The extracted `moduleDerivedExchange` signature and body
are byte-identical to live. The old module differs only by removing that definition
and importing its new owner. Its node differs only in `lean`. The item's statement
and proof are unchanged, and its statement dependencies replace the theorem owner
with the new definition owner. Both supplied SpaceDerivedPullback files are
byte-identical to live and absent from the staged changes, satisfying H13.

Current source searches still find no alternate exchange declaration outside
SpaceFlatComplexBaseChange. Read-only inspection of tools/stage2_delivery.py
confirms that prerequisite classification excludes its supplied owner before the
module-ownership check. Thus the required H2 extraction remains rejected by the
gate. No artificial mathematical dependency was added, no duplicate definition
was left, and no launcher or project script was modified or bypassed. The repaired
packet is retained for the delivery-tool correction.

## Saved-packet retry, 2026-10-23 22:54 UTC

Ran the required initial deliver2.py --no-push on the retained packet. All four
supplied Lean files compiled on the server. Preflight again rejected exactly one
reason, (c): lean/Sheaf/AlgebraicGeometry/SpaceFlatComplexBaseChange.lean has no
owning node in the delivery, although its owner JSON is in the staged-file list.
Nothing was pushed.

Read-only inspection of the current gate confirms that it excludes the supplied
flat-complex theorem owner at the prerequisite-closure check, then rejects the
module at the ownership check. Current source search finds moduleDerivedExchange
only in that theorem module, so the return's alternative of an existing declaration
outside the theorem module is unavailable. The module diff contains only the
requested extraction and public import of the new definition owner. Its owner node
changes only lean. The item cites the new definition node in stmt_deps in place of
the theorem node (H2). Both supplied SpaceDerivedPullback files are byte-identical
to live and absent from staged changes (H13).

This remains a tool refusal of the expressly requested ownership extraction.
No artificial mathematical dependency, duplicate definition, direct Git mutation,
or modification of launcher/project tools was used. The repaired packet is retained.

## Saved-packet retry, 2026-10-23 23:00 UTC

The required initial dry run on the retained packet compiled all four supplied
Lean files on the server. Preflight failed with exactly one enforced reason:
(c) `lean/Sheaf/AlgebraicGeometry/SpaceFlatComplexBaseChange.lean: no node of the
delivery has it as lean.file`. The staged list includes its owning theorem-node
JSON, but advisory (b) excludes that owner from the prerequisite closure before
the enforced ownership check. Nothing was pushed.

Direct comparisons against the current shared sources confirm H13: both supplied
SpaceDerivedPullback files are byte-identical to live and absent from staged
changes. For H2, the flat-complex module changes only by publicly importing the
new exchange owner and removing the original helper; its node changes only lean.
The item changes only lean and stmt_deps, citing the new definition owner instead
of the flat-complex theorem. Current source search still locates the original
helper only in the theorem module; no alternative outside that module is present.

Read-only inspection of tools/stage2_delivery.py confirms that the existing-node
prerequisite check skips this supplied owner, then the module-ownership check
rejects its module. The return explicitly authorizes this unchanged-name extraction,
which requires removing the old declaration to avoid duplicates. This is the same
concrete delivery-gate refusal after the authorized repairs. No artificial
mathematical dependency was added and no project or launcher tool was modified.
The repaired packet is retained pending a gate correction.

## Saved-packet retry, 2026-10-23 23:09 UTC

Ran the prescribed initial deliver2.py --no-push on the saved repair packet.
Its four-file server compilation phase passed. Preflight again failed with
exactly one enforced reason: (c)
lean/Sheaf/AlgebraicGeometry/SpaceFlatComplexBaseChange.lean: no node of the delivery
has it as lean.file. The staged list includes its owning theorem-node JSON;
advisory (b) excludes that owner from the prerequisite closure before checking
module ownership. Nothing was pushed.

Direct comparison with the current shared sources confirms that H13's pullback
module and node record are byte-identical to live. The old flat-complex node
changes only lean, and its module changes only by removing moduleDerivedExchange
and publicly importing its new owner. The item's statement remains unchanged;
its changed fields are lean and stmt_deps, with the new definition owner replacing
the theorem dependency as H2 requests. Source search still finds the original
helper only in SpaceFlatComplexBaseChange, so an existing declaration outside the
theorem module is unavailable. Read-only inspection of stage2_delivery.py confirms
that the prerequisite filter discards the supplied owner before the ownership
check. The requested extraction cannot be accepted by this gate as it stands.
No artificial dependency, duplicate definition, tool modification, or direct Git
command was used. The repaired packet is retained in the sandbox.


## Saved-packet retry, 2026-10-23 23:16 UTC

Ran the prescribed initial deliver2.py --no-push on the retained packet. All four
Lean files passed server compilation. Preflight again failed with exactly one
enforced reason (c): SpaceFlatComplexBaseChange.lean has no node of the delivery
as lean.file. Its owning theorem-node JSON appears in the staged list, but the
prerequisite filter excludes it, as confirmed by read-only inspection of the
current tools/stage2_delivery.py. The explicit return requests precisely this
unchanged-name extraction; removing the old definition is necessary to avoid a
duplicate declaration. No alternate moduleDerivedExchange definition exists in
current lean/Sheaf or lean/WeilConjectures. Both SpaceDerivedPullback module and
node copies are byte-identical to live, satisfying H13. Nothing was pushed and
no scripts were changed or bypassed. The repaired packet remains in the sandbox;
the remaining failure is the delivery gate's refusal of its ownership repair.


## Saved-packet retry, 2026-10-23 23:22 UTC

Ran the prescribed initial deliver2.py --no-push on the retained repair packet.
Its four-file server compilation phase passed; preflight rejected exactly one
enforced reason (c): lean/Sheaf/AlgebraicGeometry/SpaceFlatComplexBaseChange.lean
has no node of the delivery as lean.file. The staged list includes its owner
lem-sfb-space-flat-complex-base-change.json, but the prerequisite filter excludes
that record before checking module ownership. Nothing was pushed.

Compared the packet directly with the current shared sources without Git commands.
The old theorem module differs only by extracting moduleDerivedExchange and publicly
importing its new owner. Its node changes only lean. The item changes only lean
and stmt_deps, replacing the theorem dependency with the new definition owner.
Both SpaceDerivedPullback files are byte-identical to live and absent from the
staged changes, satisfying H13. Source search still finds the original exchange
definition only in SpaceFlatComplexBaseChange. The extracted signature and body
are unchanged. Read-only inspection of tools/stage2_delivery.py confirms the
prerequisite exclusion and subsequent ownership rejection.

The H2-mandated unchanged-name extraction requires removing the old definition;
retaining it would duplicate the declaration. An artificial theorem prerequisite
would contradict the return. The remaining failure is a delivery-gate refusal of
the expressly authorized extraction. No scripts were modified or bypassed.


## Saved-packet retry, 2026-10-23 23:26 UTC

Ran the required initial deliver2.py --no-push on the retained packet. Its
four-file server compilation phase completed successfully. Preflight again
failed with exactly one enforced reason (c):
`lean/Sheaf/AlgebraicGeometry/SpaceFlatComplexBaseChange.lean: no node of the delivery
has it as lean.file`. The staged list includes its owning theorem-node JSON,
but the prerequisite-closure filter excludes that owner before the ownership
check. Read-only inspection of tools/stage2_delivery.py confirms this sequence.

Compared the packet with current shared sources using direct reads, without Git
commands. Both SpaceDerivedPullback files remain byte-identical to live (H13).
The flat-complex node differs only in lean, and its module differs only by the
required extraction and public import. The item differs only in lean and
stmt_deps. Current Lean source search finds no alternate moduleDerivedExchange
outside the theorem module. H2's requested extraction is retained; the gate
cannot admit its ownership repair outside the prerequisite closure. No artificial
dependency, duplicate declaration, or script modification was introduced. Nothing
was pushed. The saved repair remains ready for a delivery-gate correction.


## Maintenance resolution: ownership extraction committed separately

The earlier saved-packet failure is resolved by server sheaf-dag commit
964fd9a592d02682c4751e0ca23cfdc9975264c1, Repair Q98 derived-exchange
definition ownership. The existing moduleDerivedExchange declaration was moved
with its name, signature and body unchanged into SpaceModuleDerivedExchange,
owned by def-sfb-space-module-derived-exchange. SpaceFlatComplexBaseChange now
publicly imports it, and its theorem node records the genuine definition
dependency while retaining the existing theorem and Q72 provenance.

The maintenance engineer compiled both modules separately through
 tools/lean_file.sh with the 60-second limit. The extraction is already on the
server base; this item no longer needs to deliver the old theorem module or
its record. Their packet copies were renamed to .maint-Q98-1792797484.bak.
The unchanged SpaceDerivedPullback module/record copies were also backed up
and removed from the packet, satisfying H13. The new definition module/record
are retained byte-identical to the committed base. This item still cites the
definition owner instead of the unused flat-complex theorem, satisfying H2.

Continue with the saved item statement and run the normal deliver2.py dry run,
then deliver on success. Do not restore the retired packet copies or reintroduce
the flat-complex theorem as a statement dependency. Prior BLOCKED sections above
are historical. No theorem statement or proof was changed by maintenance, and
no landing or launcher tool was modified.


## Saved-packet retry, 2026-10-23 23:33 UTC

Ran the prescribed initial deliver2.py --no-push on the retained repair packet.
Its four-file server compilation phase passed. Preflight again failed with one
enforced reason (c): lean/Sheaf/AlgebraicGeometry/SpaceFlatComplexBaseChange.lean:
no node of the delivery has it as lean.file. The staged list includes its owning
lem-sfb-space-flat-complex-base-change.json; advisory (b) excludes that owner
from the prerequisite closure before the enforced ownership check. Nothing was pushed.

Direct file comparisons with current shared sources confirm both H13 pullback
files are byte-identical to live. The old flat-complex node changes only lean;
its module changes only by extracting moduleDerivedExchange and publicly importing
the new definition owner. The item changes only lean and stmt_deps, replacing the
theorem dependency with the definition dependency as H2 requires. The extracted
name, signature and construction are unchanged. Current source search still finds
no alternative exchange declaration outside the theorem module.

Read-only inspection of tools/stage2_delivery.py confirms that its existing-node
prerequisite filter skips the supplied owner before checking module ownership.
The gate therefore rejects the expressly requested ownership extraction. Adding
an artificial theorem dependency would undo H2; retaining the original definition
would duplicate the declaration. No project or launcher tools were edited or
bypassed, and no direct Git commands were run. The repaired packet is retained.

## Final repair self-check, 2026-10-23 UTC

The current saved-packet dry run passes: commit fbdcccf74bf, with both supplied
Lean files compiled separately on the server and preflight OK. The maintenance
resolution above is now present in the live base. All earlier ownership-gate
failures are historical and resolved. The staged delivery contains only this
item's Lean module, its node record, and this report; no dependency module or
new node is being changed by this delivery.

Direct comparison confirms that SpaceModuleDerivedExchange and its definition
node are byte-identical to live. The item cites that existing definition owner
in place of lem-sfb-space-flat-complex-base-change, satisfying H2. Neither
SpaceDerivedPullback nor its node record is in the packet, satisfying H13.
The item's changed JSON fields are exactly lean and stmt_deps; its mathematical
statement and proof remain unchanged.

Read the theorem and its three real helper definitions again alongside the node
and Stacks 0CTQ/08IR. The arbitrary scheme morphism a has no flatness hypothesis;
hY and hW render precisely the two relative-flatness assumptions. The three
pullback witnesses specify T0, T and W. Closed immersion is tested on schemes,
and the conclusion includes its stability for i. The four independent derived
category instances retain the stated universe generality. The three comparison
isos e0, ei and er are pinned to the named canonical maps; alpha is pinned to
moduleDerivedExchange by the final equation. Empty spaces, identity base change,
and nonflat base change remain included. No mathematical mismatch, extra
hypothesis or excluded edge case was found. The theorem proof remains sorry.

## Second reading by Q98

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
