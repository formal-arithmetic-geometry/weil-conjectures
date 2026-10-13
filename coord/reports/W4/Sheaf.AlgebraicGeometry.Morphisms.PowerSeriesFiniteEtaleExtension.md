## What changed

Repair of the import-prune return: removed the private duplicate declarations
`AlgebraicGeometry.Scheme.depth_le_of_ringEquiv` and
`AlgebraicGeometry.Scheme.maximal_smul_top_ne_top`. The matching library helpers
are private, so importing their modules would not make them callable. Instead,
the base-stalk depth inequality now follows directly from the already imported
public `IsLocalRing.depth_eq_add_of_flat_local`, applied to the ring equivalence.
`RingHom.Flat.of_bijective` supplies flatness and `IsLocalHom.of_surjective`
supplies locality; nonnegativity of the fibre depth gives the inequality.
This uses an existing theorem instead of re-proving either duplicate fact.
No helper, signature, visibility, import, new node, or hole is added by this repair.
The parent node's first proof step records this route.


Replaced the sole sorry in `PowerSeriesFiniteEtaleExtension` by a compiling proof
with the unchanged signature and docstring. It proves base boundary depth using the
flat local depth formula, obtains a finite extension from
`exists_finite_extension_of_depth_two`, and retains its depth and restriction data.
For proper V it identifies this finite scheme as a base change from B, descends
etaleness from the open containing the specified prime, then applies stability
under base change. The V = top case is proved directly by Zariski locality.

Added three modules, one theorem each: `MvPowerSeriesFlat`,
`FiniteEtaleDescentNearClosedPoint`, and `PowerSeriesDepthTwoBaseChange`.
The first two are fully proved. All new imports of the item's module are proof-only.
The finite-base identification is the single new hole and is strictly smaller:
it neither constructs the extension nor asserts etaleness, and it does not assume
hgeneric. The proof combines it with the already constructed finite depth-two
extension and the fully proved descent lemma.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_power_series_open`
(node `lem-sbc-power-series-finite-etale-extension`), one of one original holes.
This is a decomposition, not a sorry-free target proof: one lower hole is added.

Fully proved new declarations: `MvPowerSeries.constants_flat`
(node `lem-sbc-mv-power-series-constants-flat`) and
`AlgebraicGeometry.Scheme.etale_of_flat_base_change_near_closed_point`
(node `lem-sbc-finite-etale-descent-near-closed-point`).

The only sorry in delivered files is
`AlgebraicGeometry.Scheme.exists_finite_base_of_power_series_depth_two`
(node `lem-sbc-power-series-depth-two-base-change`). It is exactly `by sorry`
in its own new module. No definition is added. Existing imported theorem holes
remain work for their own items. Net holes closed minus added here is zero.

## No longer needed

The duplicate private depth-transport and maximal-ideal helpers are no longer
needed and have been deleted. Their regular-sequence argument is replaced by
the existing flat local depth formula. No imports are added or removed by the repair.


No existing import, proof dependency, node, or module is pruned. Both original
proof dependencies are used. No cyclic import of `PowerSeriesTestFiniteExtensionFlat`,
`SmoothLocalDepthTwoFiniteFlat`, or `SmoothLocalDepthTwoFinitePurity` is introduced.
The constants-map proof uses the polynomial completion equivalence and flatness
of Noetherian completion directly, so it needs no new adic-completion theory.
The final descent proof needs no etale-locus, ramification-purity, trace,
discriminant, or finite-flatness intermediate modules.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated two private helpers already stated in the library.
Both duplicates are now removed; the repair uses a public theorem already in the
proof imports. The earlier second-reading section below describes the original
delivery and predates this repair; the next reader should verify this changed
base-stalk calculation and the removed helpers.


The original node's steps 2 and 3 had empty uses despite being non-elementary.
Step 2 is now recorded as the finite-base identification, with a source and full
proof in words. Step 3 is implemented in Lean via Mathlib's flat generalizing-map
and fpqc etale descent interfaces. No interface or target statement changed.

The omitted detail in 0EYA can be handled without localization: the map from V
to the local base is surjective because it is flat and V contains a point over
the closed point. The power-series spectrum is Noetherian, so V is quasi-compact;
fpqc descent proves etaleness over B. This gives the more general proved helper
without assuming g finite or B Noetherian. The unit route is unchanged.

Mathlib and both project roots were searched for power-series extension,
flatness, and etale descent. Logged LeanSearch calls returned Internal Server Error;
LeanFinder, Loogle and grep searches ran. The source tags 0EYA, 0EY9, 0EY6,
00MB and 02VN were read. New statements were checked on top/proper opens,
empty sources, zero variables for constants flatness, and arbitrary local bases
for descent. Proper V excludes the closed point of Spec(B[[X]]), so its
zero-section intersection is precisely the punctured spectrum. The finite-base
identification does not use the parent theorem, avoiding the existing circular
route through power-series extension flatness.

## New nodes

`lem-sbc-mv-power-series-constants-flat`: constants inclusion is flat; proved using
`MvPowerSeries.toAdicCompletionAlgEquiv`, polynomial freeness, and
`AdicCompletion.flat_of_isNoetherian`. New module `Sheaf.RingTheory.MvPowerSeriesFlat`.

`lem-sbc-finite-etale-descent-near-closed-point`: flat Noetherian base change which
is etale on an open over the local closed point implies the original map is etale.
Fully proved using lifted generalizations, quasi-compactness, restricted pullback
squares, and fpqc descent. New module
`Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleDescentNearClosedPoint`.

`lem-sbc-power-series-depth-two-base-change`: the finite extension is a base change
of a finite B-scheme, with no etaleness assertion and no hgeneric hypothesis.
This isolates the Psi identification of 0EYA, using 0EY9 and 0EY6; it is the sole
new sorry. New module `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesDepthTwoBaseChange`.
No change records or forced adaptations are needed.

## Earlier second reading (a previous round; superseded)

1. PASS: Compared the item's module with the repository using diff and the
   declaration parser. The existing public signature and docstring are byte for
   byte unchanged; the parser reports no statement changes. The other three
   delivered modules are new. No definition, target, or other module is changed.
2. PASS: Compiled all four files locally in import order without errors or
   warnings. Scratch copies with `#print axioms` show only propext,
   Classical.choice and Quot.sound for constants_flat and
   etale_of_flat_base_change_near_closed_point. The parent and the sole new hole
   additionally use sorryAx, as reported above. Checked all delivered sources:
   exactly one named theorem has `:= by sorry`; no forbidden declaration or
   hollow definition occurs. Witnesses are eliminated within theorem proofs;
   no definition chooses data from an unproved existence statement.
3. PASS: Read Stacks 0EYA, 0EY9 and 0EY6 independently. The remaining statement
   isolates the finite-base identification, not the original extension or its
   etaleness. Its proper-open hypothesis ensures the zero section meets V in
   the punctured spectrum. Full faithfulness is applied on the inverse image
   of that spectrum, then flat base change and change of opens identify the
   canonical extensions; source boundary depth identifies the supplied E.
   This argument does not require hgeneric. Checked the smallest permitted
   variable count n = 1, proper/top opens, and the empty cover. The proved
   flatness helper also covers n = 0 and the zero ring; the descent helper
   covers the empty source and arbitrary local coefficient rings. Independent
   LeanFinder search for descent of punctured formal power-series covers,
   Loogle search `MvPowerSeries, RingHom.Flat`, and local searches of both
   project roots and Mathlib found no replacement for the split statement.
   Its source, complete proof in words and node are present. Closing it requires
   formal power-series full faithfulness and canonical-extension compatibility,
   beyond a short second-reading repair.
4. PASS: Read the parent proof from its conclusion back through descent,
   finite extension and boundary depth. Both original dependencies remain
   used. The two new proved helpers use Mathlib directly, and all new parent
   imports are proof-only. No shorter existing theorem was found. No original
   node or import becomes unnecessary. Read sk-prop-input-spreading.json:
   this auxiliary node preserves its depth-two and power-series route and
   does not modify the unit or its realized fields.
5. PASS: Checked all four node statements against the Lean signatures
   verbatim, and checked that proof_deps equals the union of the steps' uses.
   The parent node records the actual reduction; the new nodes have sources,
   searches, creation data, blueprint ancestry and Lean records. The report
   correctly counts one hole closed and one hole added as a decomposition,
   with zero net hole reduction, rather than a sorry-free proof.

Second-reading changes: added this independent review section and recorded the
additional searches and axiom checks. No Lean or node repair was necessary.


## Second reading by W4

1. PASS. Diffed the delivered parent against the repository version: its existing
   signature and docstring are byte for byte unchanged. Changes are proof-only
   imports and the proof body. The three helper modules are new; no existing
   definition, target, visibility or other module is changed.
2. PASS. Compiled all four files locally in import order, without errors or
   warnings. Independently compiled scratch copies with #print axioms for all
   four declarations: constants_flat and
   etale_of_flat_base_change_near_closed_point use only propext, Classical.choice
   and Quot.sound. The parent and exists_finite_base_of_power_series_depth_two
   additionally use sorryAx. Exactly one named theorem has by sorry; no forbidden
   declaration or hollow definition is present. Existential witnesses occur only
   inside theorem proofs, with no definition selecting arbitrary data.
   Checked the repaired base-stalk calculation: localization at units gives the
   ring equivalence, bijectivity supplies flatness, surjectivity supplies locality,
   and the flat local depth formula supplies the required lower bound. Neither
   removed private duplicate helper remains.
3. PASS. Independently read Stacks 0EYA, 0EY9 and 0EY6. The remaining statement
   isolates the finite-base identification before descent, with no construction
   or etaleness conclusion from the parent, and no hgeneric assumption. On the
   inverse image of the punctured spectrum, full faithfulness identifies the
   two finite etale covers; flat base change and change of opens identify their
   canonical extensions. The supplied source-boundary depth identifies E with
   that extension. Properness of V excludes the local closed point and makes
   its zero-section intersection precisely the punctured spectrum. Checked n=1,
   empty covers and proper opens; the parent separately handles V=top. Flatness
   includes n=0 and the zero ring; the descent helper permits empty Y and top V,
   while hv forces V nonempty. Repeated LeanFinder search with
   "finite etale cover formal punctured spectrum power series descends to
   coefficient ring", Loogle "MvPowerSeries, RingHom.Flat", and grep
   "fullFaithful.*power|power.*fullFaithful|depth_two.*base|finite_base_of_power".
   None gives the remaining identification. Local searches also found no
   replacement, and the circular power-series flatness theorem is not used.
   The split has its source, complete proof in words and matching node. Closing
   it needs formal-cover comparison and canonical-extension compatibility,
   rather than a short second-reading repair.
4. PASS. Followed the proof from its conclusion back through etale descent, the
   supplied finite extension and boundary depth. Both original dependencies
   (finite extension and flat local depth formula) remain used. New parent
   imports are proof-only; public imports supply signature notions. Checked
   sk-prop-input-spreading and its realized fields: no unit step or route is
   bypassed or modified. No old dependency or module becomes unnecessary.
5. PASS. Checked the four node Lean records against their declarations and the
   union of each proof's uses against proof_deps. The parent records the repaired
   ring-equivalence depth calculation and actual reduction. New nodes contain
   sources, search records, creation metadata, blueprint ancestry and Lean
   records. The remaining hole is strictly smaller and true, so the report
   correctly counts one original hole closed and one lower hole added as a
   decomposition with net zero, rather than a sorry-free proof.

Second-reading changes: appended this review and independent search/axiom evidence.
No further Lean or node repair was necessary.
