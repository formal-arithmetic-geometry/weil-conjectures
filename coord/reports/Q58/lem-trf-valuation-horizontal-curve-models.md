## Worker report

This repairs the returned immutable head f97fa2fd39ab. The saved packet was
inspected first and its required initial dry run passed as e1d0b77244. The
mathematical self-check still reproduced the H3/H4 defects in the return, so
this is a substantive statement repair, not an unchanged re-push.

The node's prose, statement dependencies and proof are unchanged from current
main; only its `lean` record changes. No target or blueprint unit is changed.
The single module is `Sheaf.TraceFormula.ValuationHorizontalCurveModels`.
Its only postponed theorem is `AlgebraicGeometry.horizontal_curve_models`.
All helper definitions have real data and source/blueprint docstrings; all are
listed in `lean.declarations`. There are no extra nodes or dependency modules.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* The separably closed field, valuation subring and fraction-field conditions
  are `HorizontalValuationBase.K`, `fieldK`, `sepClosedK`, `V`, `commRingV`,
  `isDomainV`, `valuationV`, `algebraVK`, `fractionVK`. The algebra map of a
  domain into its fraction field is injective, so this is a valuation subring
  up to its canonical image, without a different field-extension assumption.
  The finite chain is `finitePrime` and `primeChain`.
* `B.T` is `Spec (.of B.V)`. `B.genericMap` is exactly
  `Spec.map (CommRingCat.ofHom (algebraMap B.V B.K))`; the specified generic
  fibre is therefore over `Spec K`. It is no longer an unconstrained chosen
  generic point with no connection to the given field.
* `P : MultipointedCurve B.T` is the existing multipointed-curve definition:
  flat, locally finitely presented, quasi-compact and quasi-separated curve
  and marking maps, pure fibre dimensions one and zero, and a compatible
  closed marking immersion. There is no separatedness or properness
  hypothesis on the curve and no nonemptiness hypothesis on the marking.
* Smooth generic curve and etale generic marking are `hSmooth` and `hEtale`,
  applied to the second projections of the actual pullbacks along
  `B.genericMap`.
* Reducedness of X and finiteness of its irreducible components are the
  conclusions `∃ hX : IsReduced P.X, Finite (irreducibleComponents P.X) ∧ ...`.
  They are not fields of an input datum. Binding the proof `hX` permits the
  existing birational-quasi-modification predicate to use its reduced-target
  instance explicitly.
* A reduced modification is quantified as `q`, `IsReduced Y` and the existing
  `SchemeModification q`. Its structure map over T is `q ≫ P.x`, so no
  compatibility assumption is lost. `RelativeCurve (q ≫ P.x)` concludes
  flatness, local finite presentation, quasi-compactness, quasi-separatedness,
  and pure dimension one of every fibre. It does not conclude integrality.
* `horizontalGenericCurveMap` is the map of the slice pullback functor applied
  to `Over.homMk q rfl`. `IsIso` of this actual map is the generic-isomorphism
  conclusion; no arbitrary isomorphism, or equation only after forgetting the
  generic-base projection, replaces it.
* `horizontalGenericMarkingι` is the pullback of the existing
  `P.markingBaseChange B.genericMap` along that canonical generic curve map.
  Thus it is the transported generic marking in the modification case, and
  precisely the intersection with the generic open in the general case.
* `FlatClosure.closed` supplies the marking closed immersion. Its
  `closureIdeal` is `e.ker = (j ≫ pullback.fst y η).ker`, using Mathlib's
  quasi-coherent image ideal. On affine charts this is exactly the kernel
  of restriction to the quotient by the generic marking ideal. The generic
  inclusion here is quasi-compact: the finite-height generic point is a
  quasi-compact open, and the generic marking immersion is closed.
* `FlatClosure.prescribedGenericFibre` says
  `e.ker.comap (pullback.fst y η) = j.ker`, equality of the two embedded closed
  subschemes in the actual ambient generic fibre. `flat`,
  `finitelyPresented`, `quasiCompact`, `quasiSeparated` and `pureZero` give
  the required flat finitely presented pure relative dimension zero marking.
* The modification clause explicitly quantifies over every closed immersion
  `f : F ⟶ Y` flat over T with that same embedded generic ideal. Its conclusion
  `∃ h : F ≅ E, h.hom ≫ e = f` is uniqueness as a closed subscheme of Y.
  Competitors have no finite-presentation or other extra hypothesis.
* `horizontalClosurePair` constructs the actual multipointed pair `(Y,E)`
  from the supplied curve and closure property proofs, with the given maps
  as its data. `horizontalClosurePairMap` constructs the existing
  `MultipointedCurve.Hom`, using `r`, `hr` and `hi` for the marking map and
  both compatibility equations. Its existing `.IsEtaModification` predicate
  supplies properness, isomorphisms over schematically dense opens, and
  invertibility of both canonical generic base changes.
* The general clause is an independent universal quantifier, outside the
  existence of a proper modification or its closure. It assumes integral Y,
  `RelativeCurve (q ≫ P.x)`, the existing
  `IsBirationalQuasiModification q`, and `IsOpenImmersion` of the actual
  generic map. There is no generic-isomorphism assumption here: a proper
  generic open is allowed. The existing birational predicate uses the image
  component of the actual generic point and `q.residueFieldMap`, not an
  unrelated component or field isomorphism. The conclusion supplies the
  closure of its actual generic marking intersection, with the stated flat,
  finitely presented, pure zero-dimensional properties.
* `ClosureRestrictionStable` occurs in both cases. For every open U with
  `QuasiCompact U.ι`, it equates the restricted closure ideal with
  `(pullback.snd m U.ι).ker`, the closure ideal of the restricted generic
  marking. It also supplies flatness, all three finite-presentation
  conditions, and pure dimension zero for the restricted marking over T.
  Thus it states commutation of the constructions, not just preservation of
  flatness and local finite presentation.
* Empty D and empty generic intersections are allowed. In those cases the
  image ideal is the top ideal, giving the empty closed subscheme; there is
  no `Nonempty` requirement on any marking or closure.

Existing dependency interfaces reused (full signatures and docstrings read):
`Sheaf.TraceFormula.MultipointedCurve`: `MultipointedCurve`;
`Sheaf.AlgebraicGeometry.MultipointedCurveModification`:
`MultipointedCurve.Hom`, `markingBaseChange`, `Hom.IsEtaModification`;
`Sheaf.TraceFormula.Modification`: `SchemeModification`;
`Sheaf.TraceFormula.SchematicallyDenseOpen`: `SchematicallyDenseOpen`,
through `SchemeModification`;
`Sheaf.AlgebraicGeometry.BirationalQuasiModification`:
`IsBirationalQuasiModification`;
`Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
The item itself already states the notions for these specialized helpers;
no independent notion is being introduced. Mathlib dependencies include
`Spec`, `IsSepClosed`, `ValuationRing`, `IsFractionRing`, `IsReduced`,
`IsIntegral`, `irreducibleComponents`, `Smooth`, `Etale`, `Flat`,
`LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated`,
`IsClosedImmersion`, `IsOpenImmersion`, `Scheme.Hom.ker`,
`Scheme.IdealSheafData.comap`, `pullback`, and `Over.pullback`.
The available proof-dependency modules are imported without `public`.

Edge cases checked against the signatures:

* Over a separably closed field K, the zero and one sections of A^1_K have
  abstractly isomorphic generic fibres Spec K but are different closed
  subschemes. The old uniqueness premise was false; the new ideal equality
  distinguishes them.
* A proper generic open inclusion is not an isomorphism. The general clause
  uses `IsOpenImmersion`; the erroneous extra `IsIso` premise was removed.
* A disconnected smooth generic curve has several components. Reducedness
  and finite components are conclusions and Y need not be integral in the
  modification clause. Only the general birational clause assumes integral Y.
* The zero section on A^1_V minus the closed point at its origin can have
  closure Spec K, so no finite-module or finite-morphism condition is used.
* Field bases (height zero), rank-one bases, empty markings, empty generic
  marking intersections, empty opens, and nonproper/nonseparated relative
  curves are admitted. Finite presentation always includes qc and qs.

Searches: the saved packet records LeanSearch and LeanFinder for reduced
modifications of flat finitely presented valuation curves and schematic
closures (eight generic algebraic-geometry hits, no matching theorem), Loogle
`ValuationRing, Module.Flat, Scheme` (zero hits), and Mathlib grep
`schematic closure|valuation.*modification|torsion.free.*flat` (zero hits).
For this repair, `msearch.py ... leanfinder` with
`Schematic closure of a generic marking in a relative curve over a finite height valuation ring`
returned eight valuative-criterion hits, no matching theorem.
`msearch.py ... loogle AlgebraicGeometry.Scheme.Hom.ker` returned the existing
kernel and image-ideal API, which is now reused. `msearch.py ... grep
schematicClosure|IsBirationalQuasiModification|SchemeModification AlgebraicGeometry`
returned zero Mathlib matches. `rg` of Mathlib, upstream WeilConjectures,
project `lean/Sheaf`, and `dag/nodes` found the existing project definitions
listed above; those are imported, not duplicated. A search for
`RelativeCurve|IsRelativeCurve|relativeCurve|CurveOver` found no existing
relative-curve predicate. Source `IdealSheaf/Basic.lean` and
`IdealSheaf/Functorial.lean` confirm the kernel and ideal pullback interfaces.
The source PDF was reread online at
https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf:
§1.2, §4 conventions, Remark 4.1 (pp.24–25), opening §4.2 (p.26), and
Lemma 3.5.1 (p.20). No mathematical dispute or node-statement correction remains.

## Repair of returned H3 and H4

H3, false closure uniqueness: replaced abstract generic-fibre isomorphism
with equality of embedded ideals. The zero/one-section counterexample above
is excluded for the correct reason. Competitors still need only closedness,
flatness and the prescribed generic subscheme.

H3, missing closure and restriction conclusions: both existential closures
now have the actual scheme-theoretic-image ideal of the actual generic
marking intersection; both include equality of the restricted ideal with
the restricted construction's closure ideal. The general conclusion no
longer permits an arbitrary flat zero-dimensional scheme or an empty
substitute for a nonempty generic marking.

H3, assumed reducedness and finiteness: removed the input `HorizontalModelData`
and its `reducedX`/`finiteComponents` fields, and made both propositions
conclusions of the theorem, before either universal modification clause.

H3, generic-fibre interfaces: the generic morphism is now Spec K → Spec V;
all fibre maps are canonical slice base changes. The general clause requires
an open immersion, with no erroneous isomorphism premise. The unrelated
component and arbitrary stalk-isomorphism data are removed.

H3, finite presentation: added quasi-compactness and quasi-separatedness to
the relative curve, closure, and restricted-closure conditions. The existing
multipointed-curve structure already includes both.

H4: removed private replacements `IsSchematicallyDenseOpen`, `IsDenseOpenIso`,
`ReducedModification`, `BirationalQuasiModification`, and `EtaModificationPair`.
The canonical existing definitions named above now supply all these interfaces.

## Second reading by Q58

I reopened the repaired module and unchanged node, and checked the explicit
correspondence above against Temkin's §1.2 and §4. All input assumptions are
now the valuation base, multipointed curve, and generic smoothness/etaleness.
Reducedness and finite components are outputs. The modification quantifier
uses the existing definition, its generic map is the induced one, and the
relative-curve output includes global finite presentation. The closure
ideal, its embedded generic fibre, the flat-competitor uniqueness quantifier,
the compatible eta-modification pair, and the equality after every qc open
restriction have distinct explicit clauses. The second quantifier admits a
proper generic open and applies the same closure construction to the marking
intersection; it has its own restriction clause. I checked the zero/one-section
counterexample and the empty marking/intersection cases again. Helpers only
package the node's constructions, all universes and variables are explicit,
and the only theorem proof is `sorry`. This second reading found and removed
an unnecessary uniqueness assertion from the general clause; uniqueness is
asserted exactly in the modification clause where the node states it.

## Validation

`scompile.py Q58 lem-trf-valuation-horizontal-curve-models
lean/Sheaf/TraceFormula/ValuationHorizontalCurveModels.lean` compiled the final
module in both sandbox and library positions with no errors or warnings.
The signature is synchronized verbatim, all lines have at most 100 characters,
and the only `sorry` is the intended theorem proof. The final source was also
compared with current main's node: every field other than `lean` is unchanged.
