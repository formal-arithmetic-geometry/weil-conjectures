## Worker report

Item: `lem-sfb-scalar-refinement-closure-square`, group NG, stage 2.

The main module is `Sheaf.SixFunctors.ScalarRefinementClosureSquare`. It states the two coefficient squares with their actual morphisms, and invertibility of the adjunction-transpose refinement maps. The four helper definitions contain real constructions only: the published open scalar conjugate, the composite C_c, the normalized proper-composition isomorphism, and the direct image of the published refinement map. The only postponed proof in this module is `AlgebraicGeometry.ProEtale.CondensedRing.scalarRefinementClosureSquare`; its docstring contains all five proof steps of the DAG, including the two normalization citations added at stage-1 review.

Hypothesis-by-hypothesis correspondence:

- Prime ell: `(ell : ℕ) [Fact ell.Prime]`.
- A field k in positive characteristic p distinct from ell: `(k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]`. A field's positive characteristic is prime, so this is exactly the standing setting, not an extra characteristic restriction.
- All schemes separated and finite type over k: `X Y : Over (Spec (.of k))`, each with `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` on its structural map. A compactification's proper map to Y supplies the same properties for its middle scheme by composition; its k-structure is that composite. The refinement triangle makes its ambient map a k-map. Thus no independent field structure is added or omitted for Z or Z'.
- Every morphism is a k-morphism: `f : X ⟶ Y` is a morphism of the over category; the compactification and refinement commuting triangles give the k-linearity of the remaining arrows.
- Coefficients and their ordinary derived extension: `Λ Λ' : ScalarSixRing.{u}`, `a : Λ ⟶ Λ'`, and `_ha : ListedCoefficientMap ell a`. This is the exact inductive list imported from the recorded direct-image interface: finite ell-primary commutative rings, integral/field finite extensions in the fixed algebraic closure, integral-to-field localization, field-to-algebraic-closure, continuous integral-to-finite maps, and finite composites. The algebraic closure is the finite-subextension condensed ring in that interface. No flatness is required. `scalarSixChange` is the existing total left-derived scalar extension along the pulled-back `coefficientMap`.
- The two compactifications: `c d : Compactification.BoundaryCompactification f.left`, with c the node's c and d its c'. Their `obj.obj.i` and `obj.obj.g` are the quasi-compact opens j,j' and proper maps p,p'. Both factor f. BoundaryCompactification is the recorded notion, not a private copy.
- Proper h with hj'=j, p'=ph, and the inverse-image condition: `r : d ⟶ c`. The ambient h is `r.hom.hom.hom`; `i_hom`, `hom_g`, and `r.property` are the two triangles and equality of inverse-image opens. Properness is the published refinement instance, derived from the proper maps to Y.
- Case (a): the first disjunct of `_hcases` is `IsSchemeTheoreticallyDominant` on both open immersions. This is schematic density, not merely topological density.
- Case (b): the second disjunct supplies `e : d.obj.obj.Z ≅ c.obj.obj.i.image` with `e.hom ≫ c.obj.obj.i.imageι = r.hom.hom.hom` and `d.obj.obj.i ≫ e.hom = c.obj.obj.i.toImage`. The image here is the schematic image, not the reduced closure. This is exactly being the schematic closure with its closed inclusion and induced open, allowing all isomorphic presentations. The equations force h and j', rather than adding an unrelated isomorphism. No density of c is imposed in this case.
- K in Dctf: K is in the ordinary unbounded internal-module derived category, and `_hK` is the conjunction of `constantModelBoundedConstructible` and `DerivedCategory.finiteTorAmplitude`, exactly the two recorded predicates. The category uses site universe u and coefficient abelian groups in u+1, with no equality of those universes imposed.

Clause-by-clause correspondence:

- `localizingRefinementMap Λ.X r K` is the existing open-adjunction transpose of `refinementTheta.inv`, not an arbitrary map with the same endpoints. It is defined for all boundary-preserving refinements, so it serves both cases without duplicating e_h. The first two conjuncts say that this map is invertible over Λ at K and over Λ' at T_X K. The second is the same stated isomorphism assertion applied after the prescribed coefficient change; the DAG proof explicitly treats both.
- `scalarRefinementOpenIso a j` has body exactly `derivedOpenImmersionShriekIso a.hom.hom j` with the bundled coefficient parameters exposed. It is delta_j on the ambient unbounded categories. The helper adds no choice or assumption.
- `scalarDirectImageMate a h` is the recorded unit/pullback/counit comparison gamma_h, using `scalarDirectImagePullbackData.theta`; the latter is fixed by its normalization to the published scalar mate.
- The first equality, in Lean's left-to-right composition order, is `T_Z.map e ≫ gamma_h ≫ Rh'_*.map delta_j' = delta_j ≫ e'`. This is precisely the first displayed equation with the same source T_Z(j_!K) and target Rh'_*j'_!(T_XK), in the Λ'-module derived category.
- `scalarCompactificationComparison a c K` is definitionally `gamma_p` at j_!K followed by `Rp'_*.map delta_j`, the definition of C_c in the node. Its instance at d is C_c'.
- `scalarRefinementComposition Λ r` is the inverse of `RootCoordinateFace.lowerComp` for h,p, followed by transport along `r.hom.hom.hom_g`. Its source is Rh_* followed by Rp_* and its target is Rp'_*. Both are the actual total derived module direct images.
- `scalarRefinementPushforward Λ r K` is `Rp_*.map e_h,K` followed by that compositor; this is phi_h,K with the target identified as required in the node.
- The last equality is `C_c ≫ phi_h,T_XK = T_Y.map phi_h,K ≫ C_c'`, exactly the second displayed equation. Both sides have source T_Y(Rp_*j_!K) and target Rp'_*j'_!(T_XK), so no unmentioned cast or arbitrary composition identification is suppressed.

Recorded dependency declarations used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`: `ProEtale.coefficientMap` and `CondensedRing.derivedOpenImmersionShriekIso` (their full source signatures and conjugate construction were read).
- `Sheaf.SixFunctors.ScalarSixDirectImage`: `CondensedRing.scalarSixDirectImage`; its public `ScalarDirectImageMateCoherence` interface gives `scalarDirectImageMate` and the normalized pullback data. `ScalarSixDefinitions` gives `ScalarSixRing`, `scalarSixChange` and `scalarSixPull`; `ListedCoefficientMaps` gives the exact `ListedCoefficientMap` predicate. These are the declarations used by the recorded direct-image node, not new coefficient constructions.
- `Sheaf.SixFunctors.ScalarSixPullback`: `CondensedRing.scalarSixPullback`, the source of that normalized scalar/pullback data.
- `Sheaf.Paper.CompactificationRefinementLocalizing`: `CondensedRing.localizingRefinementMap`, `refinementTheta`, `refinementOpenRestriction`, and `localizingRefinement_coherence`. Their definitions and normalization were read.
- `Sheaf.Compactification.BoundaryRefinement`: `Compactification.BoundaryCompactification`, `boundaryRefinementProperty` and `DenseBoundaryCompactification`.
- `Sheaf.Paper.FiniteConstantRingedLocalModel` publicly retains `ProEtale.constantModelBoundedConstructible` and `ConstantModelConstructibleFiniteTor` from `CondensedConstantConstructibility`; these are the internal-module predicates appropriate to this statement. It does not replace them by the added ringed-site local-model predicate.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`: `CondensedRing.compactificationOverField` and the standing over-field scheme convention. No choice of compactification is used in the theorem: c and d are arbitrary given compactifications.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: `CondensedRing.moduleObjectDerivedPushforward` and `moduleObjectDerivedPullback`. `RootCoordinateFace.lower` is exactly the former, and `RootCoordinateFace.lowerComp` its adjunction-normalized composition isomorphism; these are the same operations used by the recorded scalar direct-image interface.
- `Sheaf.Compactification.NagataDensityNormalization`: the repaired `CondensedRing.nagata_density_normalization`, described below.

All available recorded proof-dependency modules are imported. `lem-sfb-proper-direct-image-coefficient-restriction` has no recorded Lean module, so no import can yet be given for it. Its role remains explicitly in the proof docstring; it is not replaced by an assumption. The dependency repair also imports its existing compactification/closure declarations and available proof modules. Its recorded proof dependency `Sheaf.Compactification.NagataDensityNormalizationPushforward` is absent both locally and via `scompile.py --source`, so that unavailable import is omitted; the repair's proper-composition formula states the conclusion directly.

Edge cases checked mathematically before writing:

- Identity coefficients: the scalar functor and comparisons normalize to identities; both equations become the same refinement map on either side.
- Identity refinement: e is the actual normalized identity (with the published identity identifications); proper-composition transport remains present.
- K=0 and the empty scheme: all constructions are still defined and both paths agree; no Nonempty assumption occurs.
- Empty dense compactifications and empty schematic closure are admitted, without choosing a point or stage.
- A nondense compactification with an extra disjoint closed component is admitted by the closure disjunct; the extension by zero is supported on the closure. No false assertion of density is used.
- Nonflat finite maps, for example Z/ell² to Z/ell, are included by ListedCoefficientMap; all scalar extensions are derived, so the statement does not accidentally require exact underived tensor.
- Schematic closure may retain nilpotents; the `image` scheme, rather than its underlying set or reduction, is used.
- No proper base-change assertion for all unbounded complexes is added. Only the original Dctf input and its scalar extension are asserted to give invertible refinement maps.

Searches (2026-10-24 UTC; launcher msearch interface, group NG and this item):

- leanfinder: `Derived coefficient extension commutes with proper compactification refinement and schematic closure maps`. Eight results, including immersion coborder identities and affine transition limit lemmas; none states either coefficient square.
- loogle: `CategoryTheory.mateEquiv`. Twelve generic mates/coherence results, including unit/counit and vertical/horizontal pasting. These supply categorical tools but do not state the geometric coefficient squares.
- grep of Mathlib/AlgebraicGeometry: `refinement.*coefficient|coefficient.*refinement|schematicClosure`. Zero hits.
- leansearch: `Change of scalars respects compactification refinements and schematic closures`. Eight results about ordinary scalar restrictions, compactness and base change of morphism properties; no match.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the item id and the proposed full-name stems (`scalarRefinementClosure`, `scalarCompactificationComparison`, `scalarRefinementPushforward`): no existing declaration of this statement. Broader scalar/refinement searches located different strict-coefficient compact-support results, whose inputs and comparisons are not this all-listed-coefficients ambient module statement. The canonical e and gamma declarations were found and reused as described above.
- For the dependency repair: the node's recorded file is absent from the read-only tree; `scompile.py --source Sheaf.Compactification.NagataDensityNormalization` reports `Module source unavailable`. The same check for the recorded pushforward proof module reports unavailable. The existing sheaf-normalization module is present, was read, and is reused.

No statement correction, new DAG node, or STATEMENT-DISPUTED flag is needed. The item node changes only in `lean`; the dependency node likewise changes only in `lean`, under section 1(B).

## Dependency modules

`sk-lem-nagata-density-normalization`: the recorded module had been deleted (its old lean.note says so), and its source is unavailable on the live server. The replacement `Sheaf.Compactification.NagataDensityNormalization` states the node's two canonical identifications, with one theorem proof postponed and no data definition. For arbitrary commutative condensed Λ and a Noetherian compactification, `eZ` is a natural isomorphism from j_! to j_Z,! followed by Ri_*. Its normalization is the actual open unit followed by restriction of eZ and the published identity-open derived restriction, equal to the j_Z unit. This is the identity normalization on K, without requiring an arbitrary map or new isomorphism as input. `eS` is then required to equal the proper direct image of eZ, reassociation, and the inverse normalized derived direct-image compositor. Thus it is precisely Rp_*j_! ≅ R(pi)_*j_Z,!. The theorem is ambient and unbounded, with no field, admissibility, finite Tor, or constructibility assumption. This repairs a missing recorded interface, and preserves every other field of that dependency node. Its docstring gives both source proof paragraphs and the canonical normalization argument.

## Second reading by NG

Dispatcher-authorized worker self-check; no additional agent was started. The independent delivery review belongs to the maintainer. I reopened the node's two equations and the complete Lean signature: composition direction matches Lean's `≫`; c,d,r have the correct orientation d→c; the coefficient changed e is over Λ'; both compactifications include quasi-compactness; the inverse-image condition is retained in the wide-subcategory morphism; and the closure case is schematic and admits a nondense original compactification. The definitions of C and phi use precisely gamma, delta, Rp_*e, the normalized compositor and the p'=ph triangle. The dependency theorem quantifies over all unbounded objects and pins eZ by its open restriction and eS by its direct-image formula. No mathematical mismatch was found. The first compilation was clean; explicit public imports of the dependency repair's two recorded statement-dependency modules were subsequently added for the final check.
