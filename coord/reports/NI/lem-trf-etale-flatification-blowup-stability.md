## Worker report

The delivery states `AlgebraicGeometry.Scheme.Modules.etaleFlatification_blowup_stability`
in `Sheaf.AlgebraicGeometry.EtaleFlatificationBlowupStability`. Its only theorem has
`by sorry`. Ten accompanying declarations construct the particular fibre products,
projection maps, final supported-section quotient, its quotient morphism, and a
Prop packaging the chart comparison clauses. They belong to this node's construction;
there is no additional independent notion, postponed helper theorem, new node,
dependency repair, or statement correction.

Source read: `literature/stacks-project/flat.tex`, Tag 0814,
`lemma-flatten-module-etale-localize`, statement and first proof paragraph
(lines 8903 onward). The node is the stability paragraph, rather than the whole
étale-descent lemma. In particular, it retains joint surjectivity as two conditional
conclusions instead of adding covering hypotheses. Also read the recorded
strict-transform, flat-pullback, composition-comparison and admissible-blowup
interfaces, and the current blueprint's `sec-trace-formula/sk-i-curve-zero`
unit and `lem-trf-local-term-locality` source files. The theorem's docstring follows
all eight steps of the accepted DAG proof.

Hypotheses, with one correspondence for each clause:

- Schemes and morphisms: `{X S : Scheme.{u}}`, `f : X ⟶ S`.
- S qcqs: `[CompactSpace S] [QuasiSeparatedSpace S]`.
- U quasi-compact open: `U : S.Opens`, `_hU : IsCompact (U : Set S)`.
- F quasi-coherent: `F : X.Modules`, `[hF : F.IsQuasicoherent]`.
- Finite family of diagrams: `(ι : Type v) [Finite ι]`, `T V : ι → Scheme.{u}`,
  maps `e`, `g`, `j`, and `h i : j i ≫ f = g i ≫ e i`.
  `T i` denotes the original S_i, and `V i` the original X_i. The independent index
  universe does not restrict the size of a finite family.
- S_i qcqs: the dependent `CompactSpace (T i)` and `QuasiSeparatedSpace (T i)` instances.
- e_i quasi-compact and étale: the dependent `QuasiCompact (e i)` and `Etale (e i)`
  instances. j_i étale: the dependent `Etale (j i)` instances.
- J_i finite-type quasi-coherent ideals: `J i : (T i).IdealSheafData` and dependent
  `(J i).toModules.IsFiniteType` instances. `IdealSheafData` is the existing
  quasi-coherent ideal representation. Module finite type means finite local generators.
- J_i unit on e_i inverse U: `_hJ i` is disjointness of that open and `J i.support`.
  The support of an ideal is its zero set, so this is exactly the unit restriction.
- The initial transform is relatively flat: `_hflat i` applies `IsFlatOver` to
  `cokernel (kernel.ι (moduleStrictTransformRestriction (g i) (J i)
  ((tensorPullback (j i)).obj F)))`, over `pullback.snd (g i) (J i).blowupMap`.
  This is literally the body of the existing strict-transform definition. Unfolding
  avoids assuming a quasi-coherence instance for the pulled-back module.
- Any U-admissible blowup: `B : IsAdmissible S U` supplies the actual retained ideal
  `B.I`, finite type, and disjoint support. Its actual blowup and map are
  `B.I.blowup` and `B.I.blowupMap`. The conclusion supplies the finite-type module
  witness `hI` required by `moduleStrictTransform`, instead of adding a hypothesis.

Conclusions and constructions, clause by clause:

- S_1 is `B.I.blowup`; X_1 is `Limits.pullback f B.I.blowupMap`; U_1 is
  `B.I.blowupMap ⁻¹ᵁ U`. The first three conjuncts assert qcqs of S_1 and compactness
  of U_1. The fourth is quasi-coherence of `moduleStrictTransform f B.I F`.
- `EtaleFlatification.base (e i) B.I` is the actual T_i = S_i ×_S S_1.
  `EtaleFlatification.source (e i) (g i) B.I` is the actual Y_i = X_i ×_S S_1.
  The structural map to S uses `g i ≫ e i`; `h i` identifies this with `j i ≫ f`.
  The definition `sourceMap` constructs Y_i → X_1 by the two projections, and
  `structureMap` constructs Y_i → T_i by the two projections.
- The next universally quantified conjunction states qcqs of T_i,
  quasi-compactness and étaleness of T_i → S_1 (`pullback.snd`), and étaleness
  of Y_i → X_1 (`sourceMap`).
- The following two implications separately state joint surjectivity of each new
  family if that original family is jointly surjective. Surjectivity is written
  pointwise with `∀ point, ∃ i, ∃ preimage, ... = point`. Neither family is assumed
  to cover in any other clause.
- `ChartConclusion` contains the remaining local assertions. Write d for
  `pullback.fst e I.blowupMap`, A for `I.comap e`, and H for `(tensorPullback j).obj F`.
  Its first three conjuncts say `J.comap d` is finite type, its support misses the
  inverse image of U_1, and that inverse image is quasi-compact. Thus the specified
  blowup `(J.comap d).blowup → T_i` is admissible for exactly the requested open.
  This spells out `IsAdmissible`'s centre data rather than choosing an unrelated centre.
- `finalSpace` is Y_i ×_{T_i} Bl_{J O_{T_i}} T_i.
  `finalModule` is precisely the supported-section cokernel defining the strict
  transform of `sourceMap* F_1`. Its `IsFlatOver (pullback.snd _ _)` conjunct is
  flatness over T_i^*, without imposing any hypothesis on X or finite type of F.
- The isomorphism `t : T_i ≅ A.blowup` is identified with the *existing* flat
  base-change isomorphism by
  `t.hom ≫ (I.blowupFlatBaseChangeIso e).hom = (pullbackSymmetry e I.blowupMap).hom`.
  Its projection equation also records that it is over S_i.
- `c : T_i^* ≅ (A * J).blowup` is the second requested identification. Its structure
  map equation says it is over S_i. `r : T_i^* ≅ (A.comap J.blowupMap).blowup`
  is the reverse-order identification and its structure map equation likewise
  places it over S_i. These are the canonical blowup comparisons: a map to the
  specified blowup over S_i is unique by the existing blowup universal property.
- `((A * J).support : Set T) = (A.support : Set T) ∪ (J.support : Set T)`
  states exactly the composite-centre zero-set clause.
- The witnesses `hA`, `hH`, `hHJ` provide finite type of the extended I-centre,
  quasi-coherence of H, and quasi-coherence of its first J-transform. These are
  conclusions needed to instantiate the recorded `successiveModuleStrictTransform`
  interface, not new assumptions.
- The map `m` identifies the final ambient space with the reverse iterated fibre
  product. `hm` fixes its composite to X_i, the equation involving `r.hom` fixes its
  projection to the reverse final base, and `IsIso m` asserts the identification.
  These two projection conditions determine the map uniquely by fibre-product
  universality, rather than leaving an arbitrary unconstrained transport map.
- Finally `∃! θ` identifies `finalModule` with the pullback along m of
  `successiveModuleStrictTransform g J (A.comap J.blowupMap) H hHJ`, that is first
  the J-transform and then the extended-I transform. The displayed equality
  `finalQuotient ... ≫ θ.hom = ... successiveModuleStrictTransformπ ...` is the
  quotient-map compatibility. Both sides start at the *same* ordinary pullback
  `(tensorPullback (originalProjection e g I J)).obj H`. `finalQuotient` is built
  from the actual first and second quotient maps, using the normalized tensor
  composition comparisons and the projection identity. The right side is the
  actual reverse-order composite quotient with the same normalized comparisons.
  Thus uniqueness and compatibility concern module quotients, not merely an
  unspecified isomorphism between modules or underlying schemes.

Dependency declarations used, with their recorded modules read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: public `SheafOfModules.IsQuasicoherent`
  and `SheafOfModules.IsFiniteType`; no duplicate coherence predicate is introduced.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver` (affine-local relative module flatness).
- The scheme-conventions node is a collection of conventions, with no declaration;
  `CompactSpace`, `QuasiSeparatedSpace`, `QuasiCompact`, `Etale` are used directly.
- `WeilConjectures.Blowup.AdmissibleBlowup`: `AlgebraicGeometry.IsAdmissible`, retaining
  the centre; its fields `I`, `finiteType`, `disjoint_support`, and product blowup API.
- `Sheaf.AlgebraicGeometry.ModuleStrictTransform`: `moduleStrictTransform` and
  `moduleStrictTransformRestriction`; their full bodies and docstrings were read.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale` (the current
  name; the node's historical `IsEtale` spelling is a deprecated alias).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, both
  projections, `pullback.map`, and `pullbackSymmetry`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `tensorPullback`,
  `tensorPullbackSectionComp`; the section-normalized adjunction and its definition
  were read. Also `WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso`:
  `tensorPullbackCompositionIso`, based on the normalized upstream tensor adjunction.
- `WeilConjectures.Blowup.Gluing`: `IdealSheafData.blowup`, `blowupMap`.
- Existing supporting construction interfaces: `IdealSheafData.comap` in Mathlib's
  `IdealSheaf.Functorial`, `blowupFlatBaseChangeIso` in `WeilConjectures.Blowup.FlatBaseChange`,
  `moduleStrictTransformπ` in `ModuleStrictTransformKernel`, and
  `successiveModuleStrictTransform` / `successiveModuleStrictTransformπ` in
  `Sheaf.AlgebraicGeometry.StrictTransformComparisonEpimorphism`.

The proof-only imports include the recorded flat-pullback and module admissible-blowup
calculus modules, the upstream complement theorem, and quasi-coherent pullback module.
The proof nodes without a recorded Lean module are not given invented imports:
`lem-pc-quasi-compact-base-change`, `lem-trf-iterated-transform-exceptional-support`,
`lem-weil-pbc-etale-covering-base-change`, `lem-weil-pbc-etale-scheme-base-change`.
The flat blowup comparison proof nodes are already exposed by the upstream
`Blowup.FlatBaseChange` import. No new independent statement dependency is needed.

Edge cases checked mathematically against the statement and definitions:

- Empty finite family: no Nonempty or covering assumption is imposed. Each covering
  implication has exactly the original empty-family covering condition as premise.
- Empty schemes: all assertions and maps are defined; no point or affine chart is chosen.
- F = 0: the supported-section quotient and both composite quotients are zero;
  uniqueness of the comparison still makes sense.
- Unit I or J: the corresponding blowup is an isomorphism; quotient-map comparisons
  preserve the identity case. An empty preserved open is allowed.
- Non-flat F and unbounded/infinitely generated F are allowed. The only flatness
  premise is the given local J-strict-transform flatness, not flatness of F.
- On Spec k[t] with t-torsion, the supported sections are removed by the existing
  kernel/cokernel construction, so the final module is not silently ordinary pullback.
- The theorem uses all scheme universes u and finite index universes v explicitly;
  no locally Noetherian, quasi-compact X, finite-presentation f, or finite-type F
  hypothesis was added.

Searches actually run (2026-10-24), before writing:

- `msearch.py ... leanfinder 'Etale local flatification of a quasi coherent module is
  stable under admissible blowup and strict transform'`: eight hits, on scheme
  `Flat`, stalk/section flatness, flat localization and open-immersion flatness;
  no blowup-order and module-quotient compatibility statement.
- `msearch.py ... loogle '"blowup", "Flat"'`: zero hits.
- `msearch.py ... leansearch 'Etale local flatification hypotheses for a module are
  preserved under an admissible blowup'`: eight hits on module flat localization,
  base change, scalar restriction, flat morphism restrictions and étale localizations;
  no exact statement.
- `msearch.py ... grep 'blowup.*(flat|strict)|strict.*blowup|flatten.*blow'`: zero hits.
- `rg -n` on `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `etaleFlatification`, étale/blowup combinations, and blowup stability found no
  declaration stating this node. Other étale/log blowup results concern different
  constructions. Reading the strict-transform module family found the reusable
  quotient, normalized tensor, and comparison interfaces listed above.

No `STATEMENT-DISPUTED` finding. The item node changes only in `lean`.

Validation: `scompile.py NI lem-trf-etale-flatification-blowup-stability <file>`
first identified a missing Flat instance in the chart predicate, a wrong spelling
of pullback symmetry, and insufficient category information in a point binder.
The chart predicate now receives the already given Etale instance, uses
`pullbackSymmetry`, and explicitly specifies `Scheme.{u}` in that binder.
The next wrapper invocation exited 0 after its server fallback compiled the file
in 9.4 seconds (the local attempt had exhausted temporary disk space). The final
imports and delivery are checked again by the prescribed dry run.

## Second reading by NI

This is a second pass by the same worker; the dispatcher explicitly prohibits
starting another agent. The maintainer's independent review remains the external
reading of the delivery. I reopened the node and final Lean file and checked the
hypothesis and conclusion correspondences listed above against both texts.

The second pass checked especially that the two covering premises are separate
implications, that U_1 is not confused with the complement of the entire centre,
that the local final centre is J extended to the actual T_i fibre product,
that the reverse order really blows up J before extended I, and that the final
comparison fixes the quotient maps from ordinary pullback of j_i^*F. The equation
for t also fixes the exact upstream flat base-change isomorphism. Existential
finite-type/quasi-coherence witnesses are conclusions and do not restrict the
hypotheses. All helper data have explicit constructions; there is one named
postponed theorem and no data chosen from a sorry existence theorem. No statement
mismatch or node correction was found. A proof-only import was changed from public
to ordinary import, and its publicly used flat-base-change module was imported
directly. The final file has no diagnostic commands or lines exceeding 100 characters.
