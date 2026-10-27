## Worker report

The delivery states `AlgebraicGeometry.exists_localAlterationDiagram_spreading` in
`Sheaf.AlgebraicGeometry.LocalAlterationDiagramSpreading`. Its sole theorem proof is `sorry`.
The new definition node `def-per-integral-alteration-diagram` supplies the full specified
alteration diagram and its cartesian comparison, with actual structure data and predicates.
No statement correction, disputed statement, dependency repair, or new axiom is used.
The existing item's only changes are its `lean` record and the added definition dependency.

The mathematical source was read directly: Kurano--Shimomoto, *Ideal-adic completion of
quasi-excellent rings (after Gabber)*, Definition 3.2, printed p.3, and Lemma 4.4, first
proof paragraph, printed p.5, https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf.
Definition 3.2 fixes the proper witness, indexed open cover and commuting arrows; the
first paragraph on p.5 spreads this alteration cover. The DAG spells out the limit,
properness, integrality and function-field ingredients. The theorem states that DAG
assertion, including persistence on all smaller principal opens, without adding the
regularity or excellence hypotheses used elsewhere in Lemma 4.4.

### Hypotheses and clauses

- Commutative Noetherian integral domain B: `(B : Type u) [CommRing B] [IsDomain B]
  [IsNoetherianRing B]`. The prime is `(q : Ideal B) [q.IsPrime]`.
- S is precisely `Spec (.of (Localization.AtPrime q))`, not an arbitrary base with an
  unspecified map to the localization. The canonical ring map remains `algebraMap`.
- Finitely many schemes: `(I : Type w) [Finite I]`. No enumeration, ordering, nonempty
  index or equality of `u` and `w` is assumed.
- The entire specified input is the argument `D : IntegralAlterationDiagram I S`.
  The structure's `T`, `integral_T` and `noetherian_T` express every integral,
  nonempty Noetherian T_i. Mathlib's IsIntegral includes nonemptiness.
- Its `f`, `dominant_f` and `finiteType_f` express the specified maps, dense image,
  and finite type = `LocallyOfFiniteType ∧ QuasiCompact`.
- `finiteGeneric_f` means `Module.Finite S.functionField (D.T i).functionField` with
  the module structure taken from the existing `f.dominantFunctionFieldAlgebra`.
  This is the actual generic stalk map, not an arbitrarily chosen field embedding.
- The witness is `P`, `integral_P`, `noetherian_P`, `g`, `proper_g`, `surjective_g`,
  and `finiteGeneric_g`. Dominance of g used for its canonical algebra is constructed
  directly from the supplied surjectivity proof by `surj.denseRange`.
- The exact indexed open subschemes are `U : I → P.Opens`; `covers : iSup U = ⊤`
  means their union is P. The opens may be empty. `h i : (U i).toScheme ⟶ T i`
  is the specified map, and `commutes` gives `h i ≫ f i = (U i).ι ≫ g`.
- The conclusion chooses `(a : B) (ha : a ∉ q)` and a diagram E over exactly
  `Spec (.of (Localization.Away a))`. Thus all integrality, Noetherianity, finite
  type, dominance, generic finiteness, properness, surjectivity, indexed-cover and
  S_a-linearity clauses are repeated through E's fields, not left as informal claims.
- `D.IsCartesianOver E s` uses the canonical s from `Localization.awayLift` of the
  original `algebraMap B (Localization.AtPrime q)`. Its unit witness is explicitly
  `IsLocalization.map_units (M := q.primeCompl) ... ⟨a, ha⟩`.
- This comparison existentially supplies maps t_i, p and v_i on *all* vertices.
  The `IsPullback (t i) (D.f i) (E.f i) s` squares identify every T_i with the
  base change of E.T_i. `IsPullback p D.g E.g s` does so for P.
- `IsPullback (v i) (D.U i).ι (E.U i).ι p` retains the given indexed open cover.
  The equation `v i ≫ E.h i = D.h i ≫ t i` retains every specified h_i. Together
  these are a diagram isomorphism with the chosen base change, by the uniqueness
  of pullbacks. Individual abstract object isomorphisms would have lost this clause.
- The last universal quantifier covers every b outside q with
  `PrimeSpectrum.basicOpen b ≤ PrimeSpectrum.basicOpen a`, including equality.
  It produces F over Spec B[1/b] with the same full properties, and a cartesian
  comparison `F.IsCartesianOver E r`. This asserts restriction of the *chosen E*,
  rather than a second unrelated spreading of D.
- The equation `r ≫ Spec.map (ofHom (algebraMap B (Localization.Away a))) =
  Spec.map (ofHom (algebraMap B (Localization.Away b)))` fixes r as the canonical
  morphism D(b) → D(a). This map is unique: Spec B[1/a] → Spec B is an open
  immersion, hence a monomorphism; equivalently ring-localization maps are determined
  by their restriction to B. Existentially presenting this uniquely specified map
  avoids selecting arbitrary geometric data or adding a unit hypothesis on a.
- The last `D.IsCartesianOver F ...` explicitly recovers the same original entire
  specified diagram over S, now using the canonical map from Spec B_q to Spec B[1/b].
- No regularity, excellence, separatedness of f_i, nonemptiness of individual U_i,
  or projectivity of the proper witness is imposed. No source scheme is replaced
  by a reduced model, normalization, or an arbitrary cover refinement.

### Dependency interfaces read and used

All original statement-dependency node statements, `lean` records and `mathlib_match`
records were read. The actual declarations and their docstrings were read in the
read-only live-source clone. There are no unusable recorded statement interfaces.

- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `fst`,
  `snd`, `lift`; the equivalent cartesian-square API is `CategoryTheory.IsPullback`
  in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`, reexported by
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`; open subschemes
  are the existing `Scheme.Opens.toScheme` and `.ι`, not copied definitions.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper` (its universally closed
  component supplies quasi-compactness, agreeing with the node's finite-type convention).
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, with the ring
  interface and `Localization.awayLift` from `Mathlib.RingTheory.Localization.Away.Basic`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective` and `IsDominant`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
  The latter is exactly quasi-compact plus locally Noetherian.
- Added definition dependency `def-sfb-dominant-function-field-map`:
  `Sheaf.TraceFormula.LocalDimensionFormula`,
  `AlgebraicGeometry.Scheme.Hom.dominantFunctionFieldAlgebra`, read with its body.
  It uses the existing upstream `functionFieldMap` in
  `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`, the generic stalk map.
- Added definition dependency `def-weil-finitely-generated-module`:
  `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`.

The theorem has plain imports for every recorded project proof-dependency module:
`OpenImmersionInverseLimitDescent`, `DescendSurjective`, `EventuallyProper`,
`FiniteDiagramLiftOfModels`, `FiniteFamilyJointSurjectivityStage`, `LimitAffineTransition`,
`LocalizationColimitPrincipalLocalizations`, and the upstream `AffineTransitionLimit`.
The Mathlib proof leaves are already exposed by the statement imports. The proof-only
node `lem-per-integrality-prime-neighbourhood` has no recorded Lean module to import;
its mathematical statement and role are retained in the complete five-step proof docstring.
It is not a missing notion required to type this statement.

### Edge cases and review of the encoding

An empty index type is allowed. Its union of opens is empty, so it cannot cover the
nonempty integral witness P; thus no spurious empty-family instance satisfies the
hypotheses. Empty open members are allowed without any generic point on them.
IsIntegral already excludes empty T_i and P. A domain excludes the zero ring;
q = (0), q maximal, fields B and a = 1 remain included. Every b outside q is nonzero,
so D(b) contains the generic point. The case b = a is explicitly included. The
condition D(b) ⊆ D(a) is genuinely the inclusion of principal opens, not the stronger
condition a divides b. Consequently changes of exponents and arbitrary principal
subneighbourhoods are included. There is no assumption on residue characteristic.
All universes and variables are explicitly bound, with `autoImplicit false`.
The helper structure stores integrality of the base as proof data; at each occurrence
in this theorem that base is a localization of the specified domain at a nonzero
multiplicative system, so this introduces no mathematical hypothesis or excluded case.
The cartesian comparisons enforce all diagram arrows, not merely underlying points.

### Searches

The prescribed `msearch.py` searches were run for this item and recorded in
`searches.jsonl`. LeanFinder for finite-diagram spreading returned finite-type,
quasi-finite, finite morphism and spreading components, with no full-diagram theorem.
Loogle `AlgebraicGeometry.Scheme, IsLocalization` returned zero hits. Mathlib grep
`[Gg]eneric.*[Ff]inite|[Aa]lteration` in AlgebraicGeometry returned zero hits.
LeanSearch for finite-diagram spreading returned ordinary morphism spreading and
open-cover APIs, not this statement. `rg` of `lean/WeilConjectures` and `lean/Sheaf`
found no local-alteration diagram or full spreading declaration; searching the item
identifier in upstream Lean returned none. Searches for function-field maps found
`functionFieldMap` and its exact dominant canonical algebra, which are reused.

For the new diagram notion, LeanSearch and LeanFinder queried
`integral alteration diagram indexed open cover proper surjective generically finite
witness cartesian morphism`; results concern generic inverse-limit diagrams and open
covers, not this bundle. Mathlib grep for
`IntegralAlterationDiagram|[Aa]lteration.*[Dd]iagram|[Dd]iagram.*[Aa]lteration` had zero
hits. The corresponding source/project grep found no declaration. DAG definition
searches found only unrelated formal-diagram nodes, and
`tools/blueprint_refs.py search 'alteration diagram'` returned zero nodes.
The prime-to-ell alteration-topology node was read: it specifies a different category
and topology, not the specified proper-witness diagram needed here.

## New nodes

`def-per-integral-alteration-diagram` owns
`Sheaf.AlgebraicGeometry.IntegralAlterationDiagram`: the actual diagram structure,
its canonical finite-generic-field-extension predicate, and the cartesian comparison
predicate. Its source is Kurano--Shimomoto Definition 3.2 and Lemma 4.4, the latter
specialized in the item's DAG to integral witnesses. It defines no alternative schemes,
function fields, canonical field maps, finiteness, Noetherianity, properness, opens or
fibre products: every constituent is taken from the recorded dependencies. Its three
notion-search kinds and DAG search found no existing bundle. All its declarations
carry its blueprint identifier; all definitions contain real data and no sorry.

## Second reading by NF

No additional agent was started, as instructed by the dispatcher. The maintainer's
independent review remains the independent second reading. The worker reread both
modules against the node after compilation, checking all clauses listed above.
The review corrected an initial implicit requirement for integrality instances on
Spec B[1/a] before ha was available by storing base integrality in the diagram itself;
no extra mathematical assumption was introduced. It also made `q.primeCompl` explicit
in both canonical unit witnesses, and replaced a direct generic-stalk expression by
the already-recorded dominant function-field algebra. It verified that smaller-open
persistence is tied to the chosen spread E by cartesian squares and that every indexed
h_i survives. No statement mismatch remains in this self-check.
