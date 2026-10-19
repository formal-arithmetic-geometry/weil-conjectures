## Worker report

`Sheaf.AlgebraicGeometry.Sites.AffineLineInfinityStrictLocalModel` states
`AlgebraicGeometry.Scheme.affineLine_infinity_strictLocal_model`, with its whole proof
`by sorry`. This resumed worker checked the inherited files against the current node,
its dependency records, the source declarations, and the live compiler. The mathematical
statement is unchanged. Only `lean` and the permitted addition of the already recorded
local-structure node to `stmt_deps` change in the item.

For the correspondence below, B, b, Y, g, i, j, t, y and R denote the objects named in
the node; they are explanatory abbreviations, not additional Lean declarations.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Algebraically closed K:Type u | `(K : Type u) [Field K] [IsAlgClosed K]`, with explicit `universe u` |
| Natural number n | `(n : ℕ)` |
| B = Spec K[x_0,...,x_n] | `Spec (.of (MvPolynomial (Fin (n + 1)) K))` |
| Canonical b:B→Spec K | `Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin (n + 1)) K)))` |
| Y = P¹_B and its projection g | `ProjectiveLine B` and `ProjectiveLine B ↘ B` |
| Infinity section i | `ProjectiveLine.infinity B` |
| Arbitrary scheme isomorphism e:Spec K[x_0,...,x_(n+1)] ≅ A¹_B | Binder `e` has domain `Spec (.of (MvPolynomial (Fin (n + 2)) K))` and codomain `AffineSpace PUnit.{u + 1} B`; it has no extra compatibility hypothesis |
| Ordinary chart j | `e.hom ≫ ProjectiveLine.affineChart B` |
| Algebraically closed Ω:Type u and geometric point s | `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and `(s : Spec (.of Ω) ⟶ B)` |
| t=s followed by i and y=t(closedPoint Ω) | `s ≫ ProjectiveLine.infinity B` and its evaluation at `IsLocalRing.closedPoint Ω` |
| R and its canonical structural map rho | Existing `strictHenselizationRing t` and `strictHenselizationStructuralMap t` |
| Canonical K-algebra on κ(s) | `(Hom.residueFieldAlgebraMap b (s (IsLocalRing.closedPoint Ω))).toAlgebra` is the explicit algebra argument to `@Algebra.trdeg` |
| Canonical K-algebra on κ(y) | `(Hom.residueFieldAlgebraMap (g ≫ b) y).toAlgebra` is the explicit algebra argument to `@Algebra.trdeg` |
| Natural a<n+2 | `∃ a : ℕ, a < n + 2 ∧ ...` |
| Both residue transcendence degrees equal the same a | Two equalities with right side `(a : Cardinal.{u})` under the same existential |
| h belongs to R | `∃ h : strictHenselizationRing t, ...` |
| h belongs to the maximal ideal | `h ∈ @IsLocalRing.maximalIdeal _ _ (Classical.choose (AlgebraicGeometry.strictHenselizationLocalStructure t))` |
| h is nonzero | `h ≠ 0` |
| The pullback of j along rho is isomorphic to Spec R[1/h] | `Nonempty (pullback j (strictHenselizationStructuralMap t) ≅ Spec (.of (Localization.Away h)))` |

The explicit `Classical.choose` selects a proof of the proposition `IsLocalRing R`,
not a ring or other data. Proof irrelevance makes the maximal ideal independent of
this proof. It introduces no new hypothesis or postponed theorem. The conclusion
asks for an isomorphism of schemes exactly as the node does; it adds no compatibility
condition over Spec R. There are no hidden `let`, `letI`, `show`, auto-bound variables,
file-local notation, or local instances in the delivered signature.

Dependency declarations opened with their full signatures and docstrings:

- `def-weil-pbc-strict-henselization-limit`: module
  `Sheaf.AlgebraicGeometry.StrictHenselization`, declarations
  `AlgebraicGeometry.Scheme.strictHenselizationRing`, `strictHenselizationScheme`,
  and `strictHenselization_properties`; these give the chosen colimit and spectrum.
- `def-weil-pbc-strict-henselization-structural-map`: module
  `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`, declaration
  `AlgebraicGeometry.Scheme.strictHenselizationStructuralMap`, characterized by
  `exists_strictHenselizationStructuralMap` as the common composite of the limit legs.
- `def-kun-transcendence-degree`: module
  `Mathlib.RingTheory.AlgebraicIndependent.Basic`, declaration `Algebra.trdeg`.
  Its supremum of cardinalities of algebraically independent subsets is exactly
  the node's notion, with the specified algebra structures supplied explicitly.
- `def-nagata-projective-space-base-change`: module
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`, declaration
  `AlgebraicGeometry.ProjectiveSpace`; `ProjectiveLine` specializes its homogeneous
  index to `ULift (Fin 2)`. The imported `ProjectiveSpace.Line` and its `Charts`
  dependency provide the actual ordinary chart `[x:1]`, infinity chart `[1:z]`, and
  infinity section on that same base-change projective space.
- `WeilConjectures.ZetaSeries`: `AlgebraicGeometry.Scheme.Hom.residueFieldAlgebraMap`
  constructs the canonical embedding from the base field via residue-field maps.
- `lem-weil-pbc-strict-henselization-local-structure`: the existing declaration
  `AlgebraicGeometry.strictHenselizationLocalStructure` in
  `Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility` gives locality and
  strict henselianity for the exact chosen ring. See the dependency repair below.
- Proof imports: `Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg`
  (`AlgebraicGeometry.topologicalKrullDim_closed_irreducible_eq_trdeg`),
  `Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso`
  (`AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion`), and
  `Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale`
  (`AlgebraicGeometry.Scheme.strictHenselization_indEtale_of_affine_chart`).
  The declaration docstring records all four DAG proof steps and their uses.

The item cites the older blueprint's proof steps 4–6. I opened that entire proof:
its local calculation works over an algebraically closed field at arbitrary boundary
points and identifies the complementary strict-local open with Spec R[1/f], for nonzero
f in the maximal ideal. Its next paragraph compactifies affine space in P¹ over the
smaller affine space. The current `main-20261015` file at
`sec-six-functors-basics/sk-prop-sf-cbc/thm-sc-affine-torsion-cd.md` retains the unit
statement but contains no proof; this item has no `blueprint_update`. The cited older
proof therefore remains the recorded source for this auxiliary statement.

Edge cases checked: n=0 gives a one-variable base and a<2; no positive-n hypothesis
is imposed. Generic and other nonclosed points remain allowed, so the common a can
be positive. Arbitrary e may mix variables, but precomposing the chart with an
isomorphism preserves its image. All characteristics remain allowed. The infinity
coordinate is regular in the polynomial chart, and flat strict henselization
preserves regularity; its local ring is nontrivial. Thus the simultaneous conditions
h≠0 and h in the maximal ideal are appropriate. The empty scheme cannot receive
Spec Ω, so the local-structure interface excludes no actual geometric-point case.
`PUnit.{u + 1}` has one element and lives in `Type u`; all fields, schemes and cardinals
have the universe specified by the node, without an added universe equality.

Searches repeated in this resumed worker pass on 2026-10-17:

- `msearch.py leanfinder`: "The affine chart in the strict henselization of the
  projective line at infinity is the spectrum of a localization at a nonzero element
  of the maximal ideal". Eight hits on general Proj charts; no exact theorem.
- `msearch.py loogle`: `"IsOpenImmersion", "Localization.Away"`.
  Returned zero hits with the service message that Loogle is under load; this is not
  evidence of absence, and the other searches and source inspection were used.
- `msearch.py leansearch`: "The complement of infinity in the strict localization
  of the projective line is a principal open defined by a nonzero element of the
  maximal ideal". Eight component results including
  `Scheme.isOpenImmersion_SpecMap_localizationAway` and Proj basic opens, no exact result.
- `msearch.py grep`: `strictHenselization.*[Aa]way|[Aa]way.*strictHenselization`.
  Zero Mathlib hits.
- `rg` in Mathlib, the slopmaster2 `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for
  `affineLine_infinity_strictLocal_model|strictLocal.*model|strictHenselization.*[Aa]way|[Aa]way.*strictHenselization`.
  Only other strict-local comparison/model results, no existing main statement.
  Searching the upstream source for the exact node id returned no match.
- `rg strictHenselizationLocalStructure lean/Sheaf` found the exact compatibility
  theorem and its consumers. Its full source was also read with `scompile.py --source`.
  The existing definition `IsStrictlyHenselianLocalRing` was opened in
  `WeilConjectures.Mathlib.RingTheory.Henselian`; it extends `HenselianLocalRing`
  and supplies a separably closed residue field.

Validation in this pass: the only delivered Lean file compiled via `scompile.py`
in its sandbox and library paths in 1.6 s and 1.7 s, with no errors or warnings.
A separate scratch probe through the same wrapper printed the loaded strict-local
ring, checked the compatibility theorem, and checked the explicit maximal-ideal
expression. The loaded ring still prints a separate affine-diagram colimit, even
though the newer source is an abbreviation to upstream; the signature works with
that loaded interface. The delivered file has one named postponed theorem, no data
definitions, and no line over 100 columns. Node signatures are verbatim from source;
JSON retains indent 1, Unicode, and its final newline. No statement is disputed or
corrected, and no new definition node is needed.

Recovery verification on 2026-10-17: reopened the source proof and every statement-
dependency signature, and checked the sandbox JSON against the read-only base. The
consumer again compiled cleanly through `scompile.py` in both sandbox and library
paths (1.7 s each). The separate locality probe again printed the actual loaded
`strictHenselizationRing` as the affine-diagram colimit and checked the existing
compatibility theorem and explicit maximal ideal (1.8 s and 1.6 s). The inherited
signature and repair remain appropriate; no mathematical edit was necessary.

## Dependency modules

`lem-weil-pbc-strict-henselization-local-structure` changes only in `lean`, under
§1(B), using an `existing: true` record; no dependency module is delivered. The old
record names upstream local-ring instances on `Scheme.strictHenselization`, which
do not provide the instance for the loaded project `strictHenselizationRing` colimit.
The existing `Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility` theorem
`AlgebraicGeometry.strictHenselizationLocalStructure` supplies exactly the node's
locality and strict henselianity, without a residue-field identification or a
geometric factorization. Its local-ring proof is passed explicitly in the consumer.
No duplicate theorem or additional postponed proof is introduced. This existing
node is added to the item's statement dependencies, as §5 permits.

The independent reading below was already present in the inherited sandbox. This
resumed worker preserves it as that reader's work; the next reader must check the
current files and update the reading before delivery. The earlier worker narrative
that referred to a removed duplicate helper module has been replaced above.

## Earlier second reading (a previous round; superseded)

Read the sandbox node and Lean simultaneously against the actual source
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/thm-sc-affine-torsion-cd.md`.
Its local-calculation paragraph assumes an algebraically closed ground field after the
preceding descent reduction, works at arbitrary boundary points, and identifies the
complement with `Spec R[1/f]` for a nonzero local equation in the maximal ideal. The
compactification paragraph takes the ordinary affine chart in the relative projective
line and its infinity section. No closed-point, positive-characteristic, or positive-`n`
restriction is imposed by those constructions. The induction's `d > 1` is not required
for this local geometry; the node correctly includes the same model for `n = 0`.
There is no `statement_change`, and no mathematical correction or citer audit is needed.

Independent object/hypothesis/conclusion inventory and match (B, b, Y, g, i, t, y, R and
rho in this table are explanatory names, not Lean abbreviations):

| Node item | Exact Lean rendering in the final module | Verdict |
| --- | --- | --- |
| Algebraically closed field K and natural n | `(K : Type u) [Field K] [IsAlgClosed K] (n : ℕ)` | Exact; no further field or size hypotheses. |
| B with n+1 polynomial variables and canonical b | `Spec (.of (MvPolynomial (Fin (n + 1)) K))` and `Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin (n + 1)) K))))` | Exact spectrum and K-structure. |
| Y = P1 over B, projection g, infinity section i | `ProjectiveLine B`, `ProjectiveLine B ↘ B`, `ProjectiveLine.infinity B` | Exact existing projective-space model and section. |
| Arbitrary scheme isomorphism e from (n+2)-variable spectrum to the relative affine line | Binder `e : Spec (.of (MvPolynomial (Fin (n + 2)) K)) ≅ AffineSpace PUnit.{u + 1} B` | Exact; no condition of being over B is silently added. |
| j is e followed by the ordinary chart | `e.hom ≫ ProjectiveLine.affineChart B` | Exact arrow, not an arbitrary open immersion. |
| Algebraically closed geometric field Omega in the specified universe, and s | `{Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B)` | Exact; no relation to K is assumed beyond the morphism s. |
| t = s followed by infinity, and its image y | `s ≫ ProjectiveLine.infinity B`, evaluated at `IsLocalRing.closedPoint Ω` | Exact geometric point and image; y need not be closed in Y. |
| Chosen strict localization R and structural map rho | `strictHenselizationRing t`, `strictHenselizationStructuralMap t` | Exact dependency declarations; no substitute ring or map. |
| Natural number a with strict upper bound | `∃ a : ℕ, a < n + 2 ∧ ...` | Exact quantifier and bound, including a = 0. |
| Transcendence degree of the base point equals a | `@Algebra.trdeg K _ _ _ (Hom.residueFieldAlgebraMap b (s (IsLocalRing.closedPoint Ω))).toAlgebra = (a : Cardinal.{u})` | Exact canonical K-algebra, not the geometric-point field Omega. |
| Transcendence degree at y equals the same a | `@Algebra.trdeg K _ _ _ (Hom.residueFieldAlgebraMap (g ≫ b) y).toAlgebra = (a : Cardinal.{u})` | Exact structure through g followed by b and the same a. |
| h belongs to R and its maximal ideal | `∃ h : strictHenselizationRing t`, followed by `h ∈ @IsLocalRing.maximalIdeal _ _ (Classical.choose (AlgebraicGeometry.strictHenselizationLocalStructure t))` | Exact; the existing theorem supplies a proof of locality, not extra ring data or a new hypothesis. |
| h is nonzero | `h ≠ 0` | Exact, independent of maximal-ideal membership. |
| The pullback is isomorphic to Spec R[1/h] | `Nonempty (pullback j rho ≅ Spec (.of (Localization.Away h)))` | Exact existence of a scheme isomorphism with the same h, after the same a. No extra compatibility clause is added. |

Dependencies were opened and read, rather than inferred from names:

- `def-weil-pbc-strict-henselization-limit`: `strictHenselizationRing` and
  `strictHenselizationScheme` in `Sheaf.AlgebraicGeometry.StrictHenselization` give the
  coordinate colimit and its spectrum. The live source was also read with
  `scompile.py --source`. Its newer source is an abbreviation to upstream; the loaded
  interface still prints the separate `colimit (strictHenselizationAffineDiagram s)`.
  The delivered statement works with that loaded interface as well.
- `def-weil-pbc-strict-henselization-structural-map`: the opened module specifies the
  common composite of the limit projections with their neighbourhood structure maps.
- `def-kun-transcendence-degree`: Mathlib's `Algebra.trdeg` is precisely the cardinal
  supremum of algebraically independent subsets. The explicit `.toAlgebra` arguments
  use the canonical embeddings from the opened `Hom.residueFieldAlgebraMap` definition
  in `WeilConjectures.ZetaSeries`, not an arbitrary algebra instance.
- `def-nagata-projective-space-base-change`: the opened `ProjectiveSpace` definition
  is the pullback of the integral Proj model. `ProjectiveLine` specializes its homogeneous
  index to `ULift (Fin 2)`. Opened the chart definitions in `ProjectiveSpace.Charts` and
  `ProjectiveSpace.Line`: the ordinary chart is `[x:1]`, the infinity chart `[1:z]`,
  and infinity is the zero section followed by that chart. Thus these are charts on
  the exact recorded scheme, despite the dependency node not itself promising charts.
- Proof-dependency signatures and docstrings were read in
  `ClosedIrreducibleDimensionTrdeg`, `ClosedImmersionResidueFieldIso`, and
  `StrictHenselizationAffineChartIndEtale`. They respectively supply dimension/trdeg
  for an irreducible closure in a finite-type K-scheme, residue-field isomorphism for
  a closed immersion, and ind-etaleness for the canonical strict-local chart algebra
  specified by the spectrum equation. Their assumptions can be met in this model.

H13 repair and H4 mismatch found: the worker's proposed
`strictHenselizationRing_isStrictlyHenselian` was a second statement of an existing result.
My `rg` search found `AlgebraicGeometry.strictHenselizationLocalStructure` in
`Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility`. I opened its full statement
and its source returned by `scompile.py --source`; both state, without extra assumptions,
`∃ (_ : IsLocalRing (Scheme.strictHenselizationRing barY)),
IsStrictlyHenselianLocalRing (Scheme.strictHenselizationRing barY)`.
This is precisely the dependency node, which asserts neither a residue-field
identification nor a factorization of the geometric point. I also read its source
places in the local Stacks TeX: Tag 04HX identifies the affine pointed-neighbourhood
colimit with the strict henselization; 04GW identifies the residue-triple colimit; 04GP
supplies a strictly henselian local ring. They impose no Noetherianity or finite type.
Opened `IsStrictlyHenselianLocalRing`: it extends `HenselianLocalRing`, which supplies
locality, and includes separable closedness of the residue field.

An initial scratch compiler probe confirmed that the originally recorded upstream
`isLocalRing_strictHenselization` instance still cannot synthesize locality of the loaded
project ring. The same probe successfully checks the existing compatibility theorem
on that exact ring. A subsequent clean probe checked
`@IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing s) _
(Classical.choose (strictHenselizationLocalStructure s))`. Therefore I rebound the
dependency to this existing theorem under §1(B), deleted the duplicate module, imported
the compatibility module in the consumer, and passed the theorem's existing locality
proof explicitly to `maximalIdeal`. Choosing a proof of `IsLocalRing` selects no ring
object; proof irrelevance also makes the ideal independent of that choice. No helper
definition, additional postponed theorem, or new DAG node is necessary. The dependency
node changes only in `lean`, with `existing: true` and an explanatory `lean.note`.

Edge cases independently checked: `n = 0` gives base K[x0] and a < 2, with the same two
projective-line charts. Generic and other nonclosed base points remain allowed, and
both transcendence degrees may be positive. Every characteristic is covered; no
separability or characteristic-zero instance is added. Fields are nontrivial, so the
zero ring is not a base-field case; the strict-local ring is nontrivial by its local
structure. An empty scheme has no geometric point, so the dependency excludes no
legitimate empty case. The homogeneous coordinate index is always two-element and
the affine-line index is PUnit; there is no arbitrary or empty chart index in this
node. The index `Fin (n + 1)` is nonempty for every n. The same `u` for K and Omega is
specified by the node; `PUnit.{u+1}` is the singleton type in `Type u`, not an extra
universe restriction. All universes and variables in the declaration are bound.
The isomorphism e remains arbitrary and may mix polynomial variables: its whole
source maps isomorphically onto the ordinary chart, so its choice does not change the
pullback open.

Independent searches (queries differ from the first pass):

- `msearch.py ... leanfinder`: "The inverse image of the affine-line chart in the
  strict henselization at the infinity section is a localization at a nonzero element
  of the maximal ideal". Eight general local-spectrum/localization hits, no exact result.
- `msearch.py ... loogle`: `"IsStrictlyHenselianLocalRing"`. Zero Mathlib hits; the
  actual project class was opened in `WeilConjectures.Mathlib.RingTheory.Henselian`.
- `msearch.py ... leansearch`: "For the projective line over a polynomial ring, the
  complement of infinity in its strict localization is the spectrum of a principal
  localization". Eight hits on Proj charts and localization open immersions; no exact
  main statement. In particular `isOpenImmersion_SpecMap_localizationAway` supplies
  only a component, without the infinity geometry, nonzero equation, or trdeg clauses.
- `rg` on Mathlib, `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, `lean/Sheaf`,
  the current `lean/WeilConjectures`, and `dag/lean_names_upstream.json` searched for
  `strict.*(localiz.*away|principal.open)`, `localiz.*away.*strict`,
  `strict.*local.*model`, `affineLine_infinity_strictLocal_model`, and separately
  `strictHenselization.*[Ll]ocal`. No existing main theorem was found. The locality
  search found the exact compatibility theorem above, which is now reused.

No main-statement mismatch was found. The only repair is removal of the duplicate
local-structure theorem and explicit use of the existing proof. Both delivered record
signatures were checked verbatim against their source declarations; only `lean` and
the allowed additional statement dependency differ from the base. The sole delivered
Lean file has no line over 100 columns, no local notation or instance, no hidden let,
no definition with postponed data, and exactly one theorem whose proof is `by sorry`.
Its module and theorem docstrings name the source and blueprint and reproduce all four
node proof steps. No target or natural-language node statement is changed.

Final validation: the consumer alone compiled cleanly with `scompile.py` in both its
sandbox check and its library-path check (2.4 s and 2.7 s), without errors or warnings.
There are no sibling modules left to compile. The compatibility source/signature and
its explicit maximal-ideal use were separately checked through the same wrapper.

## Earlier second reading (a previous round; superseded)

I reread the current node, its source place, every statement dependency, the dependency
Lean declarations, and the delivered module independently. The source place is
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/`
`thm-sc-affine-torsion-cd.md`, whose local calculation assumes an algebraically closed
field, a smooth affine line compactified by the relative projective line, an arbitrary
boundary point, and its strict-local equation. It imposes no closed-point, characteristic,
or positive-dimensional restriction. The corresponding object and clause inventory is:

| Node object or clause | Lean rendering in `affineLine_infinity_strictLocal_model` | Verdict |
| --- | --- | --- |
| Algebraically closed field and index | `(K : Type u) [Field K] [IsAlgClosed K] (n : ℕ)` | exact |
| Polynomial base and canonical map | `B = Spec (.of (MvPolynomial (Fin (n + 1)) K))`, with `Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin (n + 1)) K)))` in both trdeg terms | exact |
| Relative projective line, projection, infinity section | `ProjectiveLine B`, `ProjectiveLine B ↘ B`, and `ProjectiveLine.infinity B` | exact |
| Arbitrary affine-line presentation and ordinary chart | `e : Spec (.of (MvPolynomial (Fin (n + 2)) K)) ≅ AffineSpace PUnit.{u + 1} B`; chart `e.hom ≫ ProjectiveLine.affineChart B` | exact; no extra over-compatibility is assumed |
| Geometric point over the base | `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and `s : Spec (.of Ω) ⟶ B` | exact |
| Boundary point | `s ≫ ProjectiveLine.infinity B`, evaluated at `IsLocalRing.closedPoint Ω` | exact |
| Strict-local ring and structural map | `strictHenselizationRing (s ≫ ProjectiveLine.infinity B)` and `strictHenselizationStructuralMap (...)` | exact recorded constructions |
| Canonical K-algebra structures | Explicit `.toAlgebra` from `Hom.residueFieldAlgebraMap b (...)` and from `Hom.residueFieldAlgebraMap (g ≫ b) (...)` as the two `@Algebra.trdeg` arguments | exact; no arbitrary algebra instance |
| Common finite transcendence degree | `∃ a : ℕ, a < n + 2` followed by both equalities to `(a : Cardinal.{u})` | exact quantifier and bound |
| Principal-open equation | `∃ h : strictHenselizationRing (...)`, with `h ∈ @IsLocalRing.maximalIdeal ...` and `h ≠ 0` | exact; the explicit local-ring proof is only a proof argument |
| Pulled-back ordinary chart | `Nonempty (pullback (e.hom ≫ ProjectiveLine.affineChart B) (strictHenselizationStructuralMap ...) ≅ Spec (.of (Localization.Away h)))` | exact existence of the stated scheme isomorphism |

I opened the dependency declarations rather than matching names. The strict-local ring is
`strictHenselizationRing` from `Sheaf.AlgebraicGeometry.StrictHenselization`; its spectrum
and limit properties are the same chosen affine pointed-etale colimit as in the node. The
structural map is the common-composite map from
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`. `Algebra.trdeg` is Mathlib's
supremum over algebraically independent families. `ProjectiveLine` is the recorded
base-change projective line, while `ProjectiveLine.affineChart` and `infinity` are its
actual `[t : 1]` and `[1 : 0]` maps. The local-structure dependency is correctly rebound
in the sandbox node to the existing
`AlgebraicGeometry.strictHenselizationLocalStructure`, whose existential local-ring proof
is needed because the loaded colimit has no synthesized `IsLocalRing` instance. The
module uses that proof explicitly in `maximalIdeal`; this does not alter the ring or add a
hypothesis.

Edge cases checked: `n = 0` gives `K[x_0]` and still permits `a < 2`; a generic or other
nonclosed base point is allowed; all characteristics are allowed; `Fin (n + 1)` is
nonempty; `PUnit.{u + 1}` supplies the singleton affine-line index; and the same universe
`u` for `K` and `Ω` is exactly the node's convention. Fields exclude the zero ring, while
an empty scheme has no morphism from `Spec Ω`. The arbitrary isomorphism `e` may mix
polynomial coordinates without changing its image chart. No hidden `let`, `letI`,
`show`, unbound variable, local notation, or extra Noetherian/finite-type assumption is
present.

Independent searches performed for this reading were:

- `msearch.py ... leanfinder "principal open strict henselization projective line infinity"`,
  which returned eight unrelated valuation/function-field and Henselian hits;
- `msearch.py ... loogle "IsOpenImmersion Localization.Away strictHenselization"`,
  which returned zero hits (the service also reported `IsOpenImmersion` as unknown);
- `msearch.py ... grep "strictHenselization.*Away|Away.*strictHenselization"`, zero hits;
- `rg` over Mathlib, `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, the project
  `lean/Sheaf` and `lean/WeilConjectures`, and `dag/nodes` for the exact theorem name,
  strict-local model/principal-open variants, and strict-henselization/Away variants.
  Only the existing local-structure compatibility theorem and unrelated component lemmas
  were found; no duplicate main statement exists.

The only mismatch found was the dependency interface inherited from the upstream-sync
record: its old upstream local-ring instances apply to `Scheme.strictHenselization`, while
this project statement uses the affine-diagram `strictHenselizationRing` interface. I kept
the item statement unchanged, added the already recorded local-structure node to its
`stmt_deps`, rebound that dependency's `lean` record to the existing compatibility theorem,
and retained the explicit `Classical.choose` local-ring proof in the module. No item
statement correction, citer audit, new definition node, or additional Lean declaration
was needed. The required `scompile.py` check of the delivered module passed in both sandbox
and library paths with no errors or warnings other than the intended `sorry` allowance.

## Second reading by Q22

I reread the current node, its source place, every dependency record, and the current
Lean file. The source local calculation assumes an algebraically closed field and the
relative projective-line compactification at an arbitrary boundary point. It adds no
closed-point, characteristic-zero, positive-dimensional, or Noetherian hypothesis.

| Node object or clause | Lean rendering | Verdict |
| --- | --- | --- |
| Algebraically closed field and natural number | `(K : Type u) [Field K] [IsAlgClosed K] (n : ℕ)` | exact |
| Polynomial base `B` and map `b` | `Spec (.of (MvPolynomial (Fin (n + 1)) K))`; `Spec.map (CommRingCat.ofHom (algebraMap K ...))` | exact |
| Relative projective line, projection, infinity section | `ProjectiveLine B`, `ProjectiveLine B ↘ B`, `ProjectiveLine.infinity B` | exact |
| Affine-line presentation and ordinary chart | `e : Spec (.of (MvPolynomial (Fin (n + 2)) K)) ≅ AffineSpace PUnit.{u + 1} B`; `e.hom ≫ ProjectiveLine.affineChart B` | exact |
| Geometric field and point | `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`; `s : Spec (.of Ω) ⟶ B` | exact |
| Boundary point and image | `s ≫ ProjectiveLine.infinity B`, evaluated at `IsLocalRing.closedPoint Ω` | exact |
| Strict-local ring and structural map | `strictHenselizationRing t`; `strictHenselizationStructuralMap t` | exact |
| Canonical `K`-algebras | `Hom.residueFieldAlgebraMap b (...)` and `Hom.residueFieldAlgebraMap (g ≫ b) (...)`, each `.toAlgebra` | exact |
| Common finite transcendence degree | `∃ a : ℕ, a < n + 2 ∧` followed by both `@Algebra.trdeg ... = (a : Cardinal.{u})` clauses | exact |
| Principal-open equation | `∃ h : strictHenselizationRing t`, `h ∈ @IsLocalRing.maximalIdeal ...` and `h ≠ 0` | exact |
| Pulled-back ordinary chart | `Nonempty (pullback (e.hom ≫ ProjectiveLine.affineChart B) (strictHenselizationStructuralMap t) ≅ Spec (.of (Localization.Away h)))` | exact |

The dependency declarations were opened. `strictHenselizationRing` is the chosen
affine pointed-etale coordinate colimit, and `strictHenselizationStructuralMap` is its
canonical map to the base. `ProjectiveLine.affineChart` is `[t : 1]` and
`ProjectiveLine.infinity` is `[1 : 0]`. Mathlib `Algebra.trdeg` is the supremum over
algebraically independent subsets. The local-structure dependency is the existing
`AlgebraicGeometry.strictHenselizationLocalStructure`; its existential `IsLocalRing`
proof is passed explicitly to `maximalIdeal`, with no change to the ring or hypotheses.

Edge cases are covered: `n = 0` gives `K[x₀]` and `a < 2`; `Fin (n + 1)` is nonempty;
all characteristics are allowed; generic and nonclosed base points are allowed; fields
exclude the zero ring; an empty scheme has no map from `Spec Ω`; and the shared universe
`u` for `K` and `Ω` is exactly the node's universe. The `PUnit` chart index is a
singleton in the stated universe.

I reran the duplicate searches with `msearch.py` (LeanFinder, Loogle, and LeanSearch)
for strict-local projective-line principal opens, and `rg` over Mathlib,
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, project `lean/Sheaf`, and
`dag/nodes` for strict-local-model and strictHenselization/`Localization.Away` variants.
No existing main statement was found; the exact related declaration is the compatibility
local-structure theorem now used by the dependency record.

The inherited upstream local-ring interface was unusable for this loaded colimit. I
retained the item statement, added `lem-weil-pbc-strict-henselization-local-structure`
to `stmt_deps`, rebound that dependency to the existing compatibility theorem with an
explanatory `lean.note`, and used its explicit local-ring proof in the consumer. No
statement correction, new definition node, citer audit, or helper was needed. The module
has one postponed theorem with `by sorry`, no hollow definition, no hidden `let`, no
local notation or instance, and no unbound variables. `scompile.py` passed both sandbox
and library checks.
