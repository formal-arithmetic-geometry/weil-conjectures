## Worker report

This repairs the returned stage-1-only packet at 1153a99cd0cd. The delivery is now the
stage-2 module `Sheaf.AlgebraicGeometry.ShriekTensorComposition`, its node record, and this
report. The node differs from the current shared node only in `lean` and the added landed
statement dependency `lem-kun-tensor-sym`. In particular the original `split_report.date`
and `split_report.summary` are retained verbatim, repairing H2. No statement correction,
new independent definition node, or dependency-interface repair is necessary.

The module contains two real helper constructions and two postponed theorems, all owned
by `lem-amb-shriek-tensor-composition` and listed in `lean.declarations`:

- `AlgebraicGeometry.Etale.compactSupportProjectionMapOfCompactification` is the
  coefficient-first canonical projection map on any compactification `c`.
- `AlgebraicGeometry.Etale.compactSupportProjectionMap` specializes that map to
  `HasCompactification.compactification f`, exactly as the existing `rightDerivedLowerShriek`
  specializes `rightDerivedLowerShriekOfCompactification`.
- `AlgebraicGeometry.Etale.compactSupportProjectionMap_comp` states the displayed composition
  identity and, as its second conjunct, the equivalent inverse identity whenever the three
  projection maps are invertible.
- `AlgebraicGeometry.Etale.compactSupportProjectionMap_comparison` is the refinement clause:
  tensor projection commutes with the canonical comparison between any two compactifications.

The helpers only compose the existing projection construction, the canonical Koszul
symmetry, and the exact-pullback comparison. Their data have no `sorry`, and they choose no
arbitrary map or unrelated natural isomorphism. Each theorem has proof `by sorry`. Its
docstring gives the source and natural-language proof; the main theorem retains all fourteen
DAG proof steps, including the noncartesian clopen-section argument.

Hypothesis and clause matching (Lean composition `a ≫ b` means first `a`, then `b`):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Finite commutative ring A | `(A : Type (u + 1)) [CommRing A] [Finite A]` on both theorems. The helper construction itself works for any commutative ring. |
| Small etale sites, ordinary unbounded D(T_et,A) | `DerivedCategoryModule A T`, the recorded abbreviation for `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))`. No D-plus, bounded, constructible, or completed category appears. |
| Exact constant-coefficient inverse image | `(upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory`; `leftDerivedUpperStarIsoMapDerivedCategory` canonically converts the existing projection map's Lf-star endpoint to this exact termwise functor. |
| Ordinary derived tensor | The recorded `derivedTensor (ModuleCat.{u + 1} A) T`, acting on objects and morphisms through its two functor variables. |
| All schemes Noetherian | `[IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]`; Mathlib's finite affine Noetherian-cover equivalence identifies this with the node's definition. Proper compactification ambients are then Noetherian as well. |
| X to Y to Z | `(f : X ⟶ Y) (g : Y ⟶ Z)`; the composite is `f ≫ g`. |
| Separated finite-type morphisms | `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` and the same for g. Their composite has these properties by the existing instances; none is added as an independent hypothesis. |
| Compactifiable morphisms | `[HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]`, retaining the compactification data needed by every occurrence of R-shriek. The composite is compactifiable under the stated Noetherian separated finite-type hypotheses. |
| Arbitrary unbounded M and K | `(M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Z)`; no other condition is imposed on either. |
| P has source Q tensor Ra_!B | The helper source is `((derivedTensor ... Y).obj K).obj ((rightDerivedLowerShriekOfCompactification ... c).obj M)`. |
| P is the actual proper/open tensor map | Its middle factor is `((projectionMapOfCompactification ... c).app M).app K`. Opening its definition shows precisely `rightDerivedLowerStarProjectionMap` followed by the inverse `derivedOpenImmersionLowerShriekProjectionIso` and the canonical compactification pullback compositor. |
| P has target Ra_!(a-star Q tensor B) | The helper target has `((derivedTensor ... X).obj (D(a-star).obj K)).obj M` inside the same R-shriek functor. The two existing signed symmetries put both endpoints in this order. |
| alpha is the proper/open tower-normalized compositor | The exact recorded `unboundedEtaleLowerShriekCompIso A f g`, which is assembled from the proper/open tower and canonical compactification comparisons; no bare Nonempty iso is chosen. |
| Left route alpha after Rg_!(P_f) after P_g | The first conjunct starts with `compactSupportProjectionMap A g (Rf_!.obj M) K`, then `(rightDerivedLowerShriek ... g).map (compactSupportProjectionMap A f M (D(g-star).obj K))`, then `alpha.hom.app (f-star(g-star K) tensor M)`. |
| Right route P_gf after 1_K tensor alpha | The first conjunct's right side starts with `((derivedTensor ... Z).obj K).map (alpha.hom.app M)`, then `compactSupportProjectionMap A (f ≫ g) M K`. |
| Under (gf)-star K = f-star g-star K | The final right-side factor is R(gf)_! of tensoring `unboundedEtaleUpperStarCompIso A f g` with the identity of M. Thus both routes end at R(gf)_!(f-star g-star K tensor M). This is the canonical identification in the node, explicitly inserted rather than assumed to be definitional equality. |
| Proper/open interchange and refinements | The main identity uses the recorded normalized alpha, whose `unboundedEtaleLowerShriekCompIso_tower` computes it on every compatible proper/open tower. The comparison theorem states `tensor(1,rho_M) ≫ P_d = P_c ≫ rho_(f-star K tensor M)` for every c,d, hence for every proper refinement and common-refinement comparison, without a cartesian or density hypothesis. Together these give the same identity on any chosen tower. |
| Equivalent identity for inverses | The second conjunct quantifies over `IsIso` for P_g, P_f, and P_gf. Its left side is `alpha.inv ≫ Rg_!(inv P_f) ≫ inv P_g`; its right side is R(gf)_! of the inverse pullback identification, then `inv P_gf`, then tensor K of `alpha.inv`. No invertibility assumption is used in the first conjunct. |
| Whole categories, no bounds or finite Tor amplitude | There is no cohomology bound, flatness, perfection, Tor-amplitude, constructibility, field, characteristic, or invertible-cardinality binder. |

Recorded dependencies and declarations read and used:

- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`
  and the recorded `DerivedCategoryModule` in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `prop-weil-pbc-inverse-image-modules-exact`:
  `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact.etaleInverseImageModulesExact`
  (declaration namespace `AlgebraicGeometry`). Its current server source was read with
  `scompile.py --source`, since the recorded upstream module is newer than the local checkout.
  The exact functor used in the formula is the recorded ModuleCat-valued `Etale.upperStar`.
- `def-kun-derived-tensor`: `WeilConjectures.SixFunctors.Etale.Derived.Tensor`,
  `AlgebraicGeometry.Etale.derivedTensor`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and its
  morphisms. `IsNoetherian` is the standard Mathlib condition; scheme morphism properties
  use the declarations named by the convention node `def-weil-scheme-morphism-properties`.
- `def-amb-etale-compact-support`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `rightDerivedLowerShriekOfCompactification` and `rightDerivedLowerShriek`.
- `lem-amb-unbounded-compact-support-comparisons`:
  `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`,
  `unboundedEtaleLowerShriekCompIso`, its `_tower` normalization, and
  `unboundedEtaleUpperStarCompIso`; canonical comparisons are the existing
  `rightDerivedLowerShriekOfCompactificationIso` used by that package.
- `lem-weil-pbc-ringed-slice-extension-tensor`:
  `Sheaf.CategoryTheory.RingedSliceExtensionTensor`,
  `SheafOfModules.ringedSlice_extension_tensor`, retained as the proof dependency fixing
  the underived extension-tensor normalization. The derived open factor uses the recorded
  `derivedOpenImmersionLowerShriekProjectionIso` of `lem-pur-etale-open-derived-tensor`.
- `def-kun-projection-formula-map`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`,
  `rightDerivedLowerStarProjectionMap`, used inside the existing compactification projection.
- Added landed dependency `lem-kun-tensor-sym`:
  `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`, `derivedTensorSymmetry`, the
  canonical braiding descended from the signed complex braiding, with actual data.

The stated proof-dependency modules are imported without `public` when only the proof uses
those modules: ambient adjoint locality, unbounded proper/open interchange, extension-zero
composition, ringed projection composition, clopen product, exact-functor derivation,
proper-open section geometry, K-injective preservation, exchange/tensor coherence, and
ringed derived pushforward composition. The two Mathlib leaves are localization's
universal property and stability of properness under pullback, available through those imports.
No dependency's recorded interface needs replacing.

Searches made in this repair:

- `msearch.py leanfinder`: "compact support derived tensor projection map commutes with
  composition proper open compactification unbounded etale". Eight hits, including scheme
  pullback coordinate identities, compactly supported continuous-map composition, and
  light-condensed tensor results; none is the node's etale compact-support identity.
- `msearch.py leansearch`: "compact support tensor projection formula compatible with
  composition of unbounded etale derived direct images". Eight hits about continuous-map
  support, tensor elements, and scheme pullback coordinates; none matches.
- `msearch.py loogle`: `CategoryTheory.Adjunction.comp`. Twelve hits on generic adjunction
  composition and its units/counits, not compact-support tensor composition.
- `msearch.py grep`: `lowerShriek|compactSupport|projectionFormula`, subdirectory
  `AlgebraicGeometry`: zero Mathlib hits.
- `rg` over the upstream WeilConjectures sources, shared `lean/Sheaf`, and
  `dag/lean_names_upstream.json`, for projection/shriek composition and the item id.
  No exact composition theorem was found. The existing `LowerShriekProjection` construction
  was found, opened, and reused. The upstream `projectionMapOfCompactification_comparison`
  requires a cartesian refinement square; it does not supply the node's noncartesian
  refinement clause. Generic proper projection composition and base-change projection
  coherence are proof tools, not existing renderings of this combined node.

Edge cases: the empty schemes, identity maps, empty or extra components of a compactification,
zero M or K, the zero finite ring, nonsemisimple finite rings such as Z/4, unbounded objects,
and objects of infinite Tor amplitude are admitted by the Lean types. In particular no
cartesian refinement assumption, dense-open assumption, or automatic projection-isomorphism
assumption has entered the forward identity. The inverse clause has exactly its conditional
invertibility assumptions. The explicit pullback compositor also retains the identity-map
case rather than identifying distinct functor constructions by definitional equality.

Validation: `scompile.py` compiled the module as a sandbox and as its library module, with no
errors or warnings. Both definitions contain only existing canonical data; both theorem
proofs are `sorry`. All universes and variables are explicit (`autoImplicit false`), lines
are at most 100 characters, and no local notation, private copy, extra axiom, or local instance
is introduced. The final dry-run and push are performed after this report is written.

## Second reading by NL

This is the author's second reading, not a claim that another agent performed an independent
review: this repair brief forbids starting agents, and the maintainer performs the independent
stage-2 review of the immutable delivery. I reopened the node and final module and checked
each binder and each clause in the table above.

The checks that determined the final rendering were: K is on Z, M on X; P_g must be applied
first, followed by Rg_! of P_f, followed by alpha; alpha is evaluated on the iterated pullback
tensor M; the opposite route needs the canonical `(gf)-star` to `f-star g-star` identification;
the same identification must be inverted in the inverse square; and both input and output
tensor factors must be exchanged when reusing the source library's right-factor projection.
The final module implements all five details. The inverse equation is the reverse of the
forward square, including its terminal identification. The comparison clause uses arbitrary
c,d and the same canonical rho as the comparison dependency, so it retains the noncartesian
refinement case. The forward equation does not assume any P is invertible.

H1 is repaired by the new module, four-declaration lean record, and actual Worker report.
H2 is repaired by restoring the original split_report fields. H8 is repaired by source and
blueprint docstrings and the full fourteen-step proof. H10 is checked by clean per-file
compilation. H11 is addressed by this binder/arrow/edge-case reading and the explicit mapping
above. No node statement, proof, or proof dependency was changed.
