## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility` states
`AlgebraicGeometry.Etale.etaleSupportMapCompatibility`, with a single `sorry` proof.
It also constructs two auxiliary maps, with real data:
`etaleSupportExactUpperTensorIso` transports the existing derived pullback tensor comparison
through the canonical comparison with termwise exact inverse image, and
`etaleSupportSumProjectionReverse` is the projection mate for the existing exact derived
sum-extension/evaluation adjunction. These are helpers belonging to this node, recorded in
`lean.declarations`; neither introduces a second tensor, pullback, or sum-extension functor.

The theorem simultaneously gives the graph-normalized sheaf comparison `a`, the derived
comparison `n`, and the sum projection isomorphism `p`. Their types and equations specify
canonical comparisons, rather than an arbitrary equivalence. There is no chosen object extracted
from a mere existence theorem. The graph condition specifies `a` inside direct image; the
homotopy condition then determines `n` on every representative. These are exactly the inverse
comparison and canonical proper-support identification of
`quasifiniteCompactSupportExact`, Steps 3 and 7. The sum projection is fixed by the equation
`(p e).inv = etaleSupportSumProjectionReverse A e`.

Hypothesis and clause correspondence:

- A finite commutative ring: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  This is the existing coefficient size convention for `Scheme.{u}` small etale sites;
  it imposes no characteristic or invertibility assumption.
- Schemes and maps: `{V T : Scheme.{u}} (e : V ⟶ T)`.
- Noetherian schemes: `[IsLocallyNoetherian V] [CompactSpace V]` and the analogous pair
  for T. Mathlib's `IsNoetherian` extends exactly these two properties. The equivalence
  with a finite affine cover by spectra of Noetherian rings is
  `isNoetherian_iff_of_finite_affine_openCover`. Splitting the class lets typeclass
  synthesis derive both properties on the pulled-back source without adding assumptions.
- Separated, etale, finite type: `[IsSeparated e] [Etale e] [LocallyOfFiniteType e]
  [QuasiCompact e]`. The last two are precisely finite type in the recorded definition.
- Every chosen compactification: `(c : Compactification e)`; its fields are the actual
  open immersion `c.i`, proper part `c.g`, and factorization `c.comm`.
- Ordinary unbounded constant-A module categories: every derived category is
  `DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))` or its T analogue.
  No boundedness, constructibility, Tor amplitude, or torsion-cohomology binder occurs.
- Exact inverse image: `(upperStar (ModuleCat A) e).mapDerivedCategory`.
  Tensor is the dependency's `derivedTensor (ModuleCat A) V`.
- `F_e^c = Rr_* Dj_!`: `rightDerivedLowerShriekOfCompactification (ModuleCat A) c`.
  `S_e`: `(etaleLowerShriek (ModuleCat A) e inferInstance).mapDerivedCategory`.
- The degree-zero comparison: `a e c` is a natural transformation from sum extension
  to `openImmersionLowerShriek ... c.i ⋙ lowerStar ... c.g`, with `IsIso (a e c)`.
  Its equation after `compactificationSheafToDirectImage` is precisely
  `etaleLowerShriekToLowerStar`, the Tag 0F4L graph-extension map. Thus a summand is
  extended with its given value on its graph and zero off it. This uses the inclusion
  into direct image, not an objectwise identification of sheaf sections with a direct sum.
- On all complexes: `(n e c).inv.app (DerivedCategory.Qh.obj P)` is exactly
  `compactSupportComparisonOnHomotopy A e c (a e c) P`. The latter applies `a` termwise
  and then the total-derived-direct-image unit. All homotopy representatives are quantified.
- The specified sum projection: `p e` is an isomorphism of bifunctors from
  `S_e(-) tensor K` to `S_e(- tensor D(e^*)K)`. Its inverse is the projection mate of
  the canonical sum adjunction and the exact pullback tensor comparison. The mate's
  transpose is the unit inclusion in the same summand, tensored with restriction of K.
  Consequently its inverse is exactly `(s,m) tensor k ↦ (s,m tensor s^*k)`; this
  characterization fixes the whole natural transformation, including its derived descent.
- Arbitrary base change: `(g : T' ⟶ T)` has no separatedness, finite-type, flatness,
  smoothness, or etaleness hypothesis. T' has only the same Noetherian hypotheses.
  The pulled-back map is `pullback.fst g e`, the source projection is
  `pullback.snd g e`, and the compactification is
  `c.ofIsPullback (IsPullback.of_hasPullback g e).flip`.
- Clause (1): the entire third conjunction is the equality of natural transformations
  `exactCompactSupportExchange A c g ≫ whiskerLeft h^* (n e' c').hom =
  whiskerRight (n e c).hom g^* ≫ (exactEtaleSumExchange A e g).hom`.
  The two existing exchange helpers use the specified inverse conjugate sum-extension
  base-change map, and the proper adjunction-mate exchange with its canonical exactness
  transport. Their source and docstrings identify them with the C and b of the node.
- Clause (2): the fourth conjunction quantifies every M and K. Its left side is
  `projectionMapOfCompactification ... c`, the composite of the actual counit-defined
  proper projection, inverse open-extension tensor comparison, and pullback composition,
  followed by `(n e c).hom`. The displayed application of
  `leftDerivedUpperStarIsoMapDerivedCategory` transports its output from the upstream
  `L(e^*)` notation to the node's exact `D(e^*)` notation. Its right side is tensoring
  `(n e c).hom.app M` with the identity on K, followed by `(p e).hom`.
  Quantification in both variables gives equality of derived natural transformations;
  no comparison is asserted merely on cohomology or stalks.
- Every compactification and refinement: c has no finiteness condition on `c.g`.
  The final conjunction quantifies `c d` and an actual `c.Refinement d`, and gives
  `(rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫ (n e d).hom = (n e c).hom`.
  Substitution of this equality in the two compatibility identities is precisely their
  agreement under proper-refinement identifications.

Dependency declarations used (full namespaces are AlgebraicGeometry or
AlgebraicGeometry.Etale unless indicated):

| Node | Module and declarations |
| --- | --- |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme: Scheme and Scheme.Hom |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper: IsProper, IsSeparated |
| def-weil-etale-morphism | Mathlib.AlgebraicGeometry.Morphisms.Etale: Etale |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType; Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact |
| def-weil-compactifications-refinements | WeilConjectures.Compactification.Refinement: Compactification.Refinement, Compactification.category; WeilConjectures.Compactification.Defs: Compactification |
| def-weil-pbc-noetherian-ring | Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing; Mathlib.AlgebraicGeometry.Noetherian: IsLocallyNoetherian, IsNoetherian, isNoetherian_iff_of_finite_affine_openCover |
| def-weil-pbc-derived-categories | Sheaf.AlgebraicGeometry.DerivedCategories and WeilConjectures.SixFunctors.Etale.Derived.Coefficients: DerivedCategoryModule and CategoryTheory.DerivedCategory |
| prop-weil-pbc-inverse-image-modules-exact | Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact: etaleInverseImageModulesExact; WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs: upperStar |
| def-kun-derived-tensor | WeilConjectures.SixFunctors.Etale.Derived.Tensor: derivedTensor |
| def-amb-etale-compact-support | WeilConjectures.SixFunctors.Etale.Derived.LowerShriek: rightDerivedLowerShriekOfCompactification |
| def-weil-pbc-etale-sum-extension | WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap: etaleLowerShriek, etaleLowerShriekUpperStarAdjunction, preservesFiniteLimits_etaleLowerShriek |
| lem-amb-etale-adjoint-locality | Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality: derivedEtaleLowerShriekUpperStarAdjunction; the same adjunction is constructed from the upstream sheaf adjunction via CategoryTheory.Adjunction.mapDerivedCategoryAdjunction |
| lem-sfb-quasifinite-compact-support-exact | Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact: quasifiniteCompactSupportExact; canonical graph comparison and proper-refinement characterization |
| def-weil-pbc-etale-shriek-base-change-map | WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap: etaleLowerShriekBaseChangeMap |
| lem-weil-pbc-etale-shriek-base-change-modules | WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules: isIso_etaleLowerShriekBaseChangeMap |
| def-kun-unbounded-exchange | Sheaf.AlgebraicGeometry.ExactUnboundedExchange: exactDerivedBaseChangeMap, exactDerivedSquareUpperStarIso |
| def-kun-projection-formula-map | WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection: rightDerivedLowerStarProjectionMap; WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection: projectionMapOfCompactification |
| lem-pur-etale-open-derived-tensor | WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection: derivedOpenImmersionLowerShriekProjectionIso |
| lem-asd-etale-compact-support-normalization | Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization: compactificationSheafToDirectImage, compactSupportComparisonOnHomotopy, exactCompactSupportExchange, exactEtaleSumExchange |

The final dependency was already landed and is added to stmt_deps to reuse its canonical
helper maps. Its stronger bundled normalization structure is not used as a hypothesis or
chosen by a Nonempty choice. No dependency record or node statement was changed.

The old comparison helper module transitively imports the Sheaf versions of the two
base-change-map modules. Directly adding their newer WeilConjectures versions produced an
actual duplicate-declaration import failure. I removed the two direct newer imports, retaining
the single existing declarations through the required comparison module; I did not copy or
redefine either map. All other recorded statement modules and the stated proof-dependency
modules are imported, with proof-only imports non-public.

Edge cases checked before stating: V empty or an empty geometric fibre (zero sums and zero
maps); A the zero ring (only zero modules, no nontriviality binder); e the identity (unit and
counit projection normalizations); a finite etale fold map (distribution over the same
summands); an open immersion (the existing open projection mate); arbitrary nonfinite proper
parts of compactifications; arbitrary identity, nonflat or non-finite-type changes of base
with Noetherian source; unbounded M and K. All survive the binders and the exactness transport.
No disputed mathematical statement was found.

Searches made:

- msearch.py leanfinder: "etale compact support proper support comparison commutes with
  base change and projection formula"; eight unrelated Mathlib hits, no such compatibility.
- msearch.py loogle: "etaleLowerShriek, rightDerivedLowerShriekOfCompactification,
  rightDerivedLowerStarProjectionMap"; zero hits, unknown upstream identifier.
- msearch.py leansearch: "Derived projection formula for extension by zero along an etale
  morphism of schemes"; eight hits (scheme etaleness and unrelated zero extension), no match.
- msearch.py grep: `etaleLowerShriek.*[Pp]rojection|[Pp]rojection.*etaleLowerShriek`;
  zero Mathlib hits.
- rg over WeilConjectures and lean/Sheaf: proper-support compatibility, etale sum tensor,
  sum projection, exact upper tensor, and the item id. Existing normalization and ordinary
  compact-support projection helpers were found and read; no existing theorem included the
  required projection compatibility. Direct searches for all three proposed declaration
  names, including dag/lean_names_upstream.json, found no collisions.
- Read the dependency declarations and their source/docstrings, including the current live
  base-change-map/module theorem through `scompile.py --source`; the local old source tree
  does not contain these newer upstream paths. Read Stacks 0F4L, 0GKF and 0GL5 from the local
  TeX and the recorded graph/derived comparison proof in quasifiniteCompactSupportExact.

Validation: scompile.py compiled the delivered module separately both at its sandbox path
and its library module path, cleanly (4.1 s and 5.1 s in the final successful run before the
node/report packaging). Every universe and binder is explicit, with autoImplicit false;
all lines are at most 100 characters. The only postponed proof is the node's own theorem,
with the eight-step natural-language proof in its docstring. No data definition uses sorry.

## Earlier second reading (a previous round; superseded)

I reread the node statement, its Stacks source places, every recorded statement dependency,
and the worker module. The item-by-item correspondence is:

- `A : Type (u + 1)` with `[CommRing A] [Finite A]` is the finite commutative coefficient ring;
  no characteristic or invertibility assumption is added.
- `V T : Scheme.{u}` and `e : V ⟶ T` are the source, target, and morphism. The binders
  `[IsLocallyNoetherian] [CompactSpace]` on both schemes are exactly Mathlib's two fields of
  `IsNoetherian`; `[Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]` is the
  recorded finite-type separated etale package.
- `c : Compactification e` is the chosen open/proper factorization. Its actual `c.i`, `c.g`,
  and `c.comm` are used; no finiteness condition on the proper part is introduced.
- The first existential `a` has the degree-zero sum-extension to direct-image type. Its
  `IsIso` clause and `compactificationSheafToDirectImage` equation are the graph-normalized
  comparison of Tags 0F4L and 0F4Y.
- The second existential `n` has the compactification derived functor to derived sum-extension
  type. Its inverse is fixed on every homotopy representative by
  `compactSupportComparisonOnHomotopy` and `a`, rather than by an arbitrary isomorphism.
- The third existential `p` has the derived sum-extension projection-formula bifunctor type;
  `(p e).inv = etaleSupportSumProjectionReverse A e` fixes its canonical mate normalization.
- The first final clause quantifies arbitrary Noetherian `T'` and arbitrary `g : T' ⟶ T`, forms
  the pullback morphism and pulled-back compactification, and states the exact exchange identity
  with `exactCompactSupportExchange` and `exactEtaleSumExchange`. No flatness, etaleness,
  separatedness, or finite-type hypothesis on `g` appears.
- The second final clause quantifies all derived `M` and `K` and states the full morphism-level
  projection identity, including the explicit `leftDerivedUpperStarIsoMapDerivedCategory`
  transport. It is not weakened to cohomology or stalks.
- The final clause quantifies every pair of compactifications and every actual refinement and
  states compatibility with `rightDerivedLowerShriekOfCompactificationIso`.

The Stacks tags were checked directly: 0F4L gives the graph open-and-closed zero extension,
0F4Y identifies it with separated etale proper-support sections, 0GKM gives the compactification
derived comparison, 0F7L/03S6 give arbitrary base-change compatibility, and 0GKF/0GL5 give the
projection formula and its derived compactification form. Their hypotheses are compatible with
the node's Noetherian, separated finite-type etale specialization. The recorded declarations
for compactifications, Noetherian schemes, derived categories, exact inverse image, tensor,
sum extension, exchange, projection, and open-immersion tensor were opened and match the uses.

Edge cases checked: empty `V` or empty fibres (zero sums and zero maps), the zero coefficient
ring, `e = 𝟙`, a finite etale fold map, an open immersion, nonfinite proper parts of a chosen
compactification, arbitrary identity/nonflat/non-finite-type base change, and unbounded inputs.
All are admitted by the binders and the stated equations.

Searches were repeated with `msearch.py` LeanFinder, Loogle, LeanSearch, grep over Mathlib,
`WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`. They found only the
already-recorded lower-shriek, tensor, graph, exchange, and normalization helpers; no existing
declaration of this compatibility or either auxiliary declaration exists. No repair note applies,
no new definition or dependency module is needed, and no citer is invalidated. I found no
mismatch and made no statement or module changes. The theorem signature in the node's `lean`
record is byte-for-byte equal to the source theorem signature.

The required `scompile.py` check passed for the sandbox and library paths (4.1 s and 4.8 s),
with only the theorem's permitted `sorry`.

## Second reading by N5

I read the node statement, its proof steps, the Stacks source places 0F4L, 0F4Y, 0GKM,
0F7L, 0GKF, 0GL5 and 03S6, and every declaration in the statement-dependency list. The
item-by-item rendering in `EtaleSupportMapCompatibility.lean` is:

- The finite coefficient ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`; no
  characteristic, torsion, or invertibility assumption is added.
- `V T : Scheme.{u}` and `e : V ⟶ T` are the source, target, and separated etale finite-type
  morphism, with exactly the two Noetherian fields on each scheme.
- `c : Compactification e` supplies the open immersion `c.i`, proper map `c.g`, and factorization;
  no finiteness condition on `c.g` is added.
- `a` is the degree-zero sum-extension-to-direct-image map. `IsIso (a e c)` and the
  `compactificationSheafToDirectImage` equation give the graph extension by zero.
- `n` is the unbounded derived comparison. Its inverse is fixed on every homotopy representative
  by `compactSupportComparisonOnHomotopy`, so it is the specified comparison rather than an
  arbitrary isomorphism.
- `p` has the derived sum-extension projection-formula type, and its inverse is exactly the
  canonical adjunction mate `etaleSupportSumProjectionReverse`.
- The base-change clause quantifies Noetherian `T'` and arbitrary `g : T' ⟶ T`, forms the
  pullback morphism and pulled-back compactification, and states the full natural-transformation
  exchange identity. No hypothesis on `g` is introduced.
- The projection clause quantifies all unbounded derived `M` and `K` and states the full
  morphism-level identity with the explicit exact inverse-image transport.
- The final clause quantifies all compactifications and actual refinements and gives the
  proper-refinement comparison equation.

The source hypotheses and all conclusion clauses match these binders and equations. Empty
schemes and fibres, the zero coefficient ring, `e = 𝟙`, finite etale fold maps, open immersions,
nonfinite proper parts, arbitrary identity/nonflat base change, and unbounded inputs remain in
scope. I found no false or ambiguous clause and no need for `statement_change`.

The required Mathlib, project, upstream-name, LeanFinder/Loogle/LeanSearch, and grep searches
found no existing compatibility theorem or duplicate auxiliary declarations. The normalization
helpers used by the module are supplied by `lem-asd-etale-compact-support-normalization`; that
dependency is present in the sandbox node and is imported directly. I checked its declarations
against their node and source docstrings. No repair note applies, and no citer is invalidated.

The only delivery-level discrepancy was that the shared base DAG snapshot predates the added
normalization dependency; the sandbox node correctly records it because the statement uses
`compactificationSheafToDirectImage`, `compactSupportComparisonOnHomotopy`,
`exactCompactSupportExchange`, and `exactEtaleSumExchange`. I retained the worker's canonical
helpers and made no duplicate definitions or weaker replacements. The node's `lean.statement`
is verbatim equal to the theorem signature. `scompile.py` compiles the module in both sandbox
and library paths with only the permitted theorem `sorry`.
