## Worker report

The module `lean/Sheaf/AlgebraicGeometry/EtaleInjectiveRetract.lean` states
`AlgebraicGeometry.Etale.exists_injective_retract_of_surjective`, with proof `sorry`.
It states the entire node, including the explicit splitting and the characterization of
its second component. No definition, theorem proof, new node or dependency replacement
is supplied. The original node is changed only in `lean`.

Hypotheses and objects, matched to the node:

- Schemes and the named morphism are `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  `[Surjective f]` is surjectivity on underlying points. There is no properness hypothesis.
- The arbitrary commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]`.
  Small rings, including the integers and prime fields, can be lifted into this universe;
  the coefficient universe follows the source's small-etale-site convention. No finiteness,
  characteristic or nonzero-ring hypothesis occurs.
- The ring sheaves `RV`, `RU` are lambda-bound and immediately applied to
  `(constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ)`.
  They are exactly the constant sheaves of rings, not the structure sheaves of X and Y.
  `etaV`, `etaU` are immediately applied to the corresponding `toSheafify` maps.
  These lambda parameters are reducible names, not additional hypotheses.
- The categories are `SheafOfModules.{u + 1} RV` and `SheafOfModules.{u + 1} RU`.
  This uses the general-site declaration explicitly allowed in the category dependency's
  `mathlib_match` and `lean.note`; its primary `Scheme.Modules` declaration is the
  structure-sheaf specialization and is not appropriate for this coefficient ring.
- The ring map `gamma : RV ⟶ f_* RU` is specified by the equation on every object W
  and constant section r. This is precisely the induced constant-section ring map in
  `def-weil-pbc-direct-image`. The right adjoint is the existing
  `SheafOfModules.pushforward` along `MorphismProperty.Over.pullback @Etale ⊤ f`,
  with scalars restricted along gamma. All site arguments are explicit.
- `LM` names the module inverse image; `am : LM ⊣ SheafOfModules.pushforward ... gamma`
  is its adjunction. The natural isomorphism `e` identifies its underlying abelian
  inverse image with `Etale.upperStar AddCommGrpCat f`. The following unit equation
  says that the module adjunction unit is the abelian unit under this identification.
  These are the exact functor/adjunction identification data furnished by
  `prop-weil-pbc-inverse-image-modules-exact`, not additional geometric restrictions.
  That proposition existentially supplies the choices; this theorem applies to every
  choice of the inverse image and adjunction with those specified identifications.
  There is no assumed monicity of the unit or of the conclusion.
- `I : SheafOfModules RV` with `[Injective I]` is the injective sheaf on Y.
  `J : SheafOfModules RU` is arbitrary; it is not assumed injective.
  `j : LM.obj I ⟶ J` with `[Mono j]` is exactly the given inclusion of inverse image.

Conclusions, matched clause by clause:

- The adjoint inclusion iota is written out as
  `am.unit.app I ≫ (SheafOfModules.pushforward ... gamma).map j`.
  The first conjunct is `Mono` of this precise composite.
- The existential `rho` has source the direct image of J and target I.
  The first existential conjunct is `iota ≫ rho = 𝟙 I`, the node's retraction equation.
- The existential `pi` has source the same direct image and target `kernel rho`.
  Its equation `pi ≫ kernel.ι rho = 𝟙 _ - rho ≫ iota` says that it is the factorization
  through that kernel of id minus iota-rho. Categorical composition is left-to-right
  in Lean. Since a kernel inclusion is monic, this equation specifies the induced map
  uniquely; no named well-definedness lemma or proof argument is hidden in a definition.
- `s : f_* J ≅ I ⨯ kernel rho` and `s.hom = prod.lift rho pi` give the isomorphism
  with components `(rho, pi)` itself, not just the existence of an unspecified summand.
  In an abelian category the finite product is the finite direct sum: the product,
  with the additive coprojections, is a biproduct. We use this concrete representative
  of the node's `I ⊕ ker rho` so no file-local biproduct instance is needed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules` and its category/morphisms;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian` supplies its abelian structure.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`;
  the sheafification unit is `CategoryTheory.toSheafify`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, together with
  `Scheme.Etale` in `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`,
  `Etale.lowerStar`, `Etale.upperStarLowerStarAdjunction`. Their complete signatures
  and docstrings were read; they allow every scheme morphism.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`. Its full signature and docstring
  specify gamma, LM, am, e and the unit equation used here; the proof will obtain the
  choices from this dependency. It is imported rather than duplicated.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.pushforward`, the module direct image from the preceding dependency.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`.
  Its extension property is exactly the injectivity notion needed here.
  The resolution part of the dependency is not used in this statement.

Edge cases checked before writing: the empty scheme Y (then a surjection has empty X)
causes no exception; a map from empty X onto nonempty Y is correctly excluded by
surjectivity. A zero coefficient ring, I = 0, J = 0, zero kernel, and f an identity
are all covered. J = 0 forces the mono's source to be zero, consistently with the
conclusion. A general surjective, nonproper f is included. The ring and module sizes
are large enough for the essentially small small etale site; there are no independent
small test-object universes or nonempty indexing assumptions. The maps gamma and
units are constrained by real equations, not unconstrained placeholder functors.

Searches made (no matching declaration of this whole statement was found):

- `msearch.py ... leanfinder`: "Surjective scheme morphism injective etale sheaf retract
  of pushforward of object containing its inverse image". Eight hits concerned stalk
  injectivity on topological spaces and the etale category; none states this result.
- `msearch.py ... loogle`: `CategoryTheory.Injective, CategoryTheory.Mono,
  CategoryTheory.Retract`. Zero hits.
- `msearch.py ... grep`: `retract|split|factorThru` in
  `CategoryTheory/Preadditive/Injective`. Eight hits include `Injective.factorThru`
  and `Injective.comp_factorThru`; they supply only the splitting step, not this lemma.
- `msearch.py ... leansearch`: "injective etale module sheaf retract pushforward along
  surjective morphism". Service unavailable: Internal Server Error; no verdict inferred.
- `rg` in the source SixFunctors tree for retracts, injectivity and upperStar, and
  monic units found `Etale.mono_unit_app_of_surjective` (Surjective.lean), which states
  the unit's monicity, not this entire conclusion for a given j and its explicit splitting.
- `rg` for the node id and proposed declaration name in `WeilConjectures`, `lean/Sheaf`
  and `dag/lean_names_upstream.json` found only a proof-docstring citation in
  `TorsionAbelianBaseChangeCancellation.lean`. No existing declaration matches.

The referenced literature files are not installed in this clone. The actual source was
read at https://stacks.math.columbia.edu/tag/0A4C, proof, first paragraph. That paragraph
supplies exactly the inclusion and summand argument; the node writes its stalk and
abelian-splitting details out explicitly. No node fault or statement dispute was found.

Validation: the server compile passed cleanly (3.8 seconds), with the sole theorem
proof left as `sorry`; after final formatting the delivery dry run is run as the final
check. No second-reading section is supplied by this worker.

## Second reading by E1

I independently opened the item node, its seven proof steps, all eight statement
 dependency nodes and their Lean records, the delivered module, the full
`etaleInverseImageModulesExact` module, and the upstream upper/lower-star definitions
and adjunction. I read the Stacks TeX `etale-cohomology.tex`, label `lemma-sandwich`
(Tag 0A4C), from the Stacks project's GitHub source because literature is absent
locally, and checked the rendered [Tag 0A4C](https://stacks.math.columbia.edu/tag/0A4C).
The ambient properness, prime coefficients and injectivity of J are needed elsewhere
in that source lemma, not for its first-paragraph stalk and splitting argument.
The node already explicitly generalizes that argument to arbitrary coefficients,
arbitrary J and merely surjective f; its seven-step proof justifies this generality.
There is no stage-2 statement correction or new/dependency node in this delivery.

Node-to-Lean checklist (objects, hypotheses and every conclusion):

1. Arbitrary schemes X,Y: `{X Y : Scheme.{u}}`. PASS. The named map is
   `(f : X ⟶ Y)` and point-surjectivity is `[Surjective f]`. I opened the Mathlib
   class in `Morphisms/UnderlyingMap.lean`: its field is `Function.Surjective f`.
   No proper, Noetherian, separated, finite-type or etale hypothesis on f. PASS.
2. A commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ]`.
   No field, prime, characteristic, nonzero or finite-ring restriction. PASS.
3. The small etale sites: `X.smallEtaleTopology` and `Y.smallEtaleTopology`.
   I read `Sites/Etale.lean`, including the jointly-surjective-cover criterion.
   These are the node's sites, not the Zariski or big etale sites. PASS.
4. Constant sheaves of rings and their module categories: RV and RU are immediately
   applied lambda names, and categories are `SheafOfModules.{u + 1} RV/RU`.
   I read `SheafOfModules` and its Hom, `toSheaf` and Abelian instance. The general
   site form is explicitly authorized in the category node's mathlib_match and note;
   `Scheme.Modules` alone would instead mean structure-sheaf modules. PASS after
   the concrete coefficient-object repair described below.
5. Direct image: `SheafOfModules.pushforward` uses precisely the base-change functor
   `MorphismProperty.Over.pullback @Etale ⊤ f`; its sectionwise definition was opened.
   The quantified gamma is constrained on every constant section by the eta equation,
   exactly the ring map in the direct-image node. This determines the induced map by
   the universal property of constant-sheaf sheafification. PASS.
6. Inverse image and its adjunction: `LM`, `am : LM ⊣ pushforward gamma`, and the
   natural isomorphism `e` to `Etale.upperStar AddCommGrpCat f` after forgetting.
   The unit equation agrees verbatim in form with the final unit clause of
   `etaleInverseImageModulesExact`. The dependency supplies these data; they are
   identifications of the named inverse image, not extra geometric hypotheses.
   Its functor uses the same base-change site functor for every f. PASS after repair.
7. Injective I on Y: `(I : SheafOfModules RV) [Injective I]`.
   I opened `CategoryTheory.Injective`, whose extension property is the node's notion.
   Arbitrary J on X: `(J : SheafOfModules RU)` with no `[Injective J]`.
   Given inclusion: `(j : LM.obj I ⟶ J) [Mono j]`. PASS.
8. The precise adjoint iota: `am.unit.app I ≫ (pushforward gamma).map j`.
   Its monicity is the first conjunct. No monicity of the unit is assumed. PASS.
9. Retraction: existential `rho : (pushforward gamma).obj J ⟶ I` and
   `iota ≫ rho = 𝟙 I`. This is rho composed with iota in ordinary notation. PASS.
10. Kernel projection: existential `pi : (pushforward gamma).obj J ⟶ kernel rho`,
    with `pi ≫ kernel.ι rho = 𝟙 _ - rho ≫ iota`.
    This is exactly factorization of id minus iota-rho; uniqueness follows from
    the monic kernel inclusion, so an extra uniqueness clause is unnecessary. PASS.
11. Explicit direct-summand isomorphism: existential
    `s : (pushforward gamma).obj J ≅ I ⨯ kernel rho`, with
    `s.hom = prod.lift rho pi`. The finite product in this abelian category is the
    binary direct sum, and its two projections fix the stated components.
    The existential order rho, pi, s is correct: the latter objects depend on rho.
    No weaker unnamed summand conclusion is substituted. PASS.

Mismatch found and repair: the original four closing lambda arguments sheafified
`RingCat.of Λ` directly in RingCat, whereas the exact-module-inverse-image dependency
uses the constant CommRingCat sheaves followed by `sheafCompose ... (forget₂
CommRingCat RingCat)`. Those are isomorphic realizations but not the same supplied
objects; the worker report's claim of direct compatibility omitted this distinction.
I replaced only these four arguments: RV/RU now forget the constant commutative ring
sheaves, and etaV/etaU are `Functor.whiskerRight` of their commutative-ring
sheafification units. This makes the categories exactly the dependency's categories;
its forgotten gamma, LM, am, e and unit clause now fit directly, without an unrecorded
comparison. I clarified the declaration docstring and regenerated `lean.statement`
verbatim from the signature. The mathematical node, all binders, all conclusions,
all dependencies and the seven-step proof were left intact. The worker report above
is retained as history; its direct-RingCat descriptions are superseded by this section.

Edge cases: empty Y forces empty X for any map to Y; both empty schemes are allowed.
Empty X mapping onto nonempty Y is correctly excluded. Zero coefficient ring,
I = 0, J = 0, zero kernel and identity f are allowed; if J = 0, the given mono forces
its inverse-image source to vanish, consistently with surjectivity and I vanishing.
Nonproper surjections are covered. No degree n or indexing family is present, so
n = 0 and empty indexing sets introduce no omitted case. There is no restriction on
characteristic. The single bound universe u and coefficient/module universe u+1
follow the essentially-small etale-site convention of the dependency and upstream;
smaller coefficient rings can be lifted, and u can be raised for larger rings.
There are no independently undersized test universes or unbound variables.

Independent searches used different wording from the first reader:

- LeanFinder via msearch: `etale sheaf injective splitting of adjoint inclusion along
  a surjection`. Eight hits on locally injective sheaf morphisms and sheafification;
  none states this adjoint/retraction/specific-kernel-splitting result.
- Loogle via msearch: `CategoryTheory.Injective, CategoryTheory.Limits.kernel`.
  Zero hits.
- LeanSearch via msearch: `injective sheaf splits off a direct image under a
  surjective scheme map`. Service unavailable (Internal Server Error), recorded
  without an absence verdict.
- Independent rg in project Lean, source SixFunctors and Mathlib injective modules
  for summands, injective splitting, `injective_retract`, `retract_of_surjective`,
  the blueprint id and the proposed full name. No existing declaration of the
  complete result. I opened upstream `UpperLowerStar/Surjective.lean`:
  `mono_unit_app_of_surjective` is only the unit-monicity step and uses sheaves valued
  in ModuleCat, not this entire constant-ring-module retract conclusion.
  Mathlib `Injective.factorThru` and `comp_factorThru` give only the retraction step;
  `Retract.injective` is the converse inheritance property. The only project citation
  of the id is in the proof docstring of TorsionAbelianBaseChangeCancellation.

H5/H6/H8/H9 review: no definitions or hidden data sorries, one named theorem with
proof `by sorry`, no theorem proved. Source and blueprint docstrings are present;
all seven proof steps, their dependency names and the final explicit kernel splitting
are carried in the theorem docstring. No private definitions, local notation or
instances. Imports are used for the chosen inverse-image data, the Abelian structure
and injectivity. The signature has no let/show binders; all variables and u are bound.
Every module line is at most 100 characters. No missing dependency module or notion
was found; the sole repair aligns concrete realizations of an existing notion.

Validation: scompile of the repaired module passed cleanly on the server in 3.6 s.
The sole proof remains sorry. Signature equality and the line-length bound were
checked mechanically in addition to the binder review above.
