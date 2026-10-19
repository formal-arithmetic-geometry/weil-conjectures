## Worker report

Existing declaration: `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso`
in `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`
(upstream `slopmaster2`, source lines 147–156). No new module or definition is delivered.
The source declaration and its surrounding variables, abbreviations, map definition,
and docstrings were read. It is an isomorphism of bifunctors on the ordinary **unbounded**
small étale derived categories, constructed as `asIso` of the canonical projection mate.
It supplies exactly this node after specializing the coefficient category, reversing the
isomorphism, and using the canonical exactness identification of inverse image below.

Source checked: Stacks `sites-cohomology.tex`, `lemma-j-shriek-and-tensor`, Tag 0GL1,
lines 4577–4588, and `sites-modules.tex`, same label, Tag 0E8I, lines 4050–4089.
The former explicitly allows arbitrary objects of the two unbounded derived categories;
its proof uses a K-flat model for the ambient complex and the latter sheaf tensor identity.
There is no repair note for this item and no `blueprint_update` on its node.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean specialization and interpretation |
| --- | --- |
| Commutative ring `C` | `C : Type (u + 1)` and `[CommRing C]`, with coefficient category `ModuleCat.{u + 1} C`. |
| Schemes and open immersion `j : U → T` | `{U T : Scheme.{u}}`, `(j : U ⟶ T)`, `[IsOpenImmersion j]`. |
| Ordinary unbounded `D(U_et,C)` and `D(T_et,C)` | `DerivedCategoryModule C U` and `DerivedCategoryModule C T`, definitionally `DerivedCategory (Sheaf _.smallEtaleTopology (ModuleCat.{u + 1} C))`. This is exactly the recorded encoding of `def-weil-pbc-derived-categories`. |
| Every `K` and `M` | Arbitrary objects of these derived categories; neither object has any property binder. |
| Termwise extension by zero | `(openImmersionLowerShriek (ModuleCat.{u + 1} C) j).mapDerivedCategory`; `D((j)_!open[A])` is the source's scoped notation for this same functor. The underived functor is the declaration recorded by `def-weil-pbc-extension-by-zero`. |
| Termwise exact inverse image | `(upperStar (ModuleCat.{u + 1} C) j).mapDerivedCategory`; the source's `Lj*` is identified with this by `leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} C) j`. This natural isomorphism is the standard comparison for an exact functor, and imposes no condition on the object. |
| Unbounded derived tensor, with direct-sum total tensor on complexes | `derivedTensor (ModuleCat.{u + 1} C) U` and the same on `T`, exactly the declaration recorded by `def-kun-derived-tensor`; its K-flat monoidal construction uses the cochain tensor, not a degreewise Tor product. |
| Left-hand side `(j! K) tensor^L M` | `((derivedTensor (ModuleCat.{u + 1} C) T).obj ((openImmersionLowerShriek (ModuleCat.{u + 1} C) j).mapDerivedCategory.obj K)).obj M`. |
| Right-hand side `j!(K tensor^L j* M)` | `(openImmersionLowerShriek (ModuleCat.{u + 1} C) j).mapDerivedCategory.obj (((derivedTensor (ModuleCat.{u + 1} C) U).obj K).obj ((upperStar (ModuleCat.{u + 1} C) j).mapDerivedCategory.obj M))`. |
| Natural isomorphism, in the stated direction | Take `.symm` of the recorded natural isomorphism. Its component is `(((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} C) j).app K).app M).symm`, then compose with `j!` of tensoring `K` with the exactness isomorphism `Lj* M ≅ D(j*) M`. Naturality in both variables is retained because all comparisons are natural isomorphisms of the displayed bifunctors. |
| Canonical comparison induced by the ordinary sheaf tensor identity | `derivedOpenImmersionLowerShriekProjectionIso` is `asIso (derivedOpenImmersionLowerShriekProjectionMap A j)`. That map is the mate for `derivedOpenImmersionLowerShriekUpperStarAdjunction A j`, with `mapDerivedCategoryUpperStarDerivedTensorIso A j`. The latter uses the canonical derived tensor comparison, obtained by deriving the ordinary inverse-image tensor comparison. Thus this is the inverse of the usual projection mate, rather than an arbitrary isomorphism. On K-flat representatives it is the ordinary tensor projection identity of 0E8I, extended by direct-sum totalization; this is the comparison specified by 0GL1. |
| No extra assumptions | All generic coefficient hypotheses of the recorded declaration are instances for `ModuleCat C`. In particular, `upperStarPreservesFlat_moduleCat` requires only `[CommRing C]`. There is no `[Finite C]`, invertibility, constructibility, boundedness or Tor-amplitude hypothesis. |

The source names its isomorphism in the opposite direction to the node. This is a
canonical reversible isomorphism, so inversion is an exact match, not a statement
correction. Likewise, replacing the source's `Lj*` by the termwise functor uses its
canonical exactness comparison; it does not change the category or objects.

For canonicality, the definition of the projection mate is important. Its transpose
is the unit followed by inverse-image tensor compatibility. In the ordinary sheaf
categories this is the adjunction/Yoneda tensor identity proved in 0E8I. The derived
adjunction is obtained from these exact functors, and the tensor compatibility is the
left-derived ordinary tensor compatibility. Representing `M` by a K-flat complex gives
the direct-sum totalization of precisely that sheaf identity, as in 0GL1. Inverting this
mate gives the arrow in the node. The additional exactness transport above is natural
and normalized by the usual localization comparison.

Dependency declarations read and used in this identification:

- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion` (full abbreviation at lines 38–39).
- `def-weil-pbc-derived-categories`: module `Sheaf.AlgebraicGeometry.DerivedCategories`
  records `AlgebraicGeometry.Etale.DerivedCategoryModule` and Mathlib's `DerivedCategory`;
  the actual abbreviation is in `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
  Its docstring and signature identify it with the unbounded localization of the
  `ModuleCat C`-valued sheaves, with the same coefficient/site universe convention.
- `def-kun-derived-tensor`: `AlgebraicGeometry.Etale.derivedTensor`,
  `WeilConjectures.SixFunctors.Etale.Derived.Tensor` (signature and K-flat construction
  docstrings read, including the direct-sum cochain total tensor convention).
- `def-weil-pbc-extension-by-zero`: `AlgebraicGeometry.Etale.openImmersionLowerShriek`,
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` (definition and
  exactness/adjunction interfaces read). The termwise derived functor is
  `Functor.mapDerivedCategory` of exactly this functor.
- `prop-weil-pbc-inverse-image-modules-exact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`,
  `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact` (docstring and full statement
  read). Its inverse image is exact and canonically the constant-ring module pullback;
  the recorded six-functor `ModuleCat C` encoding uses `Etale.upperStar` of
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`. The existing
  `leftDerivedUpperStarIsoMapDerivedCategory` in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar` gives the canonical
  termwise identification used above. No dependency is redefined or repaired.

Edge cases checked against the source and signature: the empty open immersion,
`j = identity`, the zero ring, zero `K`, zero `M`, objects unbounded in either direction,
and arbitrary characteristic are all included. In the empty case both sides vanish;
for the identity the comparison is the tensor identity; zero objects give zero on both
sides. No `Nonempty`, `Nontrivial`, boundedness, finite coefficient, or invertibility
instance excludes any of these. The common universe convention is inherited from the
recorded ordinary étale categories; it is not a new equality imposed on site universes.

Searches made with `msearch.py NX lem-pur-etale-open-derived-tensor` on 2026-10-16:

- LeanSearch: `Extension by zero commutes with unbounded derived tensor product of etale
  sheaves of modules`. Eight hits about function extension by zero, zero tensor terms,
  Ext and Kähler differentials; no sheaf/derived projection-formula match.
- LeanFinder: `Extension by zero commutes with unbounded derived tensor product on the
  small etale site`. Eight hits about formally étale algebras and light condensed
  monoidal module categories; none is this statement.
- Loogle: `"jShriek", "tensor"`. Zero hits.
- Mathlib grep via `msearch.py`: `jShriek.*[Tt]ensor|[Tt]ensor.*jShriek|
  extensionByZero.*[Tt]ensor|[Tt]ensor.*extensionByZero`, in `CategoryTheory`.
  Zero hits.
- `rg` in upstream `WeilConjectures` for `openImmersionLowerShriek` and derived tensor
  projection names found the exact natural isomorphism recorded here. Its source is
  present both in the read-only slopmaster2 checkout and in the side source mirror.
  The `OrdinaryCompactSupport` objectwise wrapper was also read, but the bifunctor
  isomorphism records naturality directly and avoids its unrelated extra imports.
- `rg` in `lean/Sheaf` for `openImmersionLowerShriek.*[Tt]ensor`,
  `[Tt]ensor.*openImmersionLowerShriek`, and
  `derivedOpenImmersionLowerShriekProjection` found no duplicate statement.
- `rg` of `dag/lean_names_upstream.json` for the three projection-formula declaration
  names found no indexed hit; direct source inspection located the declarations above.
- The required upstream grep for the literal item id found no hit.

Validation: `scratchpad/ExistingSpecialization.lean` specializes the existing isomorphism
and its exactness transport to the **exact termwise formula above**, with only the
explicit `CommRing C` and `IsOpenImmersion j` hypotheses. It is outside `lean/` and is
not part of the delivery. Compilation uses only the authorized `scompile.py` wrapper.
The first probe needed `noncomputable section` because its result is an isomorphism
(data); after this scratch-only correction the probe compiled cleanly in 5.1 seconds, with
no errors or warnings. The dry run
also independently checks the recorded existing declaration by importing its module.

No mathematical statement correction, new node, dependency module, or
`STATEMENT-DISPUTED` is needed. The original node fields are preserved except `lean`.

Retry validation on 2026-10-16: reread the current node, all five dependency records,
their recorded interfaces, the upstream projection-map and projection-isomorphism
construction, the exact inverse-image comparison, the coefficient-flatness instance,
and the two Stacks source lemmas. The stored searches in `searches.jsonl` were checked;
direct source searches were repeated and found the same existing upstream match and no
side-library duplicate. No repair note exists for this item. Removed the diagnostic
`#check` from the scratch specialization and recompiled it through `scompile.py`:
sandbox 3.5 seconds, library check 4.4 seconds, no errors or warnings. This confirms the
exact formula with only `CommRing C` and `IsOpenImmersion j` as hypotheses.

The previous attempt's dry runs stalled on shared delivery/fetch locks before preflight.
The fresh prescribed `deliver2.py NX lem-pur-etale-open-derived-tensor --no-push`
completed successfully and printed:

> OK (dry run): commit 0b430de69e compiles and passes the preflight except for the
> second reading, which the second reader writes; nothing pushed.

The delivery contains the item's node and this report only. The sandbox node was
refreshed from the shared repository, retaining its current audit fields and changing
only `lean`; its recorded signature matches the upstream source verbatim. A concurrent
upstream attachment on the base names the same projection isomorphism and exactness
comparison; this delivery supplies the complete stage-2 record and specialization
validation. No delivery was pushed, and no second-reading section was written by this
worker.


## Second reading by NX

Independent second reading, 2026-10-16. I read the item node, both source lemmas,
the existing upstream declaration with its section variables and bifunctor definitions,
and all five dependency records and their relevant source signatures. The existing
attachment is correct; no statement, Lean record, or definition needs repair. There
is no statement_change, new definition node, dependency module, or repair note.
Only this second-reading section is added to the delivery.

The node's objects, hypotheses, and conclusions, checked individually:

| Node item | Lean rendering and verdict |
| --- | --- |
| An arbitrary commutative ring C | Specialize A to `ModuleCat.{u + 1} C`, with `C : Type (u + 1)` and `[CommRing C]`. All generic coefficient-category instances are available without further assumptions; confirmed by compiling the specialization. Exact. |
| Schemes U and T and an open immersion j | `{U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]`. Read Mathlib's `AlgebraicGeometry.IsOpenImmersion` abbreviation, the recorded declaration of def-weil-open-immersion. No separatedness, quasi-compactness, or Noetherian assumption. Exact. |
| The ordinary unbounded derived categories of constant-ring module sheaves | `DerivedCategoryModule C U` and `DerivedCategoryModule C T`, expanded in `Derived.Coefficients` to `DerivedCategory (Sheaf _.smallEtaleTopology (ModuleCat.{u + 1} C))`. This is the encoding explicitly recorded and used by `Sheaf.AlgebraicGeometry.DerivedCategories`. Exact. |
| Termwise extension by zero j! | `(openImmersionLowerShriek (ModuleCat.{u + 1} C) j).mapDerivedCategory`. The source defines the ordinary functor by `localizationLowerShriek`; this is precisely the recorded def-weil-pbc-extension-by-zero, sheafification of the localized extension presheaf. Applying its exact functor to complexes gives the stated termwise functor. Exact. |
| Termwise exact inverse image j* | `(upperStar (ModuleCat.{u + 1} C) j).mapDerivedCategory`. Read the pullback definition and the exactness dependency `etaleInverseImageModulesExact`: inverse image on constant-ring modules is the usual sheaf inverse image, with its linear action and exactness. The existing `leftDerivedUpperStarIsoMapDerivedCategory` is the canonical exact-functor comparison `Lj* ≅ D(j*)`. Exact after this specified transport. |
| Unbounded derived tensor with direct-sum total tensor | `derivedTensor (ModuleCat.{u + 1} C) U` and the analogous bifunctor on T, the existing declaration of def-kun-derived-tensor. Its implementation is `curriedTensor` on the K-flat monoidal derived category, and its total-left-derived-functor interface uses the cochain tensor. No alternate tensor is introduced. Exact. |
| Every K on U, then every M on T | The source is an isomorphism in the functor category `D(U_et,C) ⥤ D(T_et,C) ⥤ D(T_et,C)`; arbitrary `K : DerivedCategoryModule C U` and `M : DerivedCategoryModule C T` are its two successive components. Neither is restricted. Exact quantifier order. |
| Left endpoint `(j! K) tensor^L M` | `derivedTensorWhiskeringLeftOpenImmersionLowerShriek` expands to tensor after applying D(j!) in the first argument. It is the target of the recorded source isomorphism and hence the source of its inverse. Exact. |
| Right endpoint `j!(K tensor^L j* M)` | The other endpoint is postcomposition by D(j!) of `derivedTensorWhiskeringRightLeftDerivedUpperStar`, followed by D(j!) of tensoring K with the component of `leftDerivedUpperStarIsoMapDerivedCategory`. It expands to the exact right endpoint in the scratch specialization. Exact. |
| A natural isomorphism in both objects and in the displayed direction | Invert `derivedOpenImmersionLowerShriekProjectionIso`, then whisker the natural exactness comparison through tensor and D(j!). Inversion, whiskering, and composition retain bifunctor naturality; this is stronger data than merely choosing unrelated objectwise isomorphisms. Exact. |
| The canonical comparison induced by the sheaf identity, with the total tensor convention | The source definition is `asIso (derivedOpenImmersionLowerShriekProjectionMap A j)`. I read that map and `Adjunction.projectionMap`: it is the unit/tensor-compatibility/counit mate. I also read `UpperStarMonoidal.Comparison`: tensor compatibility is obtained by `Functor.leftDerived₂NatTrans` from the ordinary inverse-image tensor comparison. Thus on K-flat models the mate is the adjunction/Yoneda sheaf identity of 0E8I, totalized over cochain bidegrees, and its inverse is the node's direction. No arbitrary isomorphism is substituted. Exact. |
| No boundedness, constructibility, Tor-amplitude, finiteness, or invertibility conditions | None appears in the specialized binders. In particular `upperStarPreservesFlat_moduleCat` assumes only the coefficient commutative ring, and all concrete-category/sheaf-composition hypotheses are synthesized. Exact. |

Source check: in `sites-cohomology.tex`, lemma-j-shriek-and-tensor (0GL1),
the only assumptions are a ringed site and one object of it; both derived objects are
unbounded and arbitrary. The preceding adjunction lemma also has no finiteness
assumption. In `sites-modules.tex`, lemma-j-shriek-and-tensor (0E8I), the proof is the
five displayed Hom identifications followed by Yoneda. This fixes the ordinary
comparison used above. For a scheme open immersion, localization at U identifies
with the small etale site of U; specializing to the constant ring is legitimate.
The item's proof list is empty, so no proof step is omitted from a newly written
statement docstring. The source proof route is: represent K on U by any complex,
represent M on T by a K-flat complex, restrict that model, and apply 0E8I in each
bidegree and totalize by direct sums. This is the route the recorded canonical
comparison implements.

Edge cases: U empty (including T empty), the identity immersion, the zero ring,
zero K or M, arbitrary characteristic, and complexes unbounded in both directions
are included. There is no Nonempty or Nontrivial binder. No index set or integer n
is quantified in the statement, so an empty tensor-total summand or degree zero
requires no additional hypothesis. The universe u is arbitrary; the u+1 coefficient
and module universe is exactly that of the recorded small-etale derived categories,
not a new site-universe equality. Ordinary smaller coefficient rings can be regarded
in that common larger universe. No universe or variable is unbound in the probe.

Independent searches used different words from the first reader, through msearch.py:

- LeanSearch: `Derived projection formula for the exact extension by zero functor on
  sheaves of modules` returned eight hits about projective resolutions, degree-zero
  derived functors, Ext, and group extensions; none is the sheaf projection formula.
- LeanFinder: `Canonical projection isomorphism for extension by zero along open
  embeddings and tensor product in unbounded derived categories of module sheaves`
  returned eight hits about free sheaf-of-modules pullback; none is this statement.
- Loogle: `"lowerShriek", "Tensor"` returned zero hits.
- Independent rg search for `extension.by.zero.*tensor`, its reversed phrase,
  `shriek.*tensor`, and `tensor.*shriek` in Mathlib/CategoryTheory returned no match.
  Searching upstream Etale sources found the recorded canonical bifunctor isomorphism
  and its users. Searching the project Sheaf sources found related results: I opened
  OpenExtensionProjectionFormula (Zariski structure-sheaf modules, a different category),
  FiniteCoefficientEtaleProjectionFormula (compact supports and restricted finite
  coefficients), and TensorTotalExtendNaturalIso (extension of complex indices).
  None is a replacement for this unrestricted ordinary-etale formula. Searches of
  dag/lean_names_upstream.json and the literal item id in upstream found no indexed
  attachment; direct upstream declaration inspection supplies the exact match.

H4/H5/H6/H8/H9 check: reuse of the existing upstream construction is required and
introduces no new definition, proof, axiom, private notion, file-local instance, or
notation. No new Lean module is delivered, so the new-module source/blueprint and
proof-docstring requirements do not call for rewriting upstream docstrings. I checked
programmatically that lean.statement is verbatim the source signature, from
`noncomputable def` through its result type; it matches. The sandbox node differs
from the repository node only in lean. No correction/citer audit is required.

Validation: independently reran the exact termwise specialization in
`scratchpad/ExistingSpecialization.lean` through the prescribed scompile.py wrapper.
It compiled cleanly (sandbox 7.4 seconds; library check 7.4 seconds), with no errors
or warnings. This checks all synthesized instances with only CommRing C and
IsOpenImmersion j. The scratch file is not a delivered module. The required delivery
dry run and final delivery are performed after this reading.


Delivery validation after second reading: the dry run passed preflight and compiled
at 0836a5737e. The first final-delivery attempt was rejected because the wrapper staged
coord/blueprint-index.tsv, coord/queue.md and coord/queue.tsv in addition to the two
intended files. Those files are outside this sandbox and were not edited by this reader.
Preflight also emitted a nonfatal signature warning. I read the current server source
using `scompile.py --source` and confirmed that its declaration is unchanged and still
matches the recorded signature verbatim, including noncomputable. No Lean-record change
is warranted. Retrying the prescribed delivery wrapper with the reviewed sandbox.
