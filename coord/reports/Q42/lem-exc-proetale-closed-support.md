## Worker report

This delivery records the existing declaration
`AlgebraicGeometry.ProEtale.derivedLowerStarClosedUpperShriekAdjunction` in
`WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersion` (source line 272).
No new Lean module or theorem is needed. The node is unchanged except for `lean`.
The full source, including the surrounding binders, definitions, and proof, was read;
`scompile.py --source` also returned the current server module with this declaration.

The existing construction applies to arbitrary rings and to closed immersions with
quasi-compact open complement. Its specialization is exactly the present node:

- The scheme `T` is the parameter `X : Scheme.{u}`. The node's Noetherian condition
  is `[IsLocallyNoetherian T] [CompactSpace T]`. It implies `[QuasiCompact j]`, the
  only finiteness condition the existing construction needs. There is no extra
  hypothesis on the closed subscheme or the complexes.
- The closed immersion is `(i : Z ⟶ X) [IsClosedImmersion i]`.
- The complementary open immersion is `(j : U ⟶ X) [IsOpenImmersion j]` and
  `(hij : IsCompl (Set.range i.base) (Set.range j.base))`. `IsCompl` includes both
  disjointness and exhaustiveness; neither part is omitted.
- A finite commutative coefficient ring `A : Type u` is used as
  `R := ULift.{u + 1} A`, with its inherited ring structure. The existing result
  requires only `[Ring R]`, so it applies in particular to every finite commutative
  ring without imposing nontriviality, a characteristic, or invertibility.
- The small site is exactly `Scheme.ProEt.topology X`, on weakly etale schemes over
  `X`, in both the source and the dependency. `ModuleCat.{u + 1} R` uses the larger
  module universe and does not identify the site's object and morphism universes.
- The source uses `Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)`, the presentation
  of constant-coefficient module sheaves as sheaves valued in modules. The site's
  recorded `proEtaleDerivedCategory` instead presents these as `SheafOfModules`
  over the sheafification of the constant ring `ULift A`. These express the same
  constant-coefficient notion: a sectionwise constant `A`-action extends uniquely
  to the sheafified constant ring action, and restriction recovers it. Linear
  sheaf maps agree in both presentations. This is a presentation comparison,
  not a change to a variable ring sheaf or to the structural sheaf of a scheme.
- The direct image is `ProEtale.lowerStar (ModuleCat R) i`, defined by
  precomposition with `MorphismProperty.Over.pullback @WeaklyEtale ⊤ i`.
  On sections it is `F(V ×_X Z)` with the same constant coefficient action as
  `Scheme.proEtaleConstantModuleDirectImage i A`; maps are sectionwise linear.
- The left side in the recorded signature is `lowerStar.rightDerivedFunctor`.
  Closed direct image is exact, and the construction explicitly transports its
  adjunction along `rightDerivedFunctorIsoMapDerivedCategory.symm`. Consequently
  this is the canonical termwise functor on derived categories claimed by the
  node, not merely an unrelated left adjoint.
- `closedUpperShriek (ModuleCat R) i j` is exactly
  `sectionsWithSupport (ModuleCat R) j ⋙ upperStar (ModuleCat R) i`, where
  `sectionsWithSupport.obj N = kernel ((upperStarLowerStarAdjunction _ j).unit.app N)`.
  Its maps are the induced kernel maps. Thus its total `rightDerivedFunctor`
  is precisely `Ri!₀` of the node, with the specified unit map and closed inverse
  image, rather than an arbitrarily selected right adjoint.
- The conclusion `⊣` is an adjunction, including natural Hom bijections, unit,
  counit, and triangle identities. Both functors have the full `DerivedCategory`
  of these sheaf categories as domain or codomain. `rightDerivedFunctor` is the
  total right derived functor on the homotopy-category localization, with its
  universal comparison map and K-injective computation. No `Plus`, boundedness,
  constructibility, or restriction on the right adjoint's values occurs.

Dependency declarations read and used in this identification:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` (including its complete
  constant commutative-ring sheaf and `ULift` definition).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  its underlying definition is Mathlib's `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `AlgebraicGeometry.Scheme.proEtaleBaseChange`, `proEtaleSheafInverseImage`,
  `proEtaleSheafDirectImage`, `proEtaleSheafAdjunction`, `proEtaleConstantRing`,
  `proEtaleCoefficientDirectImageMap`, `proEtaleCoefficientInverseImageMap`,
  `proEtaleConstantModuleDirectImage`, and `proEtaleConstantModulePullback`.
- `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersion`:
  `AlgebraicGeometry.ProEtale.closedUpperShriek` and `sectionsWithSupport`,
  the two declarations already attached to `def-exc-proetale-sections-with-support`.
  That attachment's lean record lists names without a module field; their actual
  owning module and complete definitions were located and read directly.

The upstream proof follows the node's route: the closed image is the supported
subcategory; kernel factorization coreflects onto it; composing gives the
sheaf-level adjunction; exactness of closed direct image and the unbounded
K-injective derived-adjunction construction give the desired adjunction.
The generic derived-functor and derived-adjunction source modules were read too.
This records an existing result, not a claim that all its upstream prerequisites
are already sorry-free.

Edge cases checked: `Z` empty (`j` the whole open), `U` empty (`i` the whole
closed scheme), the empty ambient scheme, zero sheaves and arbitrary unbounded
complexes, and the zero coefficient ring. `IsCompl` allows these cases, no
`Nonempty` or `Nontrivial` hypothesis occurs, and the kernel formula specializes
respectively to the zero support functor or the identity support functor.
No statement correction or disputed mathematical claim is needed.

Searches for existing declarations (2026-10-16):

- `msearch.py ... leanfinder` with query “A closed immersion induces a direct image
  on unbounded derived categories of pro-etale module sheaves with right adjoint
  the right derived functor of sections with closed support”: eight generic
  scheme/module-sheaf adjunction results, none the requested exceptional adjoint.
- `msearch.py ... loogle` with query
  `CategoryTheory.Adjunction.derived, CategoryTheory.Functor.rightDerivedFunctor`:
  zero results; the latter identifier is unknown to Mathlib's search service.
- `msearch.py ... grep` with query
  `derived.*Adjunction|mapDerivedCategoryRightDerivedAdjunction|closedUpperShriek`
  in `CategoryTheory`: generic derived-adjunction module hits only.
- `msearch.py ... leansearch` with query “closed immersion pro-etale sheaves direct
  image right adjoint on unbounded derived category”: service unavailable,
  Internal Server Error; the other searches and direct source reads succeeded.
- `rg` of `derivedLowerStarClosedUpperShriekAdjunction` and the item id in upstream
  `WeilConjectures` found the exact declaration, its module documentation,
  sheaf-level adjunction, and downstream unit theorem. The corresponding `rg` in
  `lean/Sheaf` and the upstream-name index produced no duplicate declaration.
  Direct upstream grep covered both the declaration's name and the blueprint id.

Validation uses only the authorized `scompile.py` and `deliver2.py --no-push`
wrappers. A scratch probe checks the complete declaration type and its
specialization with the node's actual Noetherian, finite commutative-ring and
complement hypotheses. The delivery wrapper additionally checks the existing
primary declaration against the current compiled environment.

## Second reading by Q42

I read the sandbox node and the full existing module independently, including its
section binders and the definitions of both functors. I also read the current
server source through `scompile.py --source`, and the recorded declarations of all
ten statement dependencies. The source blueprint files were read at
`/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/` (the shared
clone does not contain the untracked literature). Its lemma, order 1859, assumes
Noetherian T, closed i, complementary open j, finite coefficients, and the whole
ordinary derived categories; its preceding definition, order 1858, specifies the
unit-kernel formula and commutative coefficients. These agree with the DAG's
expanded statement. No statement correction is needed.

Object, hypothesis and conclusion checklist:

1. Ambient scheme T: `{Z U X : Scheme.{u}}`, specialized with `X := T`.
   Noetherian means `[IsLocallyNoetherian T] [CompactSpace T]`, using precisely
   the two dependency declarations. The existing declaration needs only
   `[QuasiCompact j]`. Mathlib `AlgebraicGeometry.Noetherian`, lines 204--216,
   supplies that instance for an open immersion into a locally Noetherian
   scheme, without even needing global compactness. The scratch specialization
   elaborates from the node's hypotheses without an added assumption. PASS.
2. Closed subscheme and map: `(i : Z ⟶ X) [IsClosedImmersion i]`. I checked
   Mathlib's closed-embedding and surjective-stalk definition, not a predicate
   on closed subsets alone. No reducedness, nonemptiness, finite type, or
   separately imposed Noetherian hypothesis on Z is present. PASS.
3. Open complement: `(j : U ⟶ X) [IsOpenImmersion j]` and
   `hij : IsCompl (Set.range i.base) (Set.range j.base)`. This requires exactly
   disjointness and union equal to the whole space, with the specified maps;
   no chosen affine complement or extra complement is used. PASS.
4. Finite commutative coefficient ring: specialize `{R : Type (u + 1)} [Ring R]`
   with `R := ULift.{u + 1, u} A`, where `(A : Type u) [CommRing A] [Finite A]`.
   The existing construction works for more rings, so this application covers
   every ring in the node. It requires no field, nonzero ring, residue
   characteristic, invertibility, or chosen enumeration. PASS.
5. Site and size: `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)`.
   This is the same weakly-etale small pro-etale site as the recorded
   `proEtaleDerivedCategory`. Module sections have universe `u+1`; the site's
   object and arrow universes have not been identified. The essentially-small
   site and Grothendieck/K-injective instances are supplied by imports, not
   extra hypotheses on T or A. PASS.
6. Module sheaves: the recorded category definition expands to `SheafOfModules`
   over the sheafified constant commutative ring, forgotten to `RingCat`.
   The existing theorem uses sheaves valued in `ModuleCat R`. These are two
   presentations of the same constant-coefficient module sheaves. Explicitly,
   restrict an A_X-action along the constant-presheaf map to obtain sectionwise
   A-modules; conversely sheafify the constant-presheaf action to obtain an
   A_X-action. Uniqueness of that extension gives the inverse identification
   on actions and on linear morphisms. I checked Stacks `sites-modules.tex`,
   `definition-sheaf-modules` and `lemma-sheafification-presheaf-modules`,
   lines 782--850, for this identification. It preserves the underlying
   abelian sheaf, kernels, and exactness. This is not a literal definitional
   equality with the abbreviation `proEtaleDerivedCategory`, and the lean.note
   correctly records the presentation comparison. PASS.
7. Direct image: `ProEtale.lowerStar (ModuleCat R) i` is precomposition with
   `MorphismProperty.Over.pullback @WeaklyEtale ⊤ i`. The dependency's
   `proEtaleConstantModuleDirectImage` is the same precomposition with scalars
   restricted through the sheafification of the constant-section map. Under
   the identification in item 6, both send V to `F(V ×_X Z)` and act on maps
   by the original linear components. I checked Stacks `proetale.tex`,
   `section-morphism`, lines 4674--4682, and `sites-modules.tex`,
   `definition-pushforward`, clause (1), lines 1145--1172. PASS.
8. Inverse image and support: `upperStar` is the left Kan extension followed
   by sheafification of module-valued presheaves. Under item 6 this is the
   recorded module inverse image: the canonical inverse image of the constant
   ring is the constant ring on the source, so its scalar extension recovers
   the same action. `sectionsWithSupport.obj N` is exactly
   `kernel ((upperStarLowerStarAdjunction _ j).unit.app N)`; its map is the
   induced `kernel.map`. `closedUpperShriek` composes this functor with
   `upperStar _ i`. Thus it is the prescribed sheaf functor i!_0, including
   its action on morphisms and the specified unit, rather than an arbitrary
   adjoint. These are the very declarations attached to the support
   dependency. PASS.
9. Termwise direct image on ordinary derived categories: the left side is
   `lowerStar.rightDerivedFunctor`. Exactness is installed by
   `preservesFiniteColimits_lowerStar_of_isCompl`, and the construction
   transports the adjunction by `rightDerivedFunctorIsoMapDerivedCategory`.
   I read that comparison's signature and the derived-adjunction definition.
   Thus the left side is canonically the termwise induced functor in the
   node; use of the right-derived name does not change it. PASS.
10. Specified right adjoint and all objects: the right side is
    `(closedUpperShriek (ModuleCat R) i j).rightDerivedFunctor`. Its definition
    uses the total right derived functor of the induced homotopy-category
    functor, localized at all quasi-isomorphisms. The result type `⊣`
    supplies natural Hom equivalences, unit, counit and triangle identities.
    Source and target are the full `DerivedCategory` categories. There is no
    boundedness, constructibility, finite-Tor-dimension, or restriction on the
    adjoint's values. Quantification over complexes is implicit in the
    adjunction and has the correct direction D(Z) to D(T) to D(Z). PASS.

Proof/docstring review: the existing module gives the kernel coreflection and
supported-subcategory equivalence, then the sheaf adjunction; its declaration
explains exactness and the unbounded derived-adjunction construction. The generic
right-derived source constructs the total derived functor and its comparison on
K-injectives. This accounts for all four DAG proof steps: vanishing of the support
kernel on U; unique factorization and full faithfulness; unbounded K-injective
derivation; and natural derived Hom adjunction. The source explicitly names this
blueprint item. No new theorem, hollow definition, chosen arbitrary map, duplicate
notion, or new/dependency module has been added. Existing upstream proofs are left
unchanged; this delivery does not assert that their transitive prerequisites are
sorry-free. The recorded `lean.statement` matches the existing source signature
verbatim up to the delimiter `:=`.

Edge cases: empty Z gives the zero support functor; empty U gives the entire
support kernel, canonically N; empty T allows both empty. Arbitrary zero sheaves,
zero complexes, and complexes unbounded in both directions are allowed. The zero
coefficient ring is allowed since neither `Nontrivial` nor `Nonempty` is assumed.
There is no index set or cohomological degree restriction (in particular degree
zero is covered), and no characteristic hypothesis. The declared universe u is
arbitrary; ULift is the recorded coefficient-size convention, not a restriction
on A. All section binders were checked, and `autoImplicit false` is enabled in
the scratch probe.

Independent searches (2026-10-16):

- `msearch.py Q42 lem-exc-proetale-closed-support leanfinder` with
  `exceptional inverse image closed subset kernel restriction adjunction derived
  unbounded sheaves` returned eight generic Serre quotient, scheme restriction,
  and derived truncation results, none this geometric support adjunction.
- `msearch.py ... loogle 'CategoryTheory.Adjunction.derived'` returned the generic
  derived adjunction and its unit/counit formulas, whose absolute-derived
  hypotheses do not supply this geometric instance.
- `msearch.py ... grep 'sectionsWithSupport|closedUpperShriek|supportedAway'`
  returned no Mathlib hits. Direct `rg` on Mathlib, the upstream pro-etale tree,
  and `lean/Sheaf` confirmed the exact upstream declaration and support
  constructions, and no second Sheaf statement. I also searched Mathlib module
  sheaves for constant-coefficient/category comparisons.

Mismatches and changes: no mathematical or signature mismatch was found. The
worker's existing attachment is retained, and no node or Lean source was changed.
This second-reading section adds the independent clause audit, source checks,
and the explicit action-extension explanation for the coefficient presentation.
The absent untracked literature in the shared clone was resolved by reading the
launcher's local literature copies; no source was reconstructed from a name.

Validation: `scompile.py Q42 lem-exc-proetale-closed-support
scratchpad/ExistingChecks.lean`, run from this sandbox, passed both its scratch
probe and library check (10.9 s and 11.9 s), with no warnings. The output displays
all implicit hypotheses of the existing declaration and its application with
`ULift A` under exactly the node's hypotheses. There are no delivered Lean files
to compile. Delivery preflight additionally validates the existing declaration.
