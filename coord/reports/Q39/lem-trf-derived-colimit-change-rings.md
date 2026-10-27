## Worker report

Item: `lem-trf-derived-colimit-change-rings`, group Q39, stage 2.
Module: `Sheaf.CategoryTheory.DerivedColimitChangeRings`.
Main declaration: `CategoryTheory.categoryColimitChangeRings_exists`.
Additional statement: `CategoryTheory.categoryColimitChangeRings_bar_naturality`.
Both theorem proofs are `sorry`; no theorem is proved in this delivery.

Read the item's complete statement and nine-step proof, each statement dependency's
statement and recorded Lean interface, and the full interfaces in
`DerivedColimitBar.lean`, `RingedToposMorphism.lean`, and
`DerivedChangeOfRingsCochainModel.lean`. There is no repair note for this item.
The compact-object example in `lean/Sheaf` is withdrawn, so its node's recorded
upstream `WeilConjectures.CategoryTheory.CompactObject` was read for the actual example.

Source read: `literature/stacks-project/sites-cohomology.tex`, the section
"Homology on a category", particularly examples `example-category-to-point`,
`example-left-derived-colimits`, `example-morphism-categories`, and lemma
`lemma-change-of-rings` (08PF/08PG/08PH/08Q8). The source's 08Q8 displayed order
and its "right adjoint" sentence have the typing/direction errors already corrected
in the DAG node. This delivery keeps that node statement unchanged.

The auxiliary records expand the existence statement, as in the recorded bar-system
dependency. They specify universal pairs and their maps, and contain no chosen data
from a sorried existence theorem. `categoryBarExtend` and `categoryBarRestrict` are
abbreviations of Mathlib's existing sectionwise functors, not new coefficient notions.
`categoryBarRestrictConstant` is a constructed natural isomorphism: descend the
identity sectionwise interchange using the existing derived-composition comparisons.
The generic `CategoryBarDerivedExtension` record packages the universal derived pair
and its normalized adjunction. Its specialization to ordinary modules and to module
presheaves is asserted as output of the theorem, never assumed as an extra hypothesis.
It is the constant-coefficient presentation of the dependency's derived change of rings.

Hypothesis and clause correspondence:

- A small category E in the chosen universe: `(E : Type u) [SmallCategory E]`.
  The identity-cover topology and constant coefficients are exactly those of the
  supplied `B : CategoryColimitBarSystem.{u}`. Its models use the presheaf category
  `Eᵒᵖ ⥤ ModuleCat.{u} R`, its `CategoryColimitPoint`, and its constant ring
  `categoryBarConstantRing E R`. No nonempty-index hypothesis is imposed.
- A homomorphism of commutative rings: `{R S : Type u} [CommRing R] [CommRing S]`
  and `(φ : R →+* S)`. The point and presheaf morphisms with identity underlying
  topos act on modules by the ordinary `ModuleCat.extendScalars φ` and its
  sectionwise whiskering `categoryBarExtend φ`. The adjoint is coefficient restriction,
  with the ordinary extension/restriction adjunction, so this is the h/f operation
  specified by the statement, not an arbitrary geometric morphism or tensor functor.
- Derived extension of scalars: `point` and `presheaf` in
  `CategoryColimitChangeRings`. Each has its ordinary extension functor, the
  `IsLeftDerivedFunctor` universal property, everywhere-defined pointwise property,
  the adjunction to exact derived restriction, and `transpose` specifying the
  chain-level ordinary adjunction. They are precisely Lf* and Lh*.
- For every bounded-above complex M: `iso M b hM`, where
  `M : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ`, `b : ℤ`, and
  `hM : M.IsStrictlyLE b`. Its source is
  `(B.models E S).derived.obj (presheaf.functor.obj (Q.obj M))` and its target is
  `point.functor.obj ((B.models E R).derived.obj (Q.obj M))`, both in D(S).
  Thus the order is exactly Lπ^S_! Lh* ≅ Lf* Lπ^R_!.
- Canonical and natural: `comparison` is a natural transformation on derived
  presheaves; `iso_hom` identifies the displayed bounded-above isomorphism with its
  component. `normalization`, for every derived M, target N and arrow a, states that
  transposing `comparison.app M ≫ a` under Lh* followed by Lπ^S_!, then commuting
  constants with restriction, is exactly transposing a under Lπ^R_! followed by Lf*.
  This is the full common-Hom-bijection characterization in proof steps 1--3 and 9,
  not a bare nonempty isomorphism. In particular it fixes the canonical mate for
  arbitrary derived semilinear indexing maps and coefficient squares: both routes
  have the same transpose. This characterization, together with naturality of the
  transformation, encodes the derived compatibility without choosing resolutions
  functorially or introducing arbitrary comparison arrows.
- Objectwise flat F: each explicit representative clause binds
  `hF : ∀ U : Eᵒᵖ, Module.Flat R (F.obj U)`. This is the usual module flatness,
  equivalently exactness of tensor on short exact sequences, not flatness of S/R.
- Replace derived presheaf tensor by ordinary tensor: `flatPresheaf F hF` states
  invertibility of the universal counit on F in degree zero. The standard
  `singleMapHomologicalComplex` identifies its target with the degree-zero complex
  of `categoryBarExtend φ F`. Thus this is the canonical replacement, not merely
  an unrelated isomorphism of objects.
- The chain identification: `barIso F hF` is an isomorphism of the given cochain
  complexes, from K_E(F extended to S) to the termwise scalar extension of K_E(F).
  `formula` gives its value for every n, chain c, coefficient x and scalar s.
  Mathlib writes extension as S tensor_R F, so its formula is
  `(c, s tensor x) ↦ s tensor (c,x)`, exactly the source formula after tensor symmetry.
  Both generators use `CategoryColimitBarModel.generator`, with coefficient at
  `c.right = U_0`; no bar complex, differential or coordinate system is redefined.
- The source bar complex is bounded above and flat: `barFlat F hF q` supplies
  flatness of every R-module term. Vanishing in positive degrees is already the
  `positive` field of `B.models E R`. `flatBar F hF` makes the universal point-scalar
  counit invertible on this complex, saying its ordinary scalar extension computes
  the derived tensor on the right.
- This isomorphism represents the canonical comparison: `represents F hF` equates
  its image under Q with the comparison after applying the dependency's `model`
  and the two canonical scalar-extension counits. Its type checks both paths in
  D(S), including the single-complex transport. The isomorphism is therefore tied
  to the specified bar model and to the specified derived comparison.
- Compatibility with maps of module presheaves, functors of small categories and
  commutative coefficient squares: the second theorem binds E,D,R,S,R',S', φ,ψ,
  coefficient maps a,b and `hab : b.comp φ = ψ.comp a`, an indexing functor u,
  and `t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars a`. It supplies both induced
  tensor maps tS and kS, specifies them on ALL pure tensors, and asserts the
  comparison square in every degree and on every element. The bar maps are the
  exact semilinear maps `B.map` already recorded by the dependency. No tensor map
  is assumed as extra data. Identity indexing functors and identity coefficient
  maps recover the named special cases; composition is included through the
  coefficient-square condition and the dependency's canonical maps. Both flat
  hypotheses are needed only to access the two explicit bar isomorphisms; the
  derived normalization itself does not impose flatness on either derived input.
- No flatness of S over R: nowhere is `Module.Flat R S`, injectivity of φ, faithful
  flatness, or an exactness hypothesis on extension of scalars assumed.

Dependencies used:

- `Sheaf.CategoryTheory.DerivedColimitBar`:
  `CategoryTheory.CategoryColimitBarSystem`, its `models`, `map`, `formula`,
  `CategoryColimitBarModel.generator`, `derived`, `adjunction`, `model`, and
  `positive`; `CategoryColimitPoint` contains the recorded ringed-point morphism.
- `Sheaf.CategoryTheory.RingedToposMorphism`:
  `CategoryTheory.RingedToposMorphism`, as used by the dependency's point and constant
  ring presentation. The scalar operations use the identity-topos specialization.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel` supply the universal
  coefficient extension used in the proof plan. Our coefficient-category record
  spells out the same universal pair after the bar dependency's module-category
  identification, and also specifies the induced derived adjunction.
- Mathlib `ModuleCat.extendScalars`, `ModuleCat.restrictScalars`,
  `ModuleCat.extendRestrictScalarsAdj`, `Adjunction.whiskerRight`,
  `HomologicalComplex.singleMapHomologicalComplex`, and derived Q/derived universal
  properties; upstream `Functor.mapDerivedCategoryCompIso` and
  `Functor.mapDerivedCategoryNatIso` construct the constant/restriction interchange.
- All recorded proof-dependency modules are imported, including derived adjunctions,
  exact descent, sheaf restriction, tensor colimits, Grothendieck abelian modules,
  bounded-above-flat K-flatness and flat coproducts. These remain non-public imports
  when needed only by the postponed proof.

Edge cases checked before and after writing:

- Empty E: no Nonempty assumption; all bar coproducts and colimits are zero.
- Zero modules and zero complexes: both scalar extensions and comparisons are zero.
- Identity coefficient map and identity indexing functor: the normalization is the
  ordinary identity normalization; the naturality theorem includes these inputs.
- The one-object category: the comparison reduces to scalar extension itself.
- Non-flat coefficient extension Z to Z/2: permitted. Flat F has a flat R-bar
  complex; no claim is made that its extension remains R-flat.
- Nonzero higher Tor for a non-flat input: no ordinary-tensor replacement is asserted
  for that input; only the derived isomorphism applies.
- Degree zero and negative degrees: n=0 in `formula` uses U_0; at n=2 the dependency
  supplies the signed three-face formula, with the last face restricting x. Positive
  degrees vanish from the bar model, and the naturality theorem covers all integer q.
- All bounds b and all small categories/rings of the selected universe are allowed;
  no independent index universe or equality of site object/morphism universes is added.
- Universes and variables are explicit, with `set_option autoImplicit false`.

Searches performed (2026-10-22):

- `msearch.py ... leanfinder "Derived colimit of a module presheaf commutes with
  derived extension of scalars, with bar complex coefficient comparison"`: eight
  presheaf-colimit construction/evaluation hits, including
  `PresheafOfModules.colimitPresheafOfModules` and
  `PresheafOfModules.evaluation_preservesColimit`; no derived coefficient comparison.
- `msearch.py ... loogle "ModuleCat.extendScalars, colimit"`: unknown identifier
  `colimit`, so this query was replaced by the valid quoted query below.
- `msearch.py ... loogle '"colimit", "tensor"'`: twelve tensor-preservation,
  tensor-colimit and presheaf tensor-colimit instances; none gives derived category
  homology with this bar formula and canonical coefficient comparison.
- `msearch.py ... leansearch "Left derived colimits commute with derived extension
  of coefficient scalars"`: eight ordinary Kan-extension/colimit hits and
  `ModuleCat.preservesColimit_restrictScalars`; no match.
- `msearch.py ... grep 'derived.*[Cc]olimit|[Cc]olimit.*[Ss]calar'
  Algebra/Homology`: zero Mathlib hits. The all-Mathlib search was also made.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for derived-colimit,
  CategoryColimit and the exact item id: the existing bar module was found, along
  with cotangent-transitivity proof references; no coefficient-comparison declaration.
  Searching the proposed names in both roots and `dag/lean_names_upstream.json`
  gave no collision. Read Mathlib ChangeOfRings and the upstream derived exact-functor
  interfaces for the actual tensor convention and derived interchange maps.

No new independent definition node or dependency-module repair is needed. No node field
other than `lean` is changed. No statement is disputed.

## Second reading by Q39

Final reread by this dispatcher worker; independent review is the maintainer's, as the
brief specifies. This section does not claim a separate agent performed that review.
The final reread checked the node, both theorem signatures and every record field.
It specifically checked the order Lπ^S_! Lh* versus Lf* Lπ^R_!, S-linearity of both
ends, the direction of `singleMapHomologicalComplex`, the common-Hom normalization,
objectwise rather than coefficient-ring flatness, and the two tensor-generator formulas
in the semilinear square. Compiler-guided repairs fixed the transport direction and
made the R'-module carriers of restricted coefficients explicit with `@id`, without
changing any objects or hypotheses. The displayed main comparison is an actual
isomorphism in D(S), with its hom specified by the natural comparison; this is not a
per-degree replacement. Both theorem proofs remain `sorry` and all actual helper
definitions are constructed from existing functors and natural isomorphisms.
