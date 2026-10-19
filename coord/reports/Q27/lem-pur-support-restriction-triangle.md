## Worker report

The delivery states `AlgebraicGeometry.Etale.supportRestrictionTriangle` in
`lean/Sheaf/AlgebraicGeometry/SupportRestrictionTriangle.lean`. It uses the existing
kernel-based supported-section functor and the derived-functor construction from
`Sheaf.AlgebraicGeometry.EtaleSupportedSections`.

The Lean statement renders the node as follows. `R : Type (u + 1)` with `[CommRing R]`
is the fixed coefficient ring. `T B C : Scheme.{u}` are the ambient scheme and the two
closed subschemes, represented by morphisms `b : B ⟶ T` and `c : C ⟶ T` with
`[IsClosedImmersion b]` and `[IsClosedImmersion c]`. The opens `b.openComplement` and
`c.openComplement` represent complements of the closed subschemes; their union is the
complement of `B ∩ C`, and `c.openComplement.ι ⁻¹ᵁ b.openComplement` is the open support
inside `V = T \ C`. The first existential map `a` has source supported sections on the
union and target supported sections on `b.openComplement`; its displayed composite with
`supportedEtaleSectionsι` is the support inclusion. The second map `r` has source
supported sections on `b.openComplement` and target the inverse-image (`upperStar`) of
supported sections on `c.openComplement`, and its displayed composite is restriction to
`c.openComplement`. The isomorphism `e` compares the right derived functor of the
composite with the composite of `mapDerivedCategoryPlus` and the right derived functor;
the following equality fixes it by the right-derived unit compatibility. The natural
transformation `δ` has the stated source and shifted target. Finally, for every bounded
below derived object `F`, `Triangle.mk` of the two derived maps and `δ.app F` belongs to
`distTriang`, which is the distinguished-triangle clause. These are exactly the two
support maps, the comparison isomorphism, the connecting morphism, their unit
normalization, and the distinguished-triangle conclusion in the node statement.

Dependency declarations used:

- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`,
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and related derived-category names.
- `def-weil-pbc-etale-site`: Mathlib `AlgebraicGeometry.Scheme.smallEtaleTopology`.
- `def-weil-closed-immersion`: Mathlib `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-open-immersion`: Mathlib `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-pbc-inverse-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.upperStar`.
- `def-pur-etale-derived-supported-sections`:
  `Sheaf.AlgebraicGeometry.EtaleSupportedSections`,
  `AlgebraicGeometry.Etale.supportedEtaleSections`,
  `supportedEtaleSectionsι`, and `derivedSupportedEtaleSections`.

The source module also imports the stated proof dependencies so that the stage-3 proof
plan remains visible: enough injectives, exact inverse image on module sheaves,
open-immersion etale facts, the open-closed short exact sequence, short-exact-complex
triangles, and K-injective derived-category facts.

Edge cases checked: `B` or `C` may be empty or equal to `T`; the complement opens and
 their union are still defined, so no nonemptiness assumption is introduced. The
 coefficient ring may be the zero ring. The universe is shared by all three schemes and
 the coefficient module category is `ModuleCat.{u + 1} R`, matching the small etale site
 and avoiding an independent lower test universe. No injectivity, separatedness,
Noetherian, characteristic, or boundedness hypothesis beyond the node's
`DerivedCategory.Plus` object is added.

Searches made before using the existing notions: `msearch.py` LeanFinder for the support
restriction triangle and for injective supported restriction (no matching declaration);
`msearch.py` Loogle queries `"support", "triangle"` and `"IsFlasque"` (no matching
triangle); `msearch.py` grep for `localCohomology|cohomologyWithSupport|sectionsWithSupport|support.*triangle`
and related support patterns (only unrelated algebraic local cohomology/flasque results);
`rg` over Mathlib and `WeilConjectures` for `supportRestrictionTriangle`,
`supportedEtaleSections`, `derivedSupportedEtaleSections`, and the recorded dependency
names. The exact declarations listed above were then read in their source modules and
matched to the dependency statements. No new definition node, dependency repair module,
statement correction, or `STATEMENT-DISPUTED` issue was needed.

## Earlier second reading (a previous round; superseded)

The declaration is already present in the project module `Sheaf.AlgebraicGeometry.SupportRestrictionTriangle` as `AlgebraicGeometry.Etale.supportRestrictionTriangle`. I checked the complete signature against the node: the coefficient-ring and scheme universes, both closed-immersion hypotheses, all four existential morphisms, the two pointwise map characterizations, the derived-unit compatibility, and the distinguished-triangle condition agree clause by clause. The module imports the six statement dependencies and the proof-plan modules recorded in its header. Because this is an existing project declaration, this delivery records `existing: true` and contains no Lean module.

## Second reading by Q27

I independently opened the sandbox node, the complete existing module
`lean/Sheaf/AlgebraicGeometry/SupportRestrictionTriangle.lean` (lines 1–131),
and the exact master blueprint Markdown at the node's source place. The
blueprint statement agrees verbatim with the node. I also read Stacks
`cohomology.tex`, section-cohomology-support (lines 3739–3798),
section-cohomology-support-bis (8444–8485), and
lemma-triangle-sections-with-support (8626–8654), and the recorded inverse-image
and support-functor definitions. These sources assume an arbitrary ringed
space/closed support for the analogous support construction; they impose no
Noetherian, separated, field, torsion, or characteristic assumption. The
present blueprint is specifically about fixed-coefficient small-etale module
sheaves, rather than the topological site of that Stacks analogue.

Here is my object/hypothesis/conclusion checklist, matched against the existing
Lean signature (line numbers refer to the module above):

1. A scheme `T`, and closed subschemes `B,C` of it: `{T B C : Scheme.{u}}`,
   `(b : B ⟶ T) (c : C ⟶ T)`, `[IsClosedImmersion b]` and
   `[IsClosedImmersion c]` (80–82). PASS. Closed subschemes are represented
   by their closed immersion, with no extra geometric property.
2. A fixed coefficient ring and module sheaves: `(R : Type (u + 1))
   [CommRing R]` and `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)`
   (80, 100, 103, 123). PASS. The fixed commutative coefficient ring is
   explicit in proof step 1 and the recorded support-definition node. No
   field or nonzero-ring assumption is inserted.
3. `V = T \ C` and its open inclusion `v`: `c.openComplement` and
   `c.openComplement.ι` throughout (86–98). PASS. I read
   `Scheme.Hom.openComplement` in the source closed-immersion module:
   its underlying open is exactly `(Set.range c)ᶜ`; the inclusion is the
   standard open-subscheme inclusion.
4. A bounded-below complex `F`: the final universal binder is
   `F : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
   (ModuleCat.{u + 1} R))` (123). PASS. This is the bounded-below derived
   category, not a restriction to sheaves in degree zero or to bounded
   complexes. The existential natural maps precede `∀ F`, so one family
   works simultaneously for every such object.
5. The first object is `RΓ_(B∩C)(T,F)`: the support complement is
   `b.openComplement ⊔ c.openComplement` (83, 98, 125). PASS by De Morgan's
   law: this union is exactly `T \ (B∩C)`. The existing support definition
   uses the complement open, not the support itself, as its last argument.
6. The second object is `RΓ_B(T,F)`: the complement argument is
   `b.openComplement` (84–85, 125–127). PASS.
7. The third object is `RΓ_(B∩V)(V,v*F)`: inverse image is
   `(upperStar (ModuleCat.{u + 1} R) c.openComplement.ι).mapDerivedCategoryPlus`,
   followed by `derivedSupportedEtaleSections R c.openComplement
   (c.openComplement.ι ⁻¹ᵁ b.openComplement)` (95–97). PASS. Its ambient scheme
   really is `V`, and its complement inside `V` is `V∩(T\B)`. Thus the
   support is closed in `V`, and the third term is not a support functor on `T`.
8. First arrow is support inclusion: the natural transformation `a` (83–84)
   is fixed by its composite with `supportedEtaleSectionsι` (100–102).
   PASS. It is then derived using `rightDerivedFunctorPlusNatTrans a` (125).
9. Second arrow is restriction: the natural transformation `r` (85–88)
   is fixed by the equality with inclusion followed by
   `globalSectionsUpperStarMap` (103–108). PASS. I opened that map's source:
   it is the adjunction-unit pullback on global sections, not an arbitrary
   morphism. The triangle's second arrow derives `r` and composes with
   `e.hom.app F` (126–127).
10. The third term is the composite of inverse image and the right derived
    support functor: `e` (89–94) identifies the derived composite with that
    composite, and the equality (109–122) normalizes `e` using the
    right-derived units and the exact inverse-image comparison. PASS.
    This expresses the canonical comparison required to render the displayed
    third object, rather than assuming a comparison as an extra hypothesis.
11. Connecting arrow and shift: `δ` is a natural transformation from the
    third functor to the first functor followed by `shiftFunctor ... (1 : ℤ)`
    (95–99). PASS: the last object is the first object shifted by `+1`.
12. Distinguishedness and naturality: `Triangle.mk` of the derived inclusion,
    derived restriction/comparison, and `δ.app F` lies in
    `distTriang (DerivedCategory (ModuleCat.{u + 1} R))` for every `F`
    (123–128). PASS. All three arrows come from natural transformations.
    The conclusion is in the derived category of coefficient modules, not
    the derived category of sheaves or just a long exact cohomology sequence.

Dependency interfaces checked independently: `def-weil-pbc-derived-categories`
records the six-functor encoding of `DerivedCategoryModule` and Mathlib's
`DerivedCategory.Plus`; I opened `DerivedCategories.lean` and its documented
specializations. Mathlib's `Scheme.smallEtaleTopology` is the topology on
schemes etale over `T` (Etale.lean:51), as required by
`def-weil-pbc-etale-site`. The recorded closed/open immersion declarations
are the usual scheme morphism properties. I read `upperStar` in
`UpperLowerStar/Defs.lean`: it is sheafified inverse image along etale base
change, with `upperStarLowerStarAdjunction`, hence the fixed-coefficient
inverse image of `def-weil-pbc-inverse-image`.
Finally I read all of `EtaleSupportedSections.lean`: `supportedEtaleSections`
is the actual functor-category kernel of `Sheaf.natTransΓRes`, its inclusion
is `kernel.ι`, and `derivedSupportedEtaleSections` is its existing
`rightDerivedFunctorPlus` composed with `DerivedCategory.Plus.ι`. These
are precisely the notions of `def-pur-etale-derived-supported-sections`;
no private copy or hollow data definition occurs in the item. There are
no new nodes or dependency modules in this delivery.

Edge cases: empty `T`, empty or full `B` and `C`, `B∩C` empty, and `V`
empty are all allowed by the binders and the kernel construction. Empty
support gives the kernel of restriction to the whole scheme; full support
gives restriction to the empty open. No nonemptiness premise excludes
either case. The zero coefficient ring and zero complex are included.
There is no index set or numerical parameter `n`; the shift is explicitly
the integer 1. No characteristic, torsion, or invertibility condition is
present. `universe u` is declared and all variables are explicitly bound;
the scheme and coefficient sizes follow the recorded small-etale
six-functor convention, with no independent lower test universe or added
universe equality.

Independent H4 searches run in this reading: LeanFinder via `msearch.py`
with “Localization sequence for etale cohomology with nested closed supports
and open restriction” returned generic algebraic-geometry and
Mayer–Vietoris short-complex lemmas, not this statement. Loogle's valid
query `"support", "triangle"` returned zero hits. An earlier query
`"supported" "distTriang"` was rejected as malformed and is not evidence
of absence. The logged grep query
`excision|localizationTriangle|cohomologyWithSupport` returned zero Mathlib
hits. Direct `rg` over Mathlib, upstream `WeilConjectures`, and project
`lean/Sheaf` with
`localization.*[Tt]riangle|[Tt]riangle.*[Ss]upport|[Ss]upport.*[Rr]estrict|sectionsWithSupport`
found upstream `Etale.existsUnique_distTriang_supportedLocalization` and
pro-etale sheaf-valued support constructions. I opened the former's
signature: its triangle is `Ri_! Ri^! L → L → Rj_* Lj^* L` in sheaves,
not this two-closed-support triangle of global module sections. The
pro-etale construction likewise has a different site and codomain.
The exact requested statement is already present in the project as
`AlgebraicGeometry.Etale.supportRestrictionTriangle`, so `existing: true`
is correct and no duplicate module is delivered.

H5–H9: the existing theorem has only `sorry` as proof; the module and
declaration docstrings name this source/blueprint and the declaration
docstring follows all six node proof steps, including the explicit
two-open gluing argument and resolution-independent naturality. No
statement change, source correction, new axiom, or proof was introduced.
The recorded `lean.statement` was checked against the complete signature
after whitespace normalization and agrees verbatim in its tokens.

Mismatches and changes: no mathematical mismatch was found. The earlier
second-reading paragraph was insufficiently detailed; I left it as
historical text and appended this independent object-by-object reading.
The existing declaration and the node's Lean signature are preserved.
The prescribed `scompile.py` compilation of the existing full module
completed with exit code 0 and no warnings (including a library check).
