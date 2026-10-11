## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedOpenGluing` states `derived_open_gluing` for a
ringed space covered by opens `U` and `V`. It quantifies derived-category objects `A` and
`B`, an overlap isomorphism, a global glued object with restriction isomorphisms and the
transition equation, and the compatible-map lifting clause. Open restriction is expressed
using `SheafOfModules.overFunctor`, `overMap`, and `mapDerivedCategory`; the canonical
comparison of successive restrictions uses `Functor.mapDerivedCategoryCompIso`.

The scheme dependency is Mathlib's `AlgebraicGeometry.Scheme`; the derived-category
dependency is `AlgebraicGeometry.schemeDerivedCategory` from
`Sheaf.AlgebraicGeometry.DerivedCategory`. The statement itself is generalized to the
ringed-space carrier used by the existing open-restriction and Mayer--Vietoris modules.

Edge cases checked include empty opens (the cover equation allows them), the empty overlap,
and arbitrary universe `u` with derived-category universe `w` explicitly bound.

Searches: `leanfinder` for derived gluing (no matching declaration); `loogle` for derived
category gluing (0 hits); grep of Mathlib for `perfect complex|derived category|gluing` (no
hits); grep of project sources for open derived gluing (no exact declaration).


## Second reading by H1

Read the node, all four proof steps, the two statement-dependency nodes and their
recorded declarations, and Stacks Tag 08DG in cohomology.tex, lines 11055–11124
(local literature mirror /home/ubuntu/c1-stacks-review). The tags table identifies
08DG as cohomology-lemma-glue. This section assumes only a ringed space: no scheme,
Noetherian, separated, quasi-compact, boundedness, perfection, or characteristic
hypothesis occurs. The node's source.document still says perfect.tex, but its proof
sources and the actual tag are in cohomology.tex; the module cites the actual source.
The node's mathematical statement is correct and has not been changed.

Object/hypothesis/conclusion inventory and correspondence (H3):

1. Ringed space (X,O_X): `X : RingedSpace.{u}`. Mathlib RingedSpace is
   SheafedSpace CommRingCat; `moduleRings X` is the shared structure sheaf composed
   with forget₂ CommRingCat RingCat, not a newly chosen ring sheaf. PASS.
2. Two open subspaces covering X: `U V : Opens X`, `hcover : U ⊔ V = ⊤`.
   No nonemptiness or further geometric assumption. PASS.
3. D(O_U), D(O_V), D(O_X), D(O_(U∩V)): `DerivedCategory (SheafOfModules ...)`,
   with `moduleRings X`, its `.over U`, `.over V`, and `.over (U ⊓ V)` respectively.
   Opened def-pc-derived-category and its schemeDerivedCategory signature: it is
   the very same Mathlib DerivedCategory/SheafOfModules carrier for X.toRingedSpace.
   The node here explicitly concerns ringed spaces, so specializing X to Scheme
   would be wrong. Opened def-pc-scheme and Mathlib Scheme/Hom: their locally affine
   requirement is not imposed here. The generic construction is the existing
   def-weil-abstract-derived-category Mathlib leaf, whose DerivedCategory and
   HasDerivedCategory signatures were also read, together with the
   def-weil-sheaf-of-modules-category leaf and SheafOfModules/Hom. PASS.
4. Chosen localization sizes: four `HasDerivedCategory.{w}` instances use the
   existing SheafOfModules.instAbelian, not a second chosen abelian structure.
   These are the project's explicit size convention, not mathematical finiteness
   assumptions; standard localizations are available in a sufficiently large w.
   Both u and w are explicitly bound. PASS.
5. A and B are arbitrary unbounded objects of the two local derived categories:
   `A : DerivedCategory ...over U`, `B : DerivedCategory ...over V`. PASS.
6. c is an isomorphism A|W → B|W, W=U∩V: the binder uses the two
   `SheafOfModules.overMap ... (homOfLE inf_le_left/right)` derived functors.
   Their Mathlib signatures restrict modules along Over.map of the inclusion. PASS.
7. Existence of F and isomorphisms F|U → A, F|V → B:
   `∃ F iU iV, ...`; `overFunctor ... U/V` gives restriction to the open site. PASS.
8. Transition c: let eU and eV denote, for explanation only, the canonical
   iterated-to-direct restriction isomorphisms
   `(mapDerivedCategoryCompIso ...).symm ≪≫
   mapDerivedCategoryNatIso (overFunctorMap ...)`.
   The equation now reads `eU.inv.app F ≫ res(iU.hom) ≫ c.hom =
   eV.inv.app F ≫ res(iV.hom)`. This is exactly c = g|W ∘ f⁻¹|W.
   Originally the comparison maps were absent and the two source objects were
   not canonically identified. FIXED.
9. After the same F,iU,iV have been chosen, any global E and maps A → E|U,
   B → E|V: `∀ E a b, ...`. No quantifier is moved before F. PASS.
10. Compatibility a|W = b|W ∘ c: now
    `res(a) ≫ eU.hom.app E = c.hom ≫ res(b) ≫ eV.hom.app E`.
    Originally c was composed with res(a), the wrong branch, and the composition
    comparison was used in the wrong direction without overFunctorMap. FIXED.
11. Existence of a morphism F → E with precisely the prescribed restrictions:
    `∃ f, resU(f) = iU.hom ≫ a ∧ resV(f) = iV.hom ≫ b`.
    Existence only, no uniqueness added. PASS.

The comparison isomorphisms have explicit terms throughout the signature, rather
than statement-level let binders. Their direction was checked against the source
of Functor.mapDerivedCategoryCompIso (composite-derived → iterated-derived),
Functor.mapDerivedCategoryNatIso, and SheafOfModules.overFunctorMap. Local instance
attributes register Mathlib's composition-preservation lemmas; no hypothesis or
new definition is added. The existing derivedOpenHomRestriction in the imported
Mayer–Vietoris module uses exactly this same comparison.

Edge cases: either open may be empty, both may be empty when X is empty, and the
overlap may be empty; hcover is the sole condition on them. Zero objects and zero
maps are allowed, including zero local complexes. There is no index type or n
parameter to restrict; complexes are unbounded and indexed by ℤ. All characteristics
are allowed, and there is no field assumption. The arbitrary universe u and chosen
localization universe w are bound; no finite-size or small-derived-category claim
is added. The shared universe convention is the one of the landed ringed-space
restriction modules and can be chosen large enough for the data.

Independent searches (H4), with different queries from the first reader:

- LeanFinder via msearch: `derived category descent objects open cover ringed space`:
  eight hits, including Scheme.GlueData.sheafValGluedMk, ordinary sheaf conditions,
  and scheme relative gluing; none is derived object and morphism gluing.
- Loogle via msearch: `"DerivedCategory", "glue"`: zero hits.
- LeanSearch via msearch: `Glue objects and morphisms of derived categories of module
  sheaves on two open subsets`: unavailable, Internal Server Error; no verdict
  inferred from the unavailable service.
- rg in Mathlib's Homology/DerivedCategory, the full WeilConjectures source,
  project lean/Sheaf, and dag/lean_names_upstream.json for
  `derived.*[Gg]lu|[Gg]lu.*derived|derived_open_gluing|08DG`: no exact existing
  declaration. Additional `glue|gluing|descent` searches found ordinary sheaf and
  scheme descent and the already imported derived Hom Mayer–Vietoris module,
  not this statement. Existing overFunctor/overMap/overFunctorMap and exact-functor
  derived comparison isomorphisms are used directly; no private copies.

No new definition nodes or dependency modules are needed: all carriers, restrictions
and comparisons already exist. No hollow definitions or hypotheses are introduced,
and the only theorem proof remains `by sorry` (H5,H6). Expanded the docstring into
all four DAG proof steps with their named inputs, correcting the composition wording
of step 3 without changing the node. Added the standard copyright header, removed
the unused scheme-specialization import, scoped maxHeartbeats to the theorem,
and wrapped the long signature lines (H8,H9). The Lean record is regenerated from
the exact declaration signature. Final server compilation and delivery preflight
are recorded by the delivery commands.

## Reviewer fix (R-dog1308, stage 2)

The delivered statement was generalized to `X : RingedSpace` with D(O_U), D(O_V), D(O_(U∩V))
taken on the localized sites `(moduleRings X).over _`; it used neither stmt_dep
(def-pc-scheme, def-pc-derived-category). The node's D(O_X) is def-pc-derived-category, i.e. X a
scheme, and the lead's form for D(O_U) is `schemeDerivedCategory U.toScheme` reached by
`overFunctor _ U ⋙ (Scheme.Modules.overEquiv U).functor` (G1 ce180b4c0, QcOpenDerivedLift).
Restated: `X : Scheme`, `U V : X.Opens`, `A : schemeDerivedCategory U.toScheme`,
`B : schemeDerivedCategory V.toScheme`, `c` an iso in `schemeDerivedCategory (U ⊓ V).toScheme`
between the restrictions (inverse of `overEquiv U`, `overMap (U ⊓ V ⟶ U)`, functor of
`overEquiv (U ⊓ V)`), glued `F : schemeDerivedCategory X` with tied `iU`, `iV` and the transition
equation through the explicit comparison iso (compIso, then the unit of `overEquiv U` and
`overFunctorMap`), and the morphism clause unchanged in shape. `synthInstance.maxSize 2048` is
needed for additivity of the three-fold composites.
