## Worker report

The module `Sheaf.AlgebraicGeometry.SheafCohomologyFunctor` states
`AlgebraicGeometry.Scheme.Modules.sheafCohomology_map_comp`, with proof `sorry`.
There is no new cohomology definition: the statement uses the existing
`CategoryTheory.Functor.rightDerived` on the recorded global-sections functor.
The only auxiliary declaration is a local Additive instance obtained by projecting
an existing theorem; its proof is not postponed or independently proved.

Hypothesis and clause matching:

- “Let X be a scheme” is `(X : Scheme.{u})`. The universe is explicitly bound and
  unrestricted; `set_option autoImplicit false` rejects accidental implicit variables.
- `Mod(O_X)` is Mathlib's `X.Modules`, definitionally
  `SheafOfModules.{u} X.ringCatSheaf`. Its existing Abelian instance is used.
  This specializes the dependency's general-site `SheafOfModules` without copying it.
- The additive, left-exact global-sections functor to Ab is the dependency's
  `Scheme.Modules.globalSectionsFunctor X : X.Modules ⥤ AddCommGrpCat.{u}`.
  Its recorded theorem `globalSectionsFunctor_additive_leftExact X` supplies
  additivity and preservation of every kernel. The local instance uses its first
  projection; kernel preservation is contextual justification for identifying
  the right derived functors as cohomology, not an extra assumption.
- Enough injectives is the dependency's `enoughInjectives X`, installed with
  `attribute [local instance] enoughInjectives`. Mathlib then supplies
  `HasInjectiveResolutions X.Modules`. No enough-injectives binder is added.
- “H^i is the i-th right derived functor via injective resolutions” is
  `(globalSectionsFunctor X).rightDerived i`, where `(i : ℕ)` includes degree zero.
  Mathlib defines this by injective resolutions, application of the additive
  functor to the resolution, and homology in degree i.
- “Every morphism u : G' → G induces H^i(u) : H^i(G') → H^i(G)” is the typed
  functor action `((globalSectionsFunctor X).rightDerived i).map u`.
  Its domain and codomain are exactly that functor's values on G' and G;
  no arbitrary existential choice of map replaces the canonical induced map.
- “For composable module morphisms” is `{G' G G'' : X.Modules}`,
  `(u : G' ⟶ G)` and `(φ : G ⟶ G'')`.
- “H^i(φ ∘ u) = H^i(φ) ∘ H^i(u)” is the displayed equality of the map on
  `u ≫ φ` with `map u ≫ map φ`. Lean's `≫` lists maps in application order.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (and its Hom),
  for def-pc-scheme.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules`, used through
  `AlgebraicGeometry.Scheme.Modules` from Mathlib.AlgebraicGeometry.Modules.Sheaf,
  for def-weil-sheaf-of-modules-category. Its category and Abelian structure
  specialize directly to the scheme structure sheaf; no dependency repair is needed.
- `Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact`:
  `AlgebraicGeometry.Scheme.Modules.globalSectionsFunctor` and
  `AlgebraicGeometry.Scheme.Modules.globalSectionsFunctor_additive_leftExact`,
  for lem-sc-global-sections-left-exact.
- `Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives`:
  `AlgebraicGeometry.Scheme.Modules.enoughInjectives`,
  for lem-weil-pbc-scheme-modules-enough-injectives.
- `Mathlib.CategoryTheory.Abelian.RightDerived`:
  `CategoryTheory.Functor.rightDerived`, for def-sp-left-exact-additive.
  Its full signature and docstring were read, including the additive and
  HasInjectiveResolutions requirements. `InjectiveResolution.isoRightDerivedObj`
  documents the identification with homology of any injective resolution.
- `Mathlib.Algebra.Category.Grp.Abelian` supplies the Abelian target instance.

Source checked: https://stacks.math.columbia.edu/tag/01DZ, Section 20.2,
ringed-space paragraph and equation 20.2.0.3. It defines cohomology using injective
O_X-module resolutions and states that it is a family of functors. The node takes
the underlying abelian groups, retaining the module category as the resolution
category. This is distinct from deriving global sections on abelian sheaves.
The local copy of literature/stacks-project/cohomology.tex is absent, so the
source was read on the Stacks website.

Edge cases checked before writing: i = 0 is allowed; all higher natural degrees
are allowed; zero modules, zero maps, identity maps, and the empty scheme have
no excluded binders. The functor law applies to all of them. There is no
quasi-coherence, finiteness, affineness, base-field or characteristic assumption.
For Spec k, the formula continues to hold in degree zero and in the vanishing
higher degrees. All modules in the scheme's universe are admitted, matching
the existing scheme-module dependency encoding.

Searches made (2026-10-11):

- msearch.py leansearch: “right derived functor of global sections on scheme
  modules preserves composition”. Service unavailable: Internal Server Error.
- msearch.py leanfinder: “sheaf cohomology as right derived functor of global
  sections preserves composition of module morphisms”. Eight hits, including
  SheafOfModules.comp_val, sectionsMap_comp, Scheme.Modules.Hom.comp_app and
  Sheaf.cohomologyPresheafFunctor; none is this scheme-module derived statement.
- msearch.py loogle: “Functor.rightDerived, Functor.map_comp”. Unknown identifier
  Functor.rightDerived; no hits. The declaration was located by source grep.
- msearch.py grep: “rightDerived|cohomology.*comp” in CategoryTheory/Abelian:
  found RightDerived.lean and generic derived-functor material, reused here.
- rg on WeilConjectures and lean/Sheaf for moduleCohomology,
  globalSectionsFunctor, sheaf.*cohomology.*functor and cohomology.*map_comp:
  found the recorded Γ functor and the ringed-space module-valued cohomology,
  but no exact theorem on this Γ-to-Ab right derived functor. Ringed-space
  moduleCohomology has a different codomain and is not copied or redefined.
- rg for the node id in WeilConjectures: no matches.
- rg over Mathlib, WeilConjectures and lean/Sheaf for
  sheafCohomology_map_comp, globalSectionsFunctor_additiveForCohomology,
  rightDerived.*map_comp and rightDerived.*globalSections: no existing declaration
  with either new name or this specialization. Generic Functor.map_comp was read;
  it states the law for an arbitrary functor and does not name the node's Γ or
  resolution category, so the item states its specialization without redefining Γ.

No statement correction, new node, dependency module, or STATEMENT-DISPUTED issue.
Only the item's lean field is changed. Server compilation and dry-run preflight
are the validation; the independent second reading is left to the next worker.

## Second reading by E1

I independently opened the node, the delivered module, every statement dependency's
record and declaration, and the Stacks source. The repository has no local
cohomology.tex; I read the original TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/cohomology.tex,
section-cohomology-sheaves, equation-cohomology-modules, and checked the rendered
https://stacks.math.columbia.edu/tag/01DZ (20.2.0.3). The ringed-space paragraph
assumes only a ringed space and an arbitrary module sheaf. It constructs an
injective module resolution, applies global sections, and takes degree-i homology.
Its output retains the global-sections ring action; the node expressly selects
its underlying abelian groups. There is no additional scheme finiteness or field
hypothesis inherited from the source. The statement remains unchanged.

Object, hypothesis and conclusion inventory, with final Lean and verdict:

1. Scheme X: `(X : Scheme.{u})`, using Mathlib.AlgebraicGeometry.Scheme's
   `AlgebraicGeometry.Scheme`. PASS: arbitrary schemes, not an affine specialization.
2. Abelian category Mod(O_X): `{G' G G'' : X.Modules}`. I read
   Mathlib.AlgebraicGeometry.Modules.Sheaf: `Modules := SheafOfModules.{u}
   X.ringCatSheaf`, its Category and Abelian instances, and the underlying
   SheafOfModules structure and Hom in Mathlib.Algebra.Category.ModuleCat.Sheaf.
   The latter carries a presheaf of modules whose underlying abelian presheaf is
   a sheaf, with module-linear morphisms. PASS: the dependency's scheme case,
   with neither quasicoherence nor constructibility assumed.
3. Global sections Γ to Ab: `globalSectionsFunctor X` from
   Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact. I opened its definition:
   forget to the underlying abelian presheaf then evaluate at `op ⊤`.
   Its codomain is explicitly `AddCommGrpCat.{u}`. PASS: exactly the node's Γ.
4. Γ is additive and left exact: the same module's
   `globalSectionsFunctor_additive_leftExact X` asserts Additive and preservation
   of `parallelPair f 0` for every module morphism f. PASS: the correct kernel
   condition and no added assumptions. Its `.1` is now passed explicitly to
   `Functor.rightDerived`; left exactness is supplied by the dependency rather
   than added as a hypothesis of this theorem.
5. Enough injectives: `enoughInjectives X` from
   Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives has signature
   `theorem enoughInjectives (X : Scheme.{u}) : EnoughInjectives X.Modules`.
   PASS: applies to every module sheaf. The final signature passes this explicitly
   to Mathlib's `InjectiveResolution.instHasInjectiveResolutions`, whose source
   constructs resolutions by successive injective embeddings and syzygies.
6. Degree and definition H^i = R^i Γ via module injective resolutions: `(i : ℕ)`
   and `@Functor.rightDerived X.Modules _ AddCommGrpCat.{u} _ _ ... _
   (globalSectionsFunctor X) (globalSectionsFunctor_additive_leftExact X).1 i`.
   I read Mathlib.CategoryTheory.Abelian.RightDerived's definitions:
   injectiveResolutions, application of Γ on the homotopy category, then the
   degree-i homology functor. `InjectiveResolution.isoRightDerivedObj` identifies
   this with the cohomology of any chosen resolution. PASS: exactly the recorded
   def-sp-left-exact-additive match, not Ext in abelian sheaves.
7. A module morphism and its canonical induced cohomology map:
   `(u : G' ⟶ G)` and that right derived functor's `.map u`. Its type is the
   morphism from `.obj G'` to `.obj G`. PASS: no arbitrary chosen map and no
   missing existence clause; the map is already a defined term.
8. Composable module morphisms and composition law: `(φ : G ⟶ G'')` and
   `.map (u ≫ φ) = .map u ≫ .map φ` of the same functor in each occurrence.
   PASS: `≫` orders composition left to right, so this is H^i(φ ∘ u).
   Quantifiers are X, degree, arbitrary three modules, then u and φ.

Edge cases: PASS for i = 0 and every positive natural degree, zero objects and
zero/identity maps, and the empty scheme. There is no index set in this statement;
no nonempty or nonzero assumption excludes any case. No characteristic is fixed.
The universe u is explicitly bound and arbitrary, and all scheme modules in the
recorded dependency's universe are included. No unbound variables or universes
remain (`autoImplicit false`). The generic ringed-space source covers the scheme
specialization and its empty case.

Independent searches, with different terminology from the worker:

- msearch.py leansearch, “Derived global sections on sheaves of modules preserves
  composition”: service unavailable, Internal Server Error, recorded as unavailable.
- msearch.py leanfinder, “Derived global sections of O_X modules functor action
  composition”: eight hits, including Hom.comp_app, sectionsMap_comp and
  pushforward_map_app. I checked their types: sectionwise or pushforward maps,
  not the right-derived Γ functor on scheme modules.
- msearch.py loogle, “CategoryTheory.Functor.map_comp”: six hits; the generic
  Functor.map_comp states the law for any functor. I opened Functor.Basic:
  the field supplies precisely the elementary composition law but does not name
  this node's module-resolution cohomology, so it is not an exact existing record.
- rg over pinned Mathlib/AlgebraicGeometry, WeilConjectures and lean/Sheaf for
  rightDerived.*map_comp, map_comp.*rightDerived, sheafCohomology_map_comp and
  cohomology.*functorial: no exact specialization. Further rg for moduleCohomology
  and rightDerived/globalSections found Sheaf.Topology.RingedSpaceModuleCohomology,
  which I opened. Its Γ has ModuleCat codomain and uses moduleRings; it is not
  this node's Γ-to-Ab on X.Modules. No private cohomology definition is introduced.
  The existing abelian-sheaf Ext encoding likewise uses a different resolution
  category, so it is not substituted here.

Mismatch found and repaired: the worker installed enoughInjectives as a local
instance and introduced a local additive instance. This violated the project's
ban on file-local instances in statement modules and made the signature depend
on local elaboration context. I removed both and supplied the existing dependency
proofs explicitly to Mathlib's rightDerived and resolution instance. I adjusted
only the affected docstring explanation and updated lean.statement verbatim to
match the final signature. The theorem's mathematical content and natural-language
proof steps are unchanged. There is one named theorem with proof sorry, no new
notion, no hollow definition and no independent proof of an auxiliary assertion.
All imports serve its construction; all lines are at most 100 characters.

There are no new nodes, dependency modules, or statement corrections to review.
The existing Worker report is retained above; its local-instance description
records the original implementation and is superseded by this repair.
Validation: the repaired file compiles on the server with no errors or warnings
other than permitted sorry diagnostics; the delivery dry run checks the record,
source shape, and second-reading section before pushing.
