## Worker report

This repairs returned head c521a1865864. The retained packet was first tested with
`deliver2.py --no-push`: commit 68e56e16aa passed compilation and preflight. The
subsequent mathematical self-check found the returned H3/H8/H9 defects still
present, so this delivery repairs them rather than repushing unchanged content.
The sole theorem remains `CategoryTheory.scalarLocalization_underlyingTelescope`,
with proof `sorry`. Four fully defined helpers in the same module name the section
normalization predicate, derived-unit normalization predicate, leg expression and
telescope property. They are
recorded in `lean.declarations` and have source/blueprint docstrings; they do not
introduce independent mathematical notions or any further postponed theorem.

`scalarLocalizationTelescopeProperty` is the fully written telescope conclusion,
parameterized by a predicate P. The theorem passes the actual bounded-below
predicate `fun L ↦ ∃ b : ℤ, L.IsGE b`, the actual derived functors and the canonical
scalar actions. This is a definitional presentation of the same conjunction,
not a new hypothesis or a weakened conclusion.

Hypothesis and clause correspondence:

- A small site is `{C : Type u} [SmallCategory C] {J : GrothendieckTopology C}`.
  `A : Type v` and `[CommRing A]` give the coefficient ring. `R` is a commutative
  ring sheaf and `a` its coefficient map into the compatible global sections.
  `t : A` is arbitrary. Module and derived universes remain those of the parent.
- `ringedLocalizationRing R (a t)` is the specified sheafified localization.
  `ringedSiteModules` is used directly, with no additional category alias.
- `E`, `hE`, and `hmap` pin extension on objects and morphisms to the existing
  sheafified `changeOfRings`. Its additive and finite exactness instances express
  the exact scalar-extension functor specified in the node. `E.mapDerivedCategory`
  is its termwise derived functor. `U₀`, `hU₀` and its exactness instances similarly
  pin ordinary restriction and its termwise derived functor.
- H3(1): `unitComplex` is the termwise unit on every complex, normalized by
  `unitSections` in every degree i, on every site object V and every section x.
  After the explicit equality transports for E and U₀, it sends x to the image
  of `1 ⊗ₜ x` under `toSheafify`. Tensor symmetry identifies this with the node's
  `x ⊗ 1`. `derivedUnit`, through `scalarLocalizationTelescopeDerivedUnit`, normalizes
  `adj.unit` on **every** complex K: after
  `E.mapDerivedCategoryFactors` and `U₀.mapDerivedCategoryFactors`, it equals
  `Q.map (unitComplex K)`. Thus eta is the class of the specified termwise map,
  not an arbitrary adjunction unit. These are presentations of the canonical
  unit, not a flatness, boundedness or existence restriction. Every section
  of each source module is covered; no additional naturality hypothesis on a
  chosen family is needed. This follows the existing
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction` normalization convention,
  specialized to exact extension and thus applicable to every representative.
- `∃ b : ℤ, L.IsGE b` is the bounded-below hypothesis. `A₀`, `ι`, and
  `_hc : IsColimit (Cofan.mk A₀ ι)` give the countable coproduct, including n=0.
  `_hs` is exactly `ι n ≫ s = t • 𝟙 L ≫ ι (n+1)`, in Lean's composition order:
  Its explicit `@SMul.smul` uses the existing canonical
  `scalarLocalizationDerivedLinear`, installed by the enclosing instance lambda.
- `Triangle.mk (𝟙 A₀ - s) g h ∈ distTriang ...` is the telescope triangle.
  `e : H ≅ U(F L)` and the displayed equality identify **every** leg, using the fully defined
  `scalarLocalizationTelescopeLeg`, with
  `adj.unit.app L ≫ U.map (t^(-n) • 𝟙 (F L))`. The actual scalar is
  `(IsLocalization.Away.invSelf t)^n` acting by the existing canonical localized
  coefficient action. This retains the accepted existential telescope form.
- The penultimate conjunct is the naturality equation for all derived morphisms
  `f : K ⟶ L` and every n.
- H3(2): the last conjunct is exactly
  `leg (L⟦k⟧) n ≫ ((E.mapDerivedCategory ⋙ U₀.mapDerivedCategory).commShiftIso k).hom.app L
  = (leg L n)⟦k⟧'`, with `scalarLocalizationTelescopeLeg` on both sides. It holds for
  all integers k and every n. It asserts compatibility of the legs, not a
  functorial choice of cone comparisons.

Dependency declarations used: `CategoryTheory.ringedSiteModules` from
`Sheaf.CategoryTheory.RingedSiteModules`; `CategoryTheory.ringedLocalizationRing`
and `ringedLocalizationRingUnit` from `Sheaf.CategoryTheory.RingedSectionLocalizationRing`;
`SheafOfModules.changeOfRings`, `changeOfRingsHom`, and `changeOfRingsPresheaf`
from `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`; `restrictScalars`
from Mathlib's sheaf change-of-rings module;
`CategoryTheory.Functor.mapDerivedCategory` and `mapDerivedCategoryFactors`
from Mathlib's derived-category ExactFunctor; `CategoryTheory.scalarLocalizationDerivedLinear` and
`scalarLocalizationCoefficientMap` from `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom`.
The remaining direct statement imports are the recorded site, tensor and exact-derived
interfaces. The generic leg helper takes the indicated scalar action; in the theorem both
linear structures are instantiated with the retained canonical helpers, not
quantified as arbitrary actions. A repository search for the four helper names
returned no matches; their bodies are the two normalization formulas, leg expression and telescope conjunction
formerly inline in this theorem.

H8: removed the undocumented alias `scalarLocalizationModules`. The theorem docstring
now contains all eight DAG proof steps, with the nodes each uses: scalar colimit including
torsion; tensor--Hom; exactness; complex colimit comparison; actual telescope triangle;
unit and fraction legs; arbitrary triangle comparison; naturality and shifts.

Rule 7/H9: added non-public imports for the stated proof dependencies: module
localization, module sheafification, tensor closedness, ringed-site Grothendieck
abelianness, forgetful exactness, exact-functor factorization, sequential complex
homotopy colimits, and localization universal property. Colimits and triangle
isomorphisms are already supplied by public statement imports.

Import-cycle accounting: the first repaired dry run rejected a direct statement
edge to `lem-weil-pbc-scalar-localization-derived-hom`, because that theorem's proof
uses this item. The delivery now records the existing coefficient definitions in
`def-weil-pbc-scalar-localization-coefficient-actions` and cites that definition
node instead. Its dependencies are just the site, module category, global-section
Hom action, derived category, sheaf localization and coefficient-ring localization;
none requires the Hom comparison theorem. The actual Lean definitions remain in
`ScalarLocalizationDerivedHom`, which the new node records with `existing: true`.
No declaration is duplicated. The reverse proof-only import of
`ScalarLocalizationUnderlyingTelescope` in that module remains omitted under
stages/2-statements.md §3 rule 7, since it would close the physical import cycle.
This records the return's omitted-import option, now with an acyclic DAG edge to
the definition actually used. No downstream Hom theorem is invoked or modified.

Edge cases checked: `t=0`, nilpotent t, zero divisors/torsion, a unit t, the zero
coefficient ring and an empty site impose no new side conditions. The unit formulas
are expressed after sheafification, so they do not assume tensor sheaves have only
sectionwise pure tensors. Stage n=0 uses inverse power zero and gives eta itself.
For k=0 the shift assertion retains the canonical zero-shift comparison; arbitrary
positive and negative k use the same CommShift instance. All variables/universes
are explicitly bound, with `set_option autoImplicit false`.

Searches retained from the packet: `msearch.py leanfinder` for “derived category
telescope triangle direct sum scalar localization” found only generic telescope
and derived-category interfaces; `msearch.py loogle` for “Triangle distTriang
DerivedCategory coproduct” returned a parser error and no matches; `rg` over Mathlib, WeilConjectures
and Sheaf for telescope, hocolim and scalar localization found no exact theorem.
Repair source inspection: read the full `sheafRingDerivedCoefficientAdjunction`
normalization and its termwise unit; read the landed coefficient
helper definitions, the exact-functor factorization signature, and the complex
colimit/homotopy-colimit theorem. No independent new notion is introduced by the repair.

No `STATEMENT-DISPUTED` flag and no informal statement correction: the added
normalizations and shift equation restore the node's existing statement.

Compilation repair: expanding the full induced ordinary adjunction in the unit
normalization was expensive to elaborate. The final signature directly specifies
the complex unit by its degreewise section formula instead, and then uses its
image under Q. The leg expression, normalization
predicates and telescope conjunction are also named as fully defined helpers to avoid repeatedly elaborating
their large categorical types in one statement. No compile wall-time limit was increased.

Verification: the final file passed scompile.py in both sandbox and current-library
checks, with no errors or warnings (52.1 s and 52.3 s overall wrapper timings; each
Lean invocation retained its 60 s limit). The final static self-check confirmed
only lean/stmt_deps changes to the item, the exact recorded signature, all declaration
names, no lines over 100 characters, and exactly the one named theorem sorry.

## New nodes

`def-weil-pbc-scalar-localization-coefficient-actions` records the canonical base
and localized coefficient actions, using the exact existing
`CategoryTheory.scalarLocalizationDerivedLinear` and
`CategoryTheory.scalarLocalizationCoefficientMap` from
`Sheaf.CategoryTheory.ScalarLocalizationDerivedHom`. Its statement specifies
restriction of the global-section Hom action, its induced derived action, and
the unique localized coefficient ring map. Source: Stacks 03DD/04TT, 05RU and
00CM, used in Bhatt--Scholze Proposition 6.8.14(2). There is no new module and no
new Lean construction: this is registration of already constructed data as a
separate definition node, avoiding a false dependence on the parent Hom theorem.
LeanSearch and LeanFinder returned generic sheaf scalar-action results; Loogle
returned `DerivedCategory.instLinear` and its linearity instances. Mathlib grep
returned ordinary module Hom linearity; source grep found the exact two project
definitions. DAG grep found them only as helpers of the Hom theorem, with no
independent definition node; blueprint_refs search found no matching blueprint
node. The complete search result records are in its mathlib_searches. The actual
source bodies were read: `Module.compHom` followed by `DerivedCategory.instLinear`
for the base action, and `IsLocalization.Away.lift` for the unique localized map.
Edge cases include the zero ring, empty site, t=0 and nilpotent t. The item cites
this node for its two canonical linear structures; the new node's dependencies
retain the existing module and localization conventions and explicit universes.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
