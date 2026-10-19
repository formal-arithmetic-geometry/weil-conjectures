## Worker report

Item: `def-weil-linear-scalar-localization`, group NF, stage 2.

The module `Sheaf.CategoryTheory.ScalarLocalization` constructs the raw scalar
localization, its localization functor, and the induced linear endofunctor/shift.
No statement correction, new node, or dependency replacement was needed. The
item's JSON changes only in `lean`.

Source read: the complete blueprint file
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-rationalization-karoubi.md`,
especially its displayed Hom tensor E formula and its explicit instruction that
no Karoubi completion is taken. The general ring version and the shift laws are
spelled out in this item's statement and in its category-law dependency.

Clause-by-clause correspondence:

- A commutative ring R is `(R : Type r) [CommRing R]`; the element varpi is
  `(p : R)`. Its localized coefficient ring is Mathlib `Localization.Away p`,
  with its canonical `Algebra R` and `algebraMap` structures.
- An R-linear category C is `(C : Type u) [Category.{v} C] [Preadditive C]
  [Linear R C]`. No additive-category or biproduct hypothesis is imposed.
- Objects are precisely the original objects, via the one-field wrapper
  `ScalarLocalization R C p`, constructor `ScalarLocalization.mk`, and field
  `obj : C`. The wrapper separates instances and does not adjoin any objects
  or retracts.
- The `category` instance defines Hom(K,L) to be
  `Localization.Away p ⊗[R] (K.obj ⟶ L.obj)`. This is the module base change in
  the convention of the recorded `LinearMap.baseChange` declaration. The
  source's Hom-first tensor is canonically identified with this scalar-first
  tensor by `TensorProduct.comm`; `f ⊗ a` is represented as `a ⊗ₜ[R] f`.
- `composition R C p K L M` is the unique localized-ring bilinear extension
  supplied by the FIRST conjunct of
  `exists_linear_scalarLocalization_category R C p`. This first conjunct is
  `∃!`, so its specification determines the chosen map uniquely. We do not
  select unspecified category or module data from the theorem's second,
  existential conjunct. The only choice is this uniquely determined bilinear
  map, as permitted by AGENTS.md section 5.
- `composition_tmul` states exactly the pure-tensor formula:
  `composition ... (a ⊗ f) (b ⊗ g) = (a * b) ⊗ (g ≫ f)`.
  Lean's `g ≫ f` is the source's `f` composed after `g`.
- Identities in `category` are `(1 : Localization.Away p) ⊗ₜ[R] 𝟙 K.obj`.
  `composition_laws` states both unit laws and associativity. The `category`
  instance uses these named proofs, with no `sorry` inside definition data.
- The `preadditive` instance uses the tensor's existing abelian groups and
  the extended composition's linear-map additivity. The `linear` instance
  uses the tensor's existing localized-ring module structures and the
  extended composition's linear-map homogeneity. These are genuine
  constructions, not existentially chosen structures.
- The `linearOriginal` instance uses the canonical R-module structure on
  the tensor and `LinearMap.restrictScalars R` on its composition maps.
  This is exactly restriction along `R → Localization.Away p`, not an
  independent R-action.
- `localization` is Q, with `obj K := ⟨K⟩` and
  `map f := (1 : Localization.Away p) ⊗ₜ[R] f`. Its identity proof is
  definitionally `rfl`; its composition proof is the named
  `localization_laws` statement. `localization_linear` and the two
  corresponding instances state that Q is additive and R-linear.
- An R-linear shift is represented by `(T : C ⥤ C) [T.Additive]
  [T.Linear R]`. `mapHom` is literally
  `(T.mapLinearMap R).baseChange (Localization.Away p)`, and therefore
  sends `a ⊗ f` to `a ⊗ T.map f` by `LinearMap.baseChange_tmul`.
  `map` has object map `K ↦ ⟨T.obj K.obj⟩` and uses this Hom map.
  `map_laws` gives its functor laws; `mapAdditive` and `mapLinear` expose
  its additivity and localized-ring linearity directly from `mapHom`.
- The automorphism hypothesis is an inverse `(S : C ⥤ C)` with
  `hTS : T ⋙ S = 𝟭 C` and `hST : S ⋙ T = 𝟭 C`, exactly as in the recorded
  category-law dependency. No linearity hypothesis on S is added.
  `map_automorphism` states existence of an additive, localized-ring linear
  inverse S', its object formula, its pure-tensor formula induced by S,
  and BOTH strict inverse equations. Its final equality
  `T ⋙ localization R C p = localization R C p ⋙ map R C p T` is precisely
  Q composed with the original shift equals the induced shift composed
  with Q (Lean's functor-composition notation is left-to-right).
- The parenthetical coefficient-field specialization is already the
  imported `Padic.coefficientExtension_localization_uniformizer`, with
  `Padic.coefficientExtensionIntegers` and
  `Padic.coefficientExtensionUniformizer`. It identifies the localization
  with E, including the induced tensor identification. It is not an
  extra hypothesis on the general construction and is not duplicated.

Dependency declarations read in full and used:

- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`;
  `Mathlib.RingTheory.Localization.Away.Basic` supplies its ring/algebra instances.
- `Mathlib.CategoryTheory.Linear.Basic`: `CategoryTheory.Linear`.
- `Mathlib.CategoryTheory.Linear.LinearFunctor`:
  `CategoryTheory.Functor.Linear`, `Functor.mapLinearMap`;
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`: `Functor.Additive`.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `LinearMap.baseChange`,
  `LinearMap.baseChange_tmul`, and the module-base-change conventions
  including `TensorProduct.AlgebraTensorModule.distribBaseChange`.
- `Sheaf.CategoryTheory.LinearScalarLocalization`:
  `CategoryTheory.exists_linear_scalarLocalization_category`.
- `Sheaf.NumberTheory.Padics.CoefficientExtension`: the recorded coefficient
  integers, absolute value, uniformizer, residue field, ideals, finite
  rings, degree, and transition definitions were read.
- `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`:
  `Padic.coefficientExtension_localization_uniformizer`.

All six postponed statements belong to this definition node's construction
and have source citations and full natural-language proof plans in their
docstrings: `composition_tmul`, `composition_laws`, `localization_laws`,
`localization_linear`, `map_laws`, and `map_automorphism`. Every theorem proof
is `sorry`. Definition and instance data contain no `sorry`.

Edge cases checked against the formulas: C may be empty; R may be the zero
ring; p may be zero, nilpotent, a unit, or a zero divisor. No nontriviality,
nonzeroness, torsion-freeness, or injectivity assumption is used. Inverting
zero or a nilpotent yields the zero coefficient ring and zero Hom modules;
the original object set remains unchanged. If p is a unit, the construction
still uses the same tensor definition. Objects have universe u and morphisms
have universe `max r v`, so large rings and independently large Hom types
are allowed. The identity shift and arbitrary strict linear automorphisms
are included. There is no extra shift structure required when C has no shift.

Searches (2026-10-15; index: consulted):

- `msearch.py ... leansearch "scalar extension linear category tensor product morphisms"`:
  unavailable, Internal Server Error; this is not counted as a negative result.
- `msearch.py ... leanfinder "Scalar extension of a linear category: tensor each morphism module with a localized commutative ring"`:
  eight hits; categorical localization linearity and `ModuleCat.coextendScalars`,
  none constructing the requested tensor-Hom category.
- `msearch.py ... loogle "CategoryTheory.Linear, LinearMap.baseChange"`:
  zero hits.
- `msearch.py ... grep "scalarExtension|ScalarExtension|scalarLocalization|ScalarLocalization|baseChange" CategoryTheory/Linear`:
  zero hits.
- `rg` in Mathlib's relevant Linear, Preadditive and tensor files confirmed
  the existing linear category, linear functor, and module-base-change APIs;
  no tensor-Hom scalar-localization construction was found.
- `rg` for `scalarLocalization|ScalarLocalization|scalarExtension|ScalarExtension`
  in the project and source repository found unrelated module and derived
  scalar extension, plus the stated category-law dependency. It found no
  existing definition of the requested category. A focused search for
  `ScalarLocalization|scalarLocalization` in `dag/lean_names_upstream.json`
  and the source tree returned no match (index consulted for every new name,
  all of which live under `CategoryTheory.ScalarLocalization`).
- `grep -rn 'def-weil-linear-scalar-localization'` in the source repository:
  no match. The landed dependency file was opened in full; its only
  declaration is the existence theorem, not a definition of this category.

Server validation: `scompile.py NF def-weil-linear-scalar-localization` on the
complete delivered module succeeds, with no errors or warnings (2.7 seconds
for the delivered module, nice 19, two threads, 60 seconds per file). All
universes and variables are explicitly bound. No local compiler was run.

## Second reading by NF

Independent second reader, 2026-10-15. Read the item JSON, the entire delivered
ScalarLocalization module, every statement-dependency node and its recorded
source declarations. No mathematical or implementation mismatch was found;
no Lean or node field needed changing. This section is the only review change.

Source check: read the complete blueprint definition
`def-weil-rationalization-karoubi.md`, and Bhatt--Scholze's Introduction,
page 2, including its categorical tensor-with-Q_l display and qualifications.
The former explicitly defines the raw Hom tensor E construction without
Karoubi completion. The latter motivates this coefficient change, rather than
imposing a scheme hypothesis on an arbitrary linear category. Also read
Stacks `dga.tex`, definitions 09MJ and 09MK and the surrounding section:
linear categories are explicitly not required to be additive. There is no
standing Noetherian, geometric, finiteness or nontriviality hypothesis for
this algebraic construction.

Object/hypothesis/conclusion checklist, matched against the node:

1. R is any commutative ring, p any element, and A = R[1/p] with its canonical
   R-algebra map: `(R : Type r) [CommRing R] (p : R)` and
   `Localization.Away p`. Opened the actual `Localization.Away` abbreviation
   (localization at `Submonoid.powers`) and its ring-localization API. Pass.
2. C is any R-linear category: `(C : Type u) [Category.{v} C]
   [Preadditive C] [Linear R C]`. Opened `CategoryTheory.Linear` and both
   functor classes. Preadditivity supplies exactly the abelian groups and
   additive composition required by modules, with no biproduct assumption.
   Pass.
3. Objects are unchanged: `ScalarLocalization` has exactly one field
   `obj : C`, and `localization.obj K = mk K`. The wrapper is in bijection
   with C and introduces neither formal retracts nor other objects. Pass.
4. Hom is Hom_C(K,L) tensor_R A: `category.Hom K L` is definitionally
   `Localization.Away p ⊗[R] (K.obj ⟶ L.obj)`. Opened the recorded
   `LinearMap.baseChange` declaration in Tower.lean: scalar-first order
   is the dependency's declared convention, identified with Hom-first order
   by tensor commutativity. Its existing tensor module action is precisely
   the localized coefficient action. Pass.
5. Composition is the bilinear extension with the specified formula:
   `composition` chooses only the unique bilinear map in the FIRST conjunct
   of `exists_linear_scalarLocalization_category`; `composition_tmul`
   specifies `(a*b) ⊗ (g ≫ f)`. Opened that dependency theorem in full:
   its binders are the same arbitrary ring, category and p, and its first
   conjunct is an actual uniqueness specification for this map. Choosing it
   is allowed by the non-hollow-definition rule. Lean's `g ≫ f` is exactly
   the source's f composed after g. Pass.
6. Identity, associativity and localized-ring linearity:
   `category.id` is `1 ⊗ 𝟙`, `composition_laws` supplies both units and
   associativity, and `preadditive`/`linear` use the existing tensor groups
   and modules with the linear maps' compatibility laws. No unspecified
   category witness is selected from the dependency. Pass.
7. Q is identity on objects, f maps to f tensor 1, and Q is R-linear:
   `localization`, `localization_laws`, `localization_linear`,
   `localizationAdditive`, `localizationLinear`. `linearOriginal` restricts
   the tensor action along the canonical algebraMap, through
   `restrictScalars R`; it does not posit an unrelated action. Pass.
8. An R-linear automorphism/shift induces the corresponding localized
   automorphism: T has `[T.Additive] [T.Linear R]`; `mapHom` is literally
   `(T.mapLinearMap R).baseChange A`. Opened `baseChange_tmul`: it sends
   `a ⊗ f` to `a ⊗ T.map f`. `map` uses `T.obj` on objects and this Hom map;
   `map_laws`, `mapAdditive`, `mapLinear` give its required structures.
   The automorphism premise is a strict inverse S with both equations,
   as in the recorded category-law dependency. `map_automorphism` supplies
   a localized-ring linear inverse, its object and pure-tensor maps, and
   both inverse equations; no extra linearity premise on S is imposed.
   Its final `T ⋙ localization = localization ⋙ map` is exactly Q after T
   equals induced T after Q. Pass.
9. Parenthetical O_E specialization: opened
   `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`
   and `coefficientExtension_localization_uniformizer`. The imported latter
   theorem gives the canonical localization algebra isomorphism and its
   induced tensor identification, for every finite extension E/Q_l.
   Those are the dependency's actual coefficient objects, not substitutes.
   This contextual specialization needs no repeated theorem here. Pass.

Edge cases: empty C remains empty; zero objects require no additional
structure. A zero ring, p = 0, nilpotent p, units and zero divisors are all
allowed. Inverting zero/nilpotents collapses Hom modules without deleting
objects, which still forms a category. No injectivity, nonzero-p or
nontrivial-ring premise sneaks in. There is no index-set or positive-integer
restriction; the localization includes p^0. Characteristic is unrestricted.
Universes r (ring), u (objects), v (original Hom) are independently bound,
with localized Hom universe `max r v`. No scheme or nonempty-category
hypothesis appears. The strict identity automorphism is included.

Independent duplicate search, using different wording from the first reader:

- LeanFinder: "Change coefficients in an enriched preadditive category by
  tensoring its hom modules with an algebra": eight hits, chiefly
  `TransportEnrichment.enrichedOrdinaryCategory`, `ForgetEnrichment`, and
  generic enriched-category structures. Opened the transport declaration:
  it requires enrichment and a special bijection on maps from monoidal units;
  it is not a definition of this tensor-Hom localization of an arbitrary
  `Linear R C` category.
- Loogle: `"baseChange", "Category"`: twelve hits about stability of
  morphism properties under categorical base change, not coefficient change.
- msearch grep in Mathlib CategoryTheory:
  `changeOfRings|changeCoefficients|extendScalars|tensorHom`: hits are
  monoidal tensor-on-morphisms operations, not tensoring Hom modules.
- Direct rg of upstream WeilConjectures and the project's Lean, plus the
  upstream name index, with scalarLocalization/ScalarLocalization and
  scalarExtension/ScalarExtension found only the already-read category-law
  existence theorem in the relevant category API; other results concern
  modules and derived-category scalar extension. Broader changeOfRings,
  changeCoefficients and tensorHom searches likewise concern module/sheaf
  functors and monoidal structure. No existing definition matches the item.

There are no new definition nodes or dependency modules in this delivery,
and no statement correction or citer verdict to audit. The recorded
`lean.statement` is verbatim the structure signature in the module.
Every postponed proof is a named theorem with its source and explicit proof
plan; all six proofs remain `sorry`. Definition/instance data are concrete
or use named laws; there is no local notation, private substitute, hidden
universe or unbound variable. Structural field proofs do not prove an extra
stage-2 theorem.

Second-reader validation: scompile.py compiled the entire delivered file
cleanly on the server (2.7 seconds), and checked both side-only dependency
imports separately (1.2 and 1.4 seconds). Each ran nice 19, two threads,
60 seconds per file, with no errors or warnings. No local compiler or global
build was run.
