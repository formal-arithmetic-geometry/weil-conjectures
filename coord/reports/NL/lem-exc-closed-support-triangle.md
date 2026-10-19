## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle` states
`AlgebraicGeometry.Etale.exists_etale_closedSupportTriangle`, with one `sorry` and no
new definitions or other theorems. Its docstring gives all nine proof steps of the
current DAG node, including the descent of the boundary to every derived morphism.
The node copy changes only `lean`. No statement correction is needed.

Clause-by-clause correspondence:

- Schemes Z, T, U: `{Z T U : Scheme.{u}}`.
- Closed immersion i: `(i : Z ⟶ T) [IsClosedImmersion i]`.
- Open immersion j: `(j : U ⟶ T) [IsOpenImmersion j]`.
- Complementarity: `hij : Set.range i.base = (Set.range j.base)ᶜ`.
  Since both are embeddings, this is precisely the complementary open subset,
  without choosing an additional model of its source.
- Finite ring, not necessarily commutative: `(A : Type (u + 1)) [Ring A] [Finite A]`.
  `CommRing`, `Nontrivial`, and any topology on A are absent.
- The constant coefficient module category is represented by
  `Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)`, exactly the representation
  used by the recorded closed-ambient adjoint. This is the usual encoding of
  modules over the sheafification of the constant ring presheaf: restriction
  to constant scalars gives an A-module-valued sheaf; conversely a local section
  of the constant ring sheaf is locally represented by constants, which act on
  the module sections and glue uniquely. Equality can be tested after refinement,
  so this action is well-defined and its module identities are local. This
  argument uses only left module axioms, including for noncommutative A.
  Module morphisms correspond exactly because they commute with constant scalar
  actions, hence with their local representatives. This is an encoding of the
  same sheaf notion, rather than an extra mathematical assumption.
- Ordinary unbounded derived categories:
  `_root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))`.
  There is no Plus, Bounded, constructibility or finite-amplitude subcategory.
  The scheme universe u and module universe u+1 follow the recorded ambient API;
  every finite ring can be placed in that universe by the usual universe lift.
- Closed direct image: `iPush := R(lowerStar (ModuleCat.{u + 1} A) i)`.
  For a closed immersion lowerStar is exact; its right-derived functor is
  canonically its termwise functor on the derived category. This is precisely
  the direct-image representation in lem-exc-closed-ambient.
- Ri^!: `iPush.rightAdjoint`, supplied by the instance theorem of
  lem-exc-closed-ambient. It is determined by the adjunction universal property.
- Open restriction: `jPull := D(upperStar (ModuleCat.{u + 1} A) j)`.
  This is the termwise functor of the exact open inverse image, using D rather
  than a construction requiring symmetric monoidal coefficients.
- Total unbounded right derived open direct image:
  `jPush := R(lowerStar (ModuleCat.{u + 1} A) j)`.
- Naturality: `∃ δ : jPull ⋙ jPush ⟶ (iPush.rightAdjoint ⋙ iPush) ⋙ shiftFunctor ... 1`.
  This is one natural transformation, not a separate existential boundary for
  each K. Its naturality square is exactly commutation with the third triangle
  arrow; the first two squares are naturality of the counit and unit.
- Every K: `∀ K : _root_.DerivedCategory (...)` after the existential for δ.
- First term i_*Ri^!K and first arrow: the domain of
  `(Adjunction.ofIsLeftAdjoint iPush).counit.app K` is
  `iPush.obj (iPush.rightAdjoint.obj K)`, and its codomain is K.
- Second arrow and third term:
  `(mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app K`
  has domain K and codomain `jPush.obj (jPull.obj K)`.
- Boundary to the shifted first term: `δ.app K` and `shiftFunctor ... (1 : ℤ)`.
- Distinguished triangle: `Triangle.mk ... ... (δ.app K) ∈ distTriang _`.
- No constructibility of Ri^!K: neither K nor its image has any additional binder.

Recorded statement dependencies read and used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom`.
- def-weil-closed-immersion: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- def-weil-open-immersion: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- def-weil-pbc-constant-sheaf: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`, the coefficient sheaf underlying the above encoding.
- def-weil-sheaf-of-modules-category: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, transparently `SheafOfModules`.
  Its category is encoded here by module-valued sheaves as in the ambient dependency.
- def-weil-abstract-derived-category:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory` (the needed instance is supplied by the upstream imports).
- def-weil-pbc-etale-site: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and `Scheme.Etale`.
- def-weil-triangulated-category: Mathlib's `CategoryTheory.Pretriangulated`
  and `CategoryTheory.IsTriangulated`; `Triangle.mk` and `distTriang` express the conclusion.
- def-weil-pbc-direct-image and def-weil-pbc-inverse-image:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `Etale.lowerStar`,
  `Etale.upperStar`, `Etale.upperStarLowerStarAdjunction`. Their ordinary derived
  functors and derived unit are the existing declarations of
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`, notably
  `Etale.mapDerivedUpperStarLowerStarAdjunction`.
- lem-exc-closed-ambient: `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`,
  `Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`, supplies the
  instance used by `Functor.rightAdjoint` and `Adjunction.ofIsLeftAdjoint`.
- lem-weil-pbc-kinjective-total-derived: `Sheaf.CategoryTheory.KInjectiveTotalDerived`,
  `CategoryTheory.exists_rightDerived_of_enough_isKInjective`, imported for the proof
  plan's computation on K-injective representatives. The signature uses the existing
  canonical generic right-derived functor, rather than making a second choice.

The module imports the available proof dependency modules without `public` when they
are not needed in the signature. Several Mathlib proof dependencies and the direct
image right-adjoint comparison are already supplied transitively by those imports.
The size-convention dependency has no module to import.

Edge cases checked mathematically: the empty scheme; Z empty and U=T; Z=T and U empty;
the zero ring; K=0; arbitrarily unbounded K; noncommutative finite matrix rings.
The statement excludes none of these. In the extreme complementary pairs the triangle
reduces to 0 → K → K or K → K → 0, as expected. Naturality includes identity maps,
zero maps and all derived morphisms, not merely maps of chosen representative complexes.

Searches performed before writing:

- msearch.py leanfinder, query `closed immersion open complement natural distinguished
  localization triangle derived sheaves counit unit`: 8 hits on scheme immersion and
  module restriction declarations; no ordinary-derived support triangle.
- msearch.py loogle, query `CategoryTheory.Triangle.mk, CategoryTheory.distTriang`:
  0 hits, unknown identifier CategoryTheory.Triangle.mk (the actual namespace is
  CategoryTheory.Pretriangulated).
- msearch.py leansearch, query `closed immersion derived sheaves support localization
  distinguished triangle`: 8 hits on closed immersion definitions and characterizations,
  no matching triangle.
- msearch.py grep, query `localization.*[Tt]riangle|support.*[Tt]riangle`, subdirectory
  CategoryTheory: 0 hits.
- rg in upstream WeilConjectures/SixFunctors for the node id and support/closed triangle
  patterns found `OpenClosed.Supports.supportLocalizationTriangle_distinguished`.
  Its full signature was read: it is a triangle of a specified complex with injective
  terms, not the claimed natural ordinary-derived adjunction triangle for every K.
- The same search found `Etale.Derived.Localization.existsUnique_distTriang_supportedLocalization`
  and `supportedLocalizationTriangle_mem_distTriang`. Their full signatures and assumptions
  were read: they use the compactification exceptional functors Ri_!, Ri^!, monoidal
  coefficients and functorial flat resolutions. They do not directly provide the
  node's noncommutative coefficient statement with the recorded ambient adjoint.
- rg of shared lean/Sheaf found the ambient adjoint and closed-support amplitude,
  but no existing etale statement of this node. The pro-etale support triangle is
  on a different site and has extra hypotheses. The constant-ring module equivalence
  module was also read; its published interface assumes CommRing, so it was not
  used to impose commutativity on the present statement.

Validation: scompile.py compiled the sandbox module and its library-form import separately,
cleanly, with no non-sorry warnings. The delivery dry run is recorded below after completion.

No STATEMENT-DISPUTED issue, missing prerequisite, new node, or dependency module.

Delivery dry run: deliver2.py --no-push printed OK: the module compiles and preflight
passes, except for the independent second reading intentionally reserved for the second
reader. Nothing was pushed. The first validated dry-run commit was 89a0d9553f.

## Second reading by NL

I read the current node, its blueprint source at order 1804, its nine proof
steps, every statement-dependency record, and the actual declarations used by
the signature. I also read Stacks `etale-cohomology.tex`, Section 09XP,
`lemma-sections-with-support-acyclic` (09XQ), and
`lemma-cohomology-with-support-triangle` (0A45), including the preceding
section-wide assumptions. The source assumes arbitrary schemes and a closed
subscheme with its open complement: no Noetherian, quasi-compact, separated,
characteristic or invertibility hypothesis is implicit. Stacks 0A45 is stated
for an abelian sheaf; the blueprint and the node explicitly extend the
injective-term argument to unbounded complexes and left constant-ring modules.
This is the statement being rendered, not an extra boundedness restriction.

My object/hypothesis/conclusion checklist, matched with the repaired Lean:

| Node item | Lean rendering and verdict |
| --- | --- |
| Three schemes Z, T, U | `{Z T U : Scheme.{u}}`; exact. Mathlib `Scheme` and `Scheme.Hom` are the recorded notions. |
| Closed immersion i: Z → T | `(i : Z ⟶ T) [IsClosedImmersion i]`; exact. I read the class: closed embedding plus surjectivity on stalks. |
| Complementary open j: U → T | `(j : U ⟶ T) [IsOpenImmersion j]` and `hij : Set.range i.base = (Set.range j.base)ᶜ`; exact. The recorded open-immersion definition is the locally ringed-space one. Together these say that j identifies U with the complement; U need not be a specific chosen presentation of that open. |
| Finite ring A, possibly noncommutative | `(A : Type (u + 1)) [Ring A] [Finite A]`; exact. No commutativity, nontriviality or topology is assumed. |
| Constant ring sheaf A_S | Encoded through A-module-valued sheaves, as in the actual ambient-adjoint declaration; exact by the scalar-action identification described below. |
| Sheaves of left A_S-modules on each small etale site | `Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)`; exact encoding. I read the generic `ringedSiteModules` abbreviation and the small-etale topology, rather than identifying modules with abelian sheaves that have forgotten their scalars. |
| Ordinary unbounded D(S_et,A) | `_root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))`; exact. I read Mathlib `DerivedCategory` and `HasDerivedCategory`. There is no bounded or constructible subcategory. |
| Termwise closed i_* | `R(lowerStar (ModuleCat.{u + 1} A) i)`; exact canonical representation up to the usual derived comparison, since closed direct image is exact. It is precisely the functor used by the recorded ambient-adjoint theorem. |
| Its right adjoint Ri^! | `(R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint`; exact, with the instance supplied by `isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`. I read that theorem and Mathlib `Functor.IsLeftAdjoint`, `Functor.rightAdjoint`, and `Adjunction.ofIsLeftAdjoint`. This choice is determined up to the adjunction-compatible isomorphism, not an arbitrary object chosen from bare existence. |
| Open restriction j^* | `D(upperStar (ModuleCat.{u + 1} A) j)`; exact. The actual upstream functor is sheafified inverse image, exact for this open immersion, so D applies it termwise. |
| Total unbounded Rj_* | `R(lowerStar (ModuleCat.{u + 1} A) j)`; exact. I read the upstream generic-derived interface and its unbounded adjunction. No R+ is used. |
| Naturality and every K | `∃ δ : D(upperStar … j) ⋙ R(lowerStar … j) ⟶ ((R(lowerStar … i)).rightAdjoint ⋙ R(lowerStar … i)) ⋙ shiftFunctor … 1`, followed by `∀ K`; exact. One natural transformation supplies all boundaries, including their compatibility with every derived morphism. The other two squares follow from naturality of the fixed unit and counit. |
| First term and first arrow | `(Adjunction.ofIsLeftAdjoint (R(lowerStar … i))).counit.app K`; exact domain i_*Ri^!K and codomain K. |
| Middle arrow and third term | `(mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app K`; exact domain K and codomain Rj_*j^*K. The upstream declaration explicitly needs no monoidal coefficients. |
| Boundary to shifted first term, distinguished triangle | `δ.app K` and `Triangle.mk … ∈ distTriang _`; exact. I read Mathlib's triangle fields and distinguished-triangle notation. The shift is the integer +1. |
| No constructibility of right-adjoint values | No extra predicate or binder on K or Ri^!K; exact. |

For the coefficient encoding, restriction along the constant-presheaf-to-A_S
map takes an A_S-module sheaf to an A-module-valued sheaf with the same
underlying abelian sheaf. In the reverse direction, represent a section of A_S
locally by constants, act on each restriction of a module section by those
constants, and glue. Equality after refinement makes this independent of the
representatives. Module identities and compatibility with restrictions are
local. A map commuting with constant scalars commutes with all these local
scalar actions. These constructions are inverse, preserve the underlying
abelian sheaf, and commute with direct image and restriction, including the
units and counits. Thus the representation does not silently replace A_S by
a different ring sheaf and does not need A commutative. The existing published
`EtaleConstantRingModuleEquivalence` and `ModuleSheafConstantRingEquivalence`
interfaces were opened; both assume `CommRing`, so neither justifies adding
commutativity here. No second definition of modules or derived functors is
introduced.

The actual source signatures for `lowerStar`, `upperStar`,
`upperStarLowerStarAdjunction`, and `mapDerivedUpperStarLowerStarAdjunction`
were checked in `WeilConjectures/SixFunctors/Etale/UpperLowerStar/Defs.lean`
and `Derived/UpperLowerStar.lean`. The sheaf category is Grothendieck abelian
and its derived category exists via the imported instances; these are not
additional mathematical hypotheses. `KInjectiveTotalDerived` was also read:
its theorem supplies total right derivation from enough K-injectives. The
module's proof docstring follows all nine node steps, including injective
terms, the supported kernel, section surjectivity, the exact sequence of
complexes, both adjunction identifications, and descent of boundary naturality
to all derived morphisms. The proof dependencies already stated are present
through the explicit proof imports and their public dependencies. No new node
or dependency module is delivered, and the natural-language node statement
has not changed, so no statement correction or citer audit is needed.

Edge cases: T empty; Z empty with U=T; Z=T with U empty; the zero ring;
K=0; complexes unbounded in both directions; noncommutative finite rings;
and all characteristics are included. The extreme closed-open pairs yield
the standard triangles 0 → K → K and K → K → 0. There is no index-set or
integer-degree hypothesis to exclude an empty index or degree zero. The
explicit universe `u` is bound; schemes and sites use the recorded universe,
and module carriers and coefficient rings use `u+1`, consistently with the
ambient dependency and the small-site convention. No extra universe equality
or restriction on test objects has been introduced. Every finite ring has a
model in this coefficient universe. Naturality includes zero and identity
morphisms, as well as arbitrary morphisms in the derived category.

Independent searches (using different phrases from the first reader):

- `msearch.py leanfinder`: “natural transformation from derived open pushforward
  restriction to shifted closed support counit triangle”; eight hits on
  ordinary module pushforward adjunctions, no matching derived triangle.
- `msearch.py leansearch`: “The unit of open restriction and the counit of
  closed support form a natural distinguished triangle of unbounded derived
  sheaves”; eight hits, including the generic SES triangle and restriction
  units, no matching etale statement.
- `msearch.py loogle`: `DerivedCategory.triangleOfSES_distinguished`; one
  generic SES-triangle hit. An earlier attempted query using `distTriang` as
  an identifier failed because it is notation; it was not counted as a match.
- `rg` over Mathlib category theory and homology for `recollement` and
  triangle/support combinations found no exact statement. Searches over the
  upstream SixFunctors tree and the shared `lean/Sheaf` tree, by support,
  localization and boundary terminology, found the following near matches.
- I opened upstream `OpenClosed/Supports.lean`: its
  `supportLocalizationTriangle_distinguished` concerns a specified complex
  with injective terms, not the canonical derived adjunction triangle natural
  in every K. I opened `Etale/Derived/Localization.lean`: its
  `existsUnique_distTriang_supportedLocalization` uses the compactification
  exceptional adjunction and monoidal/flat-resolution hypotheses, absent for
  general noncommutative A. It cannot replace the present declaration.
- I opened the project's `ProEtaleClosedSupportTriangle` signature: it is on
  the pro-etale site and assumes locally Noetherian/compact T and discrete
  coefficients, so it is a different statement. A full-name search confirmed
  no upstream or existing shared declaration of
  `exists_etale_closedSupportTriangle`.

Mismatch found and repaired: the worker used three `let` binders in the
statement (`iPush`, `jPull`, `jPush`). The standing brief explicitly forbids
these because they elaborate as `have` binders that obstruct later unfolding.
I expanded them to their existing functor expressions; this changes no
mathematical data or hypothesis. I updated `lean.statement` to be verbatim
the repaired signature. The shared-base node comparison changes only `lean`.
No other part of the module needed rewriting. All lines are at most 100
characters, auto-implicit variables are disabled, all universes and variables
are bound, and the sole theorem body remains `sorry` with its complete proof
plan. There are no definitions, hollow data, local instances or private copies.

Validation: `scompile.py NL lem-exc-closed-support-triangle
lean/Sheaf/AlgebraicGeometry/EtaleClosedSupportTriangle.lean` compiled both the
sandbox and library forms cleanly (2.2 s and 2.5 s), without non-sorry warnings.

Second-reader delivery dry run: `deliver2.py NL lem-exc-closed-support-triangle
--no-push` printed `OK (dry run): commit 589bae9c9c passes the preflight and
compiles; nothing pushed`. The staged set was exactly this report, the item's
node JSON, and the item's Lean module.
