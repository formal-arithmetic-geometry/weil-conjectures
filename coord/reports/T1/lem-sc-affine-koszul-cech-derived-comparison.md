## Worker report

The item is stated in `lean/Sheaf/AlgebraicGeometry/AffineKoszulCechDerivedComparison.lean`
as `AlgebraicGeometry.affine_koszul_cech_derived_comparison`. No statement correction,
dependency replacement, or disputed statement is needed. The conclusion is invertibility
of the specified canonical morphism in D(A). This is exactly the quasi-isomorphism
formulation of the node: its right-hand side is a derived object, and the node's proof
explicitly identifies its conclusion with an isomorphism in D(A).

The construction was absent, so three definition nodes and their modules are included.
Every theorem, including verification/existence theorems needed by definitions, has proof
`by sorry`. Every definition has actual data; choices are made only from named existence
theorems that specify the objects, differential, component maps, or resolution roof.
There is no arbitrary map hypothesized in the item's theorem.

The node's hypotheses and clauses correspond as follows:

| Node text | Lean rendering |
|---|---|
| A commutative ring | `(A : Type uT) [CommRing A]` |
| X = Spec(A) | Every sheaf-module carrier uses `(Spec (.of A)).toRingedSpace`; no unrelated affine scheme is supplied. |
| f_1,...,f_r, including r=0 | `(r : ℕ) (f : Fin r → A)`; there is no positivity or nonzero hypothesis. |
| U is the union of the principal opens | `koszulOpen A r f`, the existing definition `⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)` |
| F is a complex of quasi-coherent O_X-modules | `F : CochainComplex (SheafOfModules (moduleRings (Spec (.of A)).toRingedSpace)) ℤ`, with `hF : ∀ n : ℤ, (F.X n).IsQuasicoherent` |
| F represents E in D_QCoh(O_X) | `E : schemeDerivedQCohCategory (Spec (.of A))` and `e : DerivedCategory.Q.obj F ≅ E.obj` |
| M = Γ(X,F) | `((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F`; sections use the Mathlib A-module structure, not just underlying abelian groups. |
| e≥1 and the shifted tail I^i = K^(i-1) for i≤0, zero otherwise | Index a : ℕ represents exponent a+1. `(koszulOpenTail A r f a).extend ComplexShape.embeddingDownNat` has term K_(n+1) in degree -n and negative Koszul differential. It is the existing power tail, with no replacement Koszul definition. |
| Canonical power transitions | `koszulOpenTransition A r f a b h`, extended by `HomologicalComplex.extendMap`; `koszulCechHomDiagram_exists` specifies precomposition on every homogeneous cochain. |
| Total Hom over A | `CochainComplex.moduleHomComplex` uses the existing `HomComplex.Cochain` and `HomComplex.δ_hom A`, with differential d_M z - (-1)^n z d_I. |
| Filtered colimit of these complexes | `koszulCechHomColimit` is `colimit (koszulCechHomDiagram ...)`, in complexes of A-modules; Mathlib computes this degreewise. |
| Canonical map obtained through Koszul-to-alternating-Čech comparison | `koszulCechDerivedComparison` is `DerivedCategory.Q.map (koszulCechComparison ...) ≫ principalCechDerivedComparison ...`. The cocone's defining equation fixes every localized basis component and the exact totalization sign. |
| Derived sections over U | `(affineOpenSections A U).rightDerivedFunctor.obj (DerivedCategory.Q.obj F)`, followed by the same functor's map of `e.hom`. This is RΓ(U,E) in D(A), including the A-action induced by A→Γ(U,O). |
| Quasi-isomorphism | `IsIso` of that composite in `DerivedCategory (ModuleCat A)`. The theorem does not assert a bare unrelated isomorphism. |

The localization equation in `koszulCechCocone_exists` says
`(product f_j)^(a+1) • image(z)_J = (-1)^(pq+p(p-1)/2) • restriction(z(e_J))`.
Here p=card(J)-1, q=n-p. Its left multiplier is invertible on D(product f_j), so the
formula specifies the actual map rather than just an existence claim about some map.
The increasing exterior basis vector is constructed by Mathlib's `exteriorPower.ιMulti`,
`Finset.orderEmbOfFin`, and the existing tail's `extendXIso`.

`principalCechDerivedComparison_exists` fixes the Čech-derived comparison by the square
for *every* K-injective resolution F→J. It composes with RΓ of the resolution, the existing
`rightDerivedFunctorObjQIso`, and the canonical section-to-Čech augmentation on J, to give
Q of the Čech map induced by F→J. Since that augmentation and the resolution are
invertible after localization, this characterizes the canonical roof uniquely.
Its invertibility on quasi-coherent F is *not* put in the definition: it remains the
item's theorem.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`, read in Scheme.lean, including the local-affine condition and docstrings.
- `def-pc-derived-category`: `Sheaf.AlgebraicGeometry.DerivedCategory`,
  `schemeDerivedCategory`, `schemeDerivedQCohProperty`, and `schemeDerivedQCohCategory`.
  The shared category is `SheafOfModules (moduleRings X.toRingedSpace)` with Mathlib's
  Abelian instance; no chosen second Abelian/category structure is introduced.
- `def-weil-pbc-koszul-complex`: `Sheaf.Paper.KoszulComplex`,
  `ExteriorAlgebra.koszulComplex` and `koszulBoundary`; read the whole recorded signatures
  and their exterior-power, contraction, and square-zero docstrings. These are used through
  `def-sc-koszul-open-system`: `Sheaf.AlgebraicGeometry.KoszulOpenSystem`,
  `koszulOpenTail`, `koszulOpenTransition`, and `koszulOpen`.
- `def-pur-hom-complex`: read `Sheaf.Algebra.Homology.HomComplex` and all signatures.
  It is an *internal sheaf-valued* Hom complex on a general ringed site, so it cannot be
  applied to the node's complexes of A-modules to obtain Hom_A. Nothing about this
  dependency's own notion is wrong, and it is not replaced. The new module-valued wrapper
  instead uses Mathlib's already-existing homogeneous cochains and signed *linear*
  differential. It does not redefine the internal sheaf Hom.
- Other reused infrastructure: Mathlib `CochainComplex`, `HomologicalComplex.extendMap`,
  `extendXIso`, `ModuleCat`, `modulesSpecToSheaf`, and `exteriorPower.ιMulti`; the upstream
  `Functor.rightDerivedFunctor` and `Functor.rightDerivedFunctorObjQIso`; the existing
  ringed-space Grothendieck/K-injective-resolution instances.

Edge cases checked before and during writing:

- r=0: there are no nonempty subsets of Fin 0, hence the total Čech terms are zero;
  positive exterior powers of the zero free module give zero tails, so every Hom term
  and its colimit vanish; U is empty and its section/derived-section functor vanishes.
- F=0: global sections, Hom, Čech terms, and derived sections all vanish. Representation
  transport then identifies E with zero.
- A is the zero ring: Spec A is empty and the definitions include it; no nontrivial-ring
  instance is required.
- Nilpotent f_j and empty intersections: the associated principal opens are empty, so
  their sections are zero. The localization equation remains valid there.
- r=1: p=0, the sign is 1, and the map is the usual localization of the coefficient
  complex. For r=2, the p=1 sign is (-1)^q; combined with the negative tail differential
  it yields the ordinary alternating restriction difference. This checks the nontrivial
  totalization sign against Tag 08D1.
- Repeated generators and arbitrary characteristics are allowed. The cover is indexed by
  indices, not distinct functions; signs use integer scalar multiplication.
- F is unbounded in both directions: totalization has finitely many subset rows, but no
  vertical bound is introduced. Product versus direct-sum totalization agrees because
  the horizontal indexing set is finite. The ring/sheaf universe follows the shared
  `schemeDerivedCategory` convention; source and target localization universes wT,vT are
  independent and explicitly bound.

Searches (all msearch outputs are retained in the sandbox's searches.jsonl; the new node
records include the relevant outputs with dates):

- LeanFinder: “Koszul Hom complexes compare with derived sections on a principal open
  cover”: 8 hits, on generic affine localization and cover sections, no exact statement.
- Loogle: `CochainComplex.HomComplex, HomologicalComplex.QuasiIso`: 0 hits, unknown latter
  identifier. A subsequent valid query `CochainComplex.HomComplex.δ_hom` found the existing
  linear differential and its apply lemma, which are reused.
- Mathlib grep: `Koszul.*Cech|alternating.*Cech.*derived`: 0 hits;
  `moduleHomComplex|principalCechTotal|koszulCechComparison|alternating.*Cech`: 0 hits.
- LeanFinder: “A module valued total Hom complex for unbounded cochain complexes of A
  modules”: 8 hits; it found the group-valued `CochainComplex.HomComplex`, the module
  structure on its cochains, and generic linear Yoneda/complex results. Its group-valued
  complex does not expose the required ModuleCat-valued complex; its cochains are reused.
- Mathlib grep `HomComplex|δ_hom` in Algebra/Homology/HomotopyCategory: 25 returned hits,
  including the exact existing definitions read in HomComplex.lean.
- LeanFinder: “alternating Cech total complex for a finite principal open cover and Koszul
  Hom comparison”: 8 hits on generic simplicial/representation/Mayer–Vietoris machinery,
  no principal-cover alternating totalization or Koszul localization cocone.
- LeanSearch queries for module total Hom, alternating Čech totalization, and filtered
  Koszul Hom colimit comparison all returned “service unavailable: Internal Server Error”.
  Recorded as unavailable, with no mathematical inference from the failed service.
- `rg` in WeilConjectures and lean/Sheaf found no delivered names or matching constructions;
  the item's blueprint-id search in WeilConjectures also found no declaration. The current
  upstream name index contains no delivered names; upstream-overlaps.md was read.
- DAG title/concept searches and `blueprint_refs.py search` found the existing Koszul power
  system, general sheaf Hom, first-quadrant double totalization, single-module Čech
  comparison, and the two comparison theorem nodes. They do not supply the module-valued
  Hom wrapper or the unbounded alternating principal-cover construction being added.

Source text was read online because the literature files are not present on this machine:
[08D1](https://stacks.math.columbia.edu/tag/08D1),
[08D2](https://stacks.math.columbia.edu/tag/08D2),
[08D0](https://stacks.math.columbia.edu/tag/08D0),
[08C2](https://stacks.math.columbia.edu/tag/08C2), and
[0A8H](https://stacks.math.columbia.edu/tag/0A8H).
The item remains the same statement. No hypothesis such as Noetherian, regular sequence,
unit-ideal generators, or boundedness is added.

All four modules compiled together locally with relaxedAutoImplicit=false,
autoImplicit=false, and the standard warnings enabled: no errors and no warnings.
The dry-run server/preflight result is recorded below after it runs.

## New nodes

`def-sc-module-total-hom-complex` defines the ModuleCat-valued Hom complex of unbounded
A-module cochain complexes. Source: Stacks 0A8H. Its actual terms and differential are
Mathlib's existing `HomComplex.Cochain` and `δ_hom A`. Only shape and square-zero
verification are postponed. The recorded LeanFinder/Loogle/grep results found these
ingredients and the group-valued HomComplex, not the required A-module-valued complex.
Its module is `Sheaf.Algebra.Homology.ModuleHomComplex`.

`def-sc-principal-open-alternating-total` defines the finite-subset alternating total
complex with explicit sections and the exact signed differential, its coefficient
functor, restriction augmentation, and canonical derived-section roof. Source:
Cohomology 20.25, 08C2, and Perfect 08D2. It introduces the A-module section functor
using Mathlib's existing restriction-of-scalars sheaf functor. The existing open derived
sections node is AddCommGrp-valued, so it cannot retain the required A-action; this
construction supplies that action without replacing its existing additive-group notion.
The existing Čech machinery uses all tuples or single-module coefficients, and the
existing double-total node is first-quadrant. None is this finite alternating construction
with unbounded coefficients. Its module is `Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal`.
The K-injective augmentation verification has its own named theorem and full proof sketch;
no quasi-coherent derived comparison is assumed in a definition.

`def-sc-koszul-cech-comparison-construction` defines the directed module-Hom diagram,
its colimit, ordered basis evaluation, the specified localization cocone, and its derived
comparison. Source: Perfect 08CX/08D0/08D1/08D2. It uses the existing Koszul power tails
and comparison maps verbatim. The existence statement for the cocone specifies every
component by an equation with an invertible denominator and the source's sign. The
existing DAG comparison nodes are theorem nodes and carry no construction declarations;
no source or Mathlib declaration supplies this cocone. Its module is
`Sheaf.AlgebraicGeometry.KoszulCechComparisonConstruction`.

The three new node files have only the prescribed fields, cite the definitions they
use, and are all reachable through the item's added stmt_deps. All verifying `sorry`
theorems are recorded in their owning definition nodes' lean.declarations and carry
that node's blueprint id and source/proof docstrings. No library or source checkout
was edited by the worker.

Final validation: the server compile is clean. `deliver2.py T1
lem-sc-affine-koszul-cech-derived-comparison --no-push` printed `OK (dry run)`;
its only deferred requirement is the independent second reading. Nothing was pushed.
The preflight ancestry check required the complete created.item chain, rather than the
shortened cached blueprint.from.via on the item's base node. The new nodes now carry
that complete chain as computed by tools/blueprint_refs.py; no existing ancestry field
was changed. The second-reading section is intentionally left for the second reader.

## Second reading by T1

I independently reread the node, its source places (Stacks Tags 08D1 and 08D2), the
three added definition nodes, and all four delivered modules. The correspondence is:

| Node item | Lean rendering and verdict |
|---|---|
| Commutative ring A, X = Spec(A) | `(A : Type uT) [CommRing A]` and `Spec (.of A)` throughout; exact. |
| Finite list f₁,…,fᵣ, including r = 0 | `(r : ℕ) (f : Fin r → A)`; no positivity, distinctness, or unit hypothesis; exact. |
| Principal-open union U | `koszulOpen A r f = ⨆ i, PrimeSpectrum.basicOpen (f i)`; exact. |
| Quasi-coherent complex F | `F : CochainComplex (SheafOfModules (moduleRings ...)) ℤ` with
  `hF : ∀ n, (F.X n).IsQuasicoherent`; exact termwise formulation. |
| Representation by E in D_QCoh | `E : schemeDerivedQCohCategory (Spec (.of A))` and
  `e : DerivedCategory.Q.obj F ≅ E.obj`; exact. |
| M = Γ(X,F) | `((affineOpenSections A ⊤).mapHomologicalComplex
  (ComplexShape.up ℤ)).obj F`; it retains the induced A-module structure; exact. |
| Shifted tails Iᶦ = Kⁱ⁻¹ for i ≤ 0, zero otherwise | `koszulOpenTail` followed by
  `extend ComplexShape.embeddingDownNat`; exponent `e+1` and negative differential are
  explicit; exact. |
| Power transitions and filtered Hom colimit | `koszulOpenTransition`,
  `koszulCechHomDiagram`, and `koszulCechHomColimit`; exact. |
| Total A-linear Hom complex | `CochainComplex.moduleHomComplex`, using Mathlib's homogeneous
  cochains and `HomComplex.δ_hom A`; exact, with no loss of the module action. |
| Alternating Cech total and canonical Koszul map | `principalCechFunctor` and the explicit
  cocone in `koszulCechCocone_exists`, including denominator and sign; exact. |
| Derived sections over U | `(affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.obj
  (DerivedCategory.Q.obj F)` and transport along `e.hom`; exact D(A)-valued target. |
| Quasi-isomorphism conclusion | `IsIso (koszulCechDerivedComparison ... ≫ ...map e.hom)` in the
  derived category. This is the derived-category formulation of the node's quasi-isomorphism
  claim; no stronger representative-level assertion is made. |

Edge cases were checked: `r = 0` gives the empty union and zero alternating rows; positive
exterior powers of the zero free module make the Koszul Hom colimit zero. A zero complex F
gives zero on both sides. The zero ring and nilpotent or repeated generators are allowed, and
no characteristic, Noetherian, regular-sequence, boundedness, or universe restriction beyond
the displayed shared universes is introduced. Unbounded cochain degrees are retained. The
signs specialize to 1 for one generator and to the usual alternating Cech signs for two.

I repeated the existing-definition searches with `rg` over Mathlib, `WeilConjectures`, and
`lean/Sheaf`, and with LeanFinder/Loogle queries for module-valued Hom complexes, alternating
principal-open Cech totals, and the Koszul-to-Cech comparison. They found only generic Mathlib
Hom cochains and unrelated Cech/localization results; no exact existing declaration. The three
added definition nodes therefore remain necessary and each module uses the node's single notion
rather than a private duplicate. No mismatch was found and no source or node statement was
changed. All four modules compile together with `scompile.py` without errors.
