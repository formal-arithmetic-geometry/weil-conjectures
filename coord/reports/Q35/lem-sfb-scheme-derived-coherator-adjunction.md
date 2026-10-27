## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeDerivedCoheratorAdjunction` states
`AlgebraicGeometry.Scheme.Modules.exists_schemeDerivedCoheratorAdjunction`.
Its sole postponed proof is that named theorem. `DerivedCoheratorAdjunctionData`
is a structure packaging the simultaneous objects and assertions of this node;
its parameters abstract the two categories so that the chosen abelian structure
is used consistently in complexes, derived functors and the Hom formula.
There is no new module category, quasi-coherence predicate, localization, or
right-derived-functor construction. No data is defined using `sorry` or chosen
from a mere existence assertion.

Sources read: `literature/stacks-project/perfect.tex`, section-coherator,
Tag 08D6, opening paragraphs; `properties.tex`, proposition-coherator,
Tag 077P (2), including its proof. These say that the ordinary coherator exists
for any scheme and its right derived extension is right adjoint to the canonical
functor from D(QCoh) to D(Mod). No statement correction is needed.

Hypothesis and clause correspondence:

| Node | Lean rendering |
| --- | --- |
| Any scheme T | `(X : Scheme.{u})`, with no compactness, separation, Noetherian, characteristic, or nonemptiness binder. |
| Small Zariski module category M_T | `SheafOfModules.{u} X.ringCatSheaf`, exactly `ringedSiteModules` specialized to the small Zariski ringed site. This avoids changing category instances through the separately bundled `Scheme.Modules` wrapper. |
| Full quasi-coherent category A_T | `(SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory`, exactly the category in the recorded Grothendieck-generator dependency. In particular this is D(QCoh), not the full subcategory D_QCoh of the ambient derived category. |
| Induced abelian structure | The package's `abelian` field, with `inclusionAdditive`, `inclusionFiniteLimits` and `inclusionFiniteColimits`. Additivity of this faithful full inclusion forces its addition to be the inherited addition; finite limits and colimits give the induced exact abelian structure. These are conclusions, not assumptions on X. |
| Inclusion i_T | The existing full-subcategory functor `.ι`, passed as `i` to the package. |
| Additive left exact ordinary coherator | `coherator`, its `additive` and `leftExact` fields, and `adjunction : i ⊣ coherator`. |
| Unbounded Rq_T exists | The output field `resolutions` is the arbitrary-quasi-isomorphism K-injective-resolution hypothesis of the recorded definition. C_T is literally `coherator.rightDerivedFunctorOfQuasiIsoResolutions resolutions`. Its universal unit and uniqueness are those of that recorded definition, with no second choice or definition here. |
| Derived categories | The ambient `HasDerivedCategory.{w}` binder specifies the chosen localization, as required by Mathlib's derived-category interface. The package supplies its own quasi-coherent derived category in universe `max uA vA` (here u+1), where the standard localization always exists. The ambient localization universe w remains independent; it is not equated with u or u+1. No additional geometric existence assumption is made. |
| Termwise derived inclusion I_T | `i.mapDerivedCategory`; the exactness fields supply its hypotheses. `i.mapDerivedCategoryFactors` is its canonical comparison on every complex. Mathlib supplies its canonical `CommShift ℤ` and `IsTriangulated` instances. |
| Derived right adjunction | `derivedAdjunction : i.mapDerivedCategory ⊣ coherator.rightDerivedFunctorOfQuasiIsoResolutions resolutions`. Its `homEquiv` is a natural bijection by the adjunction API. |
| Canonical integer shifts on C_T | The field `shift`, with `canonicalShift : NatTrans.CommShift (coherator.rightDerivedFunctorOfQuasiIsoResolutionsUnit resolutions) ℤ`. The source homotopy and localization shifts are fixed Mathlib comparisons. On a K-injective J the derived unit is invertible, so its shift square uniquely forces C_T's comparison at QJ to be the termwise comparison conjugated by that unit. Every derived object has such a representative, so naturality forces the comparison everywhere. This specifies the canonical comparison rather than an arbitrary shift transported from an adjunction. |
| C_T triangulated with these comparisons | The `triangulated` field uses precisely the `shift` field. I_T's triangulated instance is supplied by the recorded exact-functor factorization. |
| Actual unit and counit commute with shifts | `compatible : derivedAdjunction.CommShift ℤ`; this is Mathlib's condition on the actual adjunction unit and counit for the already specified shift structures. |
| Chain-map representative normalization | `normalization`, quantified over every cochain complex B, every K-injective complex J, and every chain map `f : (i.mapHomologicalComplex (.up ℤ)).obj B ⟶ J`. The left side applies `derivedAdjunction.homEquiv` to `i.mapDerivedCategoryFactors.hom.app B ≫ DerivedCategory.Q.map f`. The right side localizes the ordinary termwise adjunct `(adjunction.mapHomologicalComplex (.up ℤ)).homEquiv B J f`, then applies the quotient/Qh comparisons and the canonical right-derived unit at J. That unit is invertible because J is K-injective. All transports are displayed; the comparisons do not get replaced by arbitrary isomorphisms. |

Recorded statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, a transparent abbreviation of `SheafOfModules`.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`, whose public
  imports supply `SheafOfModules.IsQuasicoherent` / `isQuasicoherent`. The recorded
  finite-type conjunction is not imposed: this node needs quasi-coherence alone.
- `lem-sfb-qcoh-grothendieck-generators`:
  `Sheaf.AlgebraicGeometry.QuasiCoherentGrothendieckGenerators`,
  `AlgebraicGeometry.Scheme.Modules.quasiCoherent_grothendieck_generators`.
  This uses exactly the same full-subcategory inclusion and is a proof import
  as well as the source of the induced abelian structure.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Qh`,
  `DerivedCategory.quotientCompQhIso`.
- `def-sfb-right-derived-functor`:
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` and its `Unit`.
  Its recorded universal, uniqueness and K-injective-unit theorems explain the
  canonical normalization in the statement.
- `lem-weil-pbc-exact-functor-derived-factorization`: the exact recorded Mathlib
  match `CategoryTheory.Functor.mapDerivedCategoryFactors`, in
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, together with
  `mapDerivedCategory`, its canonical shifts and triangulated instance.

All stated proof dependencies have their modules imported, including the adjoint
functor theorem, preservation of limits, Grothendieck module sheaves, K-injective
resolutions, homotopy triangulation, K-injective Hom bijections, preservation of
K-injectives by a right adjoint, termwise adjunction, canonical derived-adjunction
shifts and triangulated right adjoints. The theorem docstring gives all five
proof steps and the corresponding DAG ids. No dependency record was replaced.

Edge cases checked before writing and again against the final signature:
empty schemes; zero sheaves, B=0 and J=0; arbitrary unbounded B and J; arbitrary
integer shifts including zero and negative shifts; arbitrary schemes without
quasi-compactness or quasi-separatedness. For f=0 the termwise adjunct and its
localization are zero, as they should be. K-injectivity is required only of J,
not of B or of i(B), and there is no termwise-injectivity restriction. The output
resolution assertion does not require a monomorphism. There are no free or
automatically bound variables (`autoImplicit false`). Site/module size remains u;
the derived localization hom universe w is independent.

Searches performed with the prescribed msearch.py wrapper:

- LeanFinder: `The derived coherator is right adjoint to the inclusion of quasi coherent complexes on any scheme`.
  Eight results: sheaf/presheaf forgetful right adjoints, module pushforward,
  open restriction adjunctions and scheme-module pseudofunctors; none is this
  quasi-coherent inclusion or its derived adjunction.
- Loogle: `"IsQuasicoherent", "IsRightAdjoint"`: zero hits.
- Mathlib grep: `coherator|QCoh.*[Aa]djoint|[Aa]djoint.*QCoh`: zero hits.
- LeanSearch: `The inclusion of quasi coherent modules on a scheme has a coherator right adjoint and a derived adjunction`.
  Eight hits: `IsQuasicoherent.mk`, `isQuasicoherent`, `QuasicoherentData`,
  sheaf-to-presheaf right adjoint, pullback/pushforward and restriction
  adjunctions. None states the required result.
- `rg` of the same concept in both `lean/WeilConjectures` and `lean/Sheaf`:
  `exists_dqCoheratorAdjunction` is about D_QCoh, assumes compactness and
  quasi-separatedness, and is not the present D(QCoh) result. The algebraic-space
  `exists_derivedCoheratorAdjunction` likewise concerns D_QCoh and imposes atlas
  compactness/separation conditions. Read both signatures and docstrings.
- `grep -rn 'lem-sfb-scheme-derived-coherator-adjunction' lean/WeilConjectures`:
  no existing declaration for this node.
- `rg` for both new declaration names in Mathlib/project upstream-name records
  and both project source trees: no name collision.

No new nodes, dependency modules, node corrections or statement disputes.

## Second reading by Q35

Re-read the node and the final module clause by clause, separately from drafting.
The initial scheme-specific data package mixed the bundled `Scheme.Modules`
category instance with the ambient full-subcategory instance and failed to type.
The repaired package abstracts the inclusion and fixes one abelian structure
before forming complexes; the theorem specializes it to precisely the recorded
quasi-coherent full inclusion in `SheafOfModules`. It now compiles with the
ambient derived universe independent of the sheaf universe.

Checked the essential distinctions: D(QCoh) versus D_QCoh; arbitrary schemes
versus qcqs schemes; K-injective versus bounded or termwise-injective complexes;
ordinary adjunct of a chain map versus an unconstrained derived Hom bijection.
The final right side of `normalization` traverses Q(qJ), Qh(quotient(qJ)),
Qh(K(q)(quotient J)), C(Qh(quotient J)), and C(QJ), in that order, so it has
exactly the same target as the adjunction Hom bijection. The fixed termwise
left comparison has the correct orientation. `canonicalShift` fixes the right
shift by the derived unit; `compatible` is imposed on these same comparisons.
All requested assertions are present. The only theorem proof remains `sorry`.
The maintainer supplies the independent review described in the dispatch brief.
