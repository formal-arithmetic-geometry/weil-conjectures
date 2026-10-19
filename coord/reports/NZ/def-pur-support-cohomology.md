## Worker report

The module `Sheaf.AlgebraicGeometry.SupportCohomology` defines the group-valued
kernel-of-restriction functor and its right derived functors on the small étale site,
and the identical constructions with module coefficients on the small pro-étale site.
All definitions have real data. The one postponed theorem is the additivity of this
kernel functor, the proof obligation needed for the node's derived-functor clause;
it is named, listed in `lean.declarations`, and has its source and complete proof
description in its docstring. No statement correction or dependency repair was needed.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean realization |
| --- | --- |
| A scheme `X`, a closed immersion `i : Z ↪ X` | `{Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]`. There is no noetherian, separatedness, smoothness, characteristic, or nonemptiness assumption. |
| The complementary open immersion `j : U ↪ X` | `Scheme.supportOpenComplement i` is the open subset with underlying set `(Set.range i)ᶜ`; its canonical immersion is `(Scheme.supportOpenComplement i).ι`. This chooses the actual open complement, rather than adding another unspecified open or a hypothesis about its support. An arbitrary presentation of the complementary open is canonically isomorphic to this one. |
| Small étale site and abelian sheaves | `Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`, using the recorded sheaf convention. |
| `G(X) → G(U)` is restriction along `j` | `Etale.supportRestrictionArrow i` is the morphism from the complement object to `Scheme.Etale.mk (𝟙 X)`. The presheaf restriction is `G.obj.map (supportRestrictionArrow i).op`. |
| The group `Γ_Z(X,G)` is the kernel | `CategoryTheory.Sheaf.supportedSectionsFunctor` has object field `kernel (G.obj.map j.op)`; `Etale.supportSections i` specializes it to the indicated restriction arrow and coefficient category. |
| A morphism acts by its section map restricted to the kernels | The map field is `kernel.map`, with vertical maps `f.hom.app (op V)` and `f.hom.app (op W)` and commutative square `f.hom.naturality j.op`. The identity and composition fields are kernel uniqueness. This specifies the canonical map, not an arbitrary morphism between kernel objects. |
| The displayed construction is a functor to abelian groups | Its type is `Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}`. The named helper `supportedSectionsFunctor_additive` states the additivity needed by Mathlib's derived APIs. |
| A torsion abelian sheaf `F` | The underlying sheaf type is the recorded abelian-sheaf category. Torsion is the existing `Scheme.IsTorsionAbelianSheaf F`; nothing in the construction depends on its proof. The node explicitly defines `Γ_Z` on **all** abelian sheaves, so its derived functors are defined on that entire category and can be evaluated at every torsion `F`. There is no second construction on a torsion subcategory. |
| For `q ≥ 0`, `H^q_Z(X,F) = R^q Γ_Z(X,-)(F)` | `Etale.supportCohomology i (q : ℕ) F` is `((supportSections i).rightDerived q).obj F`. The natural-number index includes degree zero. |
| Computation using any injective resolution `F → I•` | `Etale.supportCohomologyIso i q F (I : InjectiveResolution F)` is the canonical isomorphism to the degree-`q` cohomology of `((supportSections i).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex`, defined by the existing `I.isoRightDerivedObj`. Thus the chosen resolution inside `rightDerived` does not replace the node's arbitrary-resolution formula. |
| A bounded-below complex `K`, with torsion cohomology | `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})` represents a bounded-below derived object. On the intended subdomain each cohomology sheaf is torsion. The functor is defined on all bounded-below objects, as is the right derived functor in the source, and its restriction to those with torsion cohomology needs no new definition or extra choices. |
| `RΓ_Z` is the bounded-below right derived functor | `Etale.derivedSupportSections i := (supportSections i).rightDerivedFunctorPlus`. Enough injectives and derived-category instances come from the existing sheaf/derived APIs, with no extra hypotheses. |
| `H^q_Z(X,K) = H^q(RΓ_Z(X,K))`, for every integer | `Etale.supportHypercohomology i (q : ℤ) K` is the object of `DerivedCategory.Plus.homologyFunctor _ q` on `(derivedSupportSections i).obj K`. Negative degrees are retained. |
| Identical construction on the small pro-étale site | `ProEtale.supportRestrictionArrow i` uses `Scheme.ProEt.mk`; `ProEtale.supportSections i Λ` specializes the **same** generic kernel functor to `Scheme.ProEt.topology X`. No second site, restriction operation, or kernel definition is introduced. |
| Finite-torsion coefficients in the twist conventions | `Λ : Type (u + 1)` with `[CommRing Λ]`, and `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)`, are the ordinary module-sheaf convention of the validated finite-coefficient framework. In particular one may take every coefficient ring `A_{E,n}` of the node, including its zero-ring case. The construction works for arbitrary coefficient rings and therefore imposes no extra condition on the finite-torsion cases. No Tate twist is constructed or silently substituted: a twisted coefficient sheaf is simply an input sheaf. |
| Right derived functors in that topology | `ProEtale.supportCohomology`, `supportCohomologyIso`, `derivedSupportSections`, and `supportHypercohomology` use precisely the same Mathlib APIs, in the module-sheaf category. |
| Cohomology in the corresponding derived category | The natural-number formula uses `HomologicalComplex.homologyFunctor`, and the derived-complex formula uses `DerivedCategory.Plus.homologyFunctor`, in the appropriate coefficient category. |

The definitions extending to all coefficients or sheaves do not assert additional theorems
or alter the object defined on the torsion cases: they use exactly the kernel and derived
functor prescribed by the node. In particular no torsion condition is imposed on the terms
of an injective resolution, and bounded-below torsion cohomology is not confused with a
complex whose terms are torsion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`, including
  its closed embedding and closed image. The canonical complement inclusion has Mathlib's
  `IsOpenImmersion` instance from
  `Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion`.
- `Mathlib.AlgebraicGeometry.Sites.Etale` (through `Sites.AffineEtale`):
  `Scheme.smallEtaleTopology`, `Scheme.Etale.mk`. The recorded abelian-étale-sheaf notion is
  Mathlib's `CategoryTheory.Sheaf` with `AddCommGrpCat.{u + 1}`.
- `Sheaf.AlgebraicGeometry.TorsionEtaleSheaf`: `Scheme.IsTorsionAbelianSheaf`, read to
  check the intended input subdomain; its predicate is not needed as data to define the
  unrestricted functor.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the recorded derived-category conventions
  and `Etale.DerivedCategory.torsionCohomology`, read for the distinction between torsion
  cohomology and torsion terms. The actual abelian-sheaf derived category and its `Plus`
  category are Mathlib's `DerivedCategory` and `DerivedCategory.Plus`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `Scheme.proEtaleDerivedCategory`,
  read and imported as the recorded general-site convention. For finite coefficients the
  validated framework uses the ordinary `Sheaf (Scheme.ProEt.topology X) (ModuleCat Λ)`
  encoding (see `coord/pefw-upstream-framework.md` and
  `WeilConjectures.AlgebraicGeometry.ProEtale.Proetale.Sheafification`). The small site is
  the existing `Scheme.ProEt`, not a replacement site.
- `Mathlib.CategoryTheory.Abelian.RightDerived`: `Functor.rightDerived` and
  `InjectiveResolution.isoRightDerivedObj`; the latter's signature was read in full and is
  used directly for both resolution comparison isomorphisms. `InjectiveResolution` is
  Mathlib's existing resolution structure, not a local copy.
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`:
  `Functor.rightDerivedFunctorPlus` and `DerivedCategory.Plus.homologyFunctor`.
- The recorded enough-injectives declaration is
  `CategoryTheory.IsGrothendieckAbelian.enoughInjectives`, with Mathlib's existing
  Grothendieck-abelian sheaf instances. The compile synthesizes the instances for both
  coefficient categories. No chosen `Abelian` instance or arbitrary natural isomorphism
  is postulated.
- `def-coefficient-twists-detailed` describes the permissible coefficient objects; it has
  no recorded declaration. This delivery does not require constructing those objects or
  their twists: its arbitrary coefficient ring and arbitrary module sheaf accept each
  such coefficient and twist. Consequently no missing coefficient construction is used.

Edge cases checked before writing and against the resulting definitions:

- Empty `Z`: the complement is all of `X`; restriction is canonically the identity and
  its kernel is zero. No nonempty-support assumption occurs.
- Full support, including the identity closed immersion: the complement is empty;
  sheaf sections there are zero, so the kernel gives all global sections.
- Empty `X`: both sites and complement objects still exist and the sheaf axiom gives
  zero sections over the empty scheme; the formulas remain defined.
- Zero sheaf and zero coefficient ring: categorical kernels and derived functors still
  apply. No `Nontrivial Λ` or positive characteristic is assumed.
- `q = 0` is included in the natural-number definition; every negative integer is
  admitted by hypercohomology. A bounded-below complex may start in a negative degree.
- Nilpotent structure on the closed subscheme does not change its topological open
  complement, as required for sections supported on its image.
- The small pro-étale site's object and morphism universes are kept as supplied by its
  existing definition. The generic helper has independent site-morphism and
  coefficient-morphism universes `v` and `w`; no artificial equality between them is
  imposed. All variables and universes are explicitly bound.

Searches for an existing definition (performed with `msearch.py NZ
def-pur-support-cohomology`, and direct read-only searches):

- LeanSearch, `kernel of restriction on sections of a sheaf as an additive functor`:
  unavailable, `Internal Server Error`; not treated as evidence of absence.
- LeanFinder, `support cohomology purity cohomology with support`: eight unrelated
  results concerning injectives and derived support bounds; no supported-section functor.
- LeanFinder, `additive functor sending a sheaf to the kernel of restriction along an
  arrow of its site`: eight results including `sheafIsAbelian`,
  `presheafToSheaf_additive`, `Sheaf.cohomologyPresheafFunctor`, and `Scheme.kerFunctor`;
  none defines the requested group-valued restriction kernel.
- Loogle, `"Sheaf", "support"`: twelve results about ideal-sheaf supports; no match.
  The earlier unquoted query was rejected as an unknown identifier and was replaced
  with this successful query.
- Mathlib grep, `support.*cohomology|cohomology.*support`: no matches. Further grep for
  `sectionsWithSupport|supportedSections|cohomologyWithSupport|supportCohomology` and
  `supportedSectionsFunctor|sectionsWithSupport|restrictionKernel`: no matches.
- `rg` of the upstream project for support/sections names found
  `AlgebraicGeometry.ProEtale.sectionsWithSupport` in
  `WeilConjectures/SixFunctors/ProEtale/Derived/ClosedImmersion.lean`; read its definition
  and docstring. It is a **sheaf-valued** kernel of the unit `N → j_*j^*N`, not the
  group-valued kernel of `N(X) → N(U)`. Its `closedUpperShriek` is a further pullback
  of that sheaf. Neither gives this node's functor or derived supported global sections.
- `rg` of `lean/Sheaf` for the same support/cohomology names found no existing
  definition of this node's notion. Searches of the upstream declaration-name index
  and the node id in the upstream sources found no exact match either.
- `tools/blueprint_refs.py search sections support` returned sixteen nearby nodes.
  `def-exc-proetale-sections-with-support` is the sheaf-valued construction above;
  `def-pur-flasque-support` is a property of sheaves, not supported cohomology. The
  present node is the existing DAG owner of the group-valued construction. No new
  independent notion or duplicate definition node is needed.

Source cross-check: [Stacks Project, Tag 09XP](https://stacks.math.columbia.edu/tag/09XP)
defines `Γ_Z` on all abelian sheaves by this kernel and then takes its right derived
functors. [Tag 04FS](https://stacks.math.columbia.edu/tag/04FS) confirms the support
interpretation. These agree with the node's kernel, complement and derived-functor
clauses. There is no `STATEMENT-DISPUTED` issue.

Validation: `scompile.py NZ def-pur-support-cohomology` compiled the delivered module
cleanly against the published library (including the separate sandbox/library checks).
The local stage-2 text/record checker reports no failures. The required `deliver2.py
--no-push` dry run is the final verification; no second-reading section is authored here.

## Second reading by NZ

I reread the node statement, its dependency records, and the source place
`sec-smooth-purity/sk-def-purity-conv/def-pur-support-cohomology` (the node's
Stacks cross references are Tags 09XP and 04FS). The item-by-item list and verdicts
are:

| Node object or clause | Lean rendering and verdict |
| --- | --- |
| Scheme `X` | `X : Scheme.{u}`; the recorded Mathlib `AlgebraicGeometry.Scheme` is the same scheme notion. Pass. |
| Closed immersion `i : Z ↪ X` | `{Z X : Scheme.{u}}`, `i : Z ⟶ X`, `[IsClosedImmersion i]`; exactly the recorded closed-immersion predicate. Pass. |
| Open complement `j : U ↪ X` | `i.openComplement.ι`, the canonical open complement supplied by the existing `Scheme.Hom.openComplement` declaration, is used in both sites. It has the required `IsOpenImmersion` instance and range the complement of `i`; no arbitrary unrelated open is introduced. Pass. |
| Abelian sheaves on the small étale site | `Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`; this is the recorded `Ab(X_et)` encoding. Pass. |
| Restriction `G(X) → G(U)` | `supportRestrictionArrow i` is the arrow from `Etale.mk i.openComplement.ι` to `Etale.mk (𝟙 X)`, and `supportedSectionsFunctor` evaluates `G.obj.map j.op`. Pass. |
| Definition of `Γ_Z(X,G)` | `supportedSectionsFunctor` has object `kernel (G.obj.map j.op)`, exactly the displayed kernel. Pass. |
| Action of a sheaf morphism | Its map is `kernel.map` with the two evaluation maps and `f.hom.naturality j.op`; identity and composition are proved by kernel uniqueness. Pass. |
| Functor and additivity | `supportSections i` has type `Sheaf ... AddCommGrpCat ⥤ AddCommGrpCat`; `supportedSectionsFunctor_additive` supplies the postponed additivity theorem required by right-derived APIs. Pass. |
| Torsion sheaf `F` | The existing `Scheme.IsTorsionAbelianSheaf F` is the stated input predicate; the functor is defined on all abelian sheaves and hence applies to every torsion `F`, without adding a termwise-torsion hypothesis. Pass. |
| `H^q_Z(X,F)=R^qΓ_Z(X,-)(F)`, `q≥0` | `supportCohomology i q F := ((supportSections i).rightDerived q).obj F`; `q : ℕ` includes zero. Pass. |
| Any injective resolution formula | `supportCohomologyIso` takes `I : InjectiveResolution F` and uses `I.isoRightDerivedObj` to identify the result with degree-`q` homology of the termwise supported complex. Pass. |
| Bounded-below `K` with torsion cohomology | `derivedSupportSections i` is the bounded-below right-derived functor on `DerivedCategory.Plus` and `supportHypercohomology` applies its integer homology; the definitions are total on `D+`, so the node's torsion-cohomology subdomain is included without changing it. Pass. |
| `H^q_Z(X,K)=H^q(RΓ_Z(X,K))`, `q∈ℤ` | `supportHypercohomology i q K` uses `DerivedCategory.Plus.homologyFunctor ... q`; negative degrees remain admitted. Pass. |
| Small pro-étale analogue | `ProEtale.supportRestrictionArrow`, `supportSections`, `supportCohomology`, `supportCohomologyIso`, `derivedSupportSections`, and `supportHypercohomology` repeat the same kernel and derived construction on `Scheme.ProEt.topology X`. Pass. |
| Finite-torsion coefficient convention | `Λ : Type (u + 1)` with `[CommRing Λ]` and `ModuleCat.{u + 1} Λ`; every finite-torsion coefficient object from `def-coefficient-twists-detailed` is accepted, with no nontriviality or characteristic assumption. Pass. |
| Corresponding derived category | The étale and pro-étale definitions use the corresponding `DerivedCategory.Plus` and homology functors in their coefficient categories. Pass. |

Edge cases checked: empty `Z` gives the identity restriction and zero kernel; full
support (including the identity closed immersion) gives the complement with zero
sections and hence all sections; the empty scheme, zero sheaf, and zero coefficient
ring are admitted; `q = 0` is included and integer hypercohomology includes negative
indices; bounded-below complexes may start in a negative degree; nilpotent structure
on `Z` does not alter the topological complement. The site and coefficient universes
are retained (`Scheme.{u}`, `AddCommGrpCat.{u+1}`, and `ModuleCat.{u+1} Λ`) without an
extra equality or finiteness hypothesis.

I repeated the three required searches. LeanFinder/Loogle and Mathlib grep found no
supported-section or support-cohomology construction. The upstream project search
found `AlgebraicGeometry.ProEtale.sectionsWithSupport`, but that is a sheaf-valued
kernel of `N → j_*j^*N`, not the group-valued kernel in this node. It also found the
existing canonical complement `AlgebraicGeometry.Scheme.Hom.openComplement` in the
imported closed-immersion module. I removed the worker's duplicate
`Scheme.supportOpenComplement` definition and changed both restriction arrows to use
`i.openComplement.ι`; this is the only mismatch found. No dependency module or new
node is needed, and the node statement itself remains unchanged. The module compiles
cleanly with `scompile.py` after this repair.
