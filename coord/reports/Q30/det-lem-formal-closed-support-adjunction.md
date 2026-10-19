## Worker report

The module `Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction` states
`AlgebraicGeometry.ProEtale.CondensedRing.formal_closed_support_adjunction`.
Its only postponed proof is that theorem. Fourteen declarations are recorded:
the statement and the explicit coefficient-action transport, support-kernel functor,
closed support functor, inclusions, comparison, and their inherited structures.
No node statement or dependency list is changed; no new node is needed.

Hypotheses and objects, matched against the blueprint source:

- An arbitrary condensed ring is `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}`
  with `[MonObj Λ]`. There is no `IsCommMonObj` assumption, admissibility condition,
  discrete topology, finite scalar ring, or choice of the scalar ring Λ(*).
- `X Z V : Scheme.{u}`, `i : Z ⟶ X`, `[IsClosedImmersion i]` give the closed immersion.
  `j : V ⟶ X`, `[IsOpenImmersion j]`, `[QuasiCompact j]` give precisely the
  quasi-compact open immersion. `hij : Set.range j = (Set.range i)ᶜ` says it is the
  complement. No qcqs, Noetherian, separated, or finite-type hypothesis is imposed on X.
- `FormalSupportModules Λ T` is an abbreviation of the published `CategoryTheory.Mod`
  category over `condensedRingObj Λ T = p_T^*Λ`. It is the ring-object presentation
  of the same module sheaves, with both distributive laws retained. Its abelian and
  Grothendieck structures are the published module-object structures, not chosen instances.
- The three explicit `HasDerivedCategory.{u+2}` binders implement the common enlarged
  universe of def-weil-size-convention. They are localization-existence data, supplied
  by `HasDerivedCategory.standard`; they impose no geometric condition. The small
  pro-etale site retains its object universe u+1 and morphism universe u.
- `formalSupportPullback` applies the existing sheaf inverse image to the module
  action and transports scalars along the inverse of `condensedPullbackHom`.
  `formalSupportPullbackAdjunction` is the lifted sheaf adjunction composed with
  that scalar equivalence and the existing canonical direct-image comparison.
  Thus its unit is the actual module inverse/direct-image unit.
- `formalSupportKernel` is literally `kernel` of that unit on objects, and
  `kernel.map` on maps with its commutative square supplied by unit naturality.
  `formalClosedSupport` is its composite with closed inverse image. These are the
  arbitrary-condensed-ring version of the recorded finite-coefficient construction,
  rather than a change of coefficient sheaf or an independent exceptional adjoint.

Clause correspondence:

1. `IsIso (formalSupportKernelComparison Λ i j)` identifies the support kernel
   with `i_* Gamma_Z`, through the canonical closed unit on the kernel.
   `PreservesFiniteLimits (formalClosedSupport Λ i j)` gives left exactness;
   additivity is already an explicit structural instance. The existential `a`
   is the sheaf adjunction `i_* ⊣ Gamma_Z`. Its counit is normalized by
   `comparison.app M ≫ a.counit.app M = kernelInclusion.app M`.
   This determines the adjunction and fixes the support map canonically.
2. `formalClosedSupport.rightDerivedFunctor` is the existing total right-derived
   construction. The statement includes invertibility of its derivation unit on
   every K-injective target. Its source module and the recorded generalized
   `rightDerivedFunctorOfQuasiIsoResolutions` implement the same universal pair;
   in these Grothendieck categories the standard monomorphic resolutions exist,
   so the published standard construction applies directly, without adding a
   resolution hypothesis or making a new derived-functor definition.
   The existential `b` has type `D(i_*) ⊣ RGamma_Z`, and is required to equal
   `a.mapDerivedCategoryRightDerivedAdjunction`. Exactness of i_* is supplied
   existentially as `hclosed`, rather than assumed.
   The global RHom assertion is stated on all complexes A and K-injective I.
   `Gamma_Z(I)` is asserted K-injective. The isomorphism of the actual Mathlib
   `CochainComplex.HomComplex` complexes has each component exactly the ordinary
   adjunction Hom bijection (`e.hom.f n`, `Cochain.v`, `a.homEquiv`). These complexes
   compute the two global derived Homs. In degree n they are products of global
   Hom groups, with the signed Hom differential; no identification of internal
   Hom sheaves on different sites is asserted. The component formula fixes the
   comparison and hence its naturality in both variables.
3. For each `[Injective I]`, `Epi ((formalSupportPullbackAdjunction Λ j).unit.app I)`
   is surjectivity as a module-sheaf morphism, i.e. local surjectivity on sections.
   It is not the incorrectly stronger assertion of surjectivity on every object.
4. `δ` is a natural transformation from `j^* ⋙ Rj_*` to
   `RGamma_Z ⋙ D(i_*) ⋙ shiftFunctor _ 1`. For every unbounded derived object K,
   `Triangle.mk (b.counit.app K) (c.unit.app K) (δ.app K) ∈ distTriang _`
   is exactly the displayed supported triangle. The equation fixing `c` to
   `(formalSupportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction`
   fixes the second arrow to the canonical derived open unit. The last quantified
   clause takes any distinguished triangle `F → K → Rj_*j^*K → F[1]` with this
   same unit and gives `RGamma_Z K ≅ i^*F`. This expresses precisely the fibre
   formula, without assuming a chosen functorial cone in a triangulated category.
   Naturality of the displayed triangle is expressed by the two adjunction natural
   transformations and δ, not by an objectwise choice of connecting maps.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedSupport`:
  `Scheme.sfIntrinsicSectionsWithSupport`, `Scheme.sfIntrinsicClosedUpperShriek`,
  and the `sfConstantModule*` operations. These give the recorded finite case and
  the formula generalized here. Their finite CommRingCat interface is not falsely
  applied to an arbitrary condensed ring.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`:
  `Profinite.continuousMapRingSheaf`, `continuousMapRingObj`, `continuousMapRingSheafMap`;
  and `...Condensed.EllAdic`'s four ring abbreviations, read as the closed upstream
  audit of sk-def-sfb-condensed-ring. Only the general ring-object notion is needed.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `ProEtale.coefficientRing`, `condensedRingObj`, `condensedPullbackHom`, its
  `IsMonHom` and `IsIso` instances, and `condensedPushforwardHom`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.lowerStar`, `linearLowerStar`, `comapPullbackHomCompIso`;
  and `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`:
  `Mod.comapEquivalenceOfIsIso`, `Adjunction.mapModAdjunction`.
  The usual `CondensedRing.upperStar` requires commutativity because extension
  of scalars uses bimodules there. The isomorphism-transport API used here does not.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`;
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `Scheme.proEtaleSheafInverseImage`,
  `proEtaleSheafDirectImage`, `proEtaleSheafAdjunction`. The underlying inverse image
  is the same published pro-etale sheaf functor, not another site model.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, read
  together with Mathlib `SheafOfModules`; the module-object presentation supplies
  the same sectionwise linear action data for ring objects of abelian sheaves.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  `...QuasiCompact`: `QuasiCompact`. Only the latter part of the finite-type node
  occurs, as required for j.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`, `Qh`,
  `HasDerivedCategory.standard`; `Mathlib.CategoryTheory.Triangulated.Pretriangulated`:
  `Pretriangulated`, `distTriang`, `Triangle.mk`; `...Triangulated.Triangulated`:
  `IsTriangulated`; `Mathlib.CategoryTheory.Preadditive.Injective.Basic`:
  `Injective`, and `...Resolution`: `InjectiveResolution`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions`, its unit and universal
  property, read in full; `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`:
  `Functor.rightDerivedFunctor`, `rightDerivedFunctorUnit`, their universal
  instance and invertibility on K-injectives. These are compatible universal
  constructions; the latter is used directly in the Grothendieck case.

All already-stated proof-dependency modules are imported, including open/closed
ringed geometry, site exactness, weakly-etale slice localization, module
Grothendieck categories, extension by zero, module sheafification, complex SES
triangles, K-injective derivation and the termwise adjunction. The theorem's
proof docstring follows all eleven proof steps, including the explicit local
cocycle and boundary calculation for the canonical fibre map.

Edge cases checked before and after writing:

- Empty X, empty Z (j an isomorphism), and empty V (i a nilpotent closed immersion
  with whole underlying support): the functor formula and all four clauses still
  express the expected zero/identity equivalences. No nonemptiness hypothesis occurs.
- Zero coefficient ring and zero objects give zero categories/complexes; neither
  a nontrivial ring instance nor characteristic or cardinality restriction appears.
- Noncommutative coefficients: only `MonObj` is bound, and compilation confirms
  all scalar-transport and direct-image signatures accept that generality.
- Arbitrary unbounded complexes: no `Plus`, constructible predicate, Tor bound,
  compactness of X, or injectivity of every arbitrary K-injective term is assumed.
  Degreewise injective resolutions are used only in the proof plan of the triangle.
- A sheaf epimorphism need not be objectwise surjective. The statement correctly
  uses `Epi`, and the proof plan obtains even a split epimorphism on injectives.
- The fibre comparison quantifies over a distinguished fibre of the specified
  arrow, avoiding any assumption that cones are globally chosen or unique as data.

Searches (2026-10-18):

- `msearch.py ... leansearch "The kernel of the unit for restriction to an open subset
  defines sections supported on a closed subset"`: unrelated restriction/basic-open
  matches; no matching theorem.
- `msearch.py ... leanfinder "Sections with closed support are right adjoint to closed
  immersion direct image and give a derived localization triangle"`: module
  pushforward/restriction adjunctions and ideal-sheaf adjunction; no full result.
- `msearch.py ... loogle "CategoryTheory.Adjunction, CategoryTheory.Limits.kernel"`:
  zero hits.
- `msearch.py ... grep "supportedSections|closedUpperShriek|sectionsWithSupport|homComplex"
  CategoryTheory`: existing generic HomComplex references, no all-coefficient support theorem.
- `rg` in Mathlib's Algebra/Homology finds the exact global `CochainComplex.HomComplex`
  and its `Cochain.v`; this existing object is used, not redefined.
- `rg` in upstream WeilConjectures for closed support/adjunction finds
  `SixFunctors/ProEtale/Derived/ClosedImmersion.lean`, which handles fixed-scalar
  ModuleCat-valued sheaves, not arbitrary pulled-back condensed ring objects.
  `grep -rn det-lem-formal-closed-support-adjunction .../WeilConjectures` finds no match.
- `rg` in lean/Sheaf finds intrinsic finite support, finite derived support, and
  `Paper/CondensedOpenClosedRecollement.lean`. The last assumes `IsCommMonObj` and
  concerns D-plus; it is not this all-ring, unbounded theorem. Its signature and
  proof docstring were read. No equivalent existing statement was found.
- `rg` for the fourteen proposed names in the upstream name index, upstream source
  and lean/Sheaf finds no existing declaration. The new names do not shadow a
  published notion; abbreviations name the existing category and the other
  helpers are the actual maps/functors in this node's displayed formula.

Validation: scompile.py compiled the final module as a sandbox and as its actual
library module, with no errors or warnings (6.4 and 7.0 seconds). No global build,
repository edit, or direct Git command was run. No statement fault or dispute remains.

## Second reading by Q30

Author's second pass with the JSON and Lean file both open; the independent review
is the maintainer's review after delivery. I checked each hypothesis and all four
clauses against the actual current blueprint node. During this pass I fixed the
derived adjunctions by equations to the canonical adjunctions, so the triangle
cannot silently use a rescaled unit or counit. I also checked the global Hom
comparison's component formula, the small-site and derived-category universes,
and that noncommutative, empty, and unbounded cases remain present. The kernel
comparison is the closed unit itself, and the sheaf adjunction counit is normalized
against the actual kernel inclusion. There are no new or repaired dependency nodes
and no changes to the informal statement.
