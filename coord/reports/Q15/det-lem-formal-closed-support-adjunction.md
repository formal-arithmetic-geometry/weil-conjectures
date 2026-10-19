## Worker report

The delivery states all four clauses of `det-lem-formal-closed-support-adjunction` in
`Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction`. All mathematical theorems
have `sorry` proofs. Definitions contain actual constructions. No node statement,
statement dependency, proof, or proof dependency is changed.

The source is the current main-20261015 blueprint, smooth-purity localization,
`sk-lem-formal-closed-support-adjunction.md`, and its proof. I read the source, the
node, every statement dependency and its recorded interface, and the relevant
published module-object sources, including `coord/pefw-upstream-framework.md`.

Hypotheses and objects:

- A condensed ring is `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with
  `[MonObj Λ]`. There is no commutativity, admissibility, finiteness, or topological
  hypothesis on Λ. This is the existing ring-object encoding of condensed rings.
- Schemes are `Z U X : Scheme.{u}`. Their small pro-etale sites are exactly
  `Scheme.ProEt.topology`. The site object universe is u+1 and its morphism universe
  is u; sheaf values and the chosen derived Hom universe are u+1. No equality of
  site object and morphism universes is imposed.
- The maps are `i : Z ⟶ X`, `j : U ⟶ X`, with `[IsClosedImmersion i]`,
  `[IsOpenImmersion j]`, `[QuasiCompact j]`, and
  `hij : Set.range i.base = (Set.range j.base)ᶜ`. These are exactly the complementary
  closed/open immersions and quasi-compactness of the open morphism. There is no
  qcqs, finite-type, Noetherian, or base-field hypothesis on X.
- Coefficients on X are the existing `condensedRingObj Λ X = p_X^* Λ`, the unbundled
  form of recorded `coefficientRing`. `supportModules` transparently abbreviates
  the existing category `CategoryTheory.Mod` of left modules over this ring object.
  An action in abelian sheaves is precisely a sectionwise module action compatible
  with restrictions; its morphisms are linear sheaf maps. This uses the published
  module-object framework, not fixed-scalar `ModuleCat`-valued sheaves, and does not
  introduce a new category or identify Λ with the scalar ring Λ(*).

Definition and clause correspondence:

- The formula for Gamma is the actual definition `closedSupport Λ i j =
  supportKernel Λ j ⋙ supportPullback Λ i`. `supportKernel.obj` is the categorical
  kernel of the actual module-adjunction unit; its maps are `kernel.map` using
  naturality. Kernels of left module objects are the existing sectionwise kernels.
- `supportPullback` applies the existing sheaf inverse image to the action via
  `Functor.mapMod`, then restricts scalars along the inverse of the canonical
  `condensedPullbackHom Λ f`. `supportPullbackAdjunction` is constructed from the
  existing sheaf adjunction and the explicit coefficient equivalence. This supplies
  the specified unit, not an unconstrained morphism. The upstream tensor-extension
  pullback API assumes commutativity; inverse restriction along the coefficient
  isomorphism gives the same inverse image without that restriction.
- Clause (1), kernel identification: `closedSupportKernelComparison` is the closed
  inverse/direct-image unit on the support kernel. Its `IsIso` theorem identifies
  `ker(M -> j*j^*M)` naturally with `i* Gamma(M)`.
- Clause (1), sheaf adjunction: `existsUnique_closedSupportAdjunction` states the
  adjunction with counit `closedSupportCounit`, the inverse kernel comparison
  followed by the kernel inclusion. `closedSupportAdjunction` chooses from this
  unique characterization; it does not choose an unspecified adjunction.
  `closedSupport_leftExact` states preservation of finite limits, and
  `closedSupport_additive` states additivity.
- Clause (2), derived adjunction: `closedSupportDerivedAdjunction` uses the existing
  `Adjunction.mapDerivedCategoryRightDerivedAdjunction` for exact left adjoints.
  Its left functor is termwise closed direct image and its right functor is the
  total right derived functor of the actual Gamma. The categories are the full
  ordinary unbounded derived categories, with no constructibility restriction.
  `closedSupportComputedOnKInjective` is the existing canonical computation
  isomorphism on every K-injective complex. `closedSupport_recordedDerived` gives
  the unique unit-compatible comparison to the dependency's recorded
  `rightDerivedFunctorOfQuasiIsoResolutions` for any resolution witness h. Such
  witnesses exist by the inherited Grothendieck/K-injective machinery; h is not
  an assumption of any of the four conclusions.
- Clause (2), RHom: `closedSupport_globalRHom` states an isomorphism of the global
  abelian-group Hom complexes on an arbitrary source complex A and K-injective I.
  Its component on every degree n cochain and every p,q with p+n=q is exactly the
  sheaf adjunction's Hom equivalence. This normalization gives naturality in both
  variables. Gamma(I) is K-injective because Gamma is right adjoint to exact i*,
  so these complexes compute the two global RHom objects for all derived A,K.
  The statement does not compare internal Hom sheaves on different sites.
- Clause (3): `closedSupport_injective_unit_epi` asserts `Epi` of the actual
  `supportPullbackAdjunction Λ j` unit for every `[Injective I]`. In this abelian
  sheaf category an epimorphism is sheaf-surjectivity; it does not incorrectly
  assert surjectivity on every object's sections.
- Clause (4), triangle: `closedSupport_triangle` asserts existence of a natural
  transformation δ between the specified composite functors. For every derived K,
  the triangle whose first arrow is the derived support counit, whose second is
  the derived open unit, and whose last is δ.app K is distinguished. Naturality
  is consequently for every derived morphism, including the boundary map.
- Clause (4), fibre: `closedSupport_fiber` identifies RH(K) with closed inverse
  image of the actual shifted mapping cone of the termwise open unit on a
  K-injective representative I. It accepts arbitrary K and any isomorphism
  `e : K ≅ Q.obj I`. Every K has such representatives by the existing
  `DerivedCategory.exists_iso_Q_obj_of_isKInjective`; this imposes no restriction
  on K. `closedSupport_open_isKInjective` ensures this cone represents the fibre
  of the derived open unit. The shift is -1, exactly the fibre convention.

Dependency declarations used and read:

- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedSupport`:
  `Scheme.sfIntrinsicSectionsWithSupport`, `Scheme.sfIntrinsicClosedUpperShriek`,
  and the constant module adjunction describe the finite constant-coefficient
  kernel construction referenced by the item. Those signatures require `[Finite A]`;
  the item itself explicitly generalizes that formula to arbitrary Λ. Its general
  support kernel, inverse-image transport, and comparison maps are helpers of the
  present node, not replacements of the finite dependency or independent notions.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `ProEtale.coefficientRing`, `ProEtale.condensedRingObj`,
  `condensedPullbackHom`, its isomorphism instance, and `condensedPushforwardHom`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.lowerStar`, `linearLowerStar`, `comapPullbackHomCompIso`.
- `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`:
  `Functor.mapMod`, `Adjunction.mapModAdjunction`, and scalar-transport compositions.
  The existing `Mod.comapEquivalenceOfIsIso` carries an unnecessary commutativity
  binder; the same two explicit scalar-restriction functors provide the needed
  equivalence here as an owning-node coefficient-transport helper.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  its signature and underlying `SheafOfModules` give the general sectionwise
  description. The coefficient dependency's existing internal ring object and
  published `Mod` interface give that same notion in the module-object presentation.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleSheafInverseImage` and `proEtaleSheafAdjunction` give the
  sheafified left-Kan inverse image and adjunction, the same underlying sheaf
  operations used by the published `ProEtale.upperStar` and its module lift.
- Mathlib's `Scheme.ProEt`, `ProEt.topology`, `IsClosedImmersion`,
  `IsOpenImmersion`, `QuasiCompact` (the quasi-compact part of the finite-type
  dependency), `CategoryTheory.Injective`, `InjectiveResolution`, `DerivedCategory`,
  `HasDerivedCategory`, `Pretriangulated`, and `IsTriangulated` retain their existing
  meanings. There is no locally-of-finite-type assumption in this node.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions`, its Unit and uniqueness
  declaration; `closedSupport_recordedDerived` explicitly compares the two
  universal pairs. `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor`
  `.Adjunction` supplies `mapDerivedCategoryRightDerivedAdjunction`, and `.KInjective`
  supplies `rightDerivedFunctorObjQIso`.
- Proof imports include the recorded open--closed geometric interface, site inverse
  image exactness, Grothendieck/K-injective existence, and short-exact-sequence
  triangles. No proof-dependency import cycle was introduced.

Edge cases checked against the constructions and statements:

- Z empty, U=X: the open unit is invertible, its kernel and Gamma vanish, and the
  localization triangle becomes 0 -> K -> K. The fibre cone is acyclic.
- Z=X, U empty: the open target is zero, the kernel and Gamma are the identity,
  and the triangle is K -> K -> 0.
- X empty and the zero module/zero complex remain allowed by every binder.
- Noncommutative Λ is retained: only `[MonObj Λ]` occurs, and coefficient transport
  uses restriction along an isomorphism, not the commutative tensor API.
- Unbounded complexes, arbitrary integer degrees, and nonconstructible objects are
  retained. The Hom-complex formula includes all p,q,n, including negative degrees.
- Quasi-compactness belongs to j; X need not be quasi-compact or quasi-separated.

Searches for an existing statement or construction:

- msearch LeanSearch: "Closed immersion of schemes pro-etale sheaves of modules
  sections with support right adjoint localization distinguished triangle condensed
  coefficients". Eight hits, all geometric `IsClosedImmersion` declarations and
  characterizations; no support-adjunction or localization-triangle match.

- msearch LeanFinder: "For modules over a condensed ring on the pro-etale site a
  closed immersion pushforward has right adjoint sections with support and
  localization distinguished triangle". Eight hits, all ordinary ringed-space or
  general sheaf pullback/pushforward adjunctions; none is the condensed-support
  theorem with its four clauses.
- msearch Loogle: "CategoryTheory.Adjunction, CategoryTheory.Injective,
  CategoryTheory.Triangle". No hits; the last queried identifier is not a fully
  qualified Mathlib name. Source search located `Pretriangulated.Triangle` and the
  actual distinguished-triangle API used in the file.
- msearch grep: `sectionsWithSupport|closedSupportAdjunction`, Mathlib CategoryTheory:
  no hits. Direct Mathlib searches locate the existing HomComplex, mappingCone,
  derived-category, kernel, injective, and triangulated definitions reused here.
- rg over the prescribed upstream `WeilConjectures` and shared `lean/Sheaf` for
  closedSupport, sectionsWithSupport, supportAdjunction, SectionsWithSupport:
  existing closed-support material has finite constant coefficients or ordinary
  fixed-value-category sheaves. The published ModuleObject framework has the
  coefficient ring and ordinary/derived operations, but its upper-shriek file is
  bounded constructible and assumes commutativity and finite-type schemes over a
  positive-characteristic field. None states this node's arbitrary-ring ambient
  support adjunction and triangle.
- rg of `dag/lean_names_upstream.json` and upstream source for the item id: no match.
  Inspection of SupportTriangleCompatibility confirms it uses finite constant
  coefficients, not the present arbitrary condensed ring.

No statement fault or STATEMENT-DISPUTED remains. There are no new DAG nodes or
repaired dependency modules; the canonical coefficient transport and generalized
kernel construction are helpers belonging to the formula explicitly in this item.

## Second reading by Q15

This is the author's second reading, not an independent review; the maintainer
performs the independent delivery review. I reopened the node and the complete
module and compared each clause as mapped above. The original statements and
proof source agree, so no source correction was made.

The second pass caught the commutativity restriction in the upstream pullback
and coefficient-equivalence interfaces before using them: the module now uses
actual inverse scalar restriction and its canonical adjunction for every MonObj.
It also checked that the support adjunction is uniquely counit-normalized,
RHom means the global Hom complex rather than the internal Hom on either site,
surjectivity is categorical sheaf-surjectivity, the boundary is a natural
transformation on the entire derived category, and the fibre is the shifted
mapping cone of the actual open unit. Every K is covered via any K-injective
representative (the fibre proof first compares that representative with one having
injective terms before using the degreewise surjectivity argument), and all four geometric binders match the node. Named proof
instances were changed to named theorems with the instance attribute, so every
postponed result is a named theorem. There are no hollow definitions, private
copies of coefficient objects, local notations, or unbound universe variables.

Validation: scompile.py compiles the module in both sandbox and its actual module
path under the standard 60-second limit. The last full elaboration took 7.1/7.5 s
and produced no warnings or errors. Final delivery preflight is recorded below.

Delivery validation: `deliver2.py Q15 det-lem-formal-closed-support-adjunction
--no-push` printed `OK (dry run): commit 9aa4fe82a0 passes the preflight and
compiles; nothing pushed`. Only the item's module, its node's `lean` record, and
this report are staged by the prescribed delivery tool.
