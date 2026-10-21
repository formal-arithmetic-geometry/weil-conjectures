## Worker report

Item: lem-sfb-intrinsic-finite-derived-pullback. Group: O2. Stage 2.
Delivery module: Sheaf.Paper.IntrinsicFiniteDerivedPullback.

The module states the node in five declarations, all with proof `by sorry`. It
constructs no new notion and changes only the item's `lean` field. There is no
statement correction, new node, dependency-node modification, or disputed clause.

Sources read: the whole item statement and eight-step proof; every statement
dependency's statement, Lean record, and defining source/docstring; the recorded
pro-etale framework note; Bhatt--Scholze's PDF at Lemmas 6.5.8, 6.5.9 and 6.7.11.
The PDF's Lemma 6.5.9 assumes qcqs schemes; this node explicitly isolates an
agent-written intrinsic argument for arbitrary schemes, as its `proof_origin`
explains. The declarations follow that argument and impose no qcqs hypothesis.
The small-site, constant-sheaf, module-category, fibre-product, scheme and derived
category signatures were also read directly in the Mathlib files named below.
The suggested CompactObject example is withdrawn in the local Sheaf source; I
read its node's current upstream module WeilConjectures.CategoryTheory.CompactObject.

Hypotheses and clauses, matched to Lean:

1. A finite field is `(A : Type u) [Field A] [Finite A]`. An arbitrary scheme map
   is `{X Y : Scheme.{u}} (h : X ⟶ Y)`; X is S and Y is T in the node.
   No characteristic, Noetherian, cohomological-dimension, qcqs, nonemptiness,
   topology on A, or etale-origin hypothesis occurs.
2. The small sites are `ProEt.topology X` and `ProEt.topology Y`. Their object
   universe is u+1 and their morphism universe is u. Coefficients are the existing
   `proEtaleConstantRing Y A`, the constant sheaf of `ULift.{u+1,u} A` in
   commutative rings. `proEtaleRingModules Y (proEtaleConstantRing Y A)` is exactly
   `ringedSiteModules` / Mathlib `SheafOfModules.{u+1}` over the underlying ring
   sheaf. This is ordinary constant-ring module sheaf data, with the size lift
   already required by the dependency.
3. `proEtaleConstantModulePullback h A F` is the dependency's actual inverse image
   followed by sheaf tensor extension along `proEtaleCoefficientInverseImageMap`.
   The latter is the adjoint of the specified constant-section map. The existing
   `proEtaleConstantModulePullbackFunctor h A` has these objects and the canonical
   maps: its `proEtaleRingModulePullback` uses `asIso` of that very coefficient
   map, whose hom is the same map. There is no arbitrary chosen left adjoint.
4. `intrinsicFiniteModulePullback_exact` asserts additivity and preservation of
   finite limits and finite colimits of this functor. In the abelian module
   categories these are precisely exactness.
5. `intrinsicFiniteModulePullback_derived` first asserts a natural factorization
   `Q ⋙ L.mapDerivedCategory ≅ L.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q`.
   Thus the ordinary derived functor is termwise descent, with no completion or
   resolution restriction. Its second conjunct, for every integer q, is a
   natural isomorphism of functors `D(Y) ⥤ Mod(A_X)` between
   `L.mapDerivedCategory ⋙ H_X^q` and `H_Y^q ⋙ L`. This includes naturality in K,
   and quantifies over the whole unbounded category. `Nonempty` asserts existence
   of these isomorphisms as propositions; it supplies no chosen object data.
6. `intrinsicFiniteModulePullback_constructible` renders exactly
   `IsConstructibleProEtaleModuleSheaf Y A F →
    IsConstructibleProEtaleModuleSheaf X A (proEtaleConstantModulePullback h A F)`.
   This recorded dependency declaration is the intrinsic global definition:
   `∃ s : Stratification Y, 0 < s.n ∧ ...`, locally constant restrictions and
   finite geometric stalks. Its `Stratification` extends
   `Topology.Stratification`, which includes constructibility of the strata.
   It is not an etale-origin or affine-local replacement.
7. `intrinsicFiniteModulePullback_stratification` takes ANY given witnessing
   stratification `s`, `_hn : 0 < s.n`, and the precise witness conditions `_hs`
   (locally constant restriction and finite stalks on every stratum). The output
   uses the existing actual `s.pullback h`, not an existential substitute.
   In its source, `(s.pullback h).domain i` is
   `pullback (s.immersion i) h`, the immersion is `pullback.snd`, the map to the
   old stratum is `pullback.fst`, and its subset is `h.base ⁻¹' s.stratum i`.
   The factor order is the established chosen fibre-product convention.
   This structure itself contains the constructible, locally closed, pairwise
   disjoint and covering properties. Its n is definitionally s.n. Retaining
   all empty strata is allowed by the node, so positivity is preserved for the
   empty scheme as well; no unnecessary nonempty-stratum assumption is added.
8. For each pulled-back stratum the first two conclusions are local constancy
   and finiteness at every geometric point. The second also states
   `Module.Finite (ULift A)` of the fixed-scalar geometric stalk obtained by
   the existing `proEtaleModuleRestriction`. Over the field ULift A this is
   finite-dimensionality over the same coefficient field, expressed without
   requiring the varying coefficient stalk ring to be definitionally A.
9. The next conclusion is the A-module sheaf isomorphism
   `i'^* (h^* F) ≅ h_a^* (i^* F)`, with i' and h_a the actual projections above.
10. The final stratum clause quantifies over every supplied index
    `I : Type (u+1)`, every family `U : I → (s.domain i).ProEt`, arrows a to
    `ProEt.mk (𝟙 _)`, and membership in `ProEt.precoverage`. It then quantifies
    over the SAME modules `M : I → ModuleCat.{u+1} (ULift A)`, their finiteness,
    and every given trivialization of `(i^* F).over (U j)`.
    Its conclusion gives covering arrows b from
    `(proEtaleBaseChange h_a).obj (U j)` and trivializations of the actual
    restricted pulled-back F over these objects by
    `proEtaleConstantModuleSheafOver ... (M j)`. No model or index is replaced.
    These base-change objects are literally the chosen fibre products with
    U j; the covering and trivialization claims include empty members.
11. `intrinsicFiniteDerivedPullback_bounded_constructible` takes arbitrary
    `K : proEtaleDerivedCategory Y A`, `a b : ℤ`, `_hab : a ≤ b`, vanishing
    `_hvanish` for every q with `q < a ∨ b < q`, and intrinsic constructibility
    `_hconstructible` of every H^q K. Its conclusion repeats exactly the same
    a and b for vanishing of every H^q of the specified termwise derived
    pullback, together with intrinsic constructibility for every q. This
    states the asserted inclusion of B_A(Y) in B_A(X) while retaining each
    given vanishing interval, rather than just some output bound.

Dependency declarations used (the recorded statement dependencies):

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:
  CategoryTheory.Limits.pullback, pullback.fst and pullback.snd.
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt, ProEt.topology and
  ProEt.precoverage. No site universe is forced equal to its Hom universe.
- Mathlib.CategoryTheory.Sites.ConstantSheaf: CategoryTheory.constantSheaf.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory,
  HasDerivedCategory, Q and HasDerivedCategory.standard, through the existing
  proEtaleDerivedCategory/proEtaleRingModules interface.
- Sheaf.AlgebraicGeometry.ProEtaleInverseImage: proEtaleBaseChange,
  proEtaleConstantRing, proEtaleCoefficientInverseImageMap and the actual
  proEtaleConstantModulePullback, all listed in the inverse-image node.
- Sheaf.Paper.ProEtaleFixedModuleConstructible: its recorded `declarations`
  explicitly retains IsConstructibleProEtaleModuleSheaf alongside the fixed
  encoding. This recorded module publicly imports
  Sheaf.Paper.ProEtaleConstructibleSheaf, the defining module of the ring-sheaf
  predicate used here. I read both full definitions. No dependency rebinding
  or duplicate definition is needed.

The existing functor and its exactness instances are imported from
Sheaf.Paper.ProEtaleConstantModulePullbackHomology; the fixed-scalar stalk
presentation uses proEtaleModuleRestriction from ProEtaleConstantModuleEncoding
and proEtaleGeometricFixedModuleStalk from ProEtaleGeometricStalk.
Stratification.pullback is the recorded
WeilConjectures.ConstructibleSheaf.Pullback declaration. The stated proof
modules are imported without public export for the node's proof plan:
ConstantLeftModuleInverseImage, ProEtaleBoundedConstructibleTriangulated,
ProEtaleConstantModulePullbackComposition, ProEtaleInverseImageStalk,
GeometricInverseImageConstantModule, the upstream derived ExactFunctor,
LocalizeRingedSiteMorphismGeneral and ProEtaleWeaklyEtaleLocalization.
The Mathlib proof leaves for constructible preimages, covering base change,
and weakly etale base change are already in these modules' import closure.

Edge cases checked against the actual definitions:

- X empty: s.pullback h retains s.n > 0 and only empty strata; the output local
  constancy is not made vacuous by choosing n = 0. The one-empty-stratum witness
  allowed by the node is covered when the given witness has one stratum.
- Empty members and an empty covering index are admitted; covering validity is
  asserted with the existing precoverage, without an extra Nonempty I binder.
- F = 0, K = 0, and a = b are admitted. The interval includes both endpoints.
  Each natural cohomology comparison applies also to unbounded K.
- h = identity or an immersion is included; there is no geometric restriction
  on h. All characteristics of A and of X,Y are allowed, including equal ones.
- Schemes are in universe u, the small-site objects and models in u+1. The
  coefficient lift is the recorded one, not an equality between universes.

Searches actually performed:

- msearch.py leanfinder, query `Exact inverse image on pro etale constant module
  sheaves preserves intrinsic constructibility and bounded derived cohomology`:
  eight hits, including CompHausLike.LocallyConstantModule.functor and condensed
  module constructors; no exact statement of this intrinsic scheme result.
- msearch.py leansearch, the same query: eight constant-sheaf and sheaf-congruence
  hits, no combined exactness/stratification/ordinary-derived assertion.
- msearch.py loogle, `Functor.mapDerivedCategory, Functor.IsExact`, and later
  `"mapDerivedCategory"`: service unavailable. These are unavailable searches,
  not evidence of absence.
- msearch.py grep, `constructible.*(pullback|Pullback)|[Pp]ullback.*[Cc]onstructible`:
  unavailable (the full Mathlib rg exceeded its tool timeout). Retried with
  `constructible|Constructible` restricted to `CategoryTheory/Sites`: OK, zero hits.
- Direct rg over lean/WeilConjectures and lean/Sheaf for
  `proEtaleConstantModulePullback|IsConstructibleProEtale(Module|FixedModule)Sheaf`
  located the canonical pullback, its homology functor interface, composition,
  the intrinsic predicates, and the already-proved local-model pullback theorem
  in ProEtalePullbackLocallyConstant. The etale constructibility result in
  WeilConjectures.ConstructibleSheaf.Pullback is on a different site. None of
  those declares the whole node. Their definitions are reused here.
- Direct rg for the exact item id and proposed `intrinsicFinite...Pullback`
  names in WeilConjectures, Sheaf and dag/lean_names_upstream.json found no match.
  No existing full declaration is duplicated.

Validation: the prescribed scompile.py compiled both the isolated sandbox and
library-name form cleanly twice, first at 2.2/2.4 seconds and after switching to
its recorded dependency module at 2.6/2.6 seconds. No error or warning was printed.
All five proofs are exactly sorry; autoImplicit is explicitly false and u is
explicit. The file has no line exceeding 100 characters.

## Second reading by O2

I reread the node and final file in a separate pass. This is the dispatcher's
single worker's second pass; independent maintainer review remains the delivery
review, and no separate reviewer or subagent is claimed.

The first check was the representation of constructibility. An initial thought
was that the dependency's primary fixed-module binding required a repair.
Reading its complete `declarations` list and public imports showed the exact
ring-sheaf predicate was already retained. I changed the public import to the
recorded ProEtaleFixedModuleConstructible module and made no dependency-node edit.
The original ring predicate's Stratification really includes constructible
strata, so no constructibility condition is lost by using it.

I then checked each clause against the compiled signature. The exactness
statement is for the actual constant-section tensor pullback. Derived
factorization is a natural isomorphism on complexes, and cohomology comparison
is an isomorphism of functors on the entire unbounded derived category, not
pointwise isomorphisms without naturality. The stratum theorem uses the actual
s.pullback h with projection pullbacks and retains the same M j and covering
index. It states both local constancy and finite stalks, and includes finite
dimensionality in the fixed-scalar presentation. Keeping empty strata preserves
the positive number automatically. The final theorem repeats the given a,b,
checks the strict inequalities outside the inclusive interval, and uses
intrinsic constructibility for every integer degree. No hypothesis or clause
was found missing, and no statement text was changed.
