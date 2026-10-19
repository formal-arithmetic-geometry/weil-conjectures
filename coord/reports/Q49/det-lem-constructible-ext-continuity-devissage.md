## Worker report

The delivery states det-lem-constructible-ext-continuity-devissage in
`Sheaf.Paper.ConstructibleHomContinuityDevissage`. There are two theorems, both with
`sorry` as their entire proof, and three definitions with real data. The first theorem
states formal closure and finite devissage; the second states the constructible
specialization. No source statement is corrected and no dependency is restated.

The public helper definitions belong to the comparison notion introduced by this node:

- `CategoryTheory.homContinuityComparison` constructs theta by `colimit.desc`, applied
  to the cocone mapped first by the shift and then by additive coyoneda. Hence it is an
  abelian-group homomorphism and sends a stage h to h followed by the shifted cocone map.
  Its naturality is supplied by `Functor.mapCocone`, rather than by an arbitrary map or
  a new postponed well-definedness theorem.
- `CategoryTheory.homContinuityLocus` is bijectivity of that map for every q : ℤ.
- `CategoryTheory.complexHomContinuityLocus` applies this construction to D ⋙ Q and
  Q.mapCocone of the actual complex colimit cocone. It fixes both the source diagram and
  the target cocone. It does not assume Q preserves the colimit.

Hypothesis and clause correspondence:

1. A scheme X is `(X : Scheme.{u})`. A general condensed ring in the formal part is
   `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}) [MonObj Λ]`. In particular no
   commutativity is imposed in the formal assertion. This is the ring-object encoding
   of sheaves of rings; the coefficient dependency itself records this encoding too.
2. The pulled-back ring Λ_X is `condensedRingObj Λ X`, whose data is
   `(upperStarFromPoint X).obj Λ`, and whose multiplication/unit are transported by the
   monoidal functor. This is the unbundled form of the recorded `coefficientRing`.
3. Sheaves of left modules are exactly
   `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1}) (condensedRingObj Λ X)`.
   The ordinary unbounded derived category is `DerivedCategory` of this category.
   The explicit `HasDerivedCategory.{u+1}` instance binder chooses the localization
   and its morphism universe, as in the size convention of the dependency; it does
   not impose a completeness, tensor, boundedness, or constructibility condition.
4. The filtered index is `I : Type (u+1)` with `[SmallCategory I] [IsFiltered I]`.
   The index and Hom groups are small in the same chosen universe. All universes and
   variables are explicitly bound, with `autoImplicit false`.
5. The diagram of actual complexes is `D : I ⥤ CochainComplex ... ℤ`.
   `[HasColimit D]` expresses the supplied colimit in the node, and its structure maps
   are `(colimit.cocone D).ι.app i`. `HomologicalComplexLimits` supplies the termwise
   colimit construction and evaluation comparison; the colimit is taken in complexes.
   The helper maps this cocone by `DerivedCategory.Q`, giving K_i, K and κ_i in D(Mod).
   There is no common lower bound, either explicit or concealed in a bounded subcategory.
6. The integer q and the formula for theta are the binders of
   `homContinuityComparison`; `shiftFunctor T q` gives K_i[q], K[q], and κ_i[q], and
   `preadditiveCoyoneda.obj (op C)` gives Hom(C,-) as abelian groups.
   `homContinuityLocus` quantifies over every integer q and uses `Function.Bijective`.
7. Closure under every integer shift is the first conjunct of
   `constructibleHomContinuity_devissage`, quantifying C and n : ℤ.
8. Closure under isomorphisms is its second conjunct, quantifying any C ≅ B and
   taking membership of C to membership of B. Applying the inverse gives the converse.
9. Closure under extensions is its third conjunct, quantifying a
   `Pretriangulated.Triangle` and its membership in `distTriang`. Membership of obj₁
   and obj₃ implies membership of obj₂. All three are the given derived objects.
10. The finite-construction clause is the final conjunct: for ANY ObjectProperty G
    contained in the locus, and ANY natural n, `(G.shiftClosure ℤ).extensionProductIter n`
    is contained in it. `shiftClosure` includes isomorphic integer shifts of G;
    `extensionProductIter n` is an iteration of n binary extension operations, starting
    with one generator (n+1 entries). Distinguished triangles are stable under shifts
    and isomorphisms, and the octahedral axiom reassociates iterated extensions. Thus
    every nonempty finite expression in the operations in the statement is represented.
    A collection or family of a_!L satisfying the condition is a particular choice of G.
11. In the constructible theorem, `[IsLocallyNoetherian X] [CompactSpace X]` is precisely
    the node's meaning of Noetherian, without separatedness or any base-field condition.
12. `(ℓ : ℕ) [Fact ℓ.Prime]` supplies the prime. `PadicAlgCl ℓ` is the recorded choice
    of algebraic closure of ℚ_[ℓ]. `hΛ` says either there is an intermediate field E
    with `FiniteDimensional ℚ_[ℓ] E` and Λ = its condensed ring, or Λ is the condensed
    algebraic-closure ring. This is the same coefficient encoding already used by the
    landed common-stratification declaration. The algebraic-closure coefficient is
    `Profinite.padicAlgClCondensedRing`, whose sections lie in one finite subextension;
    it is NOT the ring of all continuous maps into the topological algebraic closure.
    `[IsCommMonObj (coefficientHeartRingObj Λ)]` equips the specified commutative
    coefficients with their given commutative ring-object structure.
13. For the specialization, `coefficientHeartRingObj Λ` is the abelian ring object
    underlying the given ring sheaf. Its pulled-back module category is used everywhere.
14. The universal hypothesis `hG` quantifies every pair S,Z and every j : S ⟶ Z,
    i : Z ⟶ X with `[IsOpenImmersion j] [IsClosedImmersion i]`. This is exactly the
    admitted open-then-closed factorization a = i ∘ j; there is no imposed choice of
    image closure, reduction, stratum, or presentation.
15. `L` is an actual module over Λ_S. `IsLisseCoefficientModule ... L` means a pro-etale
    cover on which L is `Mod.IsFree`, and `Mod.IsFree` explicitly means isomorphic to
    `finiteFree R n` for n : ℕ. Ranks can vary among cover members and may be zero.
16. The object asserted to lie in the locus by `hG` is
    `(DerivedCategory.singleFunctor _ 0).obj (i_*.obj (j_!.obj L))`, with
    `CondensedRing.lowerStar` and `CondensedRing.openImmersionLowerShriek`.
    Thus it is the specified underived a_!L in degree zero, not an arbitrary functor,
    derived proper pushforward, or assumed comparison morphism.
17. The conclusion is the inclusion
    `constantModelBoundedConstructible (coefficientHeartRingObj Λ) X ≤
      complexHomContinuityLocus _ D`. It quantifies every object of the ambient ordinary
    derived category that is bounded with constructible cohomology in the finite
    CONSTANT local-model sense. It does not replace that predicate by the older
    arbitrary ring-object finite-presentation predicate.

Dependencies and declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `condensedRingObj`,
  `coefficientRing`, `coefficientRing_X`, `upperStarFromPoint`; the first is the
  unbundled encoding explicitly included in the dependency's lean.declarations.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.ModObj`, `Mod`, `Mod.forget`,
  `Mod.regular`; sk-def-sfb-module-objects has a closed upstream audit naming these
  library declarations, so it does not need a replacement Lean record or module.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; `singleFunctor` gives the degree-zero heart.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`: `Pretriangulated`,
  `Pretriangulated.Triangle`, `distTriang`, `Triangle.yoneda_exact₂`,
  `Triangle.yoneda_exact₃`, `Triangle.coyoneda_exact₂`, `Triangle.coyoneda_exact₁`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit`, `colimit`,
  `colimit.cocone`, `colimit.desc`; `IsFiltered` for the index.
- `Mathlib.CategoryTheory.Preadditive.Yoneda.Basic`: `preadditiveCoyoneda`.
- `Mathlib.Algebra.Homology.HomologicalComplexLimits`: the termwise complex-colimit
  construction `coconeOfHasColimitEval` and evaluation preservation.
- `Mathlib.CategoryTheory.Triangulated.Subcategory`: `ObjectProperty.extensionProductIter`;
  `Mathlib.CategoryTheory.ObjectProperty.Shift`: `ObjectProperty.shiftClosure`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`;
  `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `padicSubfieldCondensedRing`, `padicAlgClCondensedRing`, `padicAlgClRingObj`.
  The latter two are the closed-audit declarations of sk-def-sfb-qlbar-condensed.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `HasFiniteConstantLocalModel`, `IsConstantModelConstructible`,
  `constantModelBoundedConstructible`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.Algebra.Category.Grp.AB`: the filtered-colimit `PreservesHomology` instance,
  recorded as `instPreservesHomologyFunctorAddCommGrpCatColim` by the proof node.
- `Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four`:
  `CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`.
- `Sheaf.Paper.CoefficientHeartCommonStratification`: `IsLisseCoefficientModule` and
  `coefficientHeartRingObj`. Its landed owning node
  `det-lem-coefficient-heart-common-stratification` is added to stmt_deps to reuse these
  exact definitions rather than duplicate them.

The proof imports include the recorded Hom-exactness, filtered-colimit-exactness, and
five-lemma modules. The finite-cone-generation proof dependency has no Lean record or
Mathlib match on the base and hence no module to import; its proof is described in the
constructible theorem docstring. It is not a notion needed to type the statement.

Edge cases checked before writing and again against the file:

- q and n range over all ℤ, including zero and negative degrees.
- An empty filtered index is excluded by filteredness itself, as in the source; no
  additional nonemptiness or pointed stage is required.
- Zero diagrams and zero source objects give the zero-group comparison. No nonzero
  hypothesis is present. The finite-construction quantifier admits n = 0 (one shifted
  generator), G = empty, and arbitrary, not necessarily finite, initial collections.
- Complexes can be unbounded below with no uniform bound. Only the concluding source
  object in the constructible specialization is bounded.
- Empty X and rank-zero L are included; lisse trivializations allow n = 0 and empty covers.
- Identity open and closed immersions are allowed in hG, as are arbitrary admitted
  factorizations. The maps used are the actual module pushforward and extension by zero.
- Non-separated Noetherian schemes are allowed. No finite-type, characteristic,
  connectedness, or dimension bound is introduced.

Searches for a duplicate (all run through the authorized wrappers or in named source trees):

- msearch leanfinder, query `Hom out of objects commutes with a filtered colimit of
  complexes closed under shifts and extensions`: eight hits, including filtered
  colimits of homological complexes, small derived Hom and localization-fraction
  lemmas; none states this comparison locus or the constructible consequence.
- msearch loogle, query `CategoryTheory.ObjectProperty.IsTriangulated,
  CategoryTheory.Functor.homologicalKernel`: one hit,
  `CategoryTheory.Functor.instIsTriangulatedHomologicalKernel`. Its predicate is a
  vanishing kernel rather than an isomorphism condition for the canonical comparison.
- msearch grep, query `colimit.*yoneda|yoneda.*colimit|[Cc]ontinuity` in
  CategoryTheory/Triangulated: zero hits.
- msearch leansearch, query `Hom colimit comparison locus stable under shifts and
  extensions`: eight hits concerning morphism properties under colimits and colimit
  universal properties, not this theorem.
- rg for the exact item id in the upstream WeilConjectures tree: no declaration.
  Name/concept searches in upstream SixFunctors and shared lean/Sheaf locate site
  continuity, other cohomological continuity theorems, and downstream uses of this
  blueprint lemma; none is a statement of this node.
- Targeted shared-source searches locate existing constant-model constructibility,
  IsLisseCoefficientModule, and the Mathlib shiftClosure/extensionProductIter APIs.
  These are used, not defined again. Mod.IsFree was read in ModuleObjects/Free.lean
  to verify finite rank, rather than arbitrary-rank freeness.
- Missing upstream source modules were read with scompile.py --source, including
  Condensed.EllAdic, ProEtaleModule.DerivedCategory, ModuleObjects.DerivedCategory and
  ModuleObject.Basic. The 51-module framework note was read before using the side
  ModuleObject sources.

No STATEMENT-DISPUTED issue was found. The node's statement, proof, and proof dependencies
are unchanged. No new definition node or dependency repair is needed.

## Second reading by Q49

This is a fresh clause-by-clause rereading by the dispatcher worker; the independent
maintainer review remains the review required by this dispatch. No second agent was
started, in accordance with the explicit brief. I reopened the node, its blueprint
statement and proof, and the completed module. Items 1--17 above record the correspondence
for every hypothesis and clause, including the conditional constructible consequence.

The rereading specifically checked that the comparison is canonical and additive, that
its target is Q of the complex colimit, that no lower-bound condition appears, that the
formal theorem allows noncommutative condensed rings, and that the specialization uses
the finite constant-model predicate. I checked finiteFree's natural-number rank and
verified that the open-then-closed factorization is quantified without restricting it to
chosen strata. The finite-construction clause uses existing shiftClosure and finite
extension products, with no retract closure or infinite construction silently added.

One elaboration defect was repaired: Triangle lives in CategoryTheory.Pretriangulated,
so its binder was fully qualified. A guessed unused Homology.Limits import was removed;
the actual HomologicalComplexLimits module is imported. These repairs change no
mathematical clause. Compiler and delivery validation results are recorded below.

Validation: scompile.py compiled the sandbox and named library module cleanly, with no
errors or warnings (24.2 s sandbox; 13.1 s library). All delivered Lean declarations have
source/blueprint docstrings. Both theorem proofs are exactly sorry; all helper data is
constructed. No auto-bound variables, local notation, local instances, or private aliases
appear. All Lean lines are at most 100 characters.
