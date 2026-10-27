## Worker report

The module `Sheaf.CategoryTheory.FixedPairEquivalenceTransport` states
`CategoryTheory.Endofunctor.IsoAlgebra.fixedPair_equivalence_transport`, with one
`sorry` and no new definitions. The natural-language node is unchanged.

The source is the coefficient-category transport in blueprint main-20261015,
`sec-fourier-transform/sk-def-trace/def-fd-trace-function.md`, with the full auxiliary
argument recorded in the item's six proof steps. I read this source and Stacks
Categories, Tag 02C3, in `literature/stacks-project/categories.tex`.

Hypotheses and clauses, in signature order:

- Categories C and D: `{C : Type u} [Category.{v} C]` and
  `{D : Type u'} [Category.{v'} D]`. All four universe variables are explicit.
  Their maximum is a common sufficiently large universe, without imposing an
  unnecessary equality between the object or morphism universes.
- Arbitrary endofunctors: `(F : C ⥤ C) (G : D ⥤ D)`. Neither gets an
  `IsEquivalence`, exactness, additive, or abelian hypothesis.
- Equivalence: `(J : C ≌ D)`.
- Ordinary-composition comparison `J ∘ F ≅ G ∘ J`:
  `(b : F ⋙ J.functor ≅ J.functor ⋙ G)` in Lean's diagrammatic composition.
- Fixed pairs: `IsoAlgebra F` and `IsoAlgebra G`. These are the existing upstream
  definitions, definitionally the full subcategory specified by the dependency's
  `mathlib_match`: algebras with `IsIso A.str`. The existing `Algebra` and its
  `Hom.h` are used through this exact specialization; no replacement notion is
  introduced. `K.carrier` is `K.obj.a`, and `K.obj.str` is theta's hom.
- The displayed functor is an equivalence:
  `(mapOfNatIso b.symm).IsEquivalence`. `Functor.asEquivalence` yields an
  equivalence with this exact functor; this is stronger than merely choosing an
  unrelated equivalence and is precisely the displayed-functor assertion.
- Object action: the next conjunct gives both its carrier `J.functor.obj K.carrier`
  and structure `b.inv.app K.carrier ≫ J.functor.map K.obj.str`, the ordinary
  composite `J(theta) b_K^{-1}`.
- Arrow action: `((mapOfNatIso b.symm).map f).hom.f = J.functor.map f.hom.f`.
- Restricted Hom bijection: `Function.Bijective` of the actual transport functor's
  map between the two fixed-pair Hom types. Together with the preceding arrow
  formula, this says exactly that the Hom bijection is J's map restricted to
  intertwining arrows, not just that there exists some bijection.
- Explicit intertwining test: for every `u : K.carrier ⟶ K'.carrier` the target
  equation `(b.inv.app ... ≫ J.map theta) ≫ J.map u =
  G.map (J.map u) ≫ b.inv.app ... ≫ J.map theta'` is equivalent to
  `K.obj.str ≫ u = F.map u ≫ K'.obj.str`. These are the displayed equations
  with composition reversed into Lean's order. This quantifies over all
  underlying arrows, not only arrows already known to intertwine.
- Every target pair and every specified carrier isomorphism: the last conjunct
  quantifies `(H : IsoAlgebra G) (K : C) (v : J.functor.obj K ≅ H.carrier)`.
- Unique lift and its invertibility: `∃ θ : F.obj K ≅ K`, followed by
  `∀ t : F.obj K ⟶ K, J.functor.map t =
  b.hom.app K ≫ G.map v.hom ≫ H.obj.str ≫ v.inv ↔ t = θ.hom`.
  Taking `t = θ.hom` gives the required image, while the equivalence gives
  uniqueness among all arrows. The isomorphism type states invertibility.
- Unique lift of the inverse: the analogous quantifier on `t : K ⟶ F.obj K`
  has image `v.hom ≫ H.str.inv ≫ G.map v.inv ≫ b.inv.app K` iff `t = θ.inv`.
  This composite is exactly the inverse of the preceding conjugated structure;
  no arbitrary inverse or independent choice is substituted.
- The prescribed v is an isomorphism of pairs: `∃ e :
  (mapOfNatIso b.symm).obj (mk K θ) ≅ H` with
  `e.hom.hom.f = v.hom ∧ e.inv.hom.f = v.inv`. Thus both underlying maps
  are the specified ones, and the category's morphism condition supplies the
  two intertwining conditions.

Dependencies read and used:

- `def-nagata-category`: `CategoryTheory.Category` in
  `Mathlib.CategoryTheory.Category.Basic`; read `CategoryStruct` and `Category`.
- `def-weil-endofunctor-fixed-pair-category`: its recorded
  `CategoryTheory.Endofunctor.Algebra` in `Mathlib.CategoryTheory.Endofunctor.Algebra`,
  its `Algebra.Hom`, and `ObjectProperty.FullSubcategory` in
  `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`. The exact recorded
  specialization already has the upstream name `CategoryTheory.Endofunctor.IsoAlgebra`
  in `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`, publicly imported.
  I read that declaration, `IsIsoStr`, `carrier`, `str`, `mk`, `forget`, and
  `mapOfNatIso`, including their full signatures and docstrings. Using this
  existing name does not require a dependency repair or a second definition.
- `lem-sf-quasi-inverse-hom-bijection`: `Equivalence.fullyFaithfulFunctor`
  in `Mathlib.CategoryTheory.Equivalence` and `FullyFaithful.map_bijective`
  in `Mathlib.CategoryTheory.Functor.FullyFaithful`; full signatures/docstrings read.
- `lem-cbc-fully-faithful-isomorphism-lift`: `Functor.FullyFaithful.isoEquiv`,
  with `preimageIso` and `homEquiv` in the same FullyFaithful module, read in full.
- `lem-trf-fully-faithful-ess-surj-equivalence`: `Functor.asEquivalence`
  and `Functor.IsEquivalence` in `Mathlib.CategoryTheory.Equivalence`, read in full.
- The existing `IsoAlgebra.fullyFaithfulMapOfNatIso` in
  `WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraFullyFaithful` provides
  the full-faithfulness part of step 3 and is imported as a proof dependency.
  It does not assert essential surjectivity or the remaining clauses of this node.
  The other proof-dependency modules are already exposed by the statement imports.

Edge cases checked before writing:

- Empty C and D: the equivalence and universal clauses behave correctly; the last
  clause has no H and K to instantiate. No `Nonempty` assumption is introduced.
- Identity J and identity b: the structure and arrow formulas reduce to the
  original fixed pairs. For general v, theta is conjugation of psi by v.
- Nonidentity b with identity J: the structure is b inverse followed by theta;
  this confirms that `mapOfNatIso b.symm`, rather than `mapOfNatIso b`, has the
  node's orientation.
- Constant endofunctors, including non-equivalences on a category with multiple
  nonisomorphic objects: the statement still types and needs no inverse for F or G.
- Arbitrary v rather than only the counit: the final quantifiers retain this case.
- The inverse composite was checked by reversing the factors and inverting each:
  b, G(v), psi, v inverse become v, psi inverse, G(v inverse), b inverse.
- Objects in fixed-pair categories live in `max u v` and `max u' v'` as in
  upstream; no small-category or equal-universe restriction is imposed.

Searches (recorded by msearch.py in searches.jsonl):

- LeanFinder: "An equivalence commuting with endofunctors induces an equivalence
  of the categories of invertible fixed pairs with explicit restricted Hom
  bijection and unique lift of conjugated isomorphisms". Eight hits, including
  `Equivalence.congrLeft`, `changeFunctor`, `congrRight`, and `induced`; none gives
  this fixed-pair theorem.
- LeanFinder: "Equivalence of invertible endofunctor algebras along an equivalence
  of categories commuting with the endofunctors". Eight hits, mainly monad
  `algebraEquivOfIsoMonads` and equivalence transport; none matches this node.
- LeanSearch: "An equivalence commuting with endofunctors transports invertible
  fixed pairs and intertwining arrows". Eight hits, including `Equiv.conj`,
  `Equivalence.congrLeft`, and whiskering equivalences; no exact match.
- Loogle: `CategoryTheory.Endofunctor.Algebra, CategoryTheory.Equivalence`.
  Two hits: `Endofunctor.Adjunction.algebraCoalgebraEquiv` and
  `Endofunctor.Algebra.equivOfNatIso`. The first concerns an adjunction and the
  second naturally isomorphic endofunctors on the same category, both allowing
  noninvertible structures. Neither is the present statement.
- Mathlib grep via msearch.py:
  `IsoAlgebra|equivalenceOf.*Algebra|Algebra.*equiv|FixedPair`, subdirectory
  `CategoryTheory`. Twenty-five hits concerning monads, coalgebras and
  `Algebra.equivOfNatIso`; no exact match.
- Local rg on `lean/WeilConjectures` and `lean/Sheaf`:
  `fixedPair|FixedPair|fixed_pair|IsoAlgebra|equivalenceTransport|equivalence_transport`.
  Found the canonical upstream IsoAlgebra construction and mapOfNatIso, the
  fully-faithful transport result, and related adjunction/truncation/twist results.
  Read the applicable definitions and the full-faithfulness module; none states
  the whole item with essential surjectivity and the prescribed inverse lifts.
- `grep -rn lem-fd-fixed-pair-equivalence-transport lean/WeilConjectures`: no hit.
  `rg` for `fixedPair_equivalence_transport` across Mathlib category theory,
  `lean/WeilConjectures`, and `lean/Sheaf`: no pre-existing declaration.
  Consulted `dag/lean_names_upstream.json` for IsoAlgebra and mapOfNatIso as well.

There are no node faults, statement corrections, new nodes, or dependency repairs.
No `STATEMENT-DISPUTED` flag is needed. The module and theorem docstrings include
all six inherited proof steps and their named dependencies. Nothing is proved.

Validation: the prescribed scompile.py compiled the file cleanly both in its
private sandbox and as `Sheaf.CategoryTheory.FixedPairEquivalenceTransport`.
No errors or warnings were emitted. The only postponed proof is
`fixedPair_equivalence_transport`.

## Second reading by Q61

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
