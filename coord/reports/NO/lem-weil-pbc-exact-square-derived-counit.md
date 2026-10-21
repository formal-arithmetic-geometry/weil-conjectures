## Worker report

The module `Sheaf.CategoryTheory.ExactSquareDerivedCounit` states
`CategoryTheory.exactSquare_derived_counit`, with its sole proof `sorry`.
The node's statement, statement dependencies and proof remain unchanged. The two
auxiliary definitions are parts of this node's specified canonical comparison and
Hom normalization, rather than new independent notions. Neither has postponed data.

Hypotheses, in node order:

- The four abelian categories are `Ap`, `A`, `Bp`, `B`, with explicit `Category`
  and `Abelian` instances. Each has its own object universe, morphism universe
  and `HasDerivedCategory` universe (`wAp`, `wA`, `wBp`, `wB`). No equality of
  these universes is imposed. `DerivedCategory.Q` is complex localization.
- Arbitrary quasi-isomorphisms to K-injective resolutions are exactly `hAp`
  and `hA`: for every complex there exist a K-injective complex and a
  quasi-isomorphism into it. There is no monomorphism requirement.
  `CochainComplex.IsKInjective` is Mathlib's condition that every chain map
  from an acyclic complex is homotopic to zero.
- `Fp`, `Gp`, `F`, `G` are additive; `adjp : Fp ⊣ Gp` and `adj : F ⊣ G`
  are the fixed ordinary adjunctions. Exactness of the left adjoints is
  `PreservesFiniteLimits` and `PreservesFiniteColimits`, alongside additivity.
  Their specified ordinary counits are `adjp.counit` and `adj.counit`.
- `r`, `s` have the same additive/exact instances. Strict commutation is
  `hF : Fp ⋙ r = s ⋙ F` and `hG : Gp ⋙ s = r ⋙ G`, equality of the whole
  functors, hence on objects and morphisms. `hε` is the ordinary counit
  equation, with the equality transports written explicitly:
  `r.map (adjp.counit.app X)` equals `(eqToIso hF).hom.app (Gp.obj X)`,
  followed by `F.map ((eqToIso hG).hom.app X)` and `adj.counit.app (r.obj X)`.
- `hr` is precisely preservation of K-injective complexes by the termwise
  application of `r`; no preservation by `s`, `Gp` or `G` is assumed.
- The exact derived functors are the existing `Functor.mapDerivedCategory`.
  The arbitrary fixed right-derived pairs are `RGp, ηp, hRGp` and
  `RG, η, hRG`, where the latter hypotheses are the Mathlib
  `Functor.IsRightDerivedFunctor` universal properties at quasi-isomorphisms.
  These are not replaced by newly chosen pairs.
- The supplied isomorphism is `β : RGp ⋙ s.mapDerivedCategory ≅
  r.mapDerivedCategory ⋙ RG`. The sole comparison normalization `hβ`
  quantifies over `J` with `J.IsKInjective`. Its left side is
  `D(s)(ηp_J) ≫ β_QJ ≫ RG(φr_J)`; its right side is
  `φs_(Gp J) ≫ Q(hG_J) ≫ η_(r J)`. Here `Q(hG_J)` uses the existing
  `NatIso.mapHomologicalComplex (eqToIso hG)`, so the ordinary right square
  is transported degreewise, not replaced by an arbitrary comparison.

Conclusions, in node order:

- `∃ (dp : Fp.mapDerivedCategory ⊣ RGp) (d : F.mapDerivedCategory ⊣ RG)`
  supplies the two derived adjunctions on those fixed functors.
- `Adjunction.HasExactDerivedHomFormula` expands to the node's formula for
  every chain map `f : F(M) ⟶ I`, for all complexes `M` and `I`. It applies
  `d.homEquiv` to `F.mapDerivedCategoryFactors.hom.app M ≫ Q.map f` and
  equates it to `Q.map` of the specified ordinary transpose, followed by
  `η.app I`. The primed and unprimed conclusions both use this definition.
- The next two quantified clauses say every other adjunction satisfying
  its Hom formula equals `dp` or `d`, respectively. Thus the canonical
  specification is uniqueness from the Hom formula alone, not uniqueness
  conditional on the final square equation.
- The next two clauses give the required counit identities on K-injectives.
  For example, `D(F).map (η.app I) ≫ d.counit.app (Q.obj I)` equals
  `φ_(G I) ≫ Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app I)`.
  The latter counit is exactly the termwise ordinary counit.
- The final clause quantifies over every `N : DerivedCategory Ap`.
  `r.mapDerivedCategory.map (dp.counit.app N)` equals the canonical left
  square comparison at `RGp.obj N`, followed by `D(F)(β_N)` and
  `d.counit.app (D(r).obj N)`. The helper
  `Functor.exactSquareDerivedComparison` is defined by the inverse of
  `mapDerivedCategoryCompIso Fp r`, then `mapDerivedCategoryNatIso
  (eqToIso hF)`, then `mapDerivedCategoryCompIso s F`. Its data are fully
  constructed using the already published localization comparisons.
- No universality of `RGp ⋙ D(s)` or normalization on non-K-injectives
  appears among the assumptions. In particular none is used to hide the
  missing postcomposition absoluteness that this node deliberately avoids.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`
  (`def-sp-abelian`, Mathlib match).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q` (`def-weil-abstract-derived-category`).
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory` and `mapDerivedCategoryFactors`
  (`lem-weil-pbc-exact-functor-derived-factorization`, Mathlib match).
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `mapDerivedCategoryCompIso`, `mapDerivedCategoryNatIso` give the existing
  canonical composition and equality comparisons.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `rightDerivedFunctorOfQuasiIsoResolutions`, its unit, universality,
  uniqueness, invertibility on K-injectives and resolution comparison
  (`def-sfb-right-derived-functor`). The node permits independently fixed
  universal pairs; those are expressed by the existing general
  `Functor.IsRightDerivedFunctor` predicate from
  `Mathlib.CategoryTheory.Functor.Derived.RightDerived`, with explicit units
  on complexes as in the node, rather than restricting to the chosen pair.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`:
  `Adjunction.mapHomologicalComplex` is used for ordinary transposes and
  termwise counits; `Adjunction.mapHomotopyCategory` is the recorded proof
  dependency `lem-weil-pbc-termwise-adjunction-homotopy`.
- The proof-only imports are `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
  (`Functor.exactFunctor_derivedFunctor`) and
  `Sheaf.SixFunctors.ResolvingDerivedAdjunction`
  (`CategoryTheory.derivedAdjunctionOfResolvingClass`). Their full signatures
  and proof docstrings were read. The latter uses a common derived-Hom universe
  and monomorphic-resolution typeclass; this item's interface retains its
  independent universe and arbitrary-quasi-isomorphism hypotheses. Its proof
  plan explicitly allows passage to a common ambient universe, as the node does.

Edge cases checked before writing: the zero abelian categories and zero complexes
are admitted; the identity square gives the usual derived counit; taking both
vertical functors to be identities leaves precisely the unit normalization for
comparison of fixed derived pairs. Arbitrary unbounded complexes remain allowed.
There is no assumption of enough injective objects, monomorphic resolutions,
boundedness, or exactness of the ordinary right adjoints. Exactness of `r` alone
is not used as a substitute for its explicitly stated K-injective preservation.
The Hom formula is imposed for all complexes `I`, whereas the hypothesis on β
and the requested displayed counit identities restrict only to K-injectives.

Searches made:

- `msearch.py leanfinder`, query “An exact commuting square of adjunctions
  induces compatible derived counits when the comparison is normalized on
  K injective complexes”: eight hits, headed by `Adjunction.derived'_counit`,
  `derived_counit`, `derivedε_fac_app`, `derivedη_fac_app`.
- `msearch.py loogle`, query `CategoryTheory.Adjunction.derived_counit`:
  one hit in `Mathlib.CategoryTheory.Functor.Derived.Adjunction`.
- `msearch.py grep`, query `derived.*counit|derivedε_fac_app` in
  `CategoryTheory`: four hits in derived-adjunction and left-derived APIs.
- `msearch.py leansearch`, query “Compatibility of derived adjunction counits
  in an exact square normalized only on K injective complexes”: eight hits
  concerning derived units/counits and shift compatibility.
- Read `Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean`, in particular
  `derived`, `derivedε_fac_app` and its two postcomposition derived-property
  assumptions. These results concern one adjunction and do not state this
  exact-square consequence under normalization only on K-injectives.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for exact-square and
  derived-counit names, plus the blueprint item id (also the upstream name
  index): no matching statement. The existing equivalence-square material
  assumes equivalences and does not supply this general exact square.
  Checked all three new declaration names in Mathlib and both project roots:
  none already occurs. Search output is retained by `msearch.py` in the sandbox.

The source passages were read in `literature/stacks-project/derived.tex`:
`lemma-derived-adjoint-functors` (Tag 09T5), `lemma-K-injective-defined`
(Tag 070Y), and the adjoining existence statement for arbitrary K-injective
quasi-isomorphism resolutions. The module docstring contains all five proof
steps, including cancellation on K-injectives and naturality on arbitrary objects.
No node faults or statement disputes were found.

Validation: the prescribed `scompile.py` compiled both the sandbox module and
its library-path version without errors or warnings. All declarations and
universes are explicitly bound, with `set_option autoImplicit false`.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
