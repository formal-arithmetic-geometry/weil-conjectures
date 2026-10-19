## Worker report

The module `Sheaf.Paper.FormalClosedSupportSheaves` states all three clauses of
`det-lem-formal-closed-support-sheaves`. There is one theorem, with proof `sorry`, and two
real constructions belonging to the definition explicitly introduced by this node.
No other node, statement, proof plan or dependency list is changed.

Hypothesis and clause correspondence:

- `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, `[MonObj Λ]`,
  `[IsCommMonObj Λ]` are a commutative condensed ring, using the recorded upstream encoding.
  `hΛ` states precisely the admissible list of `sk-def-localizing-closure`, up to isomorphism
  of ring objects (`Mon.mk Λ ≅ ...`), rather than isomorphism merely of abelian sheaves.
  Its first alternative is a finite commutative discrete ring A with a power of ℓ equal
  to zero; this is equivalent to annihilation by that power on all A-modules A itself.
  The other alternatives are ℤ_ℓ, ℚ_ℓ, the algebraic closure, and E or O_E for a finite
  intermediate field E of the fixed algebraic closure. `continuousMapCondensedRing`
  uses exactly continuous functions and the given topological ring operations.
  `Profinite.padicIntegersRingObj` uses the restricted valuation topology on O_E.
  The closure's specified valuation topology on Qbar is rendered by
  `continuousMapCondensedRing (PadicAlgCl ℓ)`. This intentionally does not use the
  different upstream `padicAlgClRingObj`, which allows only finite-subextension-valued
  sections; the source node explicitly specifies the valuation topology.
- `(ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]`,
  `[Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]` give the standing prime,
  positive-characteristic field, and unequal characteristics.
- `[X.Over (Spec (.of k))]`, `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`
  on `X ↘ Spec (.of k)` give exactly the standing separated finite-type scheme X.
  Z and V are over the same field, and `i.IsOver`/`j.IsOver` make both inclusions
  k-morphisms. Their standing finiteness/separation follow from these immersions into X;
  no extra geometric hypothesis, in particular no separate quasi-compactness assumption
  on j, is imposed.
- `i : Z ⟶ X` with `[IsClosedImmersion i]`, `j : V ⟶ X` with
  `[IsOpenImmersion j]`, and `hij : Set.range j = (Set.range i)ᶜ` say exactly
  closed immersion and complementary open immersion. No reducedness of Z is assumed.
- `pulledBackModuleObjects Λ X` is the recorded module-object category, definitionally
  `Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)`.
  `upperStar Λ i` and `upperStar Λ j` use extension along the actual canonical coefficient
  maps alpha, and `lowerStar` uses restriction along their mates eta. Their coefficient
  identification with inverse-image coefficients is exactly the recorded Cartesian
  coefficient isomorphism, not an arbitrary identification or a constant-ring replacement.
- `moduleSectionsWithSupport Λ j` is `kernel (upperStarLowerStarAdjunction Λ j).unit`
  in the functor category. Evaluation preserves kernels, so its value at M is canonically
  the stated kernel of the actual unit M → j_*j^*M. Its maps are the induced kernel maps.
  `closedModuleSectionsWithSupport Λ i j` is this kernel functor followed by
  `upperStar Λ i`, precisely the node's displayed definition of Gamma_Z.
- Clause (1) is `IsIso (Functor.whiskerLeft (moduleSectionsWithSupport Λ j)
  (upperStarLowerStarAdjunction Λ i).unit)`. This asserts invertibility of the actual
  natural closed unit N → i_*i^*N, with N the supported kernel. Thus the identification
  is both canonical and natural in M; no arbitrary objectwise isomorphism is substituted.
- Clause (2): `PreservesFiniteLimits (lowerStar Λ i)` and
  `PreservesFiniteColimits (lowerStar Λ i)` say that i_* is exact in these abelian
  categories. `Nonempty (lowerStar Λ i ⊣ closedModuleSectionsWithSupport Λ i j)`
  asserts the adjunction to the specified, constructed functor Gamma_Z.
  `PreservesFiniteLimits` on Gamma_Z is left exactness, and
  `PreservesLimitsOfSize.{u + 1, u + 1}` states preservation of all small limits in
  the fixed sheaf universe of the size-convention node.
- Clause (3): the existential `Additive` instance makes the induced termwise functor
  `mapHomologicalComplex (ComplexShape.up ℤ)` available. It does not assume additivity
  and cannot select different functor data: this is a Prop. For every unbounded integer
  cochain complex I, `I.IsKInjective → CochainComplex.IsKInjective (...)` is precisely
  preservation of K-injectivity. `∀ I, Injective I → Injective (Gamma_Z.obj I)` is
  preservation of injective module sheaves. Neither clause restricts constructibility,
  boundedness, or Tor amplitude.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `compactificationOverField` and the explicit standing over-field binders. The
  compactification itself is not needed in this sheaf theorem.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, `coefficientPullbackIso`, `condensedPullbackHom`,
  `condensedPushforwardHom`, and the corresponding monoid/commutativity instances.
- `Sheaf.Paper.ModuleObjects`: `CategoryTheory.moduleObjects`,
  `AlgebraicGeometry.ProEtale.pulledBackModuleObjects`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `lowerStar`, `upperStar`, and `upperStarLowerStarAdjunction`, with the underlying
  sheaf/action/scalar-change definitions and canonical composition interfaces.
- Mathlib `AlgebraicGeometry.IsClosedImmersion`, `AlgebraicGeometry.IsOpenImmersion`,
  `CochainComplex.IsKInjective`, and `CategoryTheory.Injective` give the exact recorded
  notions; their recorded modules are imported. The size convention has no declaration
  and is represented by explicit universes u and u+1.
- `Sheaf.Paper.LocalizingClosure`: its recorded definition
  `AlgebraicGeometry.ProEtale.localizingClosureProEtale` concerns the derived closure,
  not a predicate on admissible coefficients; the admissible coefficient list in that
  node is spelled out directly in hΛ, without inventing a second localizing closure.
- Proof-only imports retain the recorded ringed recollement, immersion limit preservation,
  open comparison, inverse image, closed counit, right-adjoint limit preservation,
  ringed-site module category, exact functor homology, injective adjunction, and termwise
  homotopy adjunction interfaces. The docstring gives all seven steps of the DAG proof.

Edge cases checked before writing:

- Empty Z and full open V: the support kernel and Gamma_Z vanish; injectivity and
  K-injectivity preservation remain valid. Full Z and empty V: the open direct image
  of the zero restriction is zero, and the kernel and closed support functor identify
  with the original module. Empty X also satisfies the statement.
- Nonreduced closed subschemes are allowed: only the immersion and complementary
  topological images occur, matching pro-etale topological invariance.
- The zero coefficient ring is included in the finite discrete alternative; n=0 forces
  1=0 and is therefore allowed precisely in this zero-ring case.
- The zero module and zero complex are allowed, as are unbounded complexes.
- Small limits use the fixed u+1 bound, not only finite or countable diagrams. The
  original pro-etale site has objects in u+1 and morphisms in u; no universe equality
  is added. Every universe and variable is explicitly bound (`autoImplicit false`).

Searches:

1. `msearch.py ... leanfinder "The kernel of the unit of open restriction followed by
   closed inverse image is right adjoint to closed immersion pushforward on sheaves of
   modules"`: eight generic hits (Scheme.Modules.restrictAdjunction, Scheme.kerAdjunction,
   and general SheafOfModules pushforward/pullback adjunctions); no complete match.
2. `msearch.py ... loogle "CategoryTheory.Adjunction, CochainComplex.IsKInjective"`:
   zero hits.
3. `msearch.py ... grep "sectionsWithSupport|closedUpperShriek|supportedAway"`:
   zero Mathlib hits. Direct rg of Mathlib kernels found `Limits.ker`, a generic arrow
   kernel functor, not the present condensed support operation.
4. Direct rg of the upstream project and `lean/WeilConjectures` found
   `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersion`:
   `ProEtale.sectionsWithSupport`, `closedUpperShriek`, and its adjunction concern
   `Sheaf ... A` for a fixed abelian category A, including constant-ring modules.
   These are not the internal modules over a pulled-back condensed ring. They cannot
   state this node for general admissible condensed coefficients. The new definitions
   use exactly the recorded internal module operations, rather than copying that category.
5. Direct rg of `lean/Sheaf`, the source repository, and `dag/lean_names_upstream.json`
   found no existing `moduleSectionsWithSupport`, `closedModuleSectionsWithSupport`,
   or `formal_closed_support_sheaves`. Search of admissible coefficient predicates found
   no usable predicate for this full list; the list is consequently inline in hΛ.
   `tools/blueprint_refs.py search 'admissible coefficient'` found eleven blueprint
   statements but no additional definition node for the list beyond the cited closure.
6. Direct search for this item's id in the upstream WeilConjectures source found no match.

No statement dispute or correction is needed. No new independent notion or dependency
repair is introduced: the two helpers construct the support operation already defined by
this very node.

## Second reading by Q09

This is the author's final self-check, not an independent agent review; the dispatch brief
requires one worker and reserves independent review for the maintainer. Re-read the source
node and full Lean signature together. All three clauses match as detailed above. In
particular the kernel uses the actual open unit, the first isomorphism is the actual closed
unit and is natural, the exact functor is i_*, and the complex assertion is unbounded.
Admissibility has not been dropped: all six coefficient classes appear in hΛ. The Qbar
valuation-topology case follows the cited node literally. The field-characteristic and
separated finite-type conditions have explicit binders. The additive instance is asserted
inside the conclusion and is not an extra assumption. No mathematical mismatch was found.

## Validation

`scompile.py Q09 det-lem-formal-closed-support-sheaves <module>` succeeded with no
errors or warnings. The first `deliver2.py ... --no-push` succeeded with
`OK (dry run): commit bedcefc941 passes the preflight and compiles; nothing pushed`.
The final import audit then replaced the broad finite-type/properties proof imports with
the exact recorded Noetherian/QuasiCompact modules; the final delivery wrapper rechecks
compilation and preflight for that import-only adjustment. No theorem signature changed.


## Maintainer fix (stage-2 review of 5422e6a4a89c)

The recorded `lean` of the statement dependency `sk-def-localizing-closure` is
`Sheaf.Paper.LocalizingAdmissibleCoefficients`, which exports
`AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient ℓ Λ`, the predicate for this
node's admissible coefficient list. The worker report's claim that no usable predicate
exists is mistaken: the delivered `hΛ` was a second, inline copy of that notion. Its six
alternatives are the predicate's (`continuousMapCondensedRing T` is by definition
`Mon.mk (Profinite.continuousMapRingObj T)`, `(ℓ ^ n : A) = 0` is equivalent to
`∀ a, ℓ ^ n • a = 0`, and a finite-dimensional intermediate field is
`PadicAlgCl.FiniteIntermediateField ℓ`). The fix therefore changes no mathematics.
`hΛ` is now `IsLocalizingAdmissibleCoefficient ℓ Λ`, imported from the recorded module
in place of `Sheaf.Paper.LocalizingClosure`. The `EllAdic` import, which only the inline
list used, is dropped, and the item's `lean.statement` is updated verbatim.
