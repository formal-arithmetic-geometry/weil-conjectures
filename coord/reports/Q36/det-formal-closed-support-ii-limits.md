## Worker report

The module `Sheaf.Paper.FormalClosedSupportIILimits` states
`AlgebraicGeometry.ProEtale.CondensedRing.formalClosedSupportIILimitsAssertions`.
It introduces the proposition-valued helper structure
`ClosedSupportLimitFunctorProperties` for an additive functor between the relevant
triangulated categories.  Its fields state preservation of all products in the fixed
size universe, preservation of distinguished fiber triangles, and the explicit
projection-compatible image Roos triangle for every sequential derived limit.  Its
`comparison_isIso` field states that every compatible completion between two such Roos
triangles is invertible, without choosing a cone.

The theorem uses the standing prime and characteristic hypotheses: `[Fact ℓ.Prime]`,
`[Field k]`, `[Fact p.Prime]`, `[CharP k p]`, and `hpℓ : p ≠ ℓ`.  The standing scheme
hypotheses are `[X.Over (Spec (.of k))]`,
`[LocallyOfFiniteType (X ↘ Spec (.of k))]`,
`[QuasiCompact (X ↘ Spec (.of k))]`, and
`[IsSeparated (X ↘ Spec (.of k))]`.  It binds closed `i : Z ⟶ X`, open `j : V ⟶ X`
with `[IsClosedImmersion i]`, `[IsOpenImmersion j]`, `[QuasiCompact j]`, complementary
range equation `hij`, and open `u : S ⟶ Z` with `[IsOpenImmersion u]`.  The finite
locally free hypothesis on `L : FormalSupportModules Λ S` is rendered by a
pro-étale cover `𝒰` and, for every cover member, an isomorphism of the pullback of `L`
with `Mod.finiteFree ... n`; `n = 0` is allowed.

The six listed functors are rendered by the existing canonical declarations:
`(formalSupportPullback Λ j).mapDerivedCategory` for `j^*`,
`(formalSupportPullback Λ u).mapDerivedCategory` composed after
`(formalClosedSupport Λ i j).rightDerivedFunctor` for `u^* RΓ_Z`,
`(formalSupportPullback Λ i).mapDerivedCategory` for `i^*`,
`(lowerStar Λ j).rightDerivedFunctor` for `Rj_*`,
`(formalClosedSupport Λ i j).rightDerivedFunctor` for `RΓ_Z = RG`, and
`(derivedTensor Λ S).obj ((DerivedCategory.singleFunctor
(FormalSupportModules Λ S) 0).obj L)` for `L[0] ⊗^L_{Λ_S} -`.  The helper fields
state additivity and triangulatedness for each, all small products in the selected
size bound, fiber preservation through `F.mapTriangle`, the Roos triangle with
`e.hom ≫ Pi.π _ n = F.map (Pi.π K n)`, and invertibility of every compatible
comparison.  The closed-support functor is the canonical kernel construction from
`Sheaf.Paper.FormalClosedSupport`, so it is exactly the `i^* ker(id → j_*j^*)`
construction in the node.

Dependency declarations used:

- `AlgebraicGeometry.ProEtale.CondensedRing.formalClosedSupportAssertions` from
  `Sheaf.Paper.FormalClosedSupport` (`sk-lem-formal-closed-support`).
- `AlgebraicGeometry.ProEtale.CondensedRing.coefficientRing` and
  `condensedRingObj` from the published pro-étale coefficient framework
  (`sk-def-sfb-pulled-back-coefficients`).
- `AlgebraicGeometry.ProEtale.CondensedRing.upperStar` and `lowerStar` from
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`
  (`def-sfb-module-upper-star`, `def-sfb-module-lower-star`).
- `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` and its
  derived-category interfaces from `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
  (`def-sfb-right-derived-functor`).
- `AlgebraicGeometry.ProEtale.CondensedRing.derivedTensor` from
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor`
  (`def-sfb-derived-tensor-modules`).
- `CategoryTheory.DerivedCategory`, `CategoryTheory.IsDerivedLimitTriangle`,
  `AlgebraicGeometry.IsClosedImmersion`, `AlgebraicGeometry.IsOpenImmersion`, and
  Mathlib's `SheafOfModules`/ringed-site module interfaces for the corresponding
  dependency nodes.
- The finished upstream ℓ-adic algebraic-closure node is used via its closed audit
  declarations `Profinite.padicAlgClCondensedRing` and
  `Profinite.padicAlgClRingObj` in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`; no duplicate
  coefficient definition is introduced.

Edge cases checked: the cover rank may vary with the cover member and may be zero;
empty products are included by `PreservesLimitsOfShape`; towers have arbitrary
transition maps and include the zero tower; the Roos comparison does not choose a
cone; identity open immersions and empty closed supports use the same canonical
pullback/kernel terms; and no nonempty-index, boundedness, or extra characteristic
hypothesis was added.

Searches made: `msearch.py ... leanfinder "closed support commutes with derived limits
of sequences"` returned only unrelated topological/module-support declarations;
`msearch.py ... loogle "IsDerivedLimitTriangle, formalClosedSupport,
PreservesLimitsOfShape"` returned no hits because the composite query contained an
unavailable identifier; `msearch.py ... grep
"formalClosedSupportIILimits|closedSupport.*derived.*limit" Mathlib` returned no
hits.  `rg` over `WeilConjectures/` and `lean/Sheaf/` found no
existing `FormalClosedSupportIILimits` or equivalent declaration, and
`grep -rn "det-formal-closed-support-ii-limits"` in the source found no declaration.
The published EllAdic module and its full docstrings were read with
`scompile.py --source WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`.
The file compiled cleanly with `scompile.py` before the final docstring-only edit;
all changes after that compile are documentation and do not alter elaboration.

No `STATEMENT-DISPUTED` flag or node fault was found.

## Second reading by Q36

I reread the node and module together.  Every standing hypothesis is present, including
`p ≠ ℓ`, the separated finite-type setting on `X`, the complementary range equation,
the open immersion `u`, and the finite locally free cover with varying finite rank.
The six functors are the existing coefficient-compatible module pullback/direct-image,
closed-support right-derived, and module-object derived-tensor constructions.  The
helper structure matches each repeated clause: additivity, triangulated/fiber behavior,
all products, the image Roos triangle with its projection equations, and the
invertibility of every compatible Roos comparison.  The theorem concludes only the
assertion structure under the finite locally free hypothesis; it does not select a
limit object or weaken the comparison clause.
