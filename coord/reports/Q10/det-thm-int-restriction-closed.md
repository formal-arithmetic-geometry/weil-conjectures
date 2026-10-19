## Worker report

Q10 states `det-thm-int-restriction-closed` in
`Sheaf.SixFunctors.IntegralRestrictionClosed`.  The theorem uses the canonical open
complement `i.openComplement.ι`; Mathlib's `Scheme.Hom.range_eq_compl_range_openComplement_ι`
provides exactly the complement required by the formal-support dependency, so no extra
open-complement datum is introduced.  The module has two helper declarations.  `generatorsToLocalizing`
is the full-subcategory inclusion of bounded-constructible generators into
`IntegralCompactSupport.localizing`; `integralRestrictionClosedAssertions` packages the two
clauses and the natural comparison with every Brown right adjoint.  All data are canonical
functors and full inclusions; the only postponed proof is the theorem's `sorry`.

The theorem's hypotheses render the standing setting as follows.  `ℓ` is a prime via
`[Fact ℓ.Prime]`; `k` is a field of positive prime characteristic different from `ℓ` via
`[Field k]`, `[Fact (ringChar k).Prime]`, and `[Fact (ringChar k ≠ ℓ)]`.  `X` and `Z` are
schemes over `Spec k`, locally of finite type, quasi-compact, and separated.  The map
`i : Z ⟶ X` has `[IsClosedImmersion i]` and `[i.IsOver (Spec (.of k))]`.  The coefficient
ring is exactly `Profinite.padicIntegersRingObj ℓ E.val`, for the finite extension
`E : PadicAlgCl.FiniteIntermediateField ℓ`.

The conclusion has the following clause-by-clause rendering.

* The existential `hAdd` supplies the additive structure on the derived sections-with-support
  functor, exactly the additive witness in `det-lem-formal-closed-support-derived`.
* `hgen` sends every `generators Λ X K` witness to `localizing Λ X K`, giving the full
  inclusion needed to evaluate a Brown right adjoint on a bounded-constructible generator.
* For every generator `K`,
  `generators Λ Z (((closedModuleSectionsWithSupport Λ i i.openComplement.ι).rightDerivedFunctor).obj K)`
  is the statement `R\underline\Gamma_Z K ∈ Dbc(Z, O_E)`.
* For every boundary compactification `c`, every preservation witness `h`, every functor `G`
  and every adjunction `lowerShriek Λ c.obj.obj h ⊣ G`, the `Nonempty` natural isomorphism
  between `generatorsToLocalizing ℓ E hgen ⋙ G ⋙ (localizing Λ Z).ι` and the derived
  support functor on generators is the natural-in-`K` assertion `i^!K ≃ R\underline\Gamma_ZK`.
  Quantifying every Brown adjoint records the counit-compatible uniqueness supplied by
  `det-prop-int-brown-adjoint`, rather than choosing an arbitrary right adjoint.

Dependency declarations used (their full signatures and docstrings were read):

* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and the bounded
  constructible ambient category.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the finite-intermediate-field coefficient data.
* `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` and the condensed
  coefficient ring construction.
* `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, the module-object category.
* `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible` and
  `constantModelBoundedConstructible`/`ConstantModelBoundedConstructible`.
* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, `Scheme.Hom.openComplement`, and
  `Scheme.Hom.range_eq_compl_range_openComplement_ι`.
* `Sheaf.Paper.FormalClosedSupportDerived`:
  `AlgebraicGeometry.ProEtale.CondensedRing.formal_closed_support_derived` and
  `closedModuleSectionsWithSupport`.
* `Sheaf.SixFunctors.IntegralBrownAdjoint`:
  `IntegralCompactSupport.lowerShriek`, `image`, `localizing`, and
  `exists_integralBrownAdjoint`/`brownAdjointAssertions`.
* `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient` and the localizing
  closure interfaces.

Edge cases checked: the canonical complement works for both empty and whole-scheme closed
immersions; zero complexes remain generators when their constructibility predicate holds;
`K` is unrestricted in degree and no nonemptiness of `X` or `Z` is assumed; `hgen` and the
natural isomorphism quantify all generator objects, including the zero object.  The index and
scheme universes are both explicitly `u`, while module sheaves use `Ab.{u + 1}` as required
by the recorded interfaces.  No extra regularity, properness, or finiteness hypothesis on
`i` is added.

Searches for an existing declaration: `msearch.py ... leanfinder` with query
“integral exceptional inverse image closed immersion derived sections with support constructible”
returned only generic integral-morphism and constructible-image declarations; no theorem
matching this statement.  `msearch.py ... loogle` with
“Functor.rightDerivedFunctor, IsClosedImmersion, DerivedCategory” was rejected because the
query identifier is not in Loogle.  `msearch.py ... grep` for
`closedModuleSectionsWithSupport|integralRestrictionClosed` in Mathlib returned no hits.
`rg` over `WeilConjectures/` and shared `lean/Sheaf/` found no existing declaration of this
node (only downstream proof-plan references).  The recorded dependency modules were used
instead of private copies.

No `STATEMENT-DISPUTED` flag or node fault was found.  The module compiles cleanly with
`scompile.py`; the only postponed proof warning is the expected theorem `sorry`.

## Second reading by Q10

I reread the node, the blueprint paragraph, and the final module signature.  The canonical
open complement supplies the support functor without changing the node's objects.  The first
conclusion clause is exactly bounded constructibility of derived support; the second is a
natural full-subcategory isomorphism and quantifies Brown adjoints through their defining
adjunctions.  Every standing hypothesis is bound explicitly and no additional mathematical
hypothesis is imposed.  No mismatch was found.
