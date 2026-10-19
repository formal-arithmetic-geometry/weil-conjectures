## Worker report

The main module `Sheaf.Paper.ClosedAdjointConstructibleYoneda` states
`AlgebraicGeometry.ProEtale.CondensedRing.closedAdjointConstructibleYoneda` with
`sorry`. It identifies the given localizing exceptional right adjoint with the actual
right derived functor of the recorded support kernel. The comparison is a natural
isomorphism in the full localizing subcategory on Z, with the specified ambient counit
equation. No statement correction or new definition node is needed. There is exactly
one postponed theorem, the comparison itself; no construction has postponed data. The returned coefficient-heart replacement has been removed.

Hypotheses and clauses, against the node and its blueprint source:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The characteristic is the prime
  `(p : ℕ) [Fact p.Prime] [CharP k p]` with `(k : Type u) [Field k]` and
  `hpℓ : p ≠ ℓ`. This includes every positive field characteristic distinct from ℓ.
- `X` and `Z` are `Scheme.{u}` with `Over (Spec (.of k))`, and their structure
  morphisms have `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` instances.
  These express exactly separated finite type over k, without smoothness, reducedness,
  nonemptiness, or dimension assumptions. The explicit `i : Z ⟶ X` has
  `[IsClosedImmersion i]` and `[i.IsOver (Spec (.of k))]`.
- `E : PadicAlgCl.FiniteIntermediateField ℓ` is a finite subextension in the fixed
  algebraic closure. The condensed ring object `Λ` has `MonObj` and `IsCommMonObj`
  structures. `_hΛ` identifies it, as a ring object, with `continuousMapRingObj E`
  or `continuousMapRingObj (PadicAlgCl ℓ)`. These use the induced topologies and all
  continuous maps, not a discrete constant coefficient field or the different
  finite-subextension-valued closure object. Ring-object isomorphisms permit any
  presentation of exactly the specified coefficients.
- `constantModelBoundedConstructible Λ T` and its `FullSubcategory`, named
  `ConstantModelBoundedConstructible Λ T`, are the recorded Dbc. They impose bounded
  constructible cohomology with finite constant scalar models. `localizingClosureProEtale`
  is the recorded intersection closure in the ordinary unbounded derived module-object
  category. Its generators are Dctf. Input membership in this closure is the concluded
  witness `hK`, rather than an additional assumption or a consequence supplied by a
  replacement coefficient-heart theorem.
- `c : Compactification.BoundaryCompactification i` and `h` specify the restriction
  of the already recorded compactification lower shriek to those closures.
  `G` and `adj : localizingLowerShriek Λ c.obj.obj h ⊣ G` are the given i^! and
  adjunction of sk-prop-sf-existence. They are quantified as specified adjunction data,
  not new geometric assumptions or an arbitrary unconstrained map.
- `closed` is the stipulated closed-immersion normalization, a natural isomorphism
  from the restricted lower shriek followed by the full inclusion to the full
  inclusion followed by the exact derived direct image `(lowerStar Λ i).mapDerivedCategory`.
  Its use in the counit equation ensures the normalization is part of the adjunction
  comparison. The assertion applies to every such specified normalization and adjunction.
- The support construction uses `j : U ⟶ X`, its open-immersion and quasi-compactness
  instances, and `hij : Set.range i.base = (Set.range j.base)ᶜ`, exactly as its recorded
  dependency does. This simply presents the complementary open required to write the
  kernel construction. Every closed immersion in this Noetherian standing setting has
  such a quasi-compact complement; no closed immersion is excluded. A separate k-structure
  on U is unnecessary since it is inherited from its open immersion into X.
  `support : FormalClosedSupportAssertions Λ i j hij` specifies the normalized
  ambient support adjunction whose existence is the recorded formal-support theorem.
  Its `rightAdjoint` is to the actual `(formalClosedSupport Λ i j).rightDerivedFunctor`.
  This is existing specified adjunction data, not an assumption of the desired comparison.
- The existential `hK` establishes that every `K : ConstantModelBoundedConstructible Λ X`
  belongs to C_X. It is not an extra membership hypothesis. The existential `hS`
  establishes support-value membership in C_Z. Both are proof-valued membership data.
- Using those witnesses, `ObjectProperty.lift` restricts the inclusion and actual
  support functor with their unchanged objects and morphisms. The existential `e`
  is a natural isomorphism between the inclusion followed by G and this lifted support
  functor, in C_Z. Thus its component is precisely the required i^!K ≅ RΓ_Z K in C_Z,
  and its naturality is imposed for every morphism of Dbc by `NatIso`, not just for objects.
- The final equality for every K says that the exact closed pushforward of
  `e.hom.app K`, followed by `support.rightAdjoint.counit.app K.obj`, equals
  `closed.inv.app ...` followed by the included exceptional counit `adj.counit.app ...`.
  Both sides have source i_*i^!K and target K in D(X). This is the two-counit compatibility
  in precisely the direction of the node. The statement does not add uniqueness or an
  independent constructibility conclusion, although the source proof derives both.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`, for the standing
  setting and chosen compactifications. Read the actual side-framework source in
  `lean/WeilConjectures`, as required by `coord/pefw-upstream-framework.md`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, the closed embedding and surjective stalk maps.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `constantModelBoundedConstructible`, `ConstantModelBoundedConstructible`,
  `ConstantModelConstructibleFiniteTor`, and their underlying finite-constant-model predicates.
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`, importing `Sheaf.Paper.LocalizingClosure`:
  `IsLocalizingAdmissibleCoefficient`, `localizingClosureProEtale`, and the generic
  `CategoryTheory.localizingClosure`; no completeness condition is inserted.
- `Sheaf.Paper.CoefficientHeart` (unchanged recorded proof dependency):
  `AlgebraicGeometry.ProEtale.coefficientHeart` and its recorded `*Assertions`
  declarations. Its algebraic-closure coefficient is `padicAlgClCondensedRing`, the
  finite-subextension-valued object from sk-def-sfb-qlbar-condensed. This is the
  correct coefficient convention of that dependency node. No theorem about all
  continuous closure coefficients is substituted for it.
- `Sheaf.Paper.LocalizingExceptionalAdjoint`:
  `localizingLowerShriek` and `exists_localizingExceptionalAdjoint`. The former is used
  literally in `adj` and `closed`; the latter supplies the specified right-adjoint data.
- `Sheaf.Paper.FormalClosedSupport`:
  `FormalClosedSupportAssertions`, `formalClosedSupportAssertions`; its imported
  `Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction` defines `formalClosedSupport`,
  `formalSupportKernel`, and the normalized support inclusion. The actual right-derived
  functor and `support.rightAdjoint.counit` are used, rather than a fresh support construction.
- `Mathlib.CategoryTheory.Yoneda`: `CategoryTheory.Yoneda.fullyFaithful`, the recorded
  Mathlib proof dependency, imported for the proof plan. The support-constructibility
  proof dependency has no recorded declaration at this reading and hence no module to
  import; it is not a missing notion required to type this comparison statement.

Edge cases checked: K = 0, empty X or Z, identity closed immersion, empty open
complement, either field-coefficient branch, arbitrary characteristic p distinct from ℓ,
and nonreduced and reducible standing schemes. No nonzero, positive rank, nonempty,
reduced, connected, smooth, or fixed dimension binder excludes these cases. All schemes
and their sites use the existing universe u convention, with abelian coefficients in
u+1 and the framework's ambient derived category; no site-universe equality is added.
For i = identity, j is empty and the comparison reduces to uniqueness of a right
adjoint of the identity with the prescribed normalization. For empty Z both compared
objects are in its zero derived category. The support counit always uses its normalized
kernel adjunction, so a rescaling of the exceptional adjunction is handled by `closed`
and the resulting comparison instead of silently equating two possibly different counits.

Searches made with msearch.py, group Q41 and this item (2026-10-18):

- LeanFinder: "For a closed immersion exceptional inverse image on the localizing
  constructible pro-etale derived category is naturally isomorphic to derived sections
  with support compatibly with counits". Eight hits, primarily scheme-module open
  restriction adjunctions; no matching condensed localizing-category theorem.
- Loogle: `CategoryTheory.Adjunction.rightAdjointUniq`. Twelve hits, including
  `rightAdjointUniq` and its counit equations. They compare two adjoints on the same
  complete categories; they do not establish this geometric support membership and
  comparison restricted to Dbc inputs.
- LeanSearch: "closed immersion exceptional inverse image agrees with derived sections
  with support on constructible pro-etale complexes". Eight hits, all closed immersion
  definitions or properties; no match.
- msearch grep: `closedUpperShriek|sectionsWithSupport|rightAdjointUniq`, Mathlib
  `CategoryTheory`. Nineteen hits on generic adjunction uniqueness; no geometric match.
- Direct rg over the specified slopmaster2 `WeilConjectures`, the side `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: item id has no upstream declaration; closed-support
  results in the ordinary ModuleCat coefficient category are different from these
  internal condensed module objects. Read the side FormalClosedSupport, LocalizingClosure,
  LocalizingExceptionalAdjoint, CoefficientHeart, and RationalExceptionalRestriction
  signatures and docstrings. No existing declaration states this comparison.
- Direct rg `CoefficientHeartAssertions|theorem coefficientHeart|coefficientHeartContinuous`
  over the side library and slopmaster2 sources found the existing predicate and theorem,
  plus separate closure, filtration, common-stratification and smallness results.
  Correction after return: the finite-subextension-valued coefficient is the correct
  convention of sk-lem-coefficient-heart; this search does not justify replacing its
  record with a theorem for a different coefficient ring.
- Further LeanFinder: "Bounded constructible internal modules over continuous condensed E
  or algebraic closure Q_l have finite Tor amplitude and their constructible heart is
  abelian essentially small with finite lisse stratum filtration". Eight hits about the
  ambient categories of condensed modules (Abelian, Grothendieck, AB4/AB5), with no
  bounded constructible heart statement. Loogle `CategoryTheory.Abelian` returned twelve
  generic category declarations, not this geometric heart theorem.

## Repair of returned delivery

The maintainer returned head `4f40fde6af8f` for H13/H4. Its sole required repair is
implemented in full: the sandbox copy of `sk-lem-coefficient-heart.json` is removed,
so delivery leaves its current record unchanged; `CoefficientHeartContinuous.lean`
is removed; and the comparison no longer imports that module. The existing recorded
`Sheaf.Paper.CoefficientHeart` is imported as a proof dependency instead. No replacement
coefficient-heart theorem or new node is included. In particular, this delivery does
not assert that the existing coefficient-heart node means all continuous functions
into the algebraic closure, or claim that its theorem establishes the all-continuous
coefficient case of the comparison. The comparison signature and proof docstring are
unchanged from the independently checked returned version.

Compared against the current shared DAG, the item's only changed field is `lean`;
its statement, dependencies and proof are unchanged. The coefficient-heart node and
all of its citers remain untouched. The first required saved-packet dry run passed
as `c1ca25e455`; that mechanical pass did not resolve the mathematical return, which
is repaired by the removals above.

## Second reading by Q41

This is a second reading by the dispatched worker; no additional agent was started.
I reopened the current node, source blueprint statement and proof, comparison module,
and the unchanged coefficient-heart declaration and assertion predicate. The previous
report incorrectly called the finite-subextension-valued coefficient unusable. That
claim and the associated dependency replacement are removed.

The main signature still includes both primes, the characteristic inequality, separated
finite-type k-schemes, the closed k-immersion, and the two stated coefficient branches.
The specified adjunction and closed normalization are preserved. The open complement
and normalized support adjunction supply the recorded actual support functor. Both
input membership `hK` and support membership `hS` remain conclusions. The `NatIso` has
all Dbc inputs and values in the full localizing category on Z. Its mapped component
followed by the support counit equals the inverse closed normalization followed by
the exceptional counit, in the node's direction. Zero, empty schemes, identity closed
immersion, empty complement, and both coefficient branches remain covered. All universe
and variable binders are explicit. No further mismatch was found in the comparison
statement, which the maintainer had independently checked clause by clause.

Validation: the repaired comparison compiled cleanly through `scompile.py` in both
the private sandbox (56.8 s) and library-path check (6.0 s), under the unchanged
60-second limit. No compiler errors or warnings were emitted. The prescribed delivery
dry run is the final mechanical gate before push.
