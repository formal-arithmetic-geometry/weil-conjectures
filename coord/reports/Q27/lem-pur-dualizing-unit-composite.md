## Worker report

Item: `lem-pur-dualizing-unit-composite`. Module:
`Sheaf.Paper.DualizingUnitComposite`. Three named theorems have `sorry` proofs;
all thirteen formula/domain definitions have complete data. A section 1(B) dependency repair
adds one named coefficient theorem, with a `sorry` proof, to the module owned by
`def-pur-co-smoothness`. There is no new independent notion and no change to the
mathematical statement.

The module uses the canonical etale-origin coordinates of the recorded
`def-pur-co-smoothness`, not an arbitrary isomorphism between endpoints. That dependency's
`finiteComparedDualizing` is the comparison pullback of `Etale.dualizingComplex`, and
`finiteComparedTensorClause` uses exactly the comparison image of
`Etale.dualizingComplexTensorMap`. Its docstring specifies full faithfulness on these
representatives and compatibility with pullback, tensor, compact supports, units and
counits. Thus the equations here are the representative equations for the small
pro-etale Dctf maps, with precisely that existing comparison convention. The etale
Dctf domain represents all pro-etale Dctf objects, rather than just lisse objects.
In particular the natural isomorphism rho is only on the full Dctf subcategory;
it is not required on the whole unbounded category. This choice of coordinates
is the same one already used by the dependency's tensor clause. Transporting arbitrary
eta and rho through the fully faithful constructible-origin equivalence recovers
arbitrary eta and rho in the statement.

Hypotheses and clauses, in order:

- `P : PurityFiniteSetting.{u}` supplies the field, fixed coefficient closure,
  finite extension, prime invertible in k, and positive level. `P.Coefficient` is
  the existing size lift of the actual quotient O_E/(varpi_E^n). No independent
  coefficient ring is assumed in any theorem. The generic coefficient parameter
  on formula definitions only avoids expensive conversion of concrete ring instances.
- `[X.Over (Spec (.of P.field.k))]`, and the corresponding binders for the other
  schemes, are the stated k-schemes. `LocallyOfFiniteType` and `QuasiCompact` on
  their structure maps express finite type. There is no absolute separatedness binder.
- Each arrow is a scheme morphism with `IsOver`, `IsSeparated`,
  `LocallyOfFiniteType` and `QuasiCompact`. These are exactly the separated finite-type
  k-morphisms. Compactifications are obtained inside the three finite assertion
  definitions by the existing `finiteComparedCompactification`; none is an additional
  theorem hypothesis. No extra equality of universes is imposed.
- W_a is exactly `Etale.dualizingComplex (ModuleCat P.Coefficient) a`, the specified
  right-derived exceptional inverse image of the monoidal coefficient unit.
  `dualizingUnitModel` constructs that unit in Dctf from the constructible-single
  and flat-single theorems. `dualizingCompositeModel` puts W_h in Dctf using the
  existing exceptional preservation theorem, and obtains the invertible exponent
  from the repaired definition-owned `finiteComparedInvertibleExponent`; it does not
  assume invertible exponent as an additional hypothesis.
- `dualizingCompositeConjugate` is the coefficient-unit component of
  `finiteExceptionalComposition`, whose definition is `conjugateIsoEquiv` of
  `Etale.unboundedEtaleLowerShriekCompIso` and the actual adjunctions. It is not
  chosen from `Nonempty`, nor replaced by a freely supplied compositor.
- `dualizingCompositeSigma` is `Etale.dualizingComplexTensorMap` followed by the
  inverse of that component. The published tensor map already has W-first source,
  so it includes the symmetry of the node's pullback-first theta. This ordering
  also explains the right unitor in the unit and target clauses and the left
  unitor in source cancellation. `Etale.derivedTensor` is the existing derived
  tensor functor, not a new tensor definition; its explicit functor syntax avoids
  an expensive conversion through monoidal notation.
- The first theorem `dualizingTensor_unit` states `dualizingFiniteUnitAssertion`.
  Its underlying `dualizingUnitAssertion` equates the actual tensor map at A with
  tensoring the actual `leftDerivedUpperStarUnitIso.hom`, followed by
  `derivedTensorRightUnitor.hom`. In the node's pullback-first coordinates this is
  precisely theta_{a,A} equal to the canonical unitor. The comparison of coefficient
  units is retained explicitly.
- The second theorem `dualizingComposite_inverse` states
  `dualizingFiniteInverseAssertion`. It quantifies over every `eta : W_b ≅ 𝟙_ _`,
  with no normalization condition. `dualizingCompositeTrivialization` is tensoring
  a*(eta), then the pullback-unit isomorphism, then the right unitor: exactly t.
  `dualizingInverseAssertion` asserts an isomorphism s with `s.hom = sigma`, hence
  invertibility of this specified map, and asserts
  `s.inv ≫ t.hom = c.hom ≫ a!.map eta.hom`. Lean's composition order makes this
  exactly t composed with sigma inverse equal to a!(eta) composed with c.
  The isomorphism's inverse is determined by its specified hom; no arbitrary
  identification of the source with W_a replaces t.
- In the third theorem `dualizingComposite_sourceCancellation`,
  `dualizingFiniteSourceAssertion` quantifies over a natural isomorphism between
  Dctf inclusion followed by e! and Dctf inclusion followed by e*. Its normalized
  equation is `dualizingRhoNormalized`, for EVERY object K of that Dctf category.
  `dualizingRhoUnit` is rho at the actual coefficient unit followed by the actual
  pullback-unit comparison, so is exactly eta_e. The normalization equation is
  theta followed by rho equal to eta_e tensor identity followed by the left unitor,
  in the published W-first coordinates. This is the node's assumed equation after
  its tensor symmetry. No normalization at arbitrary ambient K is imposed.
- `dualizingSourceAssertion` asserts sigma followed by c followed by rho at W_h
  equal to eta_e tensor identity followed by the left unitor. Thus the composite
  after sigma is exactly E_{e,h}. It also asserts `IsIso sigma`. The proof that
  W_h is Dctf is constructed by `dualizingCompositeModel`, not an extra assumption.
- Every assertion includes its equation after the pullback functor of every open
  immersion j. The inverse assertion uses `mapIso s`; the source assertion includes
  `IsIso (j*.map sigma)` as well. These are exactly the restriction equations under
  the node's supplied compatibility of operation/tensor/counit/composition data:
  the restricted maps are the images of the original maps. No existence of an
  unsupplied comparison is asserted. This agrees with node proof Step 7. Arbitrary
  compatible opens are allowed; no quasi-compactness restriction on j is added.
- There is no hypothesis of smoothness, orientation, trivialized Tate twist, or
  normalized eta. All universes and variables are explicitly bound; autoImplicit
  is disabled. The coefficient category retains size u+1 over Scheme.{u}.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Coefficient`, `.coefficientCommRing` (through the recorded co-smoothness import).
- `def-weil-scheme-morphism-properties` is a convention-only record. Its morphism
  properties are Mathlib `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: imported recorded intrinsic operations;
  the representative operations are the published `Etale.upperStar.leftDerivedFunctor`
  and `Etale.derivedTensor`, as in the recorded co-smoothness interface.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: imported recorded
  `WeilConjectures.ConstructibleExceptionalCoefficients.System`; its finite operations
  are the comparison transport of the actual etale exceptional adjunction.
  The formulas use `Etale.rightDerivedUpperShriek` and its actual adjunction.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: imported recorded
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`.
  The actual representative counit transpose is `Etale.dualizingComplexTensorMap`
  (`WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps`).
- `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`: recorded
  `AlgebraicGeometry.ProEtale.IsCohomologicallySmoothFiniteCompared`,
  `finiteComparedDualizing`, `finiteComparedTensorClause`, and
  `PurityFiniteSetting.finiteComparedCoefficientFinite`, `.finiteComparedCompactification`.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`: recorded
  `AlgebraicGeometry.ProEtale.originComposition`, brought in through the
  finite exceptional composition dependency's standing-composition import.
- Mathlib `CategoryTheory.conjugateEquiv` / `conjugateIsoEquiv`
  (`Mathlib.CategoryTheory.Adjunction.Mates`), through the finite composition definition.
- Added landed statement dependency `def-pur-finite-exceptional-composition`:
  `Sheaf.Paper.PurityFiniteExceptionalComposition`,
  `WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition`.
  This is the exact canonical finite-coefficient compositor needed by sigma.
- Repaired the already cited definition `def-pur-co-smoothness`: its module
  `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison` now also supplies
  `WeilConjectures.PurityFiniteSetting.finiteComparedInvertibleExponent`.
  The unrelated theorem `lem-pur-dnc-section-geometry` has been removed from
  `stmt_deps`, and `PurityDncComparisons` is no longer imported. The definition
  node remains the owner of its seven original declarations, whose data are unchanged.
- `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek`:
  `Etale.constructibleFiniteTor_dualizingComplex`.
- Proof-only imports: `Sheaf.Paper.ProjectionMateExact`,
  `Sheaf.SixFunctors.OpenTensorNormalization`,
  `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`.
  These match the node's proof tools. Complete natural-language arguments are
  in each of the three theorem docstrings; only their proofs are postponed.

Edge cases checked by reading the formulas: identity arrows and e = identity;
empty source/target schemes; level n = 1 (allowed), level 0 (excluded by the
existing positive-level datum); rescaling eta by any unit (naturality retains
that scalar on both sides); non-separated finite-type k-schemes (no absolute
separatedness appears); nontrivial rho on Dctf only; and open restriction that
is not quasi-compact. Source cancellation never requires h smooth. These are
mathematical checks, not claims of new proof completion.

Searches for duplication, using the prescribed `msearch.py Q27
lem-pur-dualizing-unit-composite` wrapper and read-only local searches:

- leanfinder: “Counit transpose dualizing tensor map is canonical unitor at
  coefficient unit and dualizing composition inverse under arbitrary trivialization”.
  Eight generic categorical duality hits; none identifies this geometric map.
- loogle: `CategoryTheory.conjugateIsoEquiv, CategoryTheory.MonoidalCategory.leftUnitor`.
  No result; the second qualified search name was not a declaration.
- grep of Mathlib: `dualizingComplexTensorMap|conjugateIsoEquiv|rightUnitor_naturality`.
  Generic mates/unitors only; no geometric dualizing identity.
- leansearch: “The tensor comparison to exceptional inverse image at the coefficient
  unit is a unitor”. Eight generic tensor/unitor hits; no exact statement.
- `rg` of WeilConjectures and Sheaf for dualizing tensor/unit/composition,
  and literal item-id searches: no existing exact three-clause theorem.
  `SmoothDuality.Local.nonempty_dualizingComplex_comp_iso_of_unit` gives merely
  some endpoint isomorphism under an invertibility hypothesis; it does not define
  this specified sigma or its inverse equation and is not a match.

## Dependency modules

`def-pur-co-smoothness`, section 1(B): the recorded module supplied the actual
finite coefficients, compactifications, dualizing object, tensor mate and three
cohomological-smoothness clauses, but did not expose the invertible-exponent fact
needed by the existing `Etale.constructibleFiniteTor_dualizingComplex` interface.
The repaired module retains the seven existing declarations with their exact
signatures and bodies. It adds
`WeilConjectures.PurityFiniteSetting.finiteComparedInvertibleExponent`:
for the same `P`, every scheme `T` equipped with `a : T → Spec k` satisfies
`HasInvertibleExponent P.Coefficient T`. Its docstring gives the full argument:
ell lies in the maximal ideal of O_E, so ell^n annihilates the actual quotient;
ell differs from the characteristic, so ell^n is a unit in k and hence on T.
No ramification divisibility, finite-type or separatedness assumption is needed.
This is a coefficient property within the definition's standing conventions,
not a use of the geometric DNC theorem. The dependency JSON changes only `lean`,
including its required `note` and its new helper in `lean.declarations`.

No notion is newly defined: the predicate is the published
`AlgebraicGeometry.HasInvertibleExponent` in
`WeilConjectures.AlgebraicGeometry.InvertibleExponent`, whose sole field is
`∃ n : ℕ, 0 < n ∧ (n : Λ) = 0 ∧ IsUnit (n : Γ(T, ⊤))`.
Read-only `rg` searches for `HasInvertibleExponent`, `exponent_isUnit` and
`finiteComparedInvertibleExponent` in Sheaf, WeilConjectures and Mathlib found
the predicate and several theorem-module specializations, but no definition-owned
helper of this name. In particular `P.exponent_coefficient_eq_zero` requires
ramification-index divisibility and cannot supply this unconditional interface.
The existing DNC helper has the desired type but is owned by an unrelated
statement node, exactly the defect identified in the return. The explicit repair
requested by the maintainer supplies this fact at its definition owner.

## Returned delivery repair

Compared the saved packet with current main's node and module sources, including
`scompile.py --source Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`.
The live comparison module matched the read clone. The saved item differed from
main only in its Lean attachment and two added statement dependencies; the returned
head 16b9a6c9cec6 is recorded in `coord/returns/Q27.md` with the same defect.
The delivery wrapper performs the required rebase onto current live main.

H2 and mechanical theorem-stmt_dep: removed `lem-pur-dnc-section-geometry` and
its direct `PurityDncComparisons` import, replaced the helper call by the new
`finiteComparedInvertibleExponent` in the already cited definition module, and
added that dependency's lean-only repair with `lean.note`. The previously accepted
`def-pur-finite-exceptional-composition` dependency is retained. No target clause
or formula was changed. The initial saved-packet dry run passed mechanically as
8d676d57ef9; that pass did not resolve the semantic return, which this repair does.

H11 advisory: the following reading names every hypothesis and clause and checks
the repaired dependency as well.

## Second reading by Q27

This is a worker self-reading, not an independent-agent review. The dispatcher
forbids starting other agents; the maintainer provides the independent reading.
I read the item JSON, all formula definitions and the three theorem signatures,
then the source Step 1 of `lem-pur-co-smooth-etale-locality.proof.md` and the
finite-coefficient conventions and cohomological-smoothness source definitions.
The detailed correspondence is as follows.

1. Fixed coefficients: every theorem binds `P : PurityFiniteSetting.{u}` and
   instantiates formulas at `P.Coefficient`, the size lift of O_E/(varpi_E^n).
   The existing setting binds ell distinct from p and positive n. The generic
   coefficient parameter in the formula helpers is specialized by all three
   `dualizingFinite*Assertion` definitions. The repair does not introduce an
   arbitrary coefficient ring or an invertibility assumption into any theorem.
2. Schemes and arrows: `Scheme.{u}` with `Over (Spec (.of P.field.k))` gives the
   k-schemes; `LocallyOfFiniteType` and `QuasiCompact` on their structure maps
   give finite type. Each arrow has `IsOver`, `IsSeparated`,
   `LocallyOfFiniteType`, and `QuasiCompact`. There is no absolute separatedness
   condition. Each finite assertion constructs its compactifications using
   `finiteComparedCompactification`; there is no added compactification binder.
3. Category and objects: `dualizingUnitModel` places the actual coefficient unit
   in Dctf; `dualizingCompositeModel` uses the actual exceptional preservation
   theorem to place `W_h = Etale.dualizingComplex ... h` in the same category.
   The new definition-owned exponent theorem supplies precisely that theorem's
   coefficient premise. The comparison coordinates are the recorded
   `def-pur-co-smoothness` coordinates, with coefficient universe u+1 and scheme
   universe u. Neither arbitrary maps nor an equality of universes is inserted.
4. Specified c and sigma: `dualizingCompositeConjugate` is the unit component
   of `finiteExceptionalComposition`, the conjugate of the actual compact-support
   compositor. Its direction is W_ba to a!(W_b). `dualizingCompositeSigma` is
   `dualizingComplexTensorMap ... W_b ≫ c.inv`; the upstream map's W-first
   convention includes exactly the symmetry in the node. Its domain is
   W_a tensor a*(W_b) and its codomain is W_ba.
5. First clause: `dualizingTensor_unit` asserts `dualizingFiniteUnitAssertion`.
   On expanding `dualizingUnitAssertion`, the actual theta at the unit equals
   tensoring the hom of `leftDerivedUpperStarUnitIso` and then applying
   `derivedTensorRightUnitor`. Thus the coefficient-unit comparison is explicit,
   and the map is the specified unitor, as the node requires.
6. Second clause's hypothesis and t: `dualizingFiniteInverseAssertion` quantifies
   over every `eta : W_b ≅ 𝟙_ _`. `dualizingCompositeTrivialization` applies
   a*.mapIso eta, the pullback-unit comparison, and the right unitor after
   tensoring with W_a. This has exactly the source and target of t; no
   normalization on eta is assumed.
7. Second clause's conclusions: `dualizingComposite_inverse` asserts existence
   of an isomorphism s with `s.hom = dualizingCompositeSigma`, so it asserts
   invertibility of that specified map. Its second equation is
   `s.inv ≫ t.hom = c.hom ≫ a!.map eta.hom`, exactly the node's
   t composed with sigma inverse equals a!(eta) composed with c. The hom
   constraint determines the inverse and prevents an unrelated isomorphism
   from satisfying the assertion.
8. Third clause's hypotheses: `dualizingFiniteSourceAssertion` quantifies over
   rho between Dctf inclusion followed by e! and Dctf inclusion followed by e*.
   `dualizingRhoUnit` is its component at `dualizingUnitModel` followed by the
   pullback-unit isomorphism, exactly eta_e. `dualizingRhoNormalized` quantifies
   over every Dctf object K and states theta followed by rho equals eta_e
   tensor identity followed by the left unitor, the symmetric W-first form
   of the node's normalization. It does not assume rho on every ambient object.
9. Third clause's conclusions: `dualizingComposite_sourceCancellation` gives
   `dualizingSourceAssertion` with the constructed Dctf witness for W_h.
   Its first equation is sigma followed by c followed by rho at W_h equal
   eta_e tensor identity followed by the left unitor. The last two maps
   after sigma are E_{e,h}, in the required order. The next conjunct is
   `IsIso sigma`. There is no smoothness hypothesis on h or e.
10. Open restriction: the unit and inverse assertions quantify over every
    `j : V → X` with `IsOpenImmersion j`; the source assertion does the same
    for `j : V → U`. They apply the actual derived pullback to each side,
    preserving the displayed composition, and use `mapIso s` for the inverse.
    The source assertion additionally states `IsIso (j*.map sigma)`. Under
    the node's stipulated compatibility data these are precisely the restricted
    formulas. No quasi-compactness restriction is added to j.
11. Final exclusions and edge cases: no smoothness, orientation or Tate twist
    is bound anywhere. Identities, empty schemes, arbitrary eta rescaled by a
    unit, e the identity, n = 1 and schemes not separated over k are admitted.
    In the repaired coefficient lemma ell^n works for every positive level,
    including n not divisible by the ramification index; unlike the old
    Kummer exponent lemma, it does not silently exclude these levels.
12. Dependency definition read independently of the consumer: the three
    original clauses of `IsCohomologicallySmoothFiniteCompared` still state
    two-sided tensor invertibility with a pro-etale Dctf inverse, invertibility
    of the specified tensor mate on every representative, and invertibility
    of the specified base-change mate on every allowed square. Their bodies
    are unchanged. The added coefficient theorem supplies a property already
    forced by the fixed coefficients, with full source/proof docstring and
    `sorry` only in that named theorem. All definition data remain explicit.

The mismatch found on this reading was ownership of the coefficient helper;
its repaired definition-module ownership and the removed DNC dependency are
listed above. No additional statement mismatch was found, and no mathematical
statement correction or `STATEMENT-DISPUTED` flag is needed.

Validation: repaired `scompile.py` compiled both modules separately in dependency order
against the live library. `CohomologicalSmoothnessFiniteComparison` compiled in
6.5 seconds as a library module; `DualizingUnitComposite` compiled in 29.4 seconds.
Both were clean, with only the allowed postponed theorem proofs. All Lean lines
are at most 100 columns. The dependency JSON differs from main only in `lean`.
No global build, direct Git operation, or edit to the read-only project was made.
The repaired delivery dry run passed preflight and per-file compilation as
commit `6623e6b651e`; that validation run pushed nothing.
