## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds` states
`AlgebraicGeometry.ProEtale.closedEtaleTransport_bounds`, with `sorry` as its whole
proof. No definitions, axioms, new nodes, dependency repairs or statement corrections
are introduced. I read the source's Step 2 and the item's expanded five-step proof.

Hypothesis and conclusion correspondence:

- `P : PurityFiniteSetting.{u}` supplies exactly the fixed finite-field datum,
  distinct coefficient prime, finite subextension of the fixed coefficient closure,
  and positive level. `P.Ring` is the published DVR quotient and `P.Coefficient`
  its canonical universe lift; no additional ring or finiteness assumption is made.
- `Z,T : Scheme.{u}`, their `Over (Spec (.of P.field.k))` structures, and
  `LocallyOfFiniteType` plus `QuasiCompact` on their structure morphisms express
  finite-type schemes over k. There is no separatedness condition on these schemes.
- `i : Z ⟶ T`, `IsClosedImmersion i`, and `i.IsOver …` express the closed
  k-immersion. `j : W ⟶ T`, `IsOpenImmersion j`, `QuasiCompact j`, and `_hij`
  express the quasi-compact complementary open immersion.
- `c : ℕ` expresses the nonnegative integer bound, and `_hc` is precisely the
  recorded `Scheme.HasOpenComplementCondition P.Coefficient j c`, retaining both
  its all-module-sheaf vanishing clause and its constructible-sheaf clause.
- `r s : ℤ`, `_hrs : r ≤ s` give the two ordered integer bounds, including
  negative bounds and equal endpoints. `(c : ℤ)` is used in the output interval.
- The first outer conjunct has no Tor hypothesis. Its universal input `B` is in
  the dependency's `intrinsicConstructibleIntervalCategory … T r s`. The existential
  `B_e` is bounded constructible on the ordinary etale site, has
  `homologyConcentratedIn r s`, and has an isomorphism `nu_T^* B_e ≅ B.obj`.
- The natural identification for every witness is expressed as `Nonempty` of a
  natural isomorphism of functors on the full category of bounded constructible
  etale complexes with cohomology in [r,s]. Its source is `nu_T^* ⋙ P.exceptionalInverseImage i`, and its
  target is `i_e^! ⋙ nu_Z^*`. Thus for any witness alpha, compose
  `(P.exceptionalInverseImage i).mapIso alpha.symm` with its component at B_e.
  This gives the displayed identification of derived objects, natural in morphisms
  of witnesses (naturality of the natural isomorphism and functoriality of Ri!).
  The statement retains a derived isomorphism, not just cohomology isomorphisms.
- `P.exceptionalInverseImage i` is the existing intrinsic finite transported
  operation. Its ordinary etale middle functor uses compact support; for a closed
  immersion compact support is canonically closed direct image, and uniqueness of
  right adjoints identifies it with the displayed `(R(lowerStar … i)).rightAdjoint`.
  This is a comparison of canonical presentations, not a new exceptional functor.
- The first conjunct's final `constructibleInterval … Z r (s + (c : ℤ) + 1)`
  states exactly the output's bounded constructibility and cohomological interval.
- The second outer conjunct independently quantifies an ambient intrinsic B,
  assumes `intrinsicFiniteTorsionConstructible … T B` and
  `HasProEtaleTorAmplitude T P.Ring B r s`. It does not assume a cohomological
  interval separately. It quantifies EVERY bounded constructible etale B_e with
  `Nonempty (nu_T^* B_e ≅ B)` and asserts its etale `hasTorAmplitudeIn … r s`.
- Its remaining two conjuncts assert intrinsic bounded constructibility of Ri!B
  and `HasProEtaleTorAmplitude Z P.Ring (Ri!B) r (s + (c : ℤ) + 1)`.
  The etale predicate tests every degree-zero etale module sheaf. The pro-etale
  predicate tests every intrinsic degree-zero module sheaf and every K-flat
  representative used to compute derived tensor; it has no etale-origin premise
  on the test sheaf. Neither universal test is restricted to constructible sheaves.

Dependency declarations read and reused:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  its `Ring` and `Coefficient` and their ring structures.
- `def-weil-scheme-morphism-properties` is an aggregate that explicitly fixes no
  notion of its own and has no Lean record. Its finite type, closed immersion,
  open immersion and quasi-compact notions are the existing Mathlib classes.
- `Sheaf.AlgebraicGeometry.OpenComplementCondition`:
  `AlgebraicGeometry.Scheme.HasOpenComplementCondition`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: recorded
  `WeilConjectures.ConstructibleExceptionalCoefficients.System`, reexporting the
  finite operation. The finite intrinsic specialization is already defined in
  `Sheaf.Paper.ConstructibleExceptionalInverseImage` as
  `WeilConjectures.PurityFiniteSetting.exceptionalInverseImage`, transparently using
  `AlgebraicGeometry.Scheme.finiteExceptionalInverseImage` of
  `Sheaf.Paper.FiniteExceptionalInverseImage`. I use that operation unchanged.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `AlgebraicGeometry.Scheme.proEtaleSiteComparisonModules`; its existing coefficient
  comparison is realized intrinsically by
  `ProEtale.finiteCoefficientIntrinsicDerivedComparison` from
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`.
- `Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals`:
  `WeilConjectures.intrinsicConstructibleIntervalCategory`, a transparent alias of
  `constructibleIntervalCategory`; `constructibleInterval` is its object property.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `WeilConjectures.finiteTorConstructibleEtale`
  and the reexported finite-Tor predicates; their actual interval predicates are
  `Etale.DerivedCategory.hasTorAmplitudeIn` and `Scheme.HasProEtaleTorAmplitude`.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint` supplies the existing closed
  direct-image right adjoint with no new adjoint hypothesis.

All stated proof-dependency modules are imported non-publicly: finite-ring derived
origin, comparison unit, ordinary etale closed amplitude, comparison Tor amplitude,
and ordinary etale closed Tor amplitude. The docstring gives all five proof steps
and names these nodes. The natural comparison uses the invertible unit and the
closed compact-support/direct-image comparison; neither is an input assumption.

Edge cases checked before writing: empty Z; empty T (then both immersed schemes
are empty); identity closed immersion and empty complement; r=s, including negative
r; c=0; zero complex; n=1. Closed identities give the original object, which lies
in the larger stated interval. An empty scheme imposes no unwanted nonemptiness.
No finite-Tor hypothesis is present in the first assertion. No invertibility
hypothesis beyond the fixed coefficient setting and k-scheme structures is added.
Schemes stay in universe u, site objects in u+1 and morphisms in u, with module
values and lifted etale coefficients in u+1. No universe equality is imposed.

Searches made:

1. `msearch.py … leanfinder` with query “Transport etale closed immersion
   exceptional inverse image constructible cohomological intervals and Tor amplitude
   to proetale finite coefficients”: eight hits about `Scheme.Etale`, `IsEtale`,
   its instances and topology; none states this theorem.
2. `msearch.py … loogle '"TorAmplitude"'`: zero hits.
3. `msearch.py … grep 'closed.*[Ee]xceptional|[Tt]orAmplitude'`: zero hits.
4. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for closed exceptional and
   intrinsic exceptional constructions found existing support-based pro-etale
   adjoints and the intrinsic finite exceptional operation. Read the latter and
   reused it, removing a draft helper that would have repeated its construction.
   The upstream support-based functor has a different ambient formula and does
   not state this transported functor's two independent bounds.
5. Searched the item id in `lean/WeilConjectures`, and the proposed declaration
   names in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
   no match for the item theorem. Read ordinary etale Tor/cohomological bound
   declarations; neither combines the pro-etale witness and arbitrary-sheaf tests.

No statement dispute or node fault was found. The file compiled cleanly through
`scompile.py` in both sandbox and library module coordinates. The only postponed
proof is `AlgebraicGeometry.ProEtale.closedEtaleTransport_bounds`.

Final statement review restricted the natural-isomorphism domain to the same
etale cohomological interval [r,s] as clause 1, so the identification introduces
no additional cases beyond that clause. The full subcategory is the intersection
of the existing etale bounded constructibility and homology-concentration predicates.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
