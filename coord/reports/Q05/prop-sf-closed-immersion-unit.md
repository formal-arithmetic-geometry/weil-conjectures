## Worker report

Q05, 2026-10-16. This is an existing-declaration delivery: no Lean module is written.
Only the item's `lean` record changes. Both assertions already occur in published upstream
modules, and both docstrings explicitly identify `prop-sf-closed-immersion-unit`.
The ambient declaration is
`AlgebraicGeometry.ProEtale.isIso_derivedLowerStarClosedUpperShriekAdjunction_unit_app`,
in `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersion` (lines 300–314
in the reference checkout). The recorded module
`WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek` publicly imports
that module and contains the second assertion:
`AlgebraicGeometry.ProEtale.isIso_rightDerivedUpperShriekHomEquiv_id_of_isClosedImmersion`.
The constructible theorem is the record's primary declaration, declared in the recorded module.
It also supplies `rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar`, the identification
needed to read the second unit with `Ri_*` as in the node. The `lean.statement` is the
constructible declaration's current signature verbatim, without its proof or terminating `:=`.

### Hypotheses and clauses, including the two distinct units

- Prime ell, the finite extension E/Q_ell, and n >= 1: specialize the generic coefficient
  ring to `ULift.{u+1} (Padic.coefficientExtensionRing l E n)`. The ring is the dependency's
  actual quotient O_E/(varpi_E^n), with its existing commutative ring structure.
  `Padic.finite_coefficientExtensionRing l E n hn` gives its finiteness and `ULift`
  preserves finiteness. These inputs restrict the existing general statements to exactly
  the node's coefficients; there is no replacement by a field or a regular coefficient ring.
- T Noetherian: the ambient theorem is valid more generally when the complementary open
  immersion is quasi-compact. In the node's situation open subschemes of the Noetherian
  T are Noetherian, hence the source U is Noetherian and `QuasiCompact j` follows
  (`quasiCompact_of_noetherianSpace_source` in Mathlib.AlgebraicGeometry.Noetherian).
  No extra quasi-compactness assumption is needed.
- Ell invertible on T: specialize to precisely those T with
  `∀ t : T, IsUnit (l : T.presheaf.stalk t)`. The existing ambient theorem does not need
  invertibility; it covers this case without adding an assumption.
- Closed immersion i: the surrounding binder is `(i : Z ⟶ X) [IsClosedImmersion i]`,
  with X specialized to T. The complementary open j has `[IsOpenImmersion j]` and
  `hij : IsCompl (Set.range i.base) (Set.range j.base)`. This is exactly the open/closed
  pair referenced in the statement, not an assumed recollement triangle.
- Small pro-etale sites and the ordinary unbounded derived categories:
  `DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u+1} R))` and the
  corresponding category for T. These are the constant-coefficient module-sheaf
  presentation already used by the recorded closed-support dependency; `ULift`
  adjusts only the coefficient size. No equality of object and morphism universes
  is imposed on the small site (`Scheme.{u}`, site objects in u+1, morphisms in u).
- The ambient right adjoint is exactly the dependency declaration
  `derivedLowerStarClosedUpperShriekAdjunction i j hij`, whose left side is
  `((i)_*[ModuleCat R]).rightDerivedFunctor` and whose right side is
  `(closedUpperShriek (ModuleCat R) i j).rightDerivedFunctor`.
  The latter is the derived sections-with-support right adjoint. Exactness identifies
  the former with termwise direct image. This is not a choice of an unrelated adjunction.
- Every Q, without boundedness or constructibility: the ambient theorem has just
  `(Q : DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat R)))`.
  Its conclusion is `IsIso ((derivedLowerStarClosedUpperShriekAdjunction i j hij).unit.app Q)`.
  Thus it proves invertibility of the specified unit itself, not merely the existence
  of some isomorphism between its endpoints.
- Final clause's finite-type k-scheme scope: take the existing global
  `WeilConjectures.FiniteFieldDatum` D and k = D.k; impose l != D.p, finite-type
  structure morphisms on Z,T, and `i.IsOver (Spec (.of D.k))` exactly as stated.
  A closed immersion is proper, separated and finite type and admits its identity/closed
  compactification. The existing theorem permits any compactification; in particular
  it permits the one specified by the node, without asking for any ambient datum.
- The current published constructible theorem has
  `[Etale.HasBoundedBelowUpperShriek (ModuleCat.{u+1} Λ) i]`.
  This is not a new hypothesis on the node: its recorded exceptional-inverse-image
  dependency already supplies `ProEtale.finiteTypeHasBoundedBelowUpperShriek Λ D.k i`
  in `Sheaf.Paper.FiniteTypeExceptionalInverseImage`. Closed immersion supplies the
  morphism properties required by that theorem, and the two structure maps are finite
  type by the final clause. In particular the existence interface is about the etale
  adjoint transported through comparison; it never postulates an unrestricted
  pro-etale exceptional adjoint. Read the current source through `scompile.py --source`;
  the older checkout omits this typeclass binder.
- Q in D^b_c(Z,A): the second theorem has
  `hQ : ProEtale.DerivedCategory.boundedConstructible (ModuleCat Λ) Z Q`.
  This is the etale-origin presentation of bounded constructibility. At the finite
  quotient coefficients here it agrees with the intrinsic finite partition / finite stalk /
  finitely-many-cohomology-degrees condition of the recorded
  `Scheme.intrinsicFiniteTorsionConstructible`; this finite-level equivalence is precisely
  `lem-sf-proetale-constructible-origin`, recorded as
  `ProEtale.constructible_proEtale_origin` in `Sheaf.Paper.ProEtaleConstructibleOrigin`.
  The upstream definition's docstring explicitly records this coefficient restriction.
  This identification is not asserted at integral or rational coefficient stages.
- The constructible unit is
  `rightDerivedUpperShriekHomEquiv i hQ.plusEtaleOrigin
    (hQ.plusEtaleOrigin.rightDerivedLowerShriek_obj i).plus (𝟙 _)`.
  This is exactly the image of id_(Ri_! Q) under the node's own constructible Hom
  adjunction. The conclusion is `IsIso` of this map. The functor used in that Hom
  equivalence is literally `Rν_* ⋙ Etale.rightDerivedUpperShriek ⋙ Dν^*`, the same
  formula as the recorded `finiteTypeExceptionalInverseImage` after its existence
  interface is supplied. The listed
  `rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar` identifies Ri_! with Ri_*.
  For the identity/closed compactification this is the stated Ri_! = Ri_* formula;
  for another compactification it is the canonical natural identification.
- The node says the constructible assertion exists without the optional ambient datum.
  Neither theorem assumes `Scheme.HasAmbientExceptionalRightAdjointDatum`. The ambient
  closed-support adjoint in the first assertion and the comparison-defined constructible
  functor in the second are kept distinct. No ambient/constructible identification is used.

### Signatures inspected

The ambient theorem (the section binds R, Z, U, X, i closed, j open and quasi-compact):

```lean
theorem isIso_derivedLowerStarClosedUpperShriekAdjunction_unit_app
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (Q : DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} R))) :
    IsIso ((derivedLowerStarClosedUpperShriekAdjunction i j hij).unit.app Q)
```

The second theorem's current published signature (the section binds Λ commutative,
Z,X, i closed and admitting a compactification):

```lean
theorem isIso_rightDerivedUpperShriekHomEquiv_id_of_isClosedImmersion [Finite Λ]
    [Etale.HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) i]
    {Q : DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ))}
    (hQ : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z Q) :
    IsIso (rightDerivedUpperShriekHomEquiv i hQ.plusEtaleOrigin
      (hQ.plusEtaleOrigin.rightDerivedLowerShriek_obj i).plus (𝟙 _))
```

### Dependency declarations read

Read all eight statement-dependency node statements and their Lean records.

- `def-weil-scheme-morphism-properties` is a convention node (no declaration), directing
  readers to Mathlib `IsClosedImmersion`, `IsOpenImmersion`, finite type, and properness.
- `def-weil-open-closed-recollement` has no recorded Lean declaration. Its use in this
  item is to specify the complementary geometric pair. The existing unit declarations
  already use that pair via `IsCompl`; this delivery needs no new recollement definition
  or existence statement, and does not assume a triangle.
- `lem-exc-proetale-closed-support`: upstream
  `ProEtale.derivedLowerStarClosedUpperShriekAdjunction`, read with its surrounding
  binders and its `closedUpperShriek` definition in Derived.ClosedImmersion.
- `def-weil-exceptional-inverse-image`: `ProEtale.finiteTypeExceptionalInverseImage`,
  `ProEtale.finiteTypeHasBoundedBelowUpperShriek`, and the finite-setting helpers,
  in `Sheaf.Paper.FiniteTypeExceptionalInverseImage`; current server source read too.
- `def-weil-ambient-exceptional-adjoint`:
  `Scheme.HasAmbientExceptionalRightAdjointDatum` and its full underlying structure
  in `Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint`; inspected to check that
  its optional assumptions are not being smuggled into either assertion.
- `def-weil-l-adic-coefficient-extension`: `Padic.finite_coefficientExtensionRing`
  in `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, and the quotient construction
  and docstring in its import `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `def-weil-finite-field-fiber`: `WeilConjectures.FiniteFieldDatum` in
  `Sheaf.Paper.FiniteFieldFiber`, with its fields, instance declarations and coefficient data.
- `def-weil-finite-torsion-constructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible` in
  `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`; also read the underlying
  `finiteTorsionConstructible` and upstream `DerivedCategory.boundedConstructible`.

### Edge cases checked

The ambient Q may be unbounded in either direction; its type has no t-structure predicate.
Q = 0 is included. Empty Z, empty U, and empty T are allowed: `IsCompl` still expresses
complementarity and neither theorem asks for nonempty schemes or points. In particular
an empty Z has its identity/closed compactification; no positive dimension is assumed.
At n = 1 the residue coefficient ring is included. Level zero is excluded by the node's
hn, even though the generic ring theorem also allows a zero ring. Ramified finite E and
nonregular A at higher n are allowed: only a commutative finite ring is used, with no
field, finite Tor dimension, smoothness, or constructibility condition on ambient Q.
The final theorem has bounded constructibility but no finite Tor hypothesis.
The global finite-field setting applies only to the final clause, not to arbitrary
Noetherian T in the first clause.

### Searches and source checks

- `msearch.py ... leanfinder "closed immersion pro-etale derived exceptional adjunction
  unit is an isomorphism"`: eight Mathlib hits, including the open-immersion module
  counit; none is the pro-etale closed exceptional unit.
- `msearch.py ... loogle "CategoryTheory.Adjunction.unit_isIso_of_L_fully_faithful"`:
  generic fully faithful adjunction unit theorem and a triple-adjunction theorem.
  These alone are not the geometric node.
- `msearch.py ... grep "isIso.*(ClosedUpperShriekAdjunction|UpperShriekHomEquiv)"`:
  zero Mathlib matches.
- `rg` of Mathlib's Noetherian API: located `quasiCompact_of_noetherianSpace_source`.
- `rg` of upstream `WeilConjectures/` for closed-immersion units and the exact
  blueprint id: found Derived.ClosedImmersion and Derived.ClosedImmersionUpperShriek;
  opened both full declarations, their docstrings and section binders.
- `rg` of this project's `lean/Sheaf/` for the same notions: coefficient, constructibility
  and exceptional-functor interfaces found and read; no duplicate unit theorem needed.
- The upstream name index was checked; the decisive matches are the actual source
  declarations, not an index-only attachment.
- `scompile.py --source` read the current published ClosedImmersion,
  ClosedImmersionUpperShriek, UpperShriek, and FiniteTypeExceptionalInverseImage sources.
  This revealed and accounted for the bounded-below etale interface in the current
  constructible unit signature.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED flag is needed.
The generic existing declarations specialize to both assertions with their canonical units;
writing another module would duplicate the statements. The required dry run checks all three
listed declaration names by importing the recorded module and compiling `#check @...` probes.

Dry-run repair: the initial preflight required the primary name to be declared directly
in its recorded module, rather than merely imported. The primary name is now the
constructible theorem in ClosedImmersionUpperShriek; the ambient theorem remains listed
in `lean.declarations` and is publicly imported. This changes no mathematical assertion.


## Second reading by Q05

Independent reading on 2026-10-16. I opened the item, all eight statement-dependency
nodes and their recorded declarations, the actual two upstream unit declarations,
the current published constructible-unit source through `scompile.py --source`, and
the upstream constructibility definitions down through `IsConstructibleSheaf`,
`Stratification`, `IsFiniteLocallyConstantSheaf`, and `IsFiniteSheaf`.
I also opened the recorded coefficient quotient, finite-field datum, intrinsic
constructibility, exceptional-inverse-image, and optional ambient-datum modules.

The source blueprint paragraph states the ambient assertion exactly as the current
node does. Its old final proof incorrectly used the optional ambient datum; the
already reviewed node replaces that argument and explicitly scopes the final clause
to finite-type schemes over the fixed algebraic closure. I checked the node's six
proof steps against the two existing declarations, rather than reintroducing that
old ambient identification. Stacks proetale.tex, lemma
`lemma-closed-immersion-complement-retrocompact-exact` (09BM), assumes precisely a
closed immersion and retrocompact open complement. categories.tex,
`lemma-adjoint-fully-faithful` (07RB), identifies the canonical unit as invertible
when the left adjoint is fully faithful. Both source files and the blueprint are
available in the local literature mirror; their absence from this checkout is not
a mathematical or compilation blocker.

Object/hypothesis/conclusion checklist:

1. Prime ell, finite E/Q_ell, and positive level n: the coefficient dependency's
   `Padic.coefficientExtensionRing l E n` is the actual valuation-ring quotient by
   the chosen uniformizer power. `Fact l.Prime`, `Field E`, `Algebra (Padic l) E`,
   `FiniteDimensional (Padic l) E`, and `hn : 1 ≤ n` supply its stated inputs.
   Specialize upstream `R` and `Λ` to `ULift.{u+1,u}` of that quotient, whose
   finiteness is `Padic.finite_coefficientExtensionRing l E n hn`. Verdict: same ring.
2. Noetherian T and ell invertible: the ambient theorem is valid for arbitrary
   coefficient rings and schemes with quasi-compact complementary open. Noetherian
   T makes U Noetherian and supplies `QuasiCompact j` by
   `quasiCompact_of_noetherianSpace_source`. Restrict to
   `∀ t : T, IsUnit (l : T.presheaf.stalk t)` as the node requests. The existing
   theorem needs no invertibility condition, hence covers every requested T.
   Verdict: every node instance specializes; no extra hypothesis.
3. Closed i and complementary open j: `[IsClosedImmersion i]`,
   `[IsOpenImmersion j]`, and `hij : IsCompl (Set.range i.base) (Set.range j.base)`.
   The recollement dependency is used here only for this geometric pair, not its
   triangle existence, so its lack of a Lean triangle declaration is immaterial.
   Verdict: exact geometric data, with no triangle assumed.
4. Ambient categories and right adjoint: `DerivedCategory (Sheaf (ProEt.topology Z)
   (ModuleCat.{u+1} R))` and the corresponding category for T; the dependency's
   `derivedLowerStarClosedUpperShriekAdjunction i j hij` has left side the right
   derived direct image and right side derived `closedUpperShriek`. The latter is
   `i^* ker(N → j_*j^*N)`. Exactness identifies the left side with termwise i_*.
   Verdict: the node's ordinary unbounded adjunction, not a constructible substitute.
5. Every Q, then invertibility of its specified unit: the ambient declaration binds
   arbitrary `Q` in that category and concludes
   `IsIso ((derivedLowerStarClosedUpperShriekAdjunction i j hij).unit.app Q)`.
   Verdict: the actual arrow, all Q, with no boundedness or constructibility premise.
6. Additional setting only for the final clause: specialize k to `D.k` for the
   recorded `WeilConjectures.FiniteFieldDatum D`, with ell != D.p, finite-type
   structure maps on T and Z, and `i.IsOver (Spec (.of D.k))`. A closed immersion
   supplies separatedness and finite type and its identity/closed compactification.
   The existing unit theorem permits this compactification. Verdict: the final
   clause does not impose a finite-field restriction on the ambient assertion.
7. Constructible exceptional operation without optional ambient datum:
   the published theorem has `Etale.HasBoundedBelowUpperShriek (ModuleCat Λ) i`.
   The recorded `finiteTypeHasBoundedBelowUpperShriek Λ D.k i` supplies it under
   exactly the final setting. `finiteTypeExceptionalInverseImage` then unfolds to
   the same `rightDerivedUpperShriek`, whose formula is the comparison inverse
   image composed with the etale right adjoint and derived comparison direct image.
   Neither unit theorem assumes `HasAmbientExceptionalRightAdjointDatum`.
   Verdict: no additional ambient-adjoint assumption.
8. Q in intrinsic D^b_c(Z,A): upstream `boundedConstructible (ModuleCat Λ) Z Q`
   means bounded etale-constructible origin. The finite-level origin theorem
   `constructible_proEtale_origin` identifies intrinsic constructibility with this
   mathematical condition through canonical coefficient realization. I checked the
   presentations rather than asserting definitional equality: the origin theorem
   lives in ring-sheaf modules, upstream in fixed-ring module sheaves.
   `finiteCoefficientRealization` extends constant scalar actions and is an exact
   equivalence; `originConstantModules` restricts along the canonical constant-ring
   comparison; `sfIntrinsicModuleEquivalence` gives the intrinsic constant-ring
   presentation directly. On the etale side the project's finite constant values
   and upstream finitely generated geometric stalks agree: over a finite ring a
   finitely generated module is finite, and a finite module is finitely generated.
   Both predicates use finite constructible locally closed stratifications and
   local constant trivializations. Bounded intervals and finitely many nonzero
   cohomology degrees are equivalent for integer indexing, including zero objects.
   Thus the upstream hypothesis covers exactly the node's constructible inputs
   after this equivalence. Verdict: same notion, not an added origin assumption.
9. Final conclusion and canonical unit: the primary theorem concludes `IsIso` of
   `rightDerivedUpperShriekHomEquiv i hQ.plusEtaleOrigin
   (hQ.plusEtaleOrigin.rightDerivedLowerShriek_obj i).plus (𝟙 _)`.
   This is literally the image of the identity under the specified Hom adjunction.
   The third recorded declaration
   `rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar` supplies Ri_! ≅ Ri_*;
   for the node's identity/closed compactification this is the required formula.
   Verdict: the constructible unit itself is invertible, without identifying the
   two exceptional functors on arbitrary ambient objects.

Edge cases: empty Z, U, or T are admitted by the scheme types and `IsCompl`; no
nonemptiness instance appears. Empty stratifications and zero complexes are included.
The ambient Q may be unbounded in either direction. Level n=1 is admitted; n=0 is
outside the node's scope. Ramified E and nonregular coefficient quotients at higher
levels remain allowed. No field, smoothness, finite Tor, or regularity hypothesis
has been introduced on the coefficients or Q. The schemes are `Scheme.{u}` while
the small site has objects in u+1 and morphisms in u; coefficient ULift changes
presentation only. Arbitrarily large input universes can be handled in a common
larger universe, without imposing object/morphism universe equality.

Independent searches: ran `msearch.py` with LeanFinder query "The exceptional
pullback unit for the pushforward of a complex supported on a closed subscheme is
invertible", Loogle `CategoryTheory.Adjunction, "unit"`, and grep
`closedUpperShriek|rightDerivedUpperShriekHomEquiv`. Mathlib returned generic
module pullback adjunction and unit constructions, not this geometric statement.
I searched upstream and this project's Lean by `unit`, `closedUpperShriek`,
`rightDerivedUpperShriekHomEquiv`, and intrinsic/finite constructibility names.
The exact matching upstream declarations are the three already recorded. No new
notion or dependency module is needed. The current server source confirms the
primary `lean.statement` verbatim, including its bounded-below typeclass binder;
the older reference checkout lacks that binder and was not used for the signature.

Mismatch and repair: the worker's sentence saying that the origin theorem is
"precisely" a direct identification of the two predicates skips the coefficient
presentation and the finite-stalk/finitely-generated-stalk comparison. I supplied
those details above and in `lean.note`. This is a clarification of why the existing
statement matches, not a mathematical statement change. All signatures, existing
attachments, and the source-based node statement remain correct. No Lean module
was added, no definition data or theorem proof was written, and no statement
correction, new node, dependency repair, or citer audit is required.

Validation: delivery dry run compiles fresh import-and-`#check @...` probes for
all three recorded declarations through `scompile.py`; there are no delivered
Lean files requiring separate compilation. The server preflight checks the
verbatim primary signature and delivery fields.

Dry-run result: `deliver2.py Q05 prop-sf-closed-immersion-unit --no-push` printed
`OK (dry run)` at e873e98cfd; all three existing-declaration probes compiled cleanly
and server preflight passed.
