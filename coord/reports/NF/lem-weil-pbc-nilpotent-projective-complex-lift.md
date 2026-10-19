## Worker report

Stated `CochainComplex.exists_projective_lift_of_nilpotent` in
`Sheaf.RingTheory.NilpotentProjectiveComplexLift`. The sole theorem has proof `sorry`;
no definitions or proofs were added. The node is unchanged except for its `lean` record.

Read the node, all three statement dependencies and their full recorded declarations,
the recorded general class-lifting theorem, and Stacks More on Algebra,
`lemma-lift-complex-projectives` (Tag 09AR). The source concludes an isomorphism of
complexes, which is retained. No statement correction or disputed claim was needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A commutative ring: `(A : Type u) [CommRing A]`.
- An ideal with a positive nilpotence exponent: `(I : Ideal A)` and
  `hI : ∃ N : ℕ, 1 ≤ N ∧ I ^ N = ⊥`. Positive integer exponents are precisely
  positive natural exponents, and the zero ideal is `⊥`.
- The derived categories of modules: `HasDerivedCategory` binders with independent
  morphism universes `w`, `w'`, and modules in `Type (max u v)`. No smallness relative
  to the ring is imposed on module carriers.
- `C ∈ D(A)`: `C : DerivedCategory (ModuleCat.{max u v} A)`; C is unbounded.
- `E` is a cochain complex of quotient modules: its type is
  `CochainComplex (ModuleCat.{max u v} (A ⧸ I)) ℤ`.
- E is bounded above: `hEbound : ∃ b : ℤ, E.IsStrictlyLE b`.
  Mathlib `isStrictlyLE_iff` identifies this with zero terms in degrees above b.
- Every term of E is projective: `hEproj : ∀ i : ℤ, Module.Projective (A ⧸ I) (E.X i)`.
  Neither finite generation nor finite presentation is required.
- Derived scalar extension: the supplied functor `L` and counit `ε` have the
  `IsLeftDerivedFunctor` universal property for termwise `ModuleCat.extendScalars`
  on the homotopy category, localized at quasi-isomorphisms. Thus this is exactly
  the derived scalar extension of `lem-pur-derived-change-of-rings` on the
  one-object identity-covering site, written in ordinary-module categories.
  These binders specify the derived functor, not extra properties of C or E.
  They match the interface of the already recorded citing module
  `Sheaf.RingTheory.PseudoCoherentNilpotentInvariance`.
- The assumed isomorphism of derived reduction with E: `hReduction : Nonempty
  (L.obj C ≅ DerivedCategory.Q.obj E)`.
- The conclusion supplies a complex P of A-modules: the existential `P`.
- P is bounded above: `∃ b : ℤ, P.IsStrictlyLE b`.
- P has projective terms: `∀ i : ℤ, Module.Projective A (P.X i)`.
- Its image represents C: `Nonempty (DerivedCategory.Q.obj P ≅ C)`.
- Its quotient is isomorphic to E as a complex: `Nonempty
  (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
  (ComplexShape.up ℤ)).obj P ≅ E)`. Extension of scalars is `(A/I) ⊗_A P`,
  canonically P/IP, with differential induced termwise. The isomorphism is in
  the category of complexes, not just its derived localization.

Dependencies used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Qh`
  (`def-weil-abstract-derived-category`).
- `Mathlib.Algebra.Module.Projective`: `Module.Projective`
  (`def-weil-pbc-projective-module`).
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`:
  `SheafOfModules.derivedChangeOfRings` (`lem-pur-derived-change-of-rings`).
  Its scalar-extension construction is specialized by the ordinary-module
  `ModuleCat.extendScalars`; the derived universal property is Mathlib's
  `CategoryTheory.Functor.IsLeftDerivedFunctor`. No replacement object is invented.
- `Sheaf.AlgebraicGeometry.ComplexLiftClassProjective`:
  `AlgebraicGeometry.complex_lift_class_projective`, imported for the proof plan.
  The other proof inputs (projective module lifting, nilpotent upper-bound detection,
  bounded-above projective models) have no recorded Lean modules, so cannot yet be
  imported. Their ids and their uses appear in the theorem's proof docstring.

Edge cases checked: zero ring and zero ideal are permitted; I = top and nilpotence
forces the zero ring and poses no extra exception. E = 0 is permitted. N = 1 is
included, while N = 0 is correctly excluded by `1 ≤ N`. The upper bound may be
negative and E may be unbounded below. Infinite projective modules are allowed.
No Noetherian, finite generation, Tor amplitude, or boundedness assumption on C
was added. Both isomorphisms are existential propositions, not chosen data.

Searches made:

- `msearch.py leanfinder`: “A bounded above projective complex representing derived
  reduction modulo a nilpotent ideal lifts to a bounded above projective complex
  over the original ring”. Eight results on projective resolutions and K-projectivity;
  none lifts a prescribed quotient complex.
- `msearch.py loogle`: `"nilpotent", "Complex"`. Zero hits.
- `msearch.py grep`: `IsNilpotent.*(Projective|Complex)|(Projective|Complex).*IsNilpotent`.
  Zero hits in Mathlib.
- `msearch.py leansearch`: “Lift bounded above complexes of projective modules over
  a quotient by a nilpotent ideal”. Service unavailable, Internal Server Error.
- `rg` in the upstream WeilConjectures tree and project Sheaf tree for derived scalar
  extension and nilpotent complex lifting: generic derived functor infrastructure,
  the general class-lifting theorem, and perfect scalar extension found; no exact
  duplicate. The citing pseudo-coherent nilpotent-invariance statement was read
  and its universal-derived-functor interface reused.
- `grep -rn` of the exact item id in upstream WeilConjectures: no hits.
- `rg` for `exists_projective_lift_of_nilpotent` and nilpotent/projective/complex
  combinations in the upstream name index, upstream source and project source:
  only the citing pseudo-coherence module's proof docstring; no name collision.

Validation: server-only `scompile.py`, nice 19, two threads, 60 seconds per file.
The revised statement compiled cleanly in 1.3 seconds before the final import-visibility
adjustment. The delivery dry run recompiles the final module and runs preflight.

## Second reading by NF

Independently read the sandbox node and theorem with Stacks More on Algebra,
`lemma-lift-complex-projectives` (09AR), its proof, and the preceding general
lifting argument (0BCA) open. The chapter explicitly uses unbounded derived
categories; this passage imposes no Noetherian or finiteness assumption. There
is no `statement_change`, no new definition node, and no dependency module in
this delivery. No mismatch was found; the Lean and node record are unchanged.

Object/hypothesis/conclusion inventory and correspondence, in node order:

1. Commutative ring A: `(A : Type u) [CommRing A]`. Exact.
2. Ideal I in A: `(I : Ideal A)`. Exact; no properness assumption.
3. Nilpotence with an integer exponent at least one: `hI : ∃ N : ℕ,
   1 ≤ N ∧ I ^ N = ⊥`. Exact, since every allowed integer exponent is a
   positive natural number. The exponent is existential, not fixed globally.
4. Arbitrary C in D(A): `C : DerivedCategory (ModuleCat.{max u v} A)`.
   Exact. Opened the recorded Mathlib `DerivedCategory`, `HasDerivedCategory`,
   `Q` and `Qh` in `DerivedCategory.Basic`: these localize all integer-indexed
   complexes at quasi-isomorphisms, without restricting their support.
5. E is an integer-indexed cochain complex of A/I-modules: `E : CochainComplex
   (ModuleCat.{max u v} (A ⧸ I)) ℤ`. Exact, including its differentials.
6. E bounded above: `hEbound : ∃ b : ℤ, E.IsStrictlyLE b`. Exact. Opened
   `CochainComplex.isStrictlyLE_iff` in Mathlib's embedding module: it means
   `IsZero (E.X i)` for every `b < i`, not just vanishing cohomology.
7. Each term projective: `hEproj : ∀ i : ℤ, Module.Projective (A ⧸ I)
   (E.X i)`. Exact. Opened the recorded projectivity class in Mathlib and its
   lifting characterization; it is a summand-of-free condition, with no finite
   generation requirement. It is the dependency's actual notion.
8. Derived extension of scalars along A → A/I: `L`, `ε`, and
   `[L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso ...)]`. Exact
   specification of the derived functor, rather than an arbitrary functor.
   Read the full recorded `SheafOfModules.derivedChangeOfRings` signature and
   docstring, and Mathlib's `Functor.IsLeftDerivedFunctor`: the latter is the
   right Kan extension universal property along the localization `Qh`.
   On the one-object identity-cover site the abelian module category and
   termwise change of rings are ordinary modules and `ModuleCat.extendScalars`.
   The specialization is expressed in these existing ordinary-module notions;
   no second derived-tensor definition or substitute object is introduced.
   The universal property determines L up to natural isomorphism, so allowing
   any such L does not change the reduction hypothesis or theorem's strength.
   The imported site theorem supplies the corresponding existence and K-flat
   computation; its stronger computation clauses need not be repeated as
   assumptions on L. The landed pseudo-coherent nilpotent-invariance theorem
   was opened and uses the same universal-property interface.
9. Derived reduction isomorphic to the image of E: `hReduction : Nonempty
   (L.obj C ≅ DerivedCategory.Q.obj E)`. Exact, in D(A/I).
10. Existence of a cochain complex P of A-modules: the existential `P :
    CochainComplex (ModuleCat.{max u v} A) ℤ`. Exact and follows all inputs.
11. P bounded above: `(∃ b : ℤ, P.IsStrictlyLE b)`. Exact; the node does not
    require a specified bound to be preserved.
12. P termwise projective: `(∀ i : ℤ, Module.Projective A (P.X i))`. Exact.
13. P represents C: `Nonempty (DerivedCategory.Q.obj P ≅ C)`. Exact.
14. Termwise quotient isomorphic to E as a complex: `Nonempty
    (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P ≅ E)`. Exact. Read Mathlib's `extendScalars`
    objects/maps: tensor with A/I and tensor of each linear map. This is
    canonically P/IP, with the quotient differential. The isomorphism is in
    the complex category, stronger than a derived isomorphism as required.

Read all three statement-dependency nodes and their recorded declarations,
and all proof-dependency nodes. Opened the complete landed
`AlgebraicGeometry.complex_lift_class_projective` signature: it supplies
exactly the complex-level conclusion once the class conditions and a bounded
projective representative computing reduction are supplied. The docstring's
five steps match the node's five proof steps, including nilpotent Nakayama,
termwise projective lifting, upper-bound detection, projective replacement,
and application of the general lifting theorem. The three smaller proof
inputs still have no recorded Lean modules; no missing statement notion or
unavailable required import was found. The existing general theorem is the
only additional proof module to import at present.

Edge cases: I = 0 and N = 1 are included; N = 0 is correctly excluded.
The zero ring, I = top when nilpotent, C = 0, and E = 0 are permitted.
Negative upper bounds, no lower bound, infinitely generated projective terms,
and every characteristic are included. There is no index-set or scheme input;
empty bases for free modules are covered through the zero module. All four
universe variables are declared. Module carriers have size `max u v`, so can
be arbitrarily large relative to A; the separate localization morphism
universes `w`, `w'` only specify category size. There is no extra algebraic
instance, finite-generation assumption, or boundedness assumption on C.

Independent searches used different phrasing from the first reader:

- LeanFinder via `msearch.py`: “Lift a prescribed complex of projective
  quotient modules over an infinitesimal thickening of rings”. Eight hits
  concern formally smooth algebras, differentials, and infinitesimal algebra
  extensions; none lifts a prescribed projective quotient complex.
- Loogle via `msearch.py`: `"lift", "Projective"`. Twelve hits concern
  ULift projectivity, lifting linear maps along surjections, and projective
  resolution comparison maps; none is this theorem.
- LeanSearch via `msearch.py`: “Prescribed projective complex lifts across a
  nilpotent ring quotient”. Service unavailable (Internal Server Error),
  recorded without treating failure as evidence of absence.
- `rg` across the pinned Mathlib, upstream `WeilConjectures`, and this project's
  `lean/Sheaf` for projective-complex lifting in both word orders and
  nilpotent-complex lifting: only general class lifting, map lifting, ordinary
  projective resolutions, and the citing nilpotent-invariance docstring. No
  duplicate of this theorem. Exact declaration/id search of the upstream name
  index also found none.

No hollow definition, helper proof, file-local notation, or private copy was
added. The only theorem proof is `sorry`. Source references and blueprint tags
are present in both module and theorem docstrings. All binders are explicit,
and the node's `lean.statement` is verbatim the file signature.

Second-reader validation: exact signature equality and 100-character Lean line
limit checked. Server `scompile.py` compiled the sole delivered file cleanly in
1.3 seconds, nice 19, two threads, 60-second limit.
