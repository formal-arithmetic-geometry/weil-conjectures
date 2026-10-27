## Worker report

The module `Sheaf.RingTheory.LineModuleDuality` states
`Module.line_module_duality`, with a single `sorry` proof. It introduces no new
definition and preserves the accepted stage-1 split and statement verbatim.
The inherited BLOCKED ending was a stage-1 resplitting refusal, not a stage-2
failure: coord/brief-stage2.md §0 explicitly authorizes this handoff. The live
node has a passing Q91 stage-1 review and had no Lean record. There is no repair
note for this item.

Source read: Stacks `literature/stacks-project/more-algebra.tex`,
lemma-invertible, Tag 0B8I, lines 36118–36173, and section-determinants,
Tag 0FJ9, the paragraph identifying R with Hom_R(L,L) before
remark-determinant-as-socle, lines 36248–36262. The former evaluates the dual
and the latter identifies scalar endomorphisms. The node supplies the explicit
finite dual-basis proof omitted in the source; all five steps are in the theorem
docstring for stage 3.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A commutative ring R: `(R : Type u) [CommRing R]`.
- An R-module L: `(L : Type v) [AddCommGroup L] [Module R L]`. The independent
  explicit universes u, v impose no size relation on the ring and module.
- L is a direct summand of a finite free module:
  `[Module.Finite R L] [Module.Projective R L]`. This is precisely the usual
  equivalent typeclass form, not a global-freeness assumption.
  `Module.Finite.exists_comp_eq_id_of_projective` in
  Mathlib.RingTheory.Finiteness.Projective, line 30, explicitly produces
  n, f : (Fin n → R) →ₗ[R] L, g : L →ₗ[R] Fin n → R with f.comp g = id.
  Conversely, a split summand of finite free is finite by the surjective
  retraction and projective by `Module.Projective.of_split`/`iff_split`.
- At every prime p, L_p is isomorphic to R_p: `hlocal` quantifies over
  `(p : Ideal R) [p.IsPrime]` and asserts
  `Nonempty (LocalizedModule p.primeCompl L ≃ₗ[Localization.AtPrime p]
  Localization.AtPrime p)`. This is an actual linear equivalence over R_p,
  exactly as stipulated in the node, rather than a cardinal-rank assertion.
- The dual L^vee = Hom_R(L,R) is Mathlib's `Module.Dual R L`, the domain factor
  of `contractLeft R L`.
- Ordinary tensor product and canonical evaluation lambda tensor l ↦ lambda(l):
  `contractLeft R L : TensorProduct R (Module.Dual R L) L →ₗ[R] R`, with this
  exact pure-tensor formula by `contractLeft_apply`. The first conclusion is
  `Function.Bijective (contractLeft R L)`, hence this specified linear map is
  an isomorphism (packaged by `LinearEquiv.ofBijective` when needed).
- The specified R-linear scalar map r ↦ (l ↦ r • l): `LinearMap.lsmul R L`.
  Its type is `R →ₗ[R] L →ₗ[R] L`, with formula `lsmul_apply`.
  The second conclusion asserts its bijectivity, hence precisely its linear
  isomorphism property, not the existence of an unrelated equivalence.
- The dual is a tensor inverse under ordinary symmetry: the third conclusion
  `Function.Bijective (contractRight R L)` supplies the other tensor order
  `L ⊗[R] Module.Dual R L →ₗ[R] R`, with formula l tensor lambda ↦ lambda(l).
  It is the first evaluation precomposed with `TensorProduct.comm`, so these
  two canonical isomorphisms express the stated tensor-inverse clause.

Dependency declarations used and read in full with their docstrings:

- def-weil-pbc-projective-module: `Module.Projective`, imported from
  Mathlib.Algebra.Module.Projective; the split-free characterization
  `Module.Projective.iff_split` was also read (lines 235–239).
- def-weil-pbc-module-localization: `LocalizedModule`, imported from
  Mathlib.Algebra.Module.LocalizedModule.Basic, lines 86–90, with the fraction
  constructor and equality criterion at lines 99–105. `Localization.AtPrime`
  is imported from Mathlib.RingTheory.Localization.AtPrime.Basic (lines 59–62)
  to specify the localized scalar ring. These are the dependency's recorded
  declarations; no copy of localization is defined.
- def-weil-pbc-module-tensor-product: `TensorProduct` from
  Mathlib.LinearAlgebra.TensorProduct.Defs, lines 78–83, imported through
  Mathlib.LinearAlgebra.TensorProduct.Basic; `lift` and its universal-property
  docstring at Basic lines 117–140 were read. The canonical evaluation maps
  `contractLeft`, `contractRight` and their formulas come from
  Mathlib.LinearAlgebra.Contraction, lines 45–66.
- The proof-only dependency lem-weil-pbc-prime-localizations-jointly-injective
  is a Mathlib leaf: `PrimeSpectrum.toPiLocalization_injective` from
  Mathlib.RingTheory.Spectrum.Maximal.Localization, lines 165–173 (read with
  its canonical map). Its module is a plain, non-public import. All other
  proof dependencies coincide with the statement dependencies above.

Edge cases checked before writing:

- Zero ring: no Nontrivial assumption is imposed. There are no prime ideals,
  so hlocal is vacuous; every module over the zero ring and all the displayed
  domains/codomains are subsingleton. Thus all three maps are bijective.
- L = 0 over a nonzero ring is excluded by the prime-local rank-one hypothesis;
  this does not silently assert invertibility of an arbitrary zero module.
- L = R gives the familiar multiplication/evaluation identifications.
- A genuinely nontrivial invertible module need not have a global generator:
  neither `[Module.Free R L]` nor an equivalence L ≃ R is assumed.
- Over a field, L = R² fails hlocal, as required. The finite dual-basis proof
  allows n = 0 in the zero-ring case and uses no chosen nonempty basis.

Searches actually run with the prescribed msearch.py wrapper:

- leanfinder: “A finite projective module locally free of rank one has bijective
  dual tensor evaluation and scalar endomorphism map” returned reflexivity
  results, Module.Invertible.bijective/linearEquiv, bijective_curry, and the
  finite-dimensional categorical evaluation. None supplies this hypothesis.
- loogle: `Module.Invertible, Module.Invertible.toModuleEnd_bijective` returned
  Module.Invertible.toModuleEnd_bijective, which assumes Module.Invertible.
- grep, RingTheory/PicardGroup.lean:
  `class Invertible|toModuleEnd_bijective|become free of rank one` returned the
  class at line 77, scalar theorem at 257, and TODO at 56 explicitly leaving
  the prime-local rank-one characterization to be established.
- leansearch: “A finite projective module locally free of rank one has bijective
  evaluation with its dual” returned double-dual/reflexivity theorems, which
  concern L → L** rather than the tensor evaluation in this item.
- Direct rg of lean/WeilConjectures and lean/Sheaf for the item id,
  `lineModuleDuality`, `line_module_duality`, `locally.*rank.*one`, and
  `toModuleEnd_bijective` found no public exact match. The source
  WeilConjectures.Mathlib.RingTheory.PicardGroup has
  Module.Invertible.of_isLocalized_span, a result on a spanning family of
  principal localizations, not this prime-local statement. The file was read.
  Sheaf.RingTheory.RegularLocalPicardZero has a private, proved
  invertible_of_prime_localizations helper; its enclosing public theorem
  concerns regular-local Picard triviality and is not the item. The helper
  cannot be used as a public existing declaration and does not state all
  clauses. The present file neither imports it nor duplicates its name.
- The proposed declaration name was also checked in dag/lean_names_upstream.json
  and both project roots; no match. No new node or dependency repair is needed.

No statement dispute or node fault was found.

Validation: the prescribed scompile.py invocation compiled both the sandbox
probe (2.4 s) and the real library module (5.0 s) cleanly, with no warnings or
errors. The module uses `module`, public statement imports, a plain proof-only
import, an exposed public section, and explicitly bound universes and variables.

## Second reading by Q28

This is the dispatched author's second pass; the maintainer performs the
independent review, as the dispatch brief specifies. No other agent was started.
I reopened the JSON statement and the final file and checked the finite-summand
hypothesis against Mathlib's explicit finite splitting theorem. Both directions
of that equivalence hold, so the typeclass form neither adds nor drops a
hypothesis. I checked that hlocal uses R_p-linearity, not just R-linearity, and
that its quantified p includes every prime. I checked the three maps by their
pure-element formulas: contractLeft is lambda(l), lsmul is r • l, and
contractRight is lambda(l) in the swapped tensor order. Their bijectivity is
exactly the two isomorphism conclusions and the symmetric inverse clause.
The dual is Mathlib's Hom module, not a chosen inverse, and no assumption
Module.Invertible has replaced the local-rank-one hypothesis. The zero ring,
zero module, field rank-two exclusion and absence of a global generator were
checked again. No mismatch was found and no node correction was made.
