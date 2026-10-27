## Worker report

The module `Sheaf.RingTheory.CompatibleEtaleModelTower` states
`Algebra.CompatibleEtaleModelTower.exists_compatible_models`, with one `sorry` and
no other postponed theorem. The source is Stacks Project `restricted.tex`,
Tag 0AKA (`lemma-approximate`), lines 2124–2166: the compatible-model claim.
I read the preceding setup, lines 2091–2123, and the full eight-step DAG proof.
No statement correction, dependency repair or new independent notion is needed.
Only the item's `lean` record changes.

The helpers are explicit applications of existing Mathlib constructions:
`powerIdeal a m = Ideal.span {a} ^ m = (a^m)`,
`base a m = A/(a^m)`, `quotient (E := E) a m = E/a^m E`,
`quotientIdeal K a m = K A_m`; `quotientAlgebra` is
`Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map`.
`reduction` is `Ideal.Quotient.factor` applied to the inclusion of successive
extended powers. `complement` is the open complement of the actual prime-spectrum
zero locus. None chooses an unspecified map or contains postponed data. These
helpers belong to the item's notation and canonical constructions, as authorized
by the brief's missing-helper provision; no new mathematical predicate is defined.
Every helper and the theorem is listed in `lean.declarations`.

Clause-by-clause correspondence (write m = n+1 throughout):

- Commutative Noetherian A: `{A E : Type u} [CommRing A] [CommRing E]`,
  `[Algebra A E]`, `[IsNoetherianRing A]`. The common ambient universe is arbitrary,
  and the `CommAlgCat` carriers lie in that ambient ring universe.
- Ideal K and element a: `(K : Ideal A) (a : A)`. The named I = K+(a) is substituted
  directly as `K ⊔ Ideal.span {a}`, and its completeness hypothesis is
  `[IsAdicComplete (K ⊔ Ideal.span {a}) E]`.
- A_m, K_m and E_m are exactly `base`, `quotientIdeal` and `quotient`, as above.
  `n : ℕ` indexes every positive m, omitting no positive level and introducing no
  artificial level zero. The completeness of every E_m is `hcomplete` with the
  canonical quotient-base algebra instance.
- Existence of each independent finite type model D_m: `hmodels` quantifies
  `∃ D : CommAlgCat (base a (n+1))` and
  `(algebraMap (base a (n+1)) D).FiniteType`.
- D_m is etale over Spec A_m minus V(K_m): the next conjunct is precisely
  `AlgebraicGeometry.Etale (morphismRestrict (Spec.map ...) (complement ...))`.
  This is the restricted scheme morphism, not global etaleness or an arbitrary map.
- The specified type of completion identification is
  `Nonempty (AdicCompletion (K_m.map (algebraMap A_m D)) D ≃ₐ[A_m] E_m)`.
  This completes the algebra along the extended ideal K_m D and uses the canonical
  A_m-algebra structures on both sides.
- Fixing any valid C_1 and its map in advance: binders `C₁`, `v₁`, `hfinite₁`,
  `hetale₁`, `hv₁`. The latter asserts an actual completion equivalence e with
  `e (algebraMap C₁ _ x) = v₁ x`. These are exactly the hypotheses that the
  prescribed first model be valid, and they retain the prescribed map, not just
  the underlying ring. The conclusion gives `C 0 = C₁ ∧ HEq (v 0) v₁`, preserving
  both the bundled algebra and the map. HEq handles the dependent source carrier
  without an unspecified isomorphism or hidden cast.
- Chosen algebras C_m, maps v_m and transition maps t_m are the three existential
  families `C`, `v` and `t`. The first universal conjunction states finite type,
  restricted etaleness and an equivalence on completion extending v, at every m.
- t_m is an A-algebra map for m>=2: `t n : C (n+1) →+* C n` is a ring homomorphism,
  and the following equality for every `r : A` asserts that it commutes with the
  composite structure maps A → A_(m+1) → C_(m+1) and A → A_m → C_m. These composite
  actions are the canonical A-algebra actions. Thus this presentation says exactly
  A-linearity, without selecting unrelated extra A-actions on the bundled algebras.
- Actual reduction isomorphism: the next universal clause supplies
  `e : C (n+1) / (a^(n+1)) ≃+* C n` with
  `e (Ideal.Quotient.mk _ x) = t n x` for every x. Here the generator is written
  with its actual image through the base quotient algebra map. Consequently e is
  the quotient map induced by t, and commutes with A by the preceding clause.
- Compatibility with E_m → E_(m-1): the final equality is
  `v n (t n x) = reduction a (n+1) (v (n+1) x)` for every x. `reduction` is the
  canonical factor map, not a freely chosen reduction.
- No etaleness hypothesis or assertion is attached to t. In particular, the
  quotient-isomorphism clause does not silently require such etaleness.

Dependencies read and used:

- `def-weil-pbc-noetherian-ring`:
  `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing` (definition and docstring,
  lines 193–200), exactly all ideals finitely generated.
- `def-weil-pbc-adic-completion`:
  `Mathlib.RingTheory.AdicCompletion.Basic`, `AdicCompletion` (lines 167–175),
  `IsAdicComplete` (lines 39–56). The algebra structure and canonical maps are in
  `Mathlib.RingTheory.AdicCompletion.Algebra`, read at lines 70–150 and 427–440.
  Completeness of E as an A-module along I is equivalent to completeness along IE.
- `def-weil-pbc-finite-type-algebra`:
  `Mathlib.RingTheory.FiniteType`, `RingHom.FiniteType` (lines 210–222), used on
  each algebra's structural map, as the current dependency record requires.
- `def-weil-affine-spectrum`:
  `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec` and `Spec.map`,
  lines 465–490 and underlying prime-spectrum description, lines 533–537.
- `def-weil-etale-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`, lines
  36–46; its signature uses scheme morphisms. I qualified this name explicitly
  because the owning namespace also contains the different `Algebra.Etale`.

Proof-only imports follow the recorded plan: `WeilConjectures.RingTheory.EtaleAlgebraLift`
(the recorded coefficient-lift theorem and its existence companion),
`Sheaf.RingTheory.FormallyEtaleAssociatedGraded` (the recorded power-quotient and
associated-graded theorem), `Mathlib.RingTheory.AdicCompletion.Exactness` (the three
recorded exactness declarations), `Mathlib.RingTheory.AdicCompletion.Completeness`
(the complete-completion and power-kernel declarations), and
`WeilConjectures.AlgebraicGeometry.EtaleInfinitesimalNeighbourhoods` (the recorded
open-etaleness theorem). The Mathlib etale/finite-type imports also provide the
recorded finite-presentation/localization, base-change/finite-limit,
composition/cancellation and finite-type-Noetherian tools. The two proof-only
nodes `lem-per-etale-away-completion-finite-refinement` and
`lem-per-nilpotent-etale-neighbourhood-pushout-lift` currently have neither Lean
records nor Mathlib matches; no nonexistent import is inserted. The theorem's
docstring includes their role and all eight proof steps in full mathematical detail.
They are not needed to type the statement; their imports can be added when stated.

Edge cases checked before writing:

- m=1 is exactly n=0; the prescribed first model is retained with its map.
  m=2 is n=0 for a transition, reducing by a, not by a squared or a to zero.
- a=0 makes all positive base quotients A and all E_m=E. The reduction-isomorphism
  clause becomes an isomorphism C_(m+1) ≃ C_m, as it should.
- a a unit forces E=0 by I-completeness, all A_m=0, and the only base algebras are
  zero. Zero rings are permitted; there is no `Nontrivial` requirement.
- K=0 makes K_m-completion the algebra itself and the complementary open empty.
  The independent-model hypothesis then says each E_m is finite type; the given
  first map is an isomorphism. The desired tower uses the actual quotient reductions.
- K=top makes E=0 and the complement the whole base spectrum. Models may have
  zero completion without being the zero ring. The statement correctly retains
  any prescribed etale finite type first model with its map to zero.
- Nilpotent a and zero A/E are allowed. No characteristic, reducedness, faithful
  algebra action or nonzero ideal hypothesis has been added. The index is always
  the nonempty sequence of positive natural levels.

Searches actually run for this item:

1. `msearch.py ... leanfinder` with query
   `A noetherian adic algebra with etale models modulo powers of an element admits compatible finite type models with quotient transition isomorphisms`:
   eight hits, including `StandardEtalePresentation`, square-zero lifting for
   `StandardEtalePair`, `IsAdicComplete.henselianRing`, smooth lifting into complete
   rings and noetherian descent of etale algebras. None supplies this compatible
   quotient tower or preserves its prescribed first map.
2. `msearch.py ... loogle` with query
   `AdicCompletion, Algebra.FiniteType, Algebra.Etale`: zero hits.
3. `msearch.py ... grep` with query
   `compatible.*[Tt]ower|compatible.*[Mm]odel|rig.?etale`: 15 unrelated hits about
   compatible scalar towers, model theory and manifold local frames, no match.
4. `rg` on `lean/WeilConjectures/RingTheory` and `lean/Sheaf/RingTheory` for
   `EtaleAway|etaleAway|etale_away|completion.*[Ee]quiv|adicCompletion.*[Mm]ap|compatible.*[Mm]odel|Compatible.*[Mm]odel`:
   unrelated compatible module models and completion equivalences, not this claim.
5. `rg` on all `lean/WeilConjectures` and `lean/Sheaf` for the item id,
   `EtaleAway|etaleAway|etale_away|CompatibleModel`: no existing item declaration;
   generic-etale-locus and amplitude-model hits are different statements.
6. Final full-name search on Mathlib and both project source roots for
   `exists_compatible_models|namespace Algebra.CompatibleEtaleModelTower`:
   no pre-existing declaration. Mathlib quotient, scheme-restriction and completion
   sources were then read directly to reuse their exact constructions.

Validation: `scompile.py N7 lem-per-rig-etale-compatible-model-tower <module>`
compiled the sandbox and intended library module, 2.1 seconds each, no errors or
warnings. Earlier errors (scheme restriction used as a method rather than the
namespace function; unqualified `Etale` resolving to the ring notion) were repaired.
All variables and the single universe are explicit and `autoImplicit` is false.

## Second reading by N7

This is the worker's second pass with the node and final module open; the maintainer
performs the independent review after delivery, as specified in this assignment.
No second agent was started. I checked every clause again, especially the n=m-1
index shift, the algebra ideal used in each completion, preservation of `v₁` via
HEq after equality of the source algebras, the A-linearity of the ring homomorphisms
t, the evaluation formula tying each quotient equivalence to t, and use of the
canonical factor map on E. No mathematical mismatch was found and no node fields
apart from `lean` were changed. The two namespace corrections described above were
necessary Lean-interface repairs and changed no mathematical content.
