## Worker report

The module `Sheaf.RingTheory.FlatLocalizedFieldDescent` states the one theorem
`RingHom.flat_localized_field_descent`, with `sorry` as its entire proof. It defines
no new notions and changes only the item's `lean` field. The statement, dependencies,
proof and source of the node are preserved. No statement dispute or correction is needed.

Sources read: Stacks `algebra.tex`, lemma-flat-localization (Tag 00HT),
lemma-local-flat-ff (00HR), lemma-faithfully-flat-universally-injective (05CK), and
`curves.tex`, lemma-nodal (0C4D), arbitrary-field descent paragraph. Also read the
current blueprint ancestor `literature/blueprint/latest/blueprint/sec-trace-formula/
sk-i-curve-zero/lem-trf-local-term-locality.md` and its proof. The inherited node's
source mentions 00HT (1),(2); its proof correctly specializes the localization result
in (6). This is a source-place precision issue only; no field of the node is changed.

The hypotheses and clauses correspond as follows:

- Commutative rings: `{R : Type u} {S : Type v} [CommRing R] [CommRing S]`, with
  independent explicit universes. There are no Noetherian, finite-type or field-extension
  assumptions.
- The flat homomorphism: `(φ : R →+* S) (hφ : φ.Flat)` uses exactly `RingHom.Flat`.
- The maximal ideal downstairs and prime upstairs: `(p : Ideal R) [p.IsMaximal]`
  and `(q : Ideal S) [q.IsPrime]`. Primality of `p` is inferred from maximality.
- Contraction: `(hpq : p = q.comap φ)` is the equality in the node, with its orientation
  reversed to fit Mathlib's map construction.
- The objects A and B are `Localization.AtPrime p` and `Localization.AtPrime q`.
  Their local-ring structures and canonical R-to-A map are Mathlib's existing instances.
- The well-defined canonical fraction map is the actual constructed ring homomorphism
  `Localization.localRingHom p q φ hpq`, not a variable map or a well-definedness
  assumption. Its definition uses `IsLocalization.map` and the contraction equality;
  `Localization.localRingHom_mk'` gives the exact formula `r/s ↦ φ(r)/φ(s)`.
  The well-definedness clause is supplied by using this total constructed ring map.
- Flatness is the first conjunct `(Localization.localRingHom p q φ hpq).Flat`.
- Locality is `IsLocalHom (Localization.localRingHom p q φ hpq)`. On these local
  rings it is equivalent to mapping the maximal ideal into the maximal ideal by
  `IsLocalRing.local_hom_TFAE`. The identification with the extended ideals pA and qB
  is `IsLocalization.AtPrime.map_eq_maximalIdeal`.
- Faithful flatness is the next conjunct using `RingHom.FaithfullyFlat`, the recorded
  ring-map version of the dependency's `Module.FaithfullyFlat`.
- Injectivity is `Function.Injective (Localization.localRingHom p q φ hpq)`.
- The field condition is an implication `IsField (Localization.AtPrime q) → ...`,
  so none of the preceding conclusions requires the target localization to be a field.
- Vanishing pA = 0 is `p.map (algebraMap R (Localization.AtPrime p)) = ⊥`.
- The canonical residue map rho is the explicit ring homomorphism
  `(IsLocalization.AtPrime.equivQuotMaximalIdeal p (Localization.AtPrime p)).symm.
  toRingHom.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime p)))`.
  The quotient map first sends A to A/m_A, and the inverse of Mathlib's canonical
  equivalence then sends this quotient to R/p. Its fraction formula is precisely
  `r̄ * s̄⁻¹`, by `IsLocalization.AtPrime.equivQuotMaximalIdeal_symm_apply_mk`, whose
  full signature and implementation were read. Thus no arbitrary residue map is chosen.
  The conclusion `∃ e : Localization.AtPrime p ≃ₐ[R] R ⧸ p, e.toRingHom = ...`
  says exactly that this particular ring map is an isomorphism of R-algebras. The
  existential occurs inside a proposition and supplies no hollow definition or data.

Statement dependencies used:

- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`
  (definition and signature read), with its `Module.Flat` definition in
  `Mathlib.RingTheory.Flat.Basic` also read.
- `def-weil-pbc-localization-at-prime`: `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  `Localization.AtPrime`, and the canonical `Localization.localRingHom`. The recorded
  `Ideal.ResidueField` and `Ideal.Fiber` declarations were also read; the present node
  needs only the localization and its quotient by the maximal ideal, not a fibre ring.
- `def-weil-pbc-faithfully-flat-ring-map`: the recorded
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, `Module.FaithfullyFlat`, and its recorded
  ring-map form `RingHom.FaithfullyFlat` in `Mathlib.RingTheory.RingHom.FaithfullyFlat`.
  Both defining signatures were read and their modules are public imports.

Proof dependencies read and available for stage 3:

- `lem-weil-pbc-flat-local-ring-maps` is a Mathlib leaf, with
  `RingHom.Flat.localRingHom` and `Localization.isLocalHom_localRingHom` in the public
  modules above.
- `lem-weil-pbc-flat-local-hom-faithfully-flat` is a Mathlib leaf,
  `Module.FaithfullyFlat.of_flat_of_isLocalHom` in
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra` (plain proof import).
- `lem-weil-pbc-faithfully-flat-ideal-contraction` is a Mathlib leaf,
  `Ideal.comap_map_eq_self_of_faithfullyFlat` in the same proof-imported module.
  The docstring follows all four proof steps of the DAG, including the elementary
  fraction argument, without proving anything in Lean.

Edge cases checked before writing: a field with the identity map and p=q=0 gives the
canonical field identification; the flat projection k×k → k at p=0×k gives A=k and
rho the identity after localization. The identity on Z with p=q=(2) has a nonfield
localization and retains all four unconditional conclusions. A nonreduced local
ring with the identity map also retains those conclusions while its field clause is
inactive. Zero rings have no maximal/prime ideals as required here, so those cases
are correctly vacuous. Z → Q with q=0 is excluded by the genuine maximality
hypothesis on p, which is needed to identify the residue quotient. Independent ring
universes are retained, and no test object or index universe can make a hypothesis
vacuous.

Actual searches (all msearch calls used group Q122 and this item's id):

- `msearch.py ... leanfinder "A flat ring map localized at a prime above a maximal
  ideal is flat local faithfully flat and injective and a field target identifies the
  source localization with the residue quotient."` returned eight hits, including
  `instFlatAtPrime`, `RingHom.Flat.localRingHom`, `RingHom.Flat.ofLocalizationPrime`,
  and `Module.FaithfullyFlat.of_flat_of_isLocalHom`; none states the full result.
- `msearch.py ... loogle "RingHom.Flat, IsField"` returned the one hit
  `RingHom.Flat.of_isField`, whose field hypothesis is on the source and which does
  not state this node.
- `msearch.py ... grep "localRingHom|quotient.*[Ll]ift|algebraMap.*[Qq]uotient|
  toResidueField" RingTheory/Localization` returned nine hits, including the canonical
  `localRingHom` definition and fraction lemmas and quotient extension material.
- `msearch.py ... leansearch "A flat local ring homomorphism into a field makes the
  source its residue field and the canonical residue map an isomorphism."` returned
  eight hits on `IsLocalRing.residue`, its surjectivity and locality, and residue-field
  maps. None proves this flat-localized-field assertion.
- `grep -rn "lem-trf-flat-localized-field-descent" lean/WeilConjectures` and the
  equivalent full-root `rg` over `lean/Sheaf` and `lean/WeilConjectures` found no
  existing declaration tagged with this item.
- `rg -n` on `localRingHom`, `equivQuotMaximalIdeal`, field/descent variants and
  residue/equivalence variants in the project's RingTheory directories located
  unrelated localization, completion and henselization results, and existing canonical
  constructions. The final full-root search for `flat_localized_field_descent|
  flatLocalizedFieldDescent|flat.*[Ll]ocalized.*[Ff]ield|[Ff]lat.*[Rr]esidue.*[Ii]somorphism`
  in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found
  only the distinct localized-field-extension faithful-flatness and etale-completion
  material, not this statement. The new declaration name is unused.
- Direct Mathlib `rg` and reads in `RingTheory/Localization/AtPrime/Basic.lean`
  found `IsLocalization.AtPrime.equivQuotMaximalIdeal` and its inverse's fraction
  computation. These supply the canonical rho without an additional definition node.

Validation: the prescribed `scompile.py Q122 lem-trf-flat-localized-field-descent`
compiled the module on the live server, with no errors or warnings (sandbox 8.3 s,
library 2.7 s). `autoImplicit` is false; every universe and binder is explicit;
all lines are at most 100 characters. Dry-run and final-delivery results follow below.

The required `deliver2.py Q122 lem-trf-flat-localized-field-descent --no-push`
returned `OK (dry run)` at commit `ce0bd4e9d6f`: preflight and per-file compilation
passed. A final comparison with the read-only node confirmed `lean` is the only
changed field. This worker delivers directly under the dispatcher's instructions;
the maintainer's independent review supplies the second reading.

## Second reading by Q122

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
