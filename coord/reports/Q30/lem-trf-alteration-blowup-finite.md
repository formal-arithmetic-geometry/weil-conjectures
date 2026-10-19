## Worker report

The module `Sheaf.Paper.AlterationBlowupFinite` states
`AlgebraicGeometry.Orgogozo.exists_blowup_finite_surjective`. It introduces no new
construction: the target center is an ideal sheaf `I : Z.IdealSheafData`, its closed
subscheme is `I.subscheme` with closed immersion `I.subschemeι`, and its blow-up is the
canonical `I.blowup` with map `I.blowupMap`. The source blow-up is similarly the canonical
`J.blowup` for `J : W.IdealSheafData`, with map `J.blowupMap`.

The hypotheses and clauses render as follows.

* `{W Z : Scheme.{u}}` gives the source and target schemes in one universe.
* `[IsIntegral W] [IsIntegral Z]` and `[IsReduced W] [IsReduced Z]` state that both schemes
  are integral and reduced, as in the node. `[IsNoetherian W] [IsNoetherian Z]` states the
  Noetherian hypotheses.
* `(a : W ⟶ Z) (ha : IsAlteration a)` is the alteration hypothesis, using the recorded
  `AlgebraicGeometry.Orgogozo.IsAlteration` definition. It includes properness, surjectivity,
  finiteness on a dense open, and domination of irreducible components.
* `∃ I : Z.IdealSheafData` supplies the closed center. `IsNowhereDense (I.support : Set Z)`
  says its underlying closed set is nowhere dense; `IsClosedImmersion I.subschemeι` renders
  `R ↪ Z` with the canonical associated closed subscheme. `IsModification I.blowupMap`
  says the target blow-up is a modification.
* `∃ J : W.IdealSheafData` and `IsModification J.blowupMap` say that the source refinement
  is itself a blow-up modification of `W`.
* `∃ p : J.blowup ⟶ I.blowup` gives the finite map between the two blow-ups.
  `IsFinite p` and `Surjective p` render “finite surjective”, and
  `J.blowupMap ≫ a = p ≫ I.blowupMap` is exactly the required compatibility over `Z`.

The theorem proof is `sorry`, as required at stage 2. Its docstring records the source proof:
choose a dense affine locus where the alteration is finite flat and locally finitely presented,
apply the finite-after-admissible-blow-up theorem, use properness and density to obtain
surjectivity, and identify the strict transform with the blow-up of the extended center on the
source. The edge cases checked were the identity alteration (unit center), a finite map such as
`t ↦ t^2`, a blow-up of `A^2` at the origin, empty or zero-dimensional schemes, and the empty
center. The statement does not add a nonemptiness hypothesis; all such choices are conclusions
of `IsAlteration` and the source theorem.

Recorded dependency declarations used:

* `def-trf-orgogozo-induction-data` — `Sheaf.Paper.OrgogozoInductionData`,
  `AlgebraicGeometry.Orgogozo.IsAlteration` (and `IsModification`).
* `def-nagata-global-blowup` — `WeilConjectures.Blowup.Gluing`,
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup` and `blowupMap`.
* `def-weil-closed-immersion` — Mathlib,
  `AlgebraicGeometry.IsClosedImmersion` and the canonical `IdealSheafData.subschemeι`.
* `def-weil-finite-integral-morphism` — Mathlib,
  `AlgebraicGeometry.IsFinite` (the integral predicate is not needed in the signature).

The module also imports the canonical admissible-blow-up and strict-transform APIs used by the
proof route (`WeilConjectures.Blowup.AdmissibleBlowup` and
`WeilConjectures.Compactification.StrictTransform`); no private copy or local notation is used.

Searches made:

* `msearch.py ... leanfinder "blowup refinement of an alteration finite surjective morphism
  integral reduced Noetherian schemes"`: generic normalization and integral-morphism hits only;
  no alteration/blow-up theorem.
* `rg -n 'exists_finite_surjective_refinement|alteration-blowup-finite|Blowup refinement'
  lean/Sheaf /home/ubuntu/weil-src-slopmaster2/WeilConjectures`: found the stronger general
  `exists_finite_surjective_refinement` statement, but it gives arbitrary modifications rather
  than the required blow-up modifications, so it is not a duplicate.
* `rg` over Mathlib and the source for `strictTransform`, `blowup`, and finite-surjective
  alteration results: found only the canonical blow-up, admissible blow-up, and strict-transform
  infrastructure; no exact statement.
* `msearch.py ... loogle "AlgebraicGeometry.IsFinite,
  AlgebraicGeometry.Scheme.IdealSheafData.blowup, strictTransform"`: no hits (Loogle was under
  load for the related query); this does not supply an existing match.
* `msearch.py ... grep "strictTransform|finite-after-blowing-up|IsFinite.*IsProper"`: no
  matching alteration theorem in Mathlib AlgebraicGeometry.

No `STATEMENT-DISPUTED` issue or node correction was found. No new dependency node was needed.

## Second reading by Q30

Independent reading by the maintainer's reviewer (the worker delivered directly; this section
replaces the placeholder). Node `dag/nodes/sec-trace-formula/lem-trf-alteration-blowup-finite.json`
and `lean/Sheaf/Paper/AlterationBlowupFinite.lean` read side by side; the node is unchanged by the
delivery except for its `lean` record, and `lean.statement` occurs verbatim in the file.

Node statement as a list, with its Lean and verdict:

1. Schemes `W`, `Z` (no universe in the node) — `{W Z : Scheme.{u}}`, one universe, as a morphism
   requires. OK.
2. Integral, reduced, Noetherian — `[IsIntegral W] [IsIntegral Z] [IsReduced W] [IsReduced Z]
   [IsNoetherian W] [IsNoetherian Z]`; `IsReduced` is implied by `IsIntegral`, so nothing stronger.
   These supply the `[IsReduced] [IsLocallyNoetherian] [CompactSpace]` instances that
   `Orgogozo.IsModification` needs on `Z` and `W`. OK.
3. An alteration `a : W → Z` [def-trf-orgogozo-induction-data] — `(a : W ⟶ Z) (ha : IsAlteration a)`,
   the recorded declaration (proper, surjective, finite over a dense open, components dominate). OK.
4. A nowhere dense closed subscheme `R ↪ Z` — `∃ I : Z.IdealSheafData`, `IsNowhereDense
   (I.support : Set Z)`; `R = I.subscheme` (closed subschemes correspond to ideal sheaves);
   `IsClosedImmersion I.subschemeι` is a redundant (instance-true) restatement of `R ↪ Z`. OK.
5. The blowup `Bl_R(Z) → Z` [def-nagata-global-blowup] — `I.blowup`, `I.blowupMap`, the recorded
   declaration. The extra clause `IsModification I.blowupMap` is not in the node's sentence but is
   implied by clauses 2 and 4 (proper by `isProper_blowupMap_of_isLocallyNoetherian`; isomorphism over
   the dense open `Z \ V(I)`; its inverse image is the complement of the effective Cartier
   exceptional divisor, hence dense), it is argued in the node's proof (steps 2–3) and the docstring,
   and it is what the citer lem-trf-modification-closed-image-lifting needs. Not a strengthening in
   substance. OK.
6. A blowup modification `W~ → W` — `∃ J : W.IdealSheafData, IsModification J.blowupMap`. OK.
7. A finite surjective `W~ → Z~` [def-weil-finite-integral-morphism] — `∃ p : J.blowup ⟶ I.blowup,
   IsFinite p ∧ Surjective p` (`Surjective` resolves to `AlgebraicGeometry.Surjective`, checked with
   `#check`). OK.
8. Over `Z`: `W~ → W → Z` equals `W~ → Z~ → Z` — `J.blowupMap ≫ a = p ≫ I.blowupMap`. OK.
   Quantifier order: `I`, then `J`, then `p`, as in the node.

Edge cases: integral schemes are nonempty, so no empty case arises; the identity alteration (unit
ideals, `Bl = id`, `p` the identity up to the canonical isomorphism); a finite alteration such as
`t ↦ t²` (unit centre on `Z`); `Bl_0 A² → A²` (centre the origin, nowhere dense). No universe or
variable is left unbound (`#check` shows the elaborated statement).

Searches: `rg exists_finite_surjective_refinement|blowup_finite|IsAlteration` over the side
`lean/Sheaf` tree: `Orgogozo.exists_finite_surjective_refinement`
(lem-trf-alteration-finite-refinement) gives arbitrary modifications, not blowups with nowhere
dense centre, so it is not a duplicate; no Mathlib match (as recorded).

Change made: the module docstring said the source blow-up is "represented by the strict transform";
the statement quantifies over a blow-up `J.blowup`, and the docstring now says so (the strict
transform is the proof's witness). No change to the statement. Fresh per-file compile with
`nt_compile.py`: clean, only the `sorry` of the statement.
