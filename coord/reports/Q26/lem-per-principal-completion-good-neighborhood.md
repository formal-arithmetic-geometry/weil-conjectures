## Worker report

The delivery states `exists_goodNeighborhood_of_principalCompletion` in
`Sheaf.RingTheory.PrincipalCompletionGoodNeighborhood`. Its sole proof is `sorry`.
There are no definitions, additional assumptions, new nodes, dependency repairs, or
statement corrections. The item JSON changes only in `lean`.

Source read: Temkin, *Desingularization of quasi-excellent schemes in characteristic zero*,
https://math.huji.ac.il/~temkin/papers/Excellent_Desingularization.pdf,
Corollary 3.1.5(ii) and the following reducedness comparison (printed p.18), and the
shrinking in the proof of Theorem 3.4.1 (printed p.22). These compare the formal properties
with a neighborhood of the closed fibre. The node's finite-kernel argument additionally
handles injectivity of the chosen parameter. The docstring transcribes all seven DAG proof
steps, including the finite-defect ideals, saturated singular ideal, flat local descent,
nilpotence, fraction calculations, and geometric-series quotient inverses.

Hypotheses and objects, matched individually:

- The commutative ring `C` is `(C : Type u) [CommRing C]`; `u` is explicit and arbitrary.
- Quasi-excellence is `hC : IsQuasiExcellent C`, the recorded definition, not excellence
  or merely Noetherianity. Its definition includes Noetherianity, the G-ring condition,
  and J-2 for finite-type algebras.
- The distinguished element is `(t : C)`; it is not assumed nonzero or a nonunit in `C`.
- `B` is the actual type `AdicCompletion (Ideal.span {t}) C`, not an arbitrary complete
  ring or an algebra with a chosen comparison. Its canonical map is
  `algebraMap C (AdicCompletion (Ideal.span {t}) C)`, definitionally `AdicCompletion.of`.
- Reducedness of `B` is `hred : IsReduced (AdicCompletion (Ideal.span {t}) C)`.
  Mathlib's no-nonzero-nilpotents condition is precisely the node's positive-power test;
  the exponent-zero case in `IsNilpotent` only adds the already valid zero-ring case.
- Injectivity of multiplication by the image of `t` is `ht : Function.Injective
  (fun b : AdicCompletion (Ideal.span {t}) C ↦ algebraMap C _ t * b)`.
- Regularity of `B[1/t]` is `hreg : IsRegularRing (Localization.Away
  (algebraMap C (AdicCompletion (Ideal.span {t}) C) t))`. `IsRegularRing` includes
  Noetherianity and regular local rings at every prime, exactly the ring clause of
  `def-weil-regular-scheme`.

Conclusions, matched individually:

- The output element is `∃ g : C` and membership in `1+tC` is the exact principal-ideal
  expression `∃ c : C, g = 1 + t * c`.
- `A=C_g` is always the concrete `Localization.Away g`, namely localization at powers
  of `g`; there is no unconstrained output ring or map.
- Reducedness is `IsReduced (Localization.Away g)`.
- Injectivity of multiplication by `t` on `A` is the displayed `Function.Injective`
  on `fun a : Localization.Away g ↦ algebraMap C (Localization.Away g) t * a`.
- Punctured regularity is `IsRegularRing (Localization.Away
  (algebraMap C (Localization.Away g) t))`, the iterated localization `A[1/t]`.
- The completion identification is the existential ring equivalence `E` from
  `AdicCompletion (Ideal.span {t}) C` to the completion of `Localization.Away g`
  at `Ideal.span {algebraMap C (Localization.Away g) t}`.
- The first identity for `E` says it extends the localization map on **every** element
  `c : C`. Taking `c=t` states preservation of the distinguished generator.
- For **every** `n : ℕ` with `0 < n`, the equivalence `e` identifies `C/(t)^n` with
  `C_g/(t)^n`; its identity on `Ideal.Quotient.mk ... c` specifies precisely the map
  induced by localization. Since quotient representatives are surjective, `e` is
  uniquely specified, not an arbitrary quotient equivalence.
- The final identity `evalₐ ... n (E b) = e (evalₐ ... n b)` holds for every completed
  element `b`. Thus `E` is the coordinatewise canonical completion map. Equality of
  all positive coordinates determines a completed element (coordinate zero has zero
  quotient), so this characterizes the canonical map, beyond merely agreeing on `C`.
  The same identities express preservation of every positive-power quotient. The
  standard `adic-completion-mod-power` theorem identifies these finite quotients with
  the corresponding quotients of the completed rings, as explained in proof step 7.

Recorded statement dependencies read and used:

- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`; read the full definition and
  docstring (also read its recorded main `IsExcellent` and auxiliary declarations).
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  `AdicCompletion.of`, the ring and algebra instances, and `AdicCompletion.evalₐ`.
  The ring structures and canonical maps are those of the recorded completion node.
- `Sheaf.AlgebraicGeometry.IsRegularScheme` is publicly imported as recorded.
  Its node's ring clause uses Mathlib `IsRegularRing` and `IsRegularLocalRing` in
  `Mathlib.RingTheory.RegularLocalRing.Defs`; both signatures and definitions were read.
  This item concerns rings, so its scheme predicate is not substituted for ring regularity.
- Localizations use Mathlib `Localization.Away`, and quotients use
  `Ideal.Quotient.mk`; neither notion is redefined.

All stated proof dependencies are imported: the completion Noetherian theorem and flat
regularity descent use their `WeilConjectures.RingTheory` modules; completion exactness,
tensor description, completeness/mod-power, flatness, Nakayama, Noetherian localization,
and affine quasi-separatedness use their recorded Mathlib modules; the quasi-coherent
algebra and coherent-module nodes use their recorded `Sheaf.AlgebraicGeometry` modules.
For `lemma-nagata-finite-type-nil-ideal-nilpotent`, whose node has no Lean binding yet,
source grep found the already published
`AlgebraicGeometry.Scheme.IdealSheafData.exists_pow_eq_bot_of_support_eq_top` in
`WeilConjectures.Compactification.BoundarySeparationData`; that module is also imported.
No unstated dependency needs a definition to type this statement.

Edge cases checked mathematically:

- No `Nontrivial C` or `Nontrivial B` excludes the zero ring or zero completion.
- If `t` is a unit, the completion and punctured completion are zero; `g=0` is allowed
  in `1+tC`, and the zero localization gives the required neighborhood of the empty fibre.
- If `t=0`, completion is `C` and injectivity of zero multiplication forces `C=0`.
  The stated result remains valid. Nilpotent `t` is also allowed.
- For `C=k[x]`, `t=x`, all expected properties hold already with `g=1`.
- For `C=k[x] × k[ε]/(ε²)`, `t=(x,1)`, the completion forgets the bad second component.
  The statement does not falsely conclude `C` reduced: it permits `g=(1,0)`, removing
  that component. This tests the need for actual shrinking and permits zero divisors.
- The finite-quotient index includes every positive exponent, particularly `n=1`.
  There is no independent smaller ring universe or dimension bound.

Searches actually run:

1. `msearch.py ... leanfinder` with query
   `A quasi excellent ring whose principal adic completion is reduced and t torsion free and regular after inverting t has the same properties after localization at some g in 1+tC`.
   Result: 8 hits, concerning smooth localization maps, reducedness under localization,
   and locality of reducedness (`isReduced_localizationPreserves`,
   `isReduced_ofLocalizationMaximal`, and standard-smooth permanence); no completion
   detection or simultaneous shrinking theorem.
2. `msearch.py ... loogle 'AdicCompletion, IsReduced, IsRegularRing'`:
   successful query, 0 hits.
3. `msearch.py ... grep
   'completion.*regular|completion.*reduced|goodNeighborhood|good_neighborhood' RingTheory`:
   successful query, 0 hits.
4. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for completion, regularity,
   localizations, and canonical adic maps found the reusable declarations listed above.
   A dedicated search for the item id and
   `goodNeighborhood|good_neighborhood|principalCompletion|principal_completion`
   found no existing statement of this result. A further exact-name search in
   `dag/lean_names_upstream.json`, both project roots, and Mathlib found no collision
   with `exists_goodNeighborhood_of_principalCompletion`.
5. Read the recorded completion, regularity, quasi-excellence, flat descent, coherent
   module, quasi-coherent algebra, and nilpotent-ideal declarations in full rather than
   relying on their names. The requested old compact-object example is withdrawn;
   its node now points to `WeilConjectures.CategoryTheory.CompactObject`.

There is no `STATEMENT-DISPUTED` or node fault. The final signature is copied verbatim
into `lean.statement`, with explicit universes and `autoImplicit false`.

## Second reading by Q26

This is the author's separate second pass; no other agent was started, in accordance
with the dispatcher brief. The maintainer supplies the independent review.

With the node and final module open, checked each of the three assumptions on `B`
against `hred`, `ht`, and `hreg`; checked `C` is quasi-excellent, not excellent; checked
all four output clauses on `g` and `A`; and checked that the completion on the right uses
**the image of the original `t`**, not `g` or an arbitrary ideal. The base-element and
finite-quotient equations fully pin down the canonical comparison and the parameter.
The finite quotients are indexed by all positive `n` and use ideal powers on both sides.
All objects are concrete Mathlib constructions. There are no hidden `let` binders,
local instances, local notation, private notions, or extra hypotheses. No mathematical
mismatch was found. This pass added the published BoundarySeparationData proof import
when a source search found the nilpotent-ideal theorem despite its missing node record.

Validation: the module compiled using the prescribed `scompile.py` on the server;
final import-set compilation and delivery preflight are recorded below when complete.

Final validation: both the sandbox form and the named library module compiled cleanly
with `scompile.py` (final runs: 1.9 s and 1.8 s). The prescribed
`deliver2.py Q26 lem-per-principal-completion-good-neighborhood --no-push` passed:
`OK (dry run): commit 0ecf6fd3c8a passes the preflight and compiles; nothing pushed`.
