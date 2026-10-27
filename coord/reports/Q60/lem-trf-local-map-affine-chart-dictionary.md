## Worker report

The module `Sheaf.TraceFormula.LocalMapAffineChartDictionary` states
`AlgebraicGeometry.LocalMapAffineChart.exists_dictionary`, with its sole theorem
proof `sorry`. The node's statement, statement dependencies, proof and proof
dependencies are unchanged. No new or dependency node is needed.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 0CAU,
`lemma-map-approximation`, including the affine reduction and the final passage
back to spectra; `more-algebra.tex`, Tag 07PV,
`proposition-finite-type-over-G-ring`, including its first localization argument.
In particular only the stalk of S is assumed a G-ring: the theorem does not
incorrectly assume that the whole affine base ring R is a G-ring.

Hypotheses and conclusion, clause by clause:

- The schemes and structure maps are `{S X Y : Scheme.{u}}`, `f : X ⟶ S`,
  `g : Y ⟶ S`. The assumptions are `[IsLocallyNoetherian S]`,
  `[LocallyOfFiniteType f]`, `[LocallyOfFiniteType g]`, points `x`, `y`, `s`,
  and `hx : f x = s`, `hy : g y = s`. The only G-ring assumption is
  `hG : IsGRing (S.presheaf.stalk s)`.
- The affine open neighbourhoods are represented by `R A B : CommRingCat.{u}`
  and open immersions `iR : Spec R ⟶ S`, `iA : Spec A ⟶ X`,
  `iB : Spec B ⟶ Y`. Their images are the required open subsets, and each
  map identifies its affine source with its image. Points `r`, `p`, `q`
  and equalities `hr`, `hp`, `hq` assert that these images contain s, x, y.
  This presentation is the same chart data as named affine open subsets;
  it does not require arbitrary chosen charts or any additional hypothesis.
- The ring maps are `a : R ⟶ A` and `b : R ⟶ B`. The equations
  `iA ≫ f = Spec.map a ≫ iR` and `iB ≫ g = Spec.map b ≫ iR` express
  both structure maps landing in the base chart and their specified maps
  of coordinate rings.
- Noetherianity is the conjunction `IsNoetherianRing R ∧ IsNoetherianRing A ∧
  IsNoetherianRing B`. Finite generation as R-algebras is
  `a.hom.FiniteType ∧ b.hom.FiniteType`, i.e. the usual algebra structures
  supplied by the two ring maps, without existential unrelated algebra actions.
- The presentation clause is `∃ n m F π`, where
  `F : Fin m → polynomialRing R n`, the map π to B is surjective,
  `RingHom.ker π = Ideal.span (Set.range F)`, and
  `π.comp (coefficientMap R n) = b.hom`. This says precisely that B is the
  displayed quotient as an R-algebra. `polynomialRing` repeatedly applies
  the existing single-variable `Polynomial` constructor; its zero case is R.
  `coefficientMap` is the repeated `Polynomial.C` inclusion. These are
  fully defined coordinate helpers for the iterated convention of the node.
- The prime-contraction equations are `ha : r.asIdeal = p.asIdeal.comap a.hom`
  and `hb : r.asIdeal = q.asIdeal.comap b.hom`.
- The three canonical local-ring identifications are `stalkEquiv iR r s hr`,
  `stalkEquiv iA p x hp`, and `stalkEquiv iB q y hq`. This helper is a real
  composite of the inverse equality transport, the open immersion's stalk
  isomorphism, and `Spec.stalkIso`; it is not an arbitrary isomorphism.
  The two displayed equalities of ring homomorphisms identify the transported
  structure stalk maps with `Localization.localRingHom` of a and b.
  The helper `stalkMapAt` only makes point-equality transport explicit.
- The local G-ring conclusion is `IsGRing (Localization.AtPrime p.asIdeal)`.
- The theorem universally quantifies `A'`, `h : A ⟶ A'`, the hypothesis
  `h.hom.Etale`, `p' : PrimeSpectrum A'`, and the contraction equation `hh`.
  It then concludes `IsNoetherianRing A'` before introducing φ.
- The scheme U is literally `Spec A'`. The map p_U is the explicit composite
  `Spec.map h ≫ iA`; its point equality `hpx`, its `Etale` property and the
  residue-field assertion are outside the quantifier over φ, so none can
  become vacuous when there are no such φ.
- For every `φ : B ⟶ A'`, the R-algebra condition is exactly
  `φ.hom.comp b.hom = h.hom.comp a.hom`, and `hφ` is its prime-contraction
  condition. The map f_U is literally `Spec.map φ ≫ iB`.
  Its point equality is `hpy`; equality of the two composites to S expresses
  that f_U is over S with the structure on U induced by p_U.
- The residue-field hypothesis is bijectivity of the canonical field map
  `Ideal.ResidueField.map p.asIdeal p'.asIdeal h.hom hh`, which is exactly
  its being an isomorphism. The conclusion is
  `IsIso ((Spec.map h ≫ iA).residueFieldMap p')`; its source is κ(p_U(p')),
  canonically κ(x) by hpx, and its target is κ_U(p').
- The canonical U stalk identification is
  `(Spec.stalkIso A' p').commRingCatIsoToRingEquiv`. The next two equalities
  identify the actual transported stalk maps with
  `Localization.localRingHom p.asIdeal p'.asIdeal h.hom hh` and
  `Localization.localRingHom q.asIdeal p'.asIdeal φ.hom hφ`, respectively.
- `CompletionDictionary` expands to three completion equivalences EA, EB, EC
  and the four induced completed ring maps F, G, F₀, G₀.
  `HasCompletionCoordinates` is exactly the coordinate formula of the recorded
  `RingHom.exists_adicCompletion_map_of_local`: for every n ≥ 0, a class
  represented by a maps to the class represented by the original ring map of a.
  Thus all seven maps are specified at every quotient, not arbitrary maps
  merely commuting with the completion inclusions. Completion equivalences
  also satisfy the completion-map normalization in `IsCompletionIdentification`.
  The four further restriction equations express compatibility of each of
  F, G, F₀, G₀ with its source and target completion maps. The two square
  equalities `EC.toRingHom.comp F = F₀.comp EA.toRingHom` and its G analogue
  are the asserted agreement of induced maps under the identifications.
- The final `∀ N : ℕ, 1 ≤ N → ...` identifies the extended N-th power of
  the U stalk maximal ideal with the corresponding ideal of the localized
  coordinate ring completion, via EC. For `C₀ = Localization.AtPrime p'.asIdeal`,
  `IsLocalRing.maximalIdeal C₀` is exactly p'A'_{p'}, by
  `Localization.AtPrime.map_eq_maximalIdeal` from the recorded localization
  dependency. Mapping `(maximalIdeal C)^N` along `algebraMap C (Completion C)`
  is the extended ideal denoted m^N times the completion in the node.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian` (all affine sections Noetherian).
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, its `finiteType_appLE` characterization.
- `def-weil-pbc-g-ring`: `WeilConjectures.RingTheory.GRing`, `IsGRing`;
  the Noetherian condition and regularity at every prime localization are retained.
- `def-weil-affine-spectrum`: the `Spec` and `Spec.map` declarations above.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, the abbreviation for `IsNoetherian R R`.
- `def-weil-polynomial-ring`: `Mathlib.Algebra.Polynomial.Basic`, `Polynomial`,
  used recursively, not replaced by an unrelated polynomial object.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`,
  `Localization.localRingHom`; `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`,
  `Ideal.ResidueField`, `Ideal.ResidueField.map`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale` (and its public ring-map criterion).
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.residueField`, `Scheme.Hom.residueFieldMap`.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion`; its algebra structure, evaluations and completion map are
  provided by `Mathlib.RingTheory.AdicCompletion.Algebra`, publicly imported
  through the recorded G-ring and completion-map modules.
- `lem-weil-pbc-fs-adic-completion-map-local`:
  `WeilConjectures.RingTheory.CompletionMapForLocalHom`,
  `RingHom.exists_adicCompletion_map_of_local`; its complete coordinate
  characterization is used verbatim in `HasCompletionCoordinates`.

The remaining proof modules are plain imports, as required for stage 2:
`Mathlib.RingTheory.FinitePresentation`, `Mathlib.RingTheory.Localization.Submodule`,
`WeilConjectures.RingTheory.GRingEquiv`, `FiniteTypeGRing`,
`AdicCompletionRingEquiv`, and `RegularRingEquiv`. Mathlib affine-open, etale,
finite-type and Noetherian facts used by the proof plan are already exposed by
statement imports. Each of the node's nine proof steps is included in the
main theorem's docstring. No proof-only dependency module was omitted for a cycle.

All helper declarations belong to this node's chart-coordinate dictionary.
`Completion` abbreviates the recorded AdicCompletion, and the remaining helpers
are explicit formulas/compositions for this statement; they introduce no
independent ring, scheme, or completion notion requiring a new definition node.
There is no choice from an unproved existence theorem, no hollow data, no new
axiom, and no additional postponed theorem besides `exists_dictionary`.

Edge cases checked before writing and again after elaboration:

- n = 0 gives R itself and identity coefficient inclusion; m = 0 makes
  `Fin m` empty and its relation ideal zero. Neither finite number is required
  to be positive.
- x, y and s can be nonclosed points; all prime localizations are at primes,
  with no maximality hypothesis on those primes in their coordinate rings.
- The charts are neighbourhoods only; X and Y need not be quasi-compact,
  separated, globally affine or globally of finite type.
- Only O_{S,s} is a G-ring, including the case that the chosen R is not one.
- N = 1 is included in the ideal-power clause. Completion coordinates include
  n = 0 and every higher quotient level, with no completeness assumption.
- Rings with zero divisors and arbitrary characteristic are admitted. The
  zero ring cannot be a chart containing a marked prime, and the empty scheme
  supplies no x or y: these are correctly vacuous, not excluded by extra binders.
- No φ with the required contraction need exist. Noetherianity of A' and the
  p_U point, etaleness and residue claims still hold outside its quantifier.
- Universes and all term variables are explicitly bound; `autoImplicit` and
  `relaxedAutoImplicit` are disabled. All schemes/rings in a chart use the
  same arbitrary universe u, as in the recorded scheme APIs.

Searches actually run:

1. `msearch.py ... leanfinder "Affine charts of locally finite type schemes over
   locally Noetherian schemes and localization stalk maps agree with completion maps"`:
   eight hits, including `IsAffineOpen.isLocalization_stalk`, `fromSpecStalk_eq`
   and `appLE_eq_away_map`; none gives the whole chart dictionary.
2. `msearch.py ... loogle "AlgebraicGeometry.Scheme.Hom.stalkMap,
   AlgebraicGeometry.IsAffineOpen"`: four hits, including
   `IsAffineOpen.arrowStalkMapIso`, `stalkMap_injective`; these provide local
   ingredients but not the node's existence, presentation and completion claims.
3. `msearch.py ... grep "localRingHom_comp_stalkIso|stalkMapSpecIso|stalkIso"
   AlgebraicGeometry`: 25 hits, including Mathlib affine/spectrum stalk
   comparisons. The full declarations of `Spec.stalkIso`,
   `Scheme.localRingHom_comp_stalkIso`, `IsAffineOpen.arrowStalkMapIso` and
   the affine-open localization theorem were opened and read.
4. `rg -n 'lem-trf-local-map-affine-chart-dictionary|localMapAffine|
   affineChartDictionary|iteratedPolynomial|IteratedPolynomial'` in both
   `lean/WeilConjectures` and `lean/Sheaf`: no existing node declaration or
   matching dictionary. The separately required
   `grep -rn 'lem-trf-local-map-affine-chart-dictionary' lean/WeilConjectures`
   also returned no hits.
5. Further rg searches for iterated polynomials in Mathlib, WeilConjectures
   and Sheaf found unrelated iterated-derivative and affine-line results,
   not a repeated single-variable polynomial ring used here. Stalk and
   completion-map searches found the existing Mathlib maps used above and
   `localMapCompletionMap` in the downstream
   `Sheaf.TraceFormula.LocalMapCompletionApproximation`; this module is not
   imported back upstream. No duplicate completion-map construction was made:
   the theorem characterizes the existential induced maps at every coordinate.

No statement fault or STATEMENT-DISPUTED issue was found.

Validation: prescribed `scompile.py Q60 lem-trf-local-map-affine-chart-dictionary`
compiled the delivered file both as a sandbox module and at its library path,
cleanly, approximately three seconds each. No global build or direct compiler
invocation was used. All writes are confined to the assigned sandbox.

## Second reading by Q60

A separate final reading of the node and elaborated file was performed in this
worker session. The dispatcher explicitly prohibits starting other agents; this
is a self-check, not a claim of independent review. The delivery goes to the
maintainer's independent review as specified in the assignment.

The second pass checked all clauses against the binders and the expansion of
`CompletionDictionary`. One issue was corrected: p_U's point, etaleness and
residue assertion initially occurred inside the universal φ clause; they now
precede it, retaining their content even if no φ exists. Recompilation was clean.
The field-map assumption is bijectivity of the actual induced map, not abstract
isomorphism of the two residue fields. The stalk equivalences are the canonical
Mathlib composites, not arbitrary equivalences. All completion arrows have the
coordinate formula at every level in addition to their inclusion compatibility;
therefore the completion square does not silently substitute arbitrary
extensions of maps on the original local rings. The final ideal equality is for
extended powers, with every N ≥ 1, and p'A'_{p'} is the localization's maximal
ideal. The finite presentation has the actual R coefficient map and includes
zero variables and zero relations. No other mismatch was found.
