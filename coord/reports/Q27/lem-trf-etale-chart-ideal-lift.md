## Worker report

The module `Sheaf.RingTheory.EtaleChartIdealLift` states
`Algebra.exists_etale_chart_ideal_lift`, with one `sorry` and no new definitions.
The node's statement, dependency lists, and proof are unchanged. There are no new
nodes, dependency repairs, disputed statements, or mathematical node faults.

Source read: `literature/stacks-project/flat.tex`, Tag 0813,
`lemma-push-ideal`, especially the proof's standard-etale replacement,
`C = A[x]/(f)`, numerator generators, adjoining `a^m`, and annihilation.
The larger Stacks lemma assumes that `a` is a nonzerodivisor for later uses;
the chart-and-ideal-lift argument isolated in this node does not use that
hypothesis. No such hypothesis is added here.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Commutative rings and their homomorphism: `{A B : Type u}` with
  `[CommRing A] [CommRing B] [Algebra A B]`; the map is `algebraMap A B`.
  The universe `u` is an arbitrary common ambient universe, as required to
  form both spectra and their morphism in Mathlib's category of schemes.
- The given map of spectra is etale: `hEtale : AlgebraicGeometry.Etale
  (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B)))`.
- A prime ideal of `B`: `(q : Ideal B) [q.IsPrime]`.
- The scalar and positive integer: `(a : A) (m : ℕ) (hm : 1 ≤ m)`.
  Natural numbers with this bound encode exactly integers at least one.
- The finite generator list: `(r : ℕ) (j : Fin r → B)`.
- Its generated ideal: `(J : Ideal B)` and
  `hJ : Ideal.span (Set.range j) = J`.
- The prescribed power belongs to it:
  `ha : algebraMap A B a ^ m ∈ J`.
- The neighborhood: `∃ g : B, g ∉ q ∧ ...`.
- The monic polynomial: `∃ f : Polynomial A, f.Monic ∧ ...`.
- The quotient `C = A[T]/(f)` is Mathlib's `AdjoinRoot f`, whose definition
  is literally `Polynomial A ⧸ Ideal.span {f}`. No new quotient notion is used.
- The localizing element and A-algebra isomorphism are
  `∃ (h : AdjoinRoot f)
  (θ : Localization.Away g ≃ₐ[A] Localization.Away h), ...`.
- Etaleness of `Spec C_h → Spec A` is the first conjunction, using
  `AlgebraicGeometry.Etale` on the spectrum map of its structural algebra map.
- The specified basis is an existential
  `b : Module.Basis (Fin f.natDegree) A (AdjoinRoot f)` with
  `∀ i, b i = AdjoinRoot.root f ^ (i : ℕ)`. Thus the family is the actual
  powers `1,t,...,t^(d-1)`, not just abstract freeness. `f.natDegree` is `d`.
- Numerators and nonnegative exponents are
  `c : Fin r → AdjoinRoot f` and `e : Fin r → ℕ`.
  For each index, the formula equates `θ(j_i/1)` with
  `IsLocalization.mk' (M := Submonoid.powers h) (Localization.Away h)
  (c i) ⟨h ^ e i, ⟨e i, rfl⟩⟩`, exactly `c_i/h^(e_i)`.
- `K` is named by existential quantification and the defining equality
  `K = Ideal.span (Set.range c ∪ {algebraMap A (AdjoinRoot f) a ^ m})`.
  This uniquely fixes the ideal in the node; it is not an arbitrary lift.
- Its finite generation is `K.FG`.
- Extension of ideals is `Ideal.map` along the relevant localization map.
  The equality in the theorem is `Ideal.map (algebraMap C C_h) K =
  Ideal.map θ.toRingHom (Ideal.map (algebraMap B B_g) J)`, with the actual
  types expanded in the Lean file. This is precisely `KC_h = θ(JB_g)`.
- Annihilation is stated on every element of the actual quotient:
  `∀ z : AdjoinRoot f ⧸ K,
  Ideal.Quotient.mk K (algebraMap A (AdjoinRoot f) a ^ m) * z = 0`.
  This is `a_C^m(C/K)=0`, including the zero quotient.

Recorded statement-dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`;
  `Mathlib.RingTheory.Localization.Away.Basic` provides the ring/algebra
  localization interface, including `IsLocalization.mk'`.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free` and its underlying
  notion `Module.Basis`. The theorem gives the stronger explicit basis
  demanded by this node, without inventing another notion of freeness.

The proof-dependency Mathlib matches were also read:
`Algebra.IsEtaleAt.exists_isStandardEtale` in
`Mathlib.RingTheory.Unramified.LocalStructure`;
`AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway` in
`Mathlib.AlgebraicGeometry.OpenImmersion`;
the restriction instance in `Mathlib.AlgebraicGeometry.Morphisms.Etale`;
and `AdjoinRoot.powerBasis'` in `Mathlib.RingTheory.AdjoinRoot`.
These modules are imported, using plain imports for modules needed only
by the future proof. The docstring contains all six proof steps, including
both maps for the quotient/localization identification and both localized
ideal inclusions. `StandardEtalePair.equivAwayAdjoinRoot` was read as the
existing canonical comparison for that step.

Edge cases checked before and after writing:

- `r = 0`: `Fin 0` is empty, `J = ⊥`; the assumption says `a_B^m = 0`.
  The only generator of `K` is `a_C^m`, which vanishes after localization.
- `J = ⊤` or `K = ⊤`: unit ideals are allowed; the quotient is zero and the
  annihilation statement remains valid. No properness hypothesis was added.
- `a = 0`, a nilpotent scalar, and `m = 1`: all are admitted. No
  nonzerodivisor or reducedness hypothesis is needed for this subargument.
- The zero ring `B` has no prime ideal, so it cannot instantiate `q`; this
  follows from primality, with no extra `Nontrivial` hypothesis.
- A monic constant polynomial has quotient zero and an empty power basis;
  the syntax allows `f.natDegree = 0` and `Fin 0`. A prime neighborhood here
  is nonzero, so such a chart cannot be the witness in that case.
- Exponent zero is allowed and represents denominator one. Nilpotent or
  zero localizing elements are not silently excluded by the localization type.

Searches for an existing complete statement (all run through `msearch.py`,
with group Q27 and this item; raw summaries are in sandbox `searches.jsonl`):

- LeanFinder: `An etale algebra near a prime has a monic polynomial quotient
  chart and numerator lifts for a finitely generated ideal containing a
  scalar power`. Eight hits, including `StandardEtalePresentation`,
  `StandardEtalePair`, `Algebra.exists_etale_of_isEtaleAt`,
  `Algebra.IsStandardEtale`, and its local structure APIs. These provide
  charts but not the specified ideal lift with basis and annihilation.
- Loogle: `AdjoinRoot, Localization.Away, Ideal`. Zero hits.
- Mathlib grep: `etale.*ideal|ideal.*etale|equivAwayAdjoinRoot` in
  `RingTheory/Etale`. Nineteen hits; the relevant canonical chart equivalence
  is `StandardEtalePair.equivAwayAdjoinRoot`, not the combined theorem.
- LeanSearch: `An etale algebra admits a local monic quotient chart with a
  finite numerator ideal lift containing a given scalar power`. Eight hits,
  including `Algebra.Etale`, `Algebra.Etale.finitePresentation`,
  `Algebra.Etale.of_isLocalizationAway`, and `Algebra.IsEtaleAt.comp`;
  none says the combined statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for etale/chart/ideal/lift
  combinations found general ideal-lifting, root-algebra, and etale-chart
  modules, but no combined statement. The exact declaration name
  `exists_etale_chart_ideal_lift` is absent in both trees and Mathlib.
- `grep -rn 'lem-trf-etale-chart-ideal-lift' lean/WeilConjectures`
  returned no matches. `rg` of chart/ideal names in
  `dag/lean_names_upstream.json` showed unrelated etale chart residue
  triple equivalences and a conormal-basis chart, not this statement.

Compilation uses only the prescribed `scompile.py` server wrapper. The first
attempt exposed an uninferred localization submonoid in the fraction term;
this was fixed by explicitly specifying `M := Submonoid.powers h`, without
changing the mathematical statement. The final validation is recorded below.

## Second reading by Q27

This is the worker's own second pass with the node and Lean file open.
The dispatcher explicitly forbids starting other agents and assigns the
independent review to the maintainer; no independent-worker review is claimed.

I checked the input spectrum map and both output localization maps, the
A-linearity of `θ`, all generator indices and exponents, the power basis
rather than mere freeness, the exact span defining `K`, the direction of
both ideal maps, and multiplication by the same scalar power on the actual
quotient. The only elaboration repair was the explicit submonoid argument
in the fraction constructor. No hypothesis or conclusion changed, and no
local notation, private construction, auto-bound variable, or hidden `let`
was introduced. No missing dependency interface or statement correction
was required.

Validation: `scompile.py Q27 lem-trf-etale-chart-ideal-lift <EtaleChartIdealLift.lean>` returned exit 0. The wrapper's local
attempt encountered a device-space error, then its normal server
confirmation compiled the file cleanly in 4.9 seconds, at nice 19
with two threads and the unchanged 60-second limit.
