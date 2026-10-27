## Worker report

The module `Sheaf.RingTheory.ElkikPrincipalSectionApproximation` states
`exists_algHom_elkik_principal_section_approximation`, with its entire proof postponed
by `sorry`. It adds no definitions and changes only the item's `lean` record.

Source read: Elkik, *Solutions d'équations à coefficients dans un anneau hensélien*
(1973), II, Lemma 4, printed pp. 564–566, at
https://www.numdam.org/item/10.24033/asens.1258.pdf (PDF pages 12–14, zero based).
The standing Noetherian convention is on printed p. 554. Lemma 4 gives the requested
approximation for a principal henselian pair and an arbitrary smooth open; its
proof explicitly includes the nilpotent case. No statement correction is needed.
The module docstring gives all eight proof steps and names the recorded DAG inputs.

Each hypothesis and conclusion is rendered as follows:

| Node text | Lean rendering |
| --- | --- |
| Commutative Noetherian ring A | `{A B : Type u} [CommRing A] [IsNoetherianRing A]` (B's ring structure is introduced below) |
| Element t in A | `(t : A)` |
| Henselian pair (A,tA) | `[HenselianRing A (Ideal.span {t})]`; `Ideal.span {t}` is the principal ideal tA |
| Finitely presented commutative A-algebra B | `[CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]` |
| C is the inverse limit of A/t^mA | `AdicCompletion (Ideal.span {t}) A`, with its existing ring and A-algebra structures; Mathlib includes the zero-th, zero-ring coordinate, which carries no additional data |
| Open subscheme W of Spec B | `(W : (Spec (CommRingCat.of B)).Opens)`; its associated scheme and inclusion are `W.toScheme` and `W.ι` |
| W to Spec A is smooth | `(hW : Smooth (W.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))))` |
| A-algebra map u from B to C | `(u : B →ₐ[A] AdicCompletion (Ideal.span {t}) A)` |
| The restriction of Spec u to Spec C minus V(tC) has image in W | `hu` quantifies over every `x : PrimeSpectrum C`; `algebraMap A C t ∉ x.asIdeal` means x lies in D(t), and `(Spec.map (CommRingCat.ofHom u.toRingHom)) x ∈ W` is the image condition. Factoring through an open subscheme is equivalent to this pointwise containment |
| Every integer m at least 1 | `∀ m : ℕ, 1 ≤ m →`; these naturals are exactly the positive integer indices in the node |
| An A-algebra map v from B to A exists | `∃ v : B →ₐ[A] A` |
| q_m v = pi_m u | `(Ideal.Quotient.mk ((Ideal.span {t}) ^ m)).comp v.toRingHom = (AdicCompletion.evalₐ (Ideal.span {t}) m).toRingHom.comp u.toRingHom`; equality of underlying ring homomorphisms is equality of the A-algebra maps, whose additional structure is propositional |
| t may be a zero-divisor or nilpotent | No regularity, nonzero, nonnilpotence, completeness, excellence, or G-ring assumption occurs |

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`, from
  `Mathlib.RingTheory.Noetherian.Defs`, and its docstring identifying finite generation of ideals.
- `def-weil-pbc-henselian-terminology`: `HenselianRing`, publicly supplied by the
  recorded `WeilConjectures.Mathlib.RingTheory.Henselian`. Its actual definition is
  in `Mathlib.RingTheory.Henselian`, with Jacobson containment and simple-root lifting.
  This is the dependency's recorded henselian-pair notion (equivalent to its
  finite-algebra idempotent formulation). The other declarations of this multi-notion
  dependency, `HenselianLocalRing` and `IsStrictlyHenselianLocalRing`, were read but
  are not needed by this item.
- `def-weil-pbc-adic-completion`: `AdicCompletion` in
  `Mathlib.RingTheory.AdicCompletion.Basic`; its ring/A-algebra structure and
  `AdicCompletion.evalₐ` are in `Mathlib.RingTheory.AdicCompletion.Algebra`, imported publicly.
  Read `AdicCompletion.of`, `eval`, `evalₐ`, `evalₐ_of`, and `surjective_evalₐ`.
- `def-weil-pbc-finitely-presented-algebra`: `Algebra.FinitePresentation` in
  `Mathlib.RingTheory.FinitePresentation`, the finite-polynomial presentation with FG kernel.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, applied to the actual structural composite.

Already stated proof dependencies are imported non-publicly: completion modulo powers
(`AdicCompletion.pow_smul_top_eq_ker_eval`, `evalₐ_of`, `surjective_evalₐ`, in Algebra
and Completeness), Artin–Rees (`Ideal.exists_pow_inf_eq_pow_smul`, Filtration), faithfully
flat ideal contraction (`Ideal.comap_map_eq_self_of_faithfullyFlat`,
Flat.FaithfullyFlat.Algebra), one-plus units (`Ideal.mem_jacobson_bot`, Jacobson.Ideal),
and zero-locus/radical equality (`PrimeSpectrum.zeroLocus_eq_iff`, Spectrum.Prime.Topology).
The three remaining proof inputs currently have no Lean record or Mathlib match:
`lem-per-elkik-conormal-smooth-open-chart`,
`lem-per-jacobson-adic-completion-faithfully-flat`, and
`lem-per-tougeron-henselian-jacobian-correction`. They are not needed to type the
statement, and their future imports belong to the maintainer's proof-import propagation.

Edge cases checked before writing:

- `t = 0` and nilpotent t: the punctured spectrum is empty, the image condition is
  vacuous, and the completion identifies canonically with A; u gives v at every order.
- Zero-divisor, nonnilpotent t: the type imposes no cancellation condition. The recorded
  proof uses Artin–Rees on t-power torsion in place of cancelling t.
- Empty W: for nonnilpotent t the premise rules out a formal section with nonempty
  punctured source; for nilpotent t it imposes no condition and approximation still holds.
- Zero ring A: its spectrum and completed spectrum are empty, and the unique compatible
  maps satisfy the conclusion. No `Nontrivial` instance excludes this case.
- Unit t: henselianity forces the unit ideal into the Jacobson radical, so this is
  allowed only in the zero ring; it is not silently admitted for a nonzero A.
- m = 1 is included; m = 0 is excluded exactly by the node's positive-order premise.
- B is arbitrary finitely presented, not assumed globally smooth; W can be any open,
  not necessarily a principal or affine open. All variables and universe u are explicit.

Searches actually run for this item:

- `msearch.py ... leanfinder "Elkik approximation of a generically smooth formal section over a principal henselian pair"`:
  8 hits, including `Algebra.FormallySmooth.lift`, `Algebra.FormallySmooth.exists_lift`,
  `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`, standard étale pairs,
  and `Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq`. None approximate
  into the original ring under only generic smoothness.
- `msearch.py ... leansearch "Approximation of formal sections over noetherian henselian pairs with principal ideal and smooth generic image"`:
  8 hits on Hensel lifting, smoothness, and formal smoothness; no matching statement.
- `msearch.py ... loogle "HenselianRing, AdicCompletion"`: OK, 0 hits.
- `msearch.py ... grep "Elkik|henselian.*approxim|approxim.*henselian" RingTheory`:
  OK, 0 hits in Mathlib.
- `rg -n 'Elkik|elkik|principal_section_approximation|henselian.*approxim|approxim.*henselian'
  lean/WeilConjectures lean/Sheaf`: inspected existing approximation results, especially
  `WeilConjectures.RingTheory.HenselianPairApproximation` and
  `WeilConjectures.RingTheory.HenselianApproximationAlgHom`. Their full signatures
  assume `IsGRing A`; the latter gives order-one approximation. Neither is the node's theorem.
- `grep -rn 'lem-per-elkik-principal-section-approximation' lean/WeilConjectures`: no hits.
- `rg -n 'exists_algHom_elkik_principal_section_approximation'
  lean/WeilConjectures lean/Sheaf lean/.lake/packages/mathlib/Mathlib`: no hits before writing.

Validation: prescribed `scompile.py Q110 lem-per-elkik-principal-section-approximation`
compiled both its sandbox and library-module checks successfully (2.4 s and 1.7 s);
no errors or unexpected warnings. The final dry run and delivery are performed after
this report. No new nodes, dependency repair modules, statement disputes, or node faults.

## Second reading by Q110

This is the worker's own second pass, not a claim of an independent agent review;
the dispatcher requires work without subagents and assigns the independent review
to the maintainer. Re-read the node and complete Lean signature together. The sole
geometric smoothness premise is on `W.ι` followed by B's structural map; the punctured
source is defined by nonmembership of the image of t in each prime of the completion;
the formal map and its approximation are both A-algebra maps. The quotient uses
`(Ideal.span {t}) ^ m`, not a different ideal, and the completion projection is the
canonical coordinate `evalₐ`. Checked that no hypothesis on t, W, or A was introduced
beyond the node, and that every positive m is universally quantified. The theorem
concludes precisely the requested map equality. No mismatch or edit arose on this pass.
