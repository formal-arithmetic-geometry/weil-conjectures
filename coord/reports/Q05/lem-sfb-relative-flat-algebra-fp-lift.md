## Worker report

The module `Sheaf.RingTheory.RelativeFlatAlgebraFpLift` states
`RingHom.finitePresentation_iff_quotient_of_square_zero_of_flat`, with exactly one
postponed proof (`sorry`) and no definitions. The node is unchanged except for
its `lean` record. Its accepted six-step stage-1 split is preserved verbatim.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 06AG,
`lemma-deform-property`, its hypotheses, general remark (I), proof of clause (11),
and proof of clause (13). Clause (13) reduces to the square-zero case and proves
the affine polynomial-kernel lifting assertion used here. The theorem docstring
records all six steps, including the natural tensor/quotient identifications,
flat-quotient tensor injectivity, lifting kernel generators, and the square-zero
Nakayama substitution.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Commutative rings: `{R : Type u} {A : Type v} {C : Type w}` and their three
  `CommRing` instances. The universes `u v w` are explicit and independent.
- Specified ring maps `R → A → C`: `(f : R →+* A) (g : A →+* C)`; the indicated
  composite is exactly `g.comp f`. No independent or arbitrary third map appears.
- Base ideal and square-zero condition: `(I : Ideal R) (hI : I ^ 2 = ⊥)`.
- Flatness of `C` over `R`: `(hflat : (g.comp f).Flat)`. By `RingHom.Flat`, this
  is `Module.Flat R C` for precisely the algebra structure induced by the composite.
- `IA` is `I.map f`. The target ideal is written `(I.map f).map g`, equal to
  `I.map (g.comp f)` by `Ideal.map_map`, hence exactly the node's `IC`.
- The quotient ring map is
  `Ideal.quotientMap ((I.map f).map g) g Ideal.le_comap_map`.
  Here `Ideal.le_comap_map` supplies ideal containment for `I.map f` and `g`;
  it is part of Mathlib's canonical quotient map construction, not a hypothesis.
  By `Ideal.quotientMap_mk`, it sends the class of `a` to the class of `g a`.
  Its domain is exactly `A ⧸ I.map f`, and its codomain exactly `C ⧸ IC`.
- The conclusion `g.FinitePresentation ↔ (...).FinitePresentation` renders both
  directions of the finite-presentation equivalence. `RingHom.FinitePresentation`
  unfolds to the recorded `Algebra.FinitePresentation` for the specified map's
  `toAlgebra`, so the coefficient algebra is fixed, not chosen.
- There is no flatness assumption on `A`, finite generation assumption on `I`,
  Noetherian assumption, nontriviality assumption, or finite-type hypothesis.

Dependency declarations read and used:

- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`
  (definition at line 27 and `flat_algebraMap_iff`); also read `Module.Flat` and
  its tensor-injectivity characterization in `Mathlib.RingTheory.Flat.Basic`.
- `def-weil-pbc-finitely-presented-algebra`:
  `Mathlib.RingTheory.FinitePresentation`, `Algebra.FinitePresentation` (line 44)
  and `RingHom.FinitePresentation` (line 392). The latter is the ring-map encoding
  of the same notion, defined directly using the former, with no duplicate notion.
- Canonical quotient construction: `Mathlib.RingTheory.Ideal.Quotient.Operations`,
  `Ideal.quotientMap` and `Ideal.quotientMap_mk`; ideal functoriality is
  `Ideal.map_map` in `Mathlib.RingTheory.Ideal.Maps`, lines 175–178.
- Proof imports, as required by the node's accepted plan:
  `Mathlib.Algebra.MvPolynomial.Basic` (`MvPolynomial`),
  `Mathlib.LinearAlgebra.TensorProduct.Defs` (`TensorProduct`),
  `Mathlib.RingTheory.Flat.Equalizer`
  (`LinearMap.lTensor_injective_of_exact_of_flat`, lines 192ff), and the already
  public finite-presentation import
  (`Algebra.FinitePresentation.ker_fg_of_mvPolynomial`, lines 298–299).

Edge cases checked before writing:

- `I = 0`: both quotient maps identify with the original maps, giving the
  expected finite-presentation equivalence with no extra condition on `A`.
- Zero rings are admitted: no `Nontrivial` instance occurs. If `I = ⊤` and
  `I² = 0`, the base ring is the zero ring, so its unital targets are zero too.
- Empty lists of algebra or relation generators remain admitted by
  `Algebra.FinitePresentation` (its natural-number parameters may be zero).
- An infinitely generated square-zero ideal is admitted: no `I.FG` occurs.
  Both substitutions `C = D + IC` and `K = L + IK` use only finite individual
  sums and `I² = 0`, not finite generation of `I` or `K` in advance.
- A nonflat intermediate algebra is admitted. In the source argument tensoring
  the presentation uses flatness of its quotient `C`, not flatness of `P` or `A`.
- No characteristic is excluded, and the independent ring universes impose no
  equality of sizes or vacuous quantification over smaller test rings.

Searches actually run with `msearch.py Q05 lem-sfb-relative-flat-algebra-fp-lift`:

- LeanFinder: “For commutative rings R A C with C flat over R and square-zero
  ideal I of R, C is finitely presented over A if and only if C/IC is finitely
  presented over A/IA”. Eight hits: quotient, transitivity, scalar restriction,
  formal smoothness lifting, and module/algebra finite-presentation comparison;
  none gives the relative square-zero lifting equivalence.
- Loogle: `Algebra.FinitePresentation, Module.Flat`. Five hits concern smoothness
  or etaleness and require finite presentation already; none states the node.
- Mathlib grep in `RingTheory`:
  `(finitePresentation|finite_presentation|FinitePresentation).*(nilpot|square|quotient)|nilpot.*(FinitePresentation|finitePresentation)`.
  Nine hits, concerning quotient presentations and their finite generation;
  none is the lifting equivalence.
- LeanSearch: “Finite presentation of a relative algebra flat over a base lifts
  across a square-zero base ideal”. Eight hits include base change, formal
  smoothness lifting, and the definitions `RingHom.FinitePresentation` and
  `AlgHom.FinitePresentation`; none gives the converse under base flatness.
- Direct `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` for
  `finitePresentation.*(nilpot|quotient)`, `finitePresentation.*[Ii]deal`,
  `finitePresentation.*[Ff]lat`, and the node id found no exact statement.
  Additional relative/quotient/square-zero/nilpotent finite-presentation name
  searches and a literal `grep -rn` of the node id in `lean/WeilConjectures`
  found no existing declaration. Searching the proposed full name in Mathlib,
  both project roots, and `dag/lean_names_upstream.json` found no collision.

The old ending was a stage-1 unchanged-item rejection. The current node has
`status: split`, a passing Q135 stage-1 review, no `lean`, and a stage-2 queue
entry. The stage handoff in `coord/brief-stage2.md` section 0 explicitly says
this does not bar recording its Lean statement through `deliver2.py`. No
released repair note exists for this item.

Validation: the prescribed `scompile.py` compiled this file both in its sandbox
and its final library module context on the server, with no errors or unexpected
warnings (4.7 s and 6.7 s respectively). All variables are explicit and
`autoImplicit` is disabled. No statement dispute or mathematical node fault.

## Second reading by Q05

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
