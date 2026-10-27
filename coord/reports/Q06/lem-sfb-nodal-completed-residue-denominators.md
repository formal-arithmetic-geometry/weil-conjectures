## Worker report

Item: `lem-sfb-nodal-completed-residue-denominators` (stage 2, Q06).

The module `Sheaf.RingTheory.NodalCompletedResidueDenominators` states
`RingTheory.nodal_completed_residue_denominators` and
`RingTheory.nodal_completed_residue_denominators_nonunit_counterexample`.
Both proofs are `sorry`; no definition data is postponed and nothing is proved.
The second declaration formalizes the item's final warning, with the explicit
counterexample in the accepted proof's step 7. Both declarations belong to this node.

The inherited stage-1 BLOCKED ending is obsolete for this assignment: the current
node has an accepted Q12 split, no Lean record, and a stage-2 queue entry.
`coord/brief-stage2.md` section 0 explicitly authorizes the stage-2 handoff without
reopening that split. There is no released repair note for the item. The node copy
preserves every existing field and adds only `lean`.

Read source: Stacks `curves.tex`, Tag 0CBT, `remark-quadratic-extension`, including
constructions (2)/(3) and the sentence omitting their comparison. This is the
accepted node's agent-supplied local algebra ingredient of that comparison; it
asserts no general equivalence of the constructions without their nodal hypotheses.
Also read the current `literature/blueprint/latest` direct-images unit statement
and proof (3): the inherited alteration branch is provenance, and no unit or route
is changed by this statement delivery.

Hypothesis-by-hypothesis correspondence for the main theorem:

- The Noetherian local commutative ring is `A : Type u` with `[CommRing A]`,
  `[IsNoetherianRing A]`, `[IsLocalRing A]`. Its maximal ideal is always the same
  `IsLocalRing.maximalIdeal A` and its residue field is literally
  `A ⧸ IsLocalRing.maximalIdeal A`; no coefficient-field section is assumed.
- The completion R is literally `AdicCompletion (IsLocalRing.maximalIdeal A) A`,
  with its canonical Mathlib A-algebra structure. There is no free ring R or
  assumption that A is already complete.
- The injective homomorphism A -> B is `[CommRing B] [Algebra A B]` with
  `hinj : Function.Injective (algebraMap A B)`. A commutative-ring homomorphism
  supplies exactly this algebra structure; B is not assumed finite, Noetherian,
  local, normal, or a domain.
- The nonzero commutative F-algebra L is `[CommRing L] [Nontrivial L]` and
  `[Algebra (A ⧸ IsLocalRing.maximalIdeal A) L]`. The field map is automatically
  injective. L need not be a field, reduced, or a domain.
- The given R-algebra structure on `PowerSeries L` is the explicit
  `[Algebra (AdicCompletion ...) (PowerSeries L)]` binder. `psi` is a ring
  equivalence from `B ⊗[A] AdicCompletion ...` to `PowerSeries L`, and `hscalar`
  says `psi (1 ⊗ r) = algebraMap R (PowerSeries L) r` for every r. This is exactly
  the R-algebra compatibility for the canonical right-factor action: the image
  of the structure map of R is `1 ⊗ r`. It is an unbundled encoding of the given
  R-algebra equivalence, not an arbitrary replacement map or a stronger condition.
- `hideal` says that the extension of m to the tensor algebra, mapped through
  `psi.toRingHom`, equals `Ideal.span {PowerSeries.X}`. This is mC corresponding
  to tL[[t]], with equality rather than one containment.
- `hconstant` states for every a in A that the constant coefficient of
  `psi (algebraMap A B a ⊗ 1)` is its quotient class mapped by `algebraMap F L`.

Clause-by-clause correspondence for the main conclusion:

- The existential `e₁` and `e₂` are ring equivalences between exactly B/mB,
  C/mC, and L. The first representative equation specifies
  `e₁ ([b]) = [b ⊗ 1]` for every b, which uniquely determines the canonical
  tensor/quotient comparison. It uses the actual completion, not an auxiliary
  algebra with an assumed residue-field comparison.
- The second equation says `e₂ ([z]) = PowerSeries.constantCoeff (psi z)` for
  every z in C. Together they give the specified composite on [b].
- These are F-algebra equivalences, expressed without separately choosing an
  F-algebra instance on the quotients. Their canonical F-actions descend the
  A-actions, since m annihilates both quotients. For any a in A, the e₁ equation
  sends the scalar class of a to its scalar class in C; the e₂ equation and
  `hconstant` send it to `algebraMap F L [a]`. Every element of F has a lift a.
  Thus the formulas assert all the required F-compatibility and fix the maps
  uniquely on every element; no arbitrary ring isomorphism is substituted.
- The denominator assertion quantifies over all `f : A`, `u₀ : Lˣ`, and
  `h : PowerSeries L`, with `f ∈ m` and the exact equality
  `psi (f ⊗ 1) = C ↑u₀ * X + X ^ 2 * h`. The unit type implements invertibility;
  merely nonzero leading coefficients are not accepted here.
- The first two conjuncts assert injectivity of multiplication by f on A and
  by its actual image on B.
- The next conjunct is `m.map (algebraMap A B) = Ideal.span {algebraMap A B f}`.
  The following universal n conjunct is the equality of `(m ^ n).map ...` with
  `Ideal.span {(algebraMap A B f) ^ n}`. These are exactly mB=fB and m^nB=f^nB,
  including n=0, not just equality of radicals or ideals after completion.
- For every n and d in m^n, `∃! b : B, (algebraMap A B f)^n * b = algebraMap A B d`
  states existence and uniqueness of d/f^n. No field of fractions or choice of
  a division operation is introduced.
- For every b satisfying that equation and every r,h_d giving the stated
  expansion of d, the residue formula is
  `e₂ (e₁ ([b])) = r * ((↑(u₀⁻¹) : L) ^ n)`. Since L is an arbitrary ring,
  inverse of the specified unit, rather than field division, means r/u^n.
- For every second g with the same ideal membership and unit-leading expansion,
  the final conjunct gives b,c in B with f*b=g, g*c=f, b*c=1, and c*b=1.
  The earlier uniqueness clause identifies b,c with g/f and f/g.

The final sentence about nonzero coefficients is the companion theorem.
It exhibits `S : Subring (PowerSeries ℚ × PowerSeries ℚ)` with membership
exactly equality of the two constant coefficients, and an ideal m. It states
Noetherianity, locality, m-adic completeness, maximality and uniqueness of m,
and the residue equivalence S/m -> ℚ with its formula. The displayed psi from
B tensor_S completed S to `(ℚ × ℚ)[[t]]` is specified on every coefficient of
b tensor 1. It sends mC to (t), and a chosen f in m has leading coefficient
(1,0), explicitly nonzero and not a unit. Multiplication by f on S is not
injective, and mB differs from fB. This is a concrete counterexample to the
proposed weaker hypothesis, rather than an extra assumption on the main theorem.
The A -> B injection is the subtype inclusion; the F=ℚ action on L=ℚ×ℚ is diagonal.
The coefficient formula enforces the residue condition on every element of S.
The R-action on L[[t]] can be transported through the exhibited ring equivalence,
so there is no missing R-algebra compatibility in this existential example.

Dependency declarations read and reused (no dependency repair needed):

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs` (lines 193-205).
- `def-weil-pbc-adic-completion`: `AdicCompletion`,
  `Mathlib.RingTheory.AdicCompletion.Basic` (lines 159-174), with its actual
  ring/algebra structures from `Mathlib.RingTheory.AdicCompletion.Algebra`.
- `def-weil-pbc-algebra-hom-quotient`: the recorded Mathlib match gives
  `AlgHom` (`Mathlib.Algebra.Algebra.Hom`, lines 29-33),
  `Ideal.Quotient.algebra` and `Ideal.Quotient.mkₐ`
  (`Mathlib.RingTheory.Ideal.Quotient.Operations`, lines 353-371), and ideal
  operations. `[Algebra A B]`, `Ideal.map`, quotient rings, products and powers
  in the statement use those existing notions.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs` (lines 78-84, 102-108), with the
  algebra tensor product structure of `Mathlib.RingTheory.TensorProduct.Basic`.
- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries`,
  `Mathlib.RingTheory.MvPowerSeries.Basic` (lines 84-87); `PowerSeries L` is its
  standard one-variable abbreviation `MvPowerSeries Unit L`, not a new notion
  (`Mathlib.RingTheory.PowerSeries.Basic`, lines 58-63). Read `coeff`,
  `constantCoeff`, `C`, and the standard polynomial-variable operations there.
- Proof imports cover `Module.FaithfullyFlat.of_flat_of_isLocalHom`,
  `Ideal.comap_map_eq_self_of_faithfullyFlat`
  (`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`, lines 59-61, 104-108),
  the base-change instance `Module.FaithfullyFlat.instTensorProduct`
  (`...Flat.FaithfullyFlat.Basic`, lines 558-566),
  `AdicCompletion.flat_of_isNoetherian` (`...AdicCompletion.AsTensorProduct`),
  the completion-locality instance, `AdicCompletion.maximalIdeal_eq_map` and
  `AdicCompletion.residueField_map_bijective` (`...AdicCompletion.LocalRing`,
  lines 78-118 and 130-154), `TensorProduct.quotTensorEquivQuotSMul`
  (`Mathlib.LinearAlgebra.TensorProduct.Quotient`, lines 150-160),
  `TensorProduct.AlgebraTensorModule.cancelBaseChange`
  (`Mathlib.LinearAlgebra.TensorProduct.Tower`, lines 431-453),
  `PowerSeries.isUnit_iff_constantCoeff`
  (`Mathlib.RingTheory.PowerSeries.Inverse`, lines 111-113),
  `MvPowerSeries.isNoetherianRing` (`...MvPowerSeries.Equiv`, lines 215-229), and
  `IsAdicComplete` (`...AdicCompletion.Basic`, lines 45-56). Thus all recorded
  proof dependency modules are imported, including the step-7 ingredients.

Edge cases checked before accepting the retained statement:

- n=0: ideal powers extend to the top ideal, f^0=1, the unique quotient is d,
  and the residue formula is the actual constant coefficient r.
- d=0 and r=0: the unique quotient is zero; a zero leading coefficient r is
  allowed in the numerator and gives zero residue. No nonzero-numerator binder.
- g=f: the inverse-ratio witnesses are both 1. If no qualifying f exists,
  the residue equivalences still remain a nonvacuous conclusion outside the f binder.
- L=F×F and L with nilpotents: unit multiplication and coefficient shifts are
  injective even though L is not a domain. The counterexample uses the same
  split algebra with the nonunit (1,0), and witnesses an actual failure in A.
- Characteristic two is allowed in the main theorem. The rational example is
  only one witness to insufficiency; it imposes no characteristic restriction.
- A,B,L use independent explicit universes u,v,w. There is no finite-dimensional
  condition, empty-index restriction, independent test-object size, or unbound implicit.
- Local rings and the nonzero F-algebra are nontrivial as in the node; no zero
  coefficient algebra is silently included or used to justify a vacuous hypothesis.

Searches from the retained worker session, recorded in searches.jsonl:

- `msearch.py ... leanfinder "Descent of regular denominators and residue coefficients
  from a completed algebra isomorphic to power series over a nonzero residue field
  algebra"`: eight Weierstrass preparation/division hits; they impose different
  locality conditions and do not give this descent and residue theorem.
- `msearch.py ... loogle '"AdicCompletion", "PowerSeries"'`: ten hits for
  `MvPowerSeries.toAdicCompletion`, its inverse and polynomial-completion comparison;
  none has the displayed local-ring/tensor-algebra hypotheses or conclusions.
- `msearch.py ... grep 'completed_residue_denominators|constantCoeff.*(div|unit)|comap_map.*faithfullyFlat'
  RingTheory`: 25 unit, coefficient and division ingredients; no exact combined result.
- `msearch.py ... leansearch "Faithfully flat descent of regular denominators and
  the leading coefficient residue formula for an algebra whose completion is formal
  power series"`: eight hits, including regular-sequence base change and completion
  flatness, neither of which states this result.
- `rg -n 'residue.*denominator|completed.*residue|nodal.*denominator'` over
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  nearby residue/adic and nodal-geometry results, no same declaration or notion.
- `grep -rn 'lem-sfb-nodal-completed-residue-denominators' lean/WeilConjectures`:
  no match. The exact node-id/name search over both live source roots also had no match.

No new nodes, dependency modules, statement corrections, or STATEMENT-DISPUTED faults.
`CompactObject.lean` at the prescribed example path is now a withdrawn stub; its
node's live upstream record and the standing brief were read for current conventions.

Validation: the prescribed `scompile.py Q06 lem-sfb-nodal-completed-residue-denominators`
compiled the delivered module successfully in sandbox mode (2.9 s) and library mode
(2.7 s), without errors or unexpected warnings. Every variable is explicitly bound
and `autoImplicit` is disabled. Dry-run and push results are reported below.

## Second reading by Q06

This was a separate full rereading within the same worker session, not a claim that
another agent independently reviewed it; the maintainer supplies the independent
review specified in the assignment. I opened the current node and retained Lean
module together, checked each binder and conjunct against the correspondence above,
and reread the dependency signatures and Tag 0CBT. No split or statement changes
were needed. In particular, the three potential mismatches were checked explicitly:
`hscalar` is algebra compatibility, the representative formulas force the canonical
F-algebra maps, and the second declaration witnesses the final nonunit warning
under the same completed-model hypotheses. The nonunit witness includes failure
of regularity in the equal-constant subring itself, not merely in its ambient B.
Both `sorry`s have the accepted proof steps in their docstrings. The new node record
copies all accepted Q12 fields verbatim and records both declarations.

Delivery dry run: `deliver2.py Q06 lem-sfb-nodal-completed-residue-denominators --no-push`
printed `OK (dry run): commit 50695286ba1 passes the preflight and compiles; nothing pushed`.
The delivered node changes only `lean`, and the module has no line over 100 characters.


Current handoff verification (2026-10-23): reopened the current accepted node,
all statement dependencies and their full source signatures/docstrings, the proof
interface records and source declarations, Tag 0CBT, and the retained Lean module.
The only node delta is `lean`; its stored signature matches the module verbatim.
No declaration or mathematical statement was changed during this handoff.

Repeated searches:

- LeanFinder, "Faithfully flat descent from completion of regular denominators and
  residue coefficients in a formal power series algebra": eight hits on regular
  sequences, smooth lifting, descent of ring-map properties, and completion algebra
  structures; none states this combined assertion.
- Loogle, `"AdicCompletion", "PowerSeries"`: ten polynomial-completion comparison
  hits; no matching local-algebra descent result.
- Mathlib grep, `completed_residue_denominators|constantCoeff.*(div|unit)|comap_map.*faithfullyFlat`
  in RingTheory: 25 ingredient hits, no combined statement.
- Project source searches for `residue.*denominator|completed.*residue|nodal.*denominator`
  found only other residue and normalization results. Searching the exact blueprint
  id under `lean/WeilConjectures` found no declaration.

Repeated `scompile.py` succeeded in sandbox mode (2.9 s) and library mode (2.7 s),
with no errors or unexpected warnings. Repeated `deliver2.py --no-push` printed
`OK (dry run): commit 0c7b2dc7c44 passes the preflight and compiles; nothing pushed`.
The delivery contains exactly the module, node record and worker report.
