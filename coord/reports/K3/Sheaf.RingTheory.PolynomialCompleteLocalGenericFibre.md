## What changed

Proved `Polynomial.completeLocalGenericFibre` in
`Sheaf.RingTheory.PolynomialCompleteLocalGenericFibre`, preserving its signature and all
public imports. Four proved private helpers establish polynomial module finiteness,
generic formal-fibre ascent along injective finite maps, characteristic zero for Cohen
rings, and geometric regularity over characteristic-zero regular local coefficients.
The main proof obtains the regular subring from the existing 032D declaration, contracts
the maximal ideal, applies finite ascent, and handles its field/Cohen presentation.
The positive-characteristic case applies the existing 07PR declaration with one variable;
finite ascent also transports it through the presentation isomorphism. The zero-characteristic
case uses polynomial localization regularity, completion regularity and regular localization,
then the triviality of purely inseparable extensions.

Added proof imports of `Mathlib.Algebra.CharP.Invertible`,
`Mathlib.RingTheory.RegularLocalRing.Polynomial`,
`Mathlib.RingTheory.QuasiFinite.Basic`, and
`Sheaf.RingTheory.LocalizationOfRegularRing`. Updated only the item's node fields
`proof`, `proof_deps`, and `proof_origin` to record the actual argument.

## Proved and sorry left

Closed the sole original hole: `Polynomial.completeLocalGenericFibre`
(node `lem-weil-pbc-polynomial-complete-local-generic-fibre`). No `sorry` remains in the
submitted module, and no new hole or new module is added: one hole closed, zero added.
This is a proof from existing stated dependencies, not a decomposition into new holes.
The dependency declarations may themselves still depend on `sorry`, as stage 3 permits.
All four private helpers have complete proofs. Compilation passes without warnings.

## No longer needed

Removed original proof imports:

- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism` and its planned node `pqf-def-quasifinite`:
  the proof needs only ring-level quasi-finiteness, supplied by the formal-fibre ascent
  interface and proved here from finite-dimensional residue-field fibres.
- `Sheaf.RingTheory.RegularRingSmoothAscent` and planned node
  `lem-weil-pbc-regular-ring-smooth-ascent`: Mathlib directly proves regularity of the
  required polynomial localization, so smooth ascent is unnecessary on this edge.
- `Mathlib.FieldTheory.PurelyInseparable.Basic`: the public import of
  `Sheaf.RingTheory.GRing` already supplies these declarations. The corresponding
  definition node remains a proof dependency since purely inseparable triviality is used.

Temporary exploration imports of `Mathlib.Algebra.MvPolynomial.Equiv`,
`Mathlib.Algebra.Polynomial.Eval.Degree`, and `Mathlib.RingTheory.TensorProduct.Finite`
were also removed after compilation confirmed the retained imports supply what is needed.
The second reading also removed redundant proof imports of
`Mathlib.RingTheory.Localization.BaseChange`, `Mathlib.RingTheory.PolynomialAlgebra`,
and `Mathlib.RingTheory.Ideal.GoingUp`: retained imports expose the declarations needed.

These pruning claims concern this module's direct proof dependencies, not a claim that the
modules become globally unreachable: other modules, including 07PR, may still import them.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement or definition was changed, and no disputed statement was found. The original
DAG routed polynomial regularity through smooth ascent and cited scheme quasi-finiteness;
neither is necessary. Its implicit localization-of-regular-ring step is now explicitly
recorded. Transport of the positive-characteristic presentation needs no separate unproved
isomorphism lemma: the already required finite quasi-finite ascent theorem handles it.

Checked the characteristic-zero/positive-characteristic split, the field and Cohen cases,
and arbitrary finite-variable counts, including zero coefficient variables. The argument
never assumes that the generic fibre is a domain or nonzero; regular-ring localization
and tensor-isomorphism transport cover a possible zero fibre. The maximal-ideal contraction
hypothesis is used to install polynomial-localization regularity over the contracted base.
Searches through leanfinder, loogle, the prescribed grep search, and local library/Mathlib
sources found the component lemmas used here, rather than an exact theorem for the whole
statement. The source argument was read at Stacks Tag 07PV.


## Second reading by K3

1. **Unchanged interface — pass.** Compared the sole delivered Lean module against the
   repository with `diff`. The signature of `Polynomial.completeLocalGenericFibre` is
   byte for byte identical, including all hypotheses, universes and visibility. The four
   public imports are unchanged. No definition or statement change or forced adaptation
   is present. Restored the existing theorem docstring rather than changing its API text.
2. **Proof and axioms — pass.** Compiled the module locally through `lcompile.py` without
   errors or warnings. Checked `#print axioms` in a scratch copy for the main theorem and
   each of its four private helpers: only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx` from existing imported open declarations occur. Polynomial finiteness and
   Cohen characteristic zero have no `sorryAx`. No local `sorry`, forbidden declaration,
   hollow definition, or data definition choosing an arbitrary unproved witness occurs.
   The regular subring and presentation witnesses are eliminated inside a theorem proof.
3. **Split statements and searches — pass.** No statement is split off and no new hole
   is added. Read all four helper proofs: the finite-map helper uses injectivity exactly
   to contract the zero prime; finite fibres give discrete spectra; the Cohen case rules
   out both possible positive-characteristic cases. Checked coefficient fields, zero
   power-series variables, characteristic zero and positive characteristic, and the
   possible zero generic fibre. Repeated leanfinder, loogle and grep searches with new
   queries, and searched both the current library and upstream source. Related finite
   subring and regular power-series formal-fibre lemmas do not replace this polynomial
   argument: their power-series model does not cover the polynomial ring, and the
   subring wrapper is narrower and remains open. No shorter proved route was found.
4. **Top-down proof and pruning — pass, repaired imports.** The proof reduces through
   032D and 07PP, proves the characteristic-zero completion/localization argument, and
   uses existing 07PR only in positive characteristic. Every removed old proof dependency
   is listed above: `pqf-def-quasifinite` and
   `lem-weil-pbc-regular-ring-smooth-ascent`. Inspected `dag/units/sk-thm-p1.json`:
   no realized statement or step is removed or bypassed. Tested omission of each proof
   import; removed the three redundant Mathlib imports listed above and compiled their
   combined removal successfully. The other retained proof imports are needed.
5. **DAG agreement — pass.** Compared the node JSON: only `proof`, `proof_deps` and
   `proof_origin` differ. Its steps describe the finite polynomial pushout, maximal-ideal
   contraction, finite quasi-finite ascent, regular completion/localization, and field/Cohen
   cases actually used. Its dependencies are the union of the steps' uses and identify
   the imported declarations or Mathlib match. No new node or change record is needed.

Second-reading changes: restored the original theorem docstring and removed redundant
proof imports of `Mathlib.RingTheory.Localization.BaseChange`,
`Mathlib.RingTheory.PolynomialAlgebra`, and `Mathlib.RingTheory.Ideal.GoingUp`.
No proof body, signature, definition, or DAG route required correction.
