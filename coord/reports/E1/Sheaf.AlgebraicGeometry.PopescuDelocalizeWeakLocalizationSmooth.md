## What changed

The item now obtains standard smoothness of the dehomogenized localization from
`Algebra.popescu_auxiliary_isStandardSmooth`, obtains the dehomogenization
R-algebra equivalence, transports standard smoothness along its inverse, and uses
Mathlib's standard-smooth-is-smooth instance. The original item signature and
original docstring are unchanged. The two new statements have separate modules:
`PopescuDelocalizeJacobianLocalization` and `PopescuDelocalizeDehomogenizationEquiv`.
All imports newly added to the item are proof-only imports. No definition or
existing statement changed, so no change record is required.

The preceding worker's uncommitted `popescuAuxiliary` definition and its false
component statements have been replaced, rather than delivered. The uncommitted
whole-construction standard-smooth theorem and its node have been removed. The
actual source quotient is now written directly in both component statements:
the original f-relations inserted in variables 1,...,n+m, localized at
x₀*w*∏sⱼ. This uses concrete Mathlib quotient and localization constructions;
no arbitrary data is chosen from an unproved existence theorem.

## Proved and sorry left

Hole closed: `Algebra.popescu_delocalize_weak_localization_smooth` (one of the
item's one original holes).

Holes added:
- `Algebra.popescu_auxiliary_isStandardSmooth`, node
  `lem-weil-pbc-popescu-delocalize-jacobian-localization`, in
  `Sheaf.AlgebraicGeometry.PopescuDelocalizeJacobianLocalization`.
- `Algebra.popescu_delocalize_dehomogenization_equiv_exists`, node
  `lem-weil-pbc-popescu-delocalize-dehomogenization-equiv`, in
  `Sheaf.AlgebraicGeometry.PopescuDelocalizeDehomogenizationEquiv`.

This is a decomposition, not a complete proof: one original hole closed, two
new holes added, net minus one in this delivered branch's import closure. The
item has no direct sorry, but still depends on these two named obligations.
The Jacobian component has no homogenization, g-relations or degree bounds; the
isomorphism component asserts no smoothness and needs no Jacobian hypothesis.
Each therefore supplies a distinct, strictly partial part of the original plan.

Compilation: all three delivered modules compile cleanly through lcompile.py.
The explicit axiom checks show only propext, Classical.choice, Quot.sound and
sorryAx (the two listed component theorems). There is no axiom declaration,
unsafe, opaque, implemented_by, extern or sorry in a definition.

## No longer needed

No repository module import is removed and no library module is claimed pruned.
The draft's proof-only public import of Smooth.StandardSmooth is gone; its
unused whole-construction module is gone; the faulty auxiliary definition and
its instances are gone. The remaining added item imports are all private.

Compared to the old item's proof_deps, the direct edges to
`def-weil-pbc-mv-polynomial-ring`, `def-weil-pbc-polynomial-partial-derivative`,
`def-weil-ring-localization-away`,
`lem-weil-pbc-localization-away-universal-property`, and
`def-weil-pbc-smooth-ring-map` are no longer needed by the item's reduction.
The polynomial, derivative and localization tools remain needed inside the
new components (and the smooth definition remains in the item's stmt_deps).
`def-weil-pbc-standard-smooth-algebra` and
`lem-weil-pbc-standard-smooth-is-smooth` remain direct proof dependencies.
No node realizing a unit step is bypassed; the unit's realized fields are kept.

## Where the brief, the DAG or earlier work was wrong

The draft compiled, but its definition was not the algebra its docstrings and
node described: popescuAuxiliary was just P/(F), ignored s and g, and had no
inverse relations. Its alleged smoothness and equivalence were false.
For R=Q, n=0,m=1,c=1,t=0, f₀=1, h=0, s₀=1 and d₀=2, every hypothesis holds,
but F₀=w² and P/(F₀) has a nonzero nilpotent, so is not smooth over Q.
For R=Q,n=m=c=t=0,s₀=0,h=0, all relations are empty and hypotheses hold;
the draft equivalence would identify a zero localization with Q[x₀,w].
These faulty statements have no repository users and are not delivered.

The draft's two sorry theorems had no matching individual nodes or blueprint
proof tags, and the standard-smooth node's Lean signature was an ellipsis.
The replacement components have complete source-backed proofs in their
docstrings and separate nodes with verbatim signatures and genuine searches.
The old item documentation was incorrectly replaced and has been restored.

## New nodes

`lem-weil-pbc-popescu-delocalize-jacobian-localization`: the source's
localized original-f quotient is standard smooth. Its proof adjoins one
inverse variable and uses the triangular Jacobian minor Δ*a. It is stated in
PopescuDelocalizeJacobianLocalization.lean. Three searches were attempted via
msearch.py; LeanSearch was unavailable, Loogle found no exact statement, and
grep found generic submersive-presentation machinery.

`lem-weil-pbc-popescu-delocalize-dehomogenization-equiv`: the two explicit
localized quotients are isomorphic. Its proof expands finite support sums,
checks relations in both directions and checks inverse maps on generators.
It is stated in PopescuDelocalizeDehomogenizationEquiv.lean. LeanSearch was
unavailable; Loogle found tensor/localization and inverse-adjunction tools;
grep found mvPolynomialQuotientEquiv, which adjoins an inverse of one element
and does not provide the partial-homogenization equivalence.

No change record: only the existing item's proof and DAG proof fields change.

## Second reading by E1

1. Compared the item with the repository using diff and checked its declaration
   signature byte for byte. Verdict: unchanged hypotheses, conclusion,
   universes and visibility; original docstring and open Classical restored.
   All additional imports are proof-only. New statements and objects are
   confined to their new modules; no existing definition has changed.
2. Compiled every delivered module in import order through lcompile.py, with
   no error or warning. Checked every theorem's axioms using scratch copies:
   only propext, Classical.choice, Quot.sound and sorryAx are reachable.
   Only the two explicitly listed public component theorems contain sorry.
   No data definition or forbidden declaration is present. Verdict: the
   reduction is kernel-checked, conditional on its two genuine open components.
3. Read the two new component statements against Stacks Tag 07F9's final
   isomorphism and Definition 00T6 (official pages read because the local
   literature files are absent). Verified variable insertion i.castSucc.succ,
   the last index n+m+1, and localization at the same complete product in
   both rings. For the Jacobian lemma, c≤N gives an injective selected-variable
   map; s₀=hΔ in the quotient makes Δ invertible after localizing. The enlarged
   minor is triangular, not necessarily diagonal, and has determinant Δ*a.
   For the equivalence, hg kills g after inverting sⱼ₊₁, and hdegree is exactly
   what justifies the support-sum exponent identity. Tested c=0, m=0, t=0,
   zero base rings and zero products s: the corrected two localizations both
   become zero when necessary; no nonzero assumption was added. Searched
   Mathlib, upstream and lean/ with Jacobian, localization, homogenization,
   and dehomogenization terms, plus the three recorded msearch kinds.
   Read the nearby StrictlyStandardLocalizationSmooth and global complete
   intersection criterion: these require different hypotheses or have a
   different conclusion. Read the upstream dehomogenization results: they
   concern degree-zero homogeneous localization, not these quotient rings.
   Verdict: true component statements, no exact reusable declaration found;
   neither is a renamed statement of the whole item.
4. Read dag/units/sk-thm-p1.json, including all realized steps. The item is a
   lower tool in its finite-etale-lifting branch, not a replacement for any
   realized unit statement or step. The reduction follows its seven-step
   plan, grouped into the Jacobian and isomorphism parts. Compared all old
   proof_deps with the reduction and listed each removed direct edge above;
   no whole library module is claimed pruned. Imports have been minimized
   for the new files; all added item imports are private. Verdict: route kept,
   shortest transport step uses the existing Mathlib theorem and instance.
5. Opened each delivered node and checked proof steps, their uses union,
   proof_origin, source, chapter, unit and verbatim Lean signature. New nodes
   record the two remaining holes individually with complete proof routes;
   the parent records exactly their use and standard-smooth transport.
   Verdict: DAG agrees with Lean; no unrecorded hole and no unit edits.

Changes made by second reading: replaced the false auxiliary algebra and
false component statements with the concrete source localization; removed
irrelevant Jacobian hypotheses from the equivalence; removed the redundant
whole-construction theorem/module/node; added two correctly matched nodes;
restored the existing signature documentation; removed a proof-only public
import and letI warnings; rewrote the report to count decomposition honestly.
