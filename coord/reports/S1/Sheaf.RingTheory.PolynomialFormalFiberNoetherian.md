## What changed

Proved `Polynomial.formalFiber_isNoetherian` in
`Sheaf.RingTheory.PolynomialFormalFiberNoetherian` without changing any binder,
universe, visibility, or conclusion. Hilbert's basis theorem supplies Noetherianity
of the polynomial ring; localization preserves it. Register Noetherianity of the
completion using `AdicCompletion.isNoetherianRing`, then apply
`Ideal.isNoetherianRing_fiber`. Added the proof-only import
`Mathlib.RingTheory.Polynomial.Basic` for Hilbert's basis theorem.
The theorem-local unused-variable linter setting preserves the signature's
hypotheses, which the geometric-regularity component uses but this component does not.
Updated the node's proof and proof_origin to describe the compiled argument;
its two proof dependencies are unchanged. The unit sk-thm-p1's realized route is unchanged.

## Proved and sorry left

Closed the sole hole: `Polynomial.formalFiber_isNoetherian`
(node `lem-weil-pbc-another-helper-g-ring-noetherian-component`).
No sorry remains in the delivered module; no holes or declarations were added.
The two existing component theorems already have proofs in the library.
Local compilation passes without warnings. The delivery dry run checks the axioms.

## No longer needed

Removed the following unused proof-only imports. Their nodes were not in the
old `proof_deps`; both old proof dependencies remain used and none was pruned:

- `Sheaf.RingTheory.FiniteOverCompleteLocalProduct`:
  `lem-weil-pbc-finite-over-complete-local-product`.
- `Sheaf.RingTheory.CompletionFiniteExtension`:
  `lem-weil-pbc-completion-finite-extension`.
- `Sheaf.RingTheory.Derivation.CompletionAndLocalization`:
  `lem-weil-pbc-derivation-extends`.
- `Sheaf.RingTheory.FormallySmoothAdic`:
  `def-weil-pbc-formally-smooth-adic`.
- `Sheaf.RingTheory.FormallySmoothCompleteLocalRegular`:
  `lem-weil-pbc-formally-smooth-complete-local-regular`.
- `Sheaf.RingTheory.HypersurfaceDerivationRegular`:
  `lem-weil-pbc-hypersurface-derivation-regular`.
- `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`:
  `lem-weil-pbc-localization-prime-residue-field-iso`.
- `Sheaf.RingTheory.PolynomialLocalCompletionFormallySmooth`:
  `lem-weil-pbc-polynomial-local-completion-formally-smooth`.

These are unused by this Noetherianity component. Other parts of the project may
still require them; this report does not claim they leave the entire targets' closure.
Kept the existing public imports to preserve the importer-visible interface.

## Where the brief, the DAG or earlier work was wrong

The module imported eight modules belonging to the geometric-regularity argument,
although its own node already specified the sufficient two-lemma Noetherianity route.
The planned proof works directly once Mathlib's Hilbert basis theorem is imported.
No statement correction, new node, or forced adaptation was necessary.

## Second reading by S1

1. Interface: PASS. Read the full repository/sandbox diff. The existing theorem
   signature from `theorem formalFiber_isNoetherian` through `:= by` is byte for
   byte unchanged: same universe, instances, characteristic and primality
   hypotheses, ideal contractions, inequalities, nonzero condition, completion,
   and fibre conclusion. No definitions or other modules changed. Both public
   imports remain; the Hilbert basis theorem import is proof-only.
2. Proof: PASS. Compiled the delivered module with lcompile.py without errors or
   warnings. Compiled a scratch copy with `#print axioms
   Polynomial.formalFiber_isNoetherian`: exactly `propext`, `Classical.choice`,
   `Quot.sound`, with no `sorryAx`. Inspected the whole file: no remaining sorry,
   axiom, unsafe, opaque, implemented_by, extern, or data construction from an
   unproved existence statement. The first local instance uses polynomial and
   localization Noetherianity; the second applies the completion theorem; the
   final application proves precisely the specified fibre Noetherianity.
3. Split statements: PASS, none added. Read both imported component theorems:
   completion Noetherianity applies to every ideal of a Noetherian ring, and fibre
   Noetherianity applies to every prime of the base of a Noetherian algebra.
   Their hypotheses hold for this completed localization. The argument does not
   require the extra geometric-regularity hypotheses and retains all of them.
4. Route and pruning: PASS. Searched lean/Sheaf and lean/WeilConjectures for fibre
   Noetherianity and searched Mathlib adic-completion sources with msearch.py;
   read Mathlib's Polynomial.isNoetherianRing and the upstream fibre module.
   No shorter existing theorem replacing this composition was found. The three
   proof-only imports supply Hilbert basis, completion, and fibre Noetherianity;
   the public imports supply the existing interface. Read sk-thm-p1.json's
   `realized`: this component is below its unit steps and no unit route is
   bypassed. All eight removed imports are listed above. The original
   `proof_deps` consists of the same two used nodes, so none of its nodes became
   unused; no claim is made about global module reachability.
5. Nodes: PASS. Compared the delivered node with its repository version; only
   `proof` and `proof_origin` changed. Its two `proof_deps` name exactly the
   completion and fibre theorems used, and its proof text also records the
   Mathlib polynomial/localization instances. No new nodes or change records
   are needed.

Second reading changed only this report: clarified that the eight removed
imports were not members of the original two-node proof_deps, and recorded
these independent checks. The Lean proof and DAG update needed no repair.
