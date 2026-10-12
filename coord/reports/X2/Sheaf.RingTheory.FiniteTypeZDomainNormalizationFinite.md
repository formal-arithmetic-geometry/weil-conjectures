## What changed

Proved `RingTheory.finiteTypeZDomain_integralClosure_finite` without changing its signature.
Added the proof-only import `Mathlib.RingTheory.DedekindDomain.IntegralClosure`.
Two proved private helpers establish that fields are N-2 and that every ring ring-isomorphic
to ℤ is Nagata. The integer proof follows Stacks Tag 0335: nonzero primes are maximal;
the zero-prime quotient is normal Noetherian of characteristic zero and uses
`IsIntegralClosure.finite`. The source was read in the local Stacks copy
`/home/ubuntu/c1-stacks-review/algebra.tex`, at `proposition-ubiquity-nagata`.

The main proof uses a universe lift of ℤ, applies the existing Nagata-to-universally-Japanese
theorem, specializes N-2 to the trivial canonical fraction-field extension, and transports
finiteness to K using `FractionRing.algEquiv` and `AlgEquiv.mapIntegralClosure`.
The node's three proof steps and proof origin now describe this implementation.
Local compilation is clean, including after pruning the redundant imports.

## Proved and sorry left

Proved the item's only sorry, `RingTheory.finiteTypeZDomain_integralClosure_finite`
(node `lem-weil-pbc-finite-type-z-domain-normalization-finite`). Both private helpers
`RingTheory.isN2_field` and `RingTheory.isNagataRing_of_equiv_int` are fully proved.
No sorry remains in the delivered module; no sorry or new statement module was added.
The imported theorem `isUniversallyJapanese_of_isNagataRing` remains sorry-backed in
`Sheaf.RingTheory.NagataUniversallyJapanese`
(node `lem-weil-pbc-nagata-universally-japanese`); this is the intended next proof item.
The proof is therefore a completed reduction, not an axiom-free closure of the whole branch.

## No longer needed

Removed direct imports `Sheaf.RingTheory.JapaneseDomain` and
`Sheaf.RingTheory.NagataRing`: their definitions remain available through the public
imports of `Sheaf.RingTheory.NagataUniversallyJapanese`. Their definition nodes remain needed;
no module in the transitive target closure is pruned by removing these direct imports.
No use of `isN1_of_isN2` is needed: N-2 is applied directly to the trivial extension.
The trial imports `Mathlib.RingTheory.Int.Basic` and
`Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic` were also removed: their necessary
facts are already imported by `Mathlib.RingTheory.DedekindDomain.IntegralClosure`.

The second reading additionally marks
`lem-weil-pbc-char-zero-field-extension-separable` as no longer needed by this
item: its separably-generated result is replaced here by the direct Mathlib
perfect-field algebraic separability instances. No whole module is pruned from
the target closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or unit-route error was found. The existing Japanese/Nagata
definitions quantify over the base ring's universe, so applying the theorem to ℤ directly
would cover only Type 0 algebras. Lifting ℤ into A's universe solves this without changing
any definition or statement. Likewise N-2 initially gives finiteness in `FractionRing A`,
so the last step must transport it to the provided K; that transport is fully proved here.
The existing characteristic-zero dependency is stated as separably generated; this finite
extension proof needs only the direct perfect-field separability instances in Mathlib.
The unit route stays unchanged and no new nodes are introduced.

## Second reading by X2

1. Compared the sole delivered module with the repository by `diff`: the existing
   theorem signature is byte for byte unchanged. No definition, target statement,
   public import, or other existing declaration changed. There are no change records.
2. Compiled the module locally without errors or warnings. Scanned for `sorry`,
   `axiom`, `unsafe`, `opaque`, `implemented_by`, and `extern`: none occur in the
   delivered code. A scratch copy prints axioms for both private helpers and the
   main theorem; the helpers use only the allowed standard axioms, while the main
   theorem additionally uses `sorryAx` from the existing open
   `isUniversallyJapanese_of_isNagataRing`. This is a valid completed reduction.
3. No statements were split off, and no new sorry was introduced. Read both fully
   proved private helpers: field extensions are finite over the original field by
   transitivity, and submodules of the resulting Noetherian module are finite.
   For the integer-isomorphic ring, the zero prime quotient is integrally closed
   Noetherian of characteristic zero; every nonzero prime is maximal. These cover
   all primes, including `(0)` and `(p)` in the integer case. The theorem handles
   characteristic-p finite type domains as well as characteristic-zero ones,
   and transports across arbitrary fraction-field universes without strengthening
   the hypotheses.
4. Repeated independent Lean Finder, Loogle, and local Mathlib/library searches
   for finite normalization over the integers. Only the already-used normal-base
   finite-separable-extension theorem was found; it does not prove the item for
   an arbitrary finite type domain. Imports are minimal for the statement and
   proof: all added proof imports are plain imports. Read `dag/units/sk-thm-p1.json`:
   this node is below its realized statement and steps, all of which remain;
   the integer Nagata, universally Japanese, and trivial-extension route is kept.
5. Compared the existing and delivered node records and read the Mathlib leaf
   statements. The new proof steps and origin match the compiled proof. Found
   one stale edge: `lem-weil-pbc-char-zero-field-extension-separable` is represented
   by `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`, which this
   proof never uses. Removed it from step 1 and `proof_deps`; the elementary
   characteristic-zero algebraic separability instances are already named in
   the step text. All other old proof dependencies are used, and the existing
   `IsIntegralClosure.finite` leaf is used directly.

Changed only the stale dependency edge, the corresponding docstring citation,
and this report. No proof repair was needed.
