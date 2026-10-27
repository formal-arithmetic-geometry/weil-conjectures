## What changed

Proved `WeilConjectures.integralExceptionalSupport_exists` in
`Sheaf.Paper.IntegralExceptionalInverseImage`. Transported adic completeness,
uniformizer regularity, finite quotient rings and prime-power torsion to the
explicit lifted integer ring. Instantiated the generic ordinary-etale Brown
construction at that ring, including coproduct preservation, exactness, scalar
linearity, evaluated adjunctions, quotient mates, a uniform lower bound and
preservation of normalized bounded-below systems.

Private proved helpers reuse the private Brown construction and evaluation
arguments through proof-only `import all` imports. The site-comparison existence
proof now shares the same completeness and regularity lemma. All existing public
statements, definitions and signatures are preserved. The node records the actual
support proof and its dependencies. No other module is changed.

## Proved and sorry left

Closed: `WeilConjectures.integralExceptionalSupport_exists`.

Original holes retained, both attached to
`def-pur-adic-exceptional-system-realization`:

- `WeilConjectures.integralExceptionalCoordinates_properties`.
- `WeilConjectures.integralExceptionalInverseImage_on_ctf`.

Original holes: 3. Closed: 1. Added: 0. Remaining: 2. No split-off statements.
The remaining declarations retain their original statements and full proof plans.

## No longer needed

Removed the direct proof import of
`Sheaf.NumberTheory.Padics.AdicLimitFiniteModules` and the corresponding direct
node dependency `lem-pod-adic-limit-finite-modules`: the shared arithmetic lemma
uses `Padic.nonunit_coefficient_stages` instead. That module remains a transitive
dependency of the latter theorem and is not withdrawn. No module or declaration
is pruned. All other original dependencies remain needed.

## Where the brief, the DAG or earlier work was wrong

The specialized etale exceptional-adjoint theorem is phrased for the integer ring
of a coefficient extension field; this module instead uses a universe lift of the
original integer ring. Those presentations are not definitionally equal. The
generic Brown and evaluation proofs require only completeness, regularity and
finite prime-power-torsion quotients, so they apply directly after proving these
properties for the lifted ring. The integral finite-Tor comparison still needs
the reduction-limit adjunction, the normalized effectivity argument and the
compact-support comparison recorded in its original proof plan.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
