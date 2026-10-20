## What changed

Proved all twelve holes of `Sheaf.AlgebraicGeometry.StandardGroupSchemes`, preserving
all existing declaration signatures, visibility and definition bodies. Constructed the
additive, roots-of-unity and Frobenius-kernel Hopf algebras from the displayed coordinate
maps, and used Mathlib's affine Hopf spectrum construction for their group laws.

The two coordinate quotients are surjective and respect counit and comultiplication;
monoidal naturality of `algSpec` proves the group homomorphism property. Their spectra
are closed immersions. The prime binomial identity verifies relative Frobenius respects
addition. The quotient's pushout universal property, transported through `algSpec`,
identifies alpha with the scheme-theoretic Frobenius kernel, respecting its inclusion.

Named private helpers prove the needed generator calculations and universal property.
The node's proof now records this route. No new mathematical nodes are introduced.

## Proved and sorry left

Closed all 12 holes, in namespace `AlgebraicGeometry.StandardGroupSchemes` and node
`def-sc-gm-ga`:

- `additiveGroup_existsUnique`
- `rootsRelations`
- `rootsGroup_existsUnique`
- `alphaRelations`
- `alphaGroup_existsUnique`
- `rootsCoordinate_inverse`
- `rootsLaurent_commutes`
- `quotient_surjective`
- `roots_isClosedSubgroupScheme`
- `alpha_isClosedSubgroupScheme`
- `frobenius_isMonHom`
- `alpha_isFrobeniusKernel`

Holes added: 0. Holes remaining: 0. No statements split off. Every private helper is
proved, and no data definition contains a hole. The relation checks allow the zero
coordinate target algebra; the roots construction includes n=1. No perfectness or
reducedness hypothesis is introduced.

## No longer needed

Removed proof imports `Mathlib.Algebra.CharP.Frobenius` and
`WeilConjectures.Mathlib.Algebra.CharP.Lemmas`; the narrower
`Mathlib.Algebra.CharP.Lemmas` supplies the prime binomial identity directly. The proof
uses neither `iterateFrobeniusOfPrime` nor an explicit tensor-product presentation of
the kernel: the quotient pushout universal property proves the pullback directly.
All public imports and declared mathematical dependency nodes remain used. No module
is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. Uniqueness is implemented with `GrpObj.ext`
and `MonObj.ext`: multiplication determines the remaining group structure. Named private
Hopf constructions avoid repeating their expansions. An explicit equality identifies
the two presentations of the tensor map before applying monoidal naturality; this
avoids expensive definitional comparison through chosen limit objects.

An earlier interrupted sandbox report claimed completion before the final four proofs
were written; this report supersedes it. All twelve are now present and compiled.

Resumed validation on 2026-10-20: comparison against the current sources confirms
that all existing signatures, visibility, public imports and definition bodies are
unchanged. The fresh single-file compile passed in 10.4 seconds. The required
`deliver3.py --no-push` completed successfully, including its declaration axiom
probe and server preflight; its review class is CODEX because the node proof record
is updated. The earlier interrupted delivery attempts made no push.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
