## What changed

Proved `WeilConjectures.IntegralExceptionalMapping.descendedHom_naturality`
without changing its statement or any definition. A proved private helper computes
the inverse descended Hom bijection: transpose through the source reconstruction
adjunction and the system adjunction, apply the target total-limit functor, then
postcompose with the inverse target unit. The target reconstruction triangle
cancels the inserted counit. The two naturality assertions follow from the
system adjunction's Hom naturality and the actual reconstruction unit/counit
naturality squares. The forward right-naturality assertion follows by applying
the inverse bijection and cancelling the two inverse pairs.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.IntegralExceptionalMapping.descendedHom_naturality`.
The private inverse formula is proved without holes. Added no holes and split off
no statements.

One original hole remains unchanged:
`WeilConjectures.IntegralExceptionalMapping.integralExceptionalDescendedCounit`
(node `lem-coef-integral-exceptional-descended-counit`). Its remaining content is
the comparison of the specified total mapping-complex construction with the
categorical descended adjunction, including the resulting unit and counit formulas.

## No longer needed

No DAG node or module is withdrawn. The existing six-step route and unit are
retained. The proved naturality assertion uses only the categorical adjunctions,
full inclusions, and isomorphism facts already present in `Domains`; it needs no
additional proof-dependency imports.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The latest blueprint's integral Brown-adjoint unit
contains a short compactification/adjoint assertion; the detailed six-step
mapping-complex comparison is in the accepted DAG and existing declaration
comment. No equality of total derived maps was inferred from equality of finite
projections. Identity maps, zero objects, and empty schemes require no additional
hypothesis in the naturality calculation: it uses only category laws and the
supplied adjunction identities.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
