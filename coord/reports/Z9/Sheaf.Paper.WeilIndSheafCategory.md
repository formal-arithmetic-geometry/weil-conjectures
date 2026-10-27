## What changed

Filled seven of the eight existing proof bodies in
`Sheaf.Paper.WeilIndSheafCategory`. All original public signatures, public imports,
definitions, and target statements are preserved. Added proved private helpers for
presheaf realization of the Ind extension, its adjunctions and exactness, the
explicit small fixed-pair model, and Frobenius equivalence.

The normalized Ind square follows from uniqueness of left Kan extensions; its
Yoneda components are the specified inverse Kan units. Heart abelianness is
transported along the explicit carrier equivalence. Frobenius equivalence uses
`isomorphismFieldTransport`, with inverse t-exactness supplying essential
surjectivity on the heart. Inverse-image adjunction and exactness lift through the
existing IsoAlgebra interfaces. Open extension is obtained from a common-stage
heart adjunction, lifted to Ind and then to fixed pairs using the invertible
inverse mate, and compared to the specified adjoint by uniqueness.

One new source lemma isolates the exact common-stage open-heart adjunction before
Ind or Frobenius structures. It has a full source proof in its docstring and a
matching DAG node. The item node records the actual proof route. No source-library
file or another group's module is changed. Elaboration-only changes and consumer
checks are recorded in `coord/changes/Z9-weil-ind-proof-inference.md`.

## Proved and sorry left

Original holes closed:

- `WeilConjectures.zlWeilHeart_abelian`.
- `WeilConjectures.zlIndSquare_existsUnique`.
- `WeilConjectures.zlIndFrobenius_exact`.
- `WeilConjectures.zlIndWeilPull_isLeftAdjoint`.
- `WeilConjectures.zlIndWeilPull_isRightAdjoint`.
- `WeilConjectures.zlIndWeilPull_exact`.
- `WeilConjectures.zlIndWeilOpenShriek_exact`.

The original hole `WeilConjectures.zlPullComp_existsUnique` remains, with its
unchanged statement and source proof, node `def-zl-weil-ind-sheaf-category`.
One hole is added: `WeilConjectures.commonStageOpenHeartAdjunction`, node
`lem-zl-common-stage-open-heart-adjunction`, in
`Sheaf.Paper.CommonStageOpenHeartAdjunction`.

This is seven original holes closed and one added. The open-extension part is a
decomposition: the parent contains the proved Ind adjunction, inverse-mate,
fixed-pair, and adjoint-comparison arguments. It is not seven independent complete
proofs from already stated dependencies. No hole is inside a definition or private
helper. Imported dependencies retain their previously recorded holes.

## No longer needed

No original public import is removed. The node originally had no proof steps or
proof dependencies to prune. No module or declaration is withdrawn, and the unit
route is preserved. No source-library declaration is removed or replaced.

The proof does not import `Sheaf.Paper.CommonStageWeilShriek` or
`Sheaf.Paper.CommonAdicOpenSectionData`: both reach this item and would form an
import cycle. They are not claimed as pruned modules; other consumers need them.
The longer Frobenius route using common-stage identity and composition is
unnecessary: the existing isomorphism-field transport API gives the equivalence.
Exploratory compositor imports and helpers are absent from the delivery.

## Where the brief, the DAG or earlier work was wrong

The item node originally has an empty proof plan. Its reviewed-proof metadata says
four holes had been closed by G7, but the restored source has all eight holes; this
delivery starts from the current source and reconstructs seven proofs. The
quarantine/rework record is preserved; absence from a build was not treated as
withdrawal authorization.

The common open-extension interfaces either import this item or require
separatedness of the schemes over the field. The item assumes only finite type,
so neither supplies the required theorem directly. The new heart lemma retains
the nonseparated case and adds no hypothesis to the item.

For the retained compositor obligation, rational naturality was implemented and
checked by tensor induction. The common-stage descent and original-stage unit
normalization attempts encountered expensive dependent elaboration of the chosen
stage system. Those incomplete attempts remain only in scratch files. This
partial delivery retains the original named hole and adds no renamed compositor
obligation. The seven other proofs compiled together in the profiling scratch
module; the final delivery modules are checked again by lcompile and deliver3.

## New nodes

`lem-zl-common-stage-open-heart-adjunction` states exact extension by zero as a
left adjoint to the fixed common-stage heart restriction. It involves neither Ind
objects nor Frobenius pairs. Its source proof follows finite-level exact open
extension, normalized Roos reconstruction, rational localization, and common-stage
descent. Empty and identity opens, zero objects, and nonseparated finite-type
schemes were checked as edge cases.

Change record: `coord/changes/Z9-weil-ind-proof-inference.md`.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
