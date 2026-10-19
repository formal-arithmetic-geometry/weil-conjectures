## What changed

Filled all four proofs in `Sheaf.Paper.PurityDncFamilyIntrinsic`. The section-over-field
identity follows by associativity from the published, proved
`Scheme.Hom.deformationSpaceSection_deformationSpaceProj`. Over-morphism extensionality
gives the section/map identity. The geometric domain theorem reuses the already stated
`WeilConjectures.purityDncDomain`: its six clauses are definitionally the same, including
the underlying section despite the different proofs of its over-field equation.

The Picard assertion applies
`WeilConjectures.PurityFiniteSetting.sectionInvariantIntrinsic_invertible` to the actual
projection and section. Its instances come from the domain theorem, the published
separatedness/quasi-compactness instances, and `purityDncCompactifiable`. The family is
exactly the defined object with the same compactification instance, so Lean accepts the
result directly, including finite-Tor membership and both tensor inverse isomorphisms.

The existing node `def-pur-dnc-section-family` now records these Lean realization steps.
Its geometric proof dependencies remain: those are still the proof obligations of the
existing `purityDncDomain`, which this delivery reuses. No statement, definition, public
import, hypothesis, universe, or target was changed. No consumer adaptation is needed.

## Proved and sorry left

Closed four of four original holes, all attached to `def-pur-dnc-section-family`:

- `WeilConjectures.purityDncIntrinsicSection_over`.
- `WeilConjectures.purityDncIntrinsicSection_comp_map`.
- `WeilConjectures.purityDncIntrinsicDomain`.
- `WeilConjectures.purityDncIntrinsicFamily_pic`.

Zero holes remain in the item; zero holes added; zero split-offs. The domain wrapper
uses the existing holed `purityDncDomain`; the Picard theorem also uses the existing
holed `purityDncCompactifiable` and `sectionInvariantIntrinsic_invertible`. These are
existing dependencies, not new assertions or globally completed geometric proofs.

The final module compiled without errors or warnings in 5.6 seconds using the required
remote `lcompile.py`. The delivery dry run additionally checks the delivery against the
current library.

## No longer needed

Removed these six unused proof imports from the item:

- `Sheaf.AlgebraicGeometry.DncAffineBlowupComplement`
  (`lem-pur-dnc-affine-blowup-complement`).
- `Sheaf.AlgebraicGeometry.EtaleLocalNormalForm`
  (`sbc-thm-etale-local-normal-form`).
- `Sheaf.AlgebraicGeometry.EtaleReesChart` (`lem-pur-dnc-etale-rees-chart`).
- `Sheaf.Paper.PurityFiniteSetting` (`def-pur-conventions`; already public through
  `PuritySectionInvariantIntrinsic`).
- `WeilConjectures.Blowup.Gluing` (`def-nagata-global-blowup`,
  `def-nagata-global-blowup-glue-data`, `def-nagata-global-blowup-local-model`).
- `WeilConjectures.Compactification.StrictTransform` (`def-nagata-strict-transform`).

The intrinsic wrapper needs none of these directly: it uses the existing geometric
domain interface and the section-invariant interface. No global node deletion is
claimed: the geometric nodes remain the plan for the existing `purityDncDomain`, and
some modules are also reached elsewhere or through public imports. No blueprint unit
statement or unit step is bypassed. No unused proof imports remain in the item.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The module repeated the six geometric domain clauses
already stated in `PurityDncFamily`, so no second geometric construction or proof is
necessary here. Its two section identities also follow from the published proved
identity without reopening affine augmentation calculations. The retained domain
hypotheses allow empty bases and varying relative dimension, exactly as before.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
