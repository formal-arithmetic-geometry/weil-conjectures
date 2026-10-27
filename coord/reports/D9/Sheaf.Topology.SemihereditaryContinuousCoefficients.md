## What changed

Proved `Profinite.semihereditary_continuous_coefficients_admissible` without changing
its signature, public imports, or existing definitions. Added private proof imports
of `Sheaf.RingTheory.SemihereditaryFiniteFreeSubmodule` and
`Sheaf.RingTheory.SemihereditaryTorsionlessFlat`, and Mathlib's double-complex,
module short-complex, and finite-ideal-image APIs.

The proof follows all four existing DAG steps. Finitely generated projective ideals
are finitely presented by Mathlib. For a finitely presented module, its presentation
as a finite-free quotient gives a finitely generated kernel, projective by the
existing finite-free-submodule theorem. A private two-term construction, adapted
from the already proved private construction in
`ScalarPerfectCohomologyAndPidModels`, supplies the actual bounded finite-projective
complex and proves its augmentation is a quasi-isomorphism. Evaluation embeds all
continuous functions into the full product, so the existing torsionless-flat
theorem applies. Evaluation at the point supplies the stipulated ring equivalence.

For t-admissibility, the private section-ring comparison proves that the
reconstructed section multiplication is pointwise, using
`Sheaf.μ_comp_map_mul`. Projectivity of finitely generated ideals is transported
along evaluation at the terminal object. The same finite-presentation and
finite-projective resolution arguments apply at the scalar-ring universe. The
canonical scalar restriction map is explicitly factored through the constant
function map and the section-ring equivalences, proving its flatness.

Read Hemo--Richarz--Scholbach, Definition 6.1 and Lemmas 6.7(1), 6.10, including
their proofs, and the current blueprint unit. The unit route is preserved. All
new helpers are private and proved; there are no new objects selected by unproved
existence assertions.

## Proved and sorry left

Closed the one original hole:
`Profinite.semihereditary_continuous_coefficients_admissible`.
Added zero holes; zero holes remain in the delivered module. This proof uses the
existing named theorems
`Submodule.projective_of_finite_of_projective_ideals` and
`Module.Flat.of_injective_pi_of_projective_fg_ideals`, whose existing holes remain
in their own modules and are not claimed as proved here. No results are split off.

## No longer needed

None. Every declared proof dependency is used, and the original DAG plan is
unchanged. No module or node is withdrawn, and no public import is removed.
The proof-only imports added here are all used.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The scalar identification in the last DAG
step requires proving compatibility with the reconstructed section-ring
multiplication, not simply treating its ring structure as definitionally equal to
the pointwise one. This comparison is proved privately in this module. Empty
profinite sets and the zero ring cause no exception: evaluation into an empty
product remains injective, and the two-term construction covers rank zero.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
