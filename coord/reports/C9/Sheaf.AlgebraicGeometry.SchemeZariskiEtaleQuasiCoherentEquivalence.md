## What changed

Proved the three foundational helper theorems in
`Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence` without changing
any declaration signature, definition, instance attribute, public import, or universe.

`smallEtaleModulePresheaf_isSheaf` glues ring maps elementwise using the existing
set-valued regular-function sheaf theorem. Separatedness proves that the glued
function preserves zero, one, addition and multiplication, and gives uniqueness.
`smallEtaleModuleOverHasWeakSheafify` transports Mathlib's small-universe additive
sheafification along `Scheme.Etale.overEquiv V`, which identifies the slice with
`V.left.Etale`. `smallEtaleModuleOverWEqualsLocallyBijective` transfers the
corresponding local-bijection criterion along the inverse equivalence. Its
cover-preservation hypothesis comes from the existing dense-subsite instance.

The three new private proof imports are `Mathlib.AlgebraicGeometry.Sites.AffineEtale`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`, and
`WeilConjectures.AlgebraicGeometry.Sites.Ga`. There are no new
modules or DAG nodes. Empty schemes and empty charts require no extra hypotheses:
both sheaf transport results apply to every chart, and preserve section universe u.

Validation: `lcompile.py` compiled the final module successfully in 21.9 seconds.
The three included `#print axioms` checks each report exactly `propext`,
`Classical.choice`, and `Quot.sound`; none depends on `sorryAx`.

## Proved and sorry left

Closed three of the original four holes, with no holes added:

- `AlgebraicGeometry.Scheme.Modules.smallEtaleModulePresheaf_isSheaf`.
- `AlgebraicGeometry.Scheme.Modules.smallEtaleModuleOverHasWeakSheafify`.
- `AlgebraicGeometry.Scheme.Modules.smallEtaleModuleOverWEqualsLocallyBijective`.

The single remaining hole is the unchanged theorem
`AlgebraicGeometry.Scheme.Modules.scheme_zariski_etale_quasiCoherent_equivalence`,
node `lem-trf-scheme-zariski-etale-quasi-coherent-equivalence`. This is a partial
proof delivery, not a decomposition: zero holes are split off.

## No longer needed

Removed the following private imports, which are unused by the definitions,
statements and completed helper proofs:

- `Mathlib.AlgebraicGeometry.Modules.Tilde`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`.
- `WeilConjectures.AlgebraicGeometry.EtaleQuasiCoherentDescent`.
- `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`.
- `WeilConjectures.AlgebraicGeometry.Descent`.
- `WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`.
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`.
- `WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`.

No DAG dependency or module is claimed globally unnecessary. The existing main
proof plan is retained because its theorem remains unfinished. In particular,
removing these unused imports does not withdraw any source-library declaration.
The public imports stay verbatim.

## Where the brief, the DAG or earlier work was wrong

The main theorem's planned proof dependencies cannot currently be imported by
this module. `tools/import_direction.py may` rejects
`Sheaf.AlgebraicGeometry.EtaleExtensionFreePresentationsHom`: it already reaches
this module through `Sheaf.AlgebraicGeometry.ZariskiEtaleTensorSections`, whose
public import supplies `ZariskiEtaleModuleContext` and the other constructions.
`Sheaf.TraceFormula.ZariskiEtaleFunctorComparisonSquare` likewise uses that
construction layer. Thus these declared dependencies are mathematically
available but not directly usable here without a separate construction-layer
refactoring and corresponding consumer/node updates. This delivery leaves that
larger refactoring and the main theorem intact, and closes the three independent
helper holes instead, as allowed for a module with several holes.

The affine-site and slice-equivalence APIs already supply the small-universe
sheafification construction described in the helper docstrings; no new
existence assumption or arbitrary witness is required.

The generic `Presheaf.isSheaf_comp_of_isSheaf` cannot be applied directly to
forgetting commutativity in universe u on this site: it asks for preservation
of limits with an object index in universe u+1. Elementwise gluing avoids that
size restriction.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
