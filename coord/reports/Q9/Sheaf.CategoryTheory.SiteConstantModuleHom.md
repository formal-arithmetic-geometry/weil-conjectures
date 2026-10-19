## What changed

Proved `CategoryTheory.siteConstantModule_hom` in
`Sheaf.CategoryTheory.SiteConstantModuleHom`, retaining its exact signature and the
three existing public constructions. New private helpers construct the canonical
constant-Hom presheaf map, extend it using Mathlib's module sheafification hom
bijections, prove its unit formula, and prove two-variable naturality by the
sheafification universal property. Local injectivity uses finitely many generators;
local surjectivity uses the existing finite-presentation lifting theorem.
The locally bijective criterion on additive sheaves and reflection through
`SheafOfModules.toSheaf` prove that the comparison is an isomorphism.
The slice formula is evaluation of the unit formula.

Validation on the current compile server: the generalized lifting module, the assigned
module (19.2 seconds), and the unchanged direct consumer
`Sheaf.CategoryTheory.SiteConstantModuleHomSurjective` (2.1 seconds) all compile cleanly.
The theorem signature and the three existing public definition bodies are unchanged.
An explicit `#print axioms CategoryTheory.siteConstantModule_hom` check reports only
`propext`, `Classical.choice`, and `Quot.sound`.

Generalized `Sheaf.CategoryTheory.FinitePresentationLocalLift` from one universe to
independent site object, site arrow, and coefficient universes; its construction,
explicit theorem text and proof are unchanged. This avoids duplicating the existing
finite-presentation lifting argument. Updated the item's proof plan/dependencies and
the helper node's Lean note. Change record:
`coord/changes/constant-module-hom-local-lift-universes.md`.

Mathlib searches used LeanFinder, Loogle, and grep; no exact arbitrary-site
internal-Hom theorem was found. The useful existing APIs were
`PresheafOfModules.homEquivOfIsLocallyBijective`,
`PresheafOfModules.restrictHomEquivOfIsLocallySurjective`, and
`Sheaf.isLocallyBijective_iff_isIso`.

## Proved and sorry left

Closed the sole original hole: `CategoryTheory.siteConstantModule_hom`
(node `lem-pur-site-constant-module-hom`). No holes added, no split-offs, and
no `sorry` remains in either delivered Lean module.

The generalized `CategoryTheory.finitePresentation_linearLiftSieve_mem`
(node `lem-sf-finite-presentation-local-linear-lift`) retains its original complete proof.
All private helpers are proved, and every data definition is constructed explicitly.

## No longer needed

Removed proof imports:

- `Sheaf.CategoryTheory.SiteConstantModuleHomInjective`;
- `Sheaf.CategoryTheory.SiteConstantModuleHomSurjective`;
- `Sheaf.CategoryTheory.SiteConstantModuleUnit`;
- `Sheaf.CategoryTheory.LocalModuleHom`;
- `Sheaf.Paper.SiteSheafificationSectionsLocal`;
- `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`;
- `Mathlib.CategoryTheory.Sites.CoverLifting`.

Removed proof dependencies and their obsolete top-level tool-use entries:

- `lem-sf-constant-module-hom-locally-injective` and
  `lem-sf-constant-module-hom-locally-surjective`: their single-universe comparisons
  do not apply to the assigned theorem's independently sized site; the proof now
  works on the recorded upstream internal Hom directly, with the same finite
  generator argument and the generalized existing local linear lifting theorem.
- `lem-sf-local-module-hom-sheaf`: `SheafOfModules.homObj` already supplies its sheaf
  structure; the additional set-valued local-Hom construction is unnecessary.
- `lem-sf-constant-module-unit-locally-bijective`: Mathlib's existing `toSheafify`
  instances supply the local bijectivity for the actual unit at the required universes.
- `lem-pc-sites-sheafification-underlying-sets` and
  `lem-weil-pbc-site-sheafification-sections-local`: module sheafification's linear
  hom equivalences already perform the scalar extension and separatedness argument.
- `lem-weil-pbc-site-constant-restriction`: the formalized localization clause is
  directly the unit formula at V.left, evaluated at the identity slice object.

These modules/nodes are unnecessary for this item's proof; other independent
import paths may still use them. All original public imports are preserved.
The unit route is unchanged: this still proves the constant-model calculation
used by lisse-morphism rigidity in `sk-prop-a1-inv`.

## Where the brief, the DAG or earlier work was wrong

The declared local Hom injectivity/surjectivity and unit interfaces identify the
site object, site arrow, and coefficient universes, whereas the assigned theorem
explicitly allows two independent site universes. They cannot be applied directly.
The finite-presentation lifting argument has no such restriction; generalizing its
section variables suffices and does not change any mathematical assertion.

The scalar gluing step is already implemented in Mathlib's linear sheafification
API, so reproducing it is unnecessary. The stated localization conjunct follows
from the first conjunct and the definitions; no separate restriction isomorphism
is needed for this particular formal statement.
The unchanged theorem docstring records the original proof plan; the updated DAG
node records the implemented proof and its smaller dependency list.

Tool failure in earlier attempts: two delivery dry runs failed during worktree
creation when `git checkout --detach origin/sheaf-dag` exceeded the tool's
600-second timeout. The normal command was retried, and the same exception
recurred. Neither dry run reached preflight; nothing was pushed. A
`tools/downstream.py` invocation was killed without output and was retried.
The resumed session reran the downstream command successfully; it confirms the
existing `SiteConstantModuleHomSurjective` module is the only pre-existing direct
importer/user of the lifting lemma. All three sandbox modules compile against
current sources, including that unchanged consumer. The 2026-10-19 resumed session completed the required delivery dry run successfully
(commit `62165f7b7f`), including compilation and preflight. A fresh `lcompile.py --all`
check also accepted all three sandbox modules against the current compile cache.
No launcher or project tool was modified.

On this resumption, `lcompile.py --all` again accepted all three retained modules.
The required downstream check again found exactly the unchanged direct consumer
listed above. Source comparison confirmed that the assigned theorem's signature
and its three original public construction bodies are identical to current sources.

Edge cases checked in the argument: zero source, zero target, the zero ring, empty
finite generating/relation sets, the empty site, and empty covering sieves. Finite
intersections include the empty intersection, and equality is obtained using
separatedness on the actual covering sieve without a nonempty-cover assumption.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
