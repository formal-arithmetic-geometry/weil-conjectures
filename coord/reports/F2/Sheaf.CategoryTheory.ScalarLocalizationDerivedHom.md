## What changed

Proved `CategoryTheory.scalarLocalization_exact` and
`CategoryTheory.scalarLocalization_derivedHom`, preserving their complete signatures.
Exactness follows from sectionwise flatness, the change-of-rings/tensor comparison,
and the ordinary extension/restriction adjunction. For derived Hom, descend that
ordinary adjunction along quasi-isomorphisms, apply the existing normalized
localization telescope and relative Hom telescope, identify the resulting colimit
with localized fractions, and verify linearity and all five compatibility clauses.
All additional proof helpers are private and fully proved.

Moved the six existing coefficient-action declarations, with unchanged types, bodies,
attributes and public names, into
`Sheaf.CategoryTheory.ScalarLocalizationCoefficientActions`. The item publicly
re-exports them. Redirected the single coefficient import in
`ScalarLocalizationModuleColimit`, `ScalarLocalizationTelescopeCore`, and
`ScalarLocalizationUnderlyingTelescope` to that lower module. This removes the cycle
that would otherwise prevent the Hom proof from importing its telescope dependency.
The existing coefficient-action node now points to its own module; no new node was
introduced. The proof node records the implemented argument. The underlying telescope
also explicitly imports the statement dependencies formerly exposed through the Hom
module.

Validation: the complete five-module packet compiles with no warnings; the item
takes 34.6 seconds. The six moved declaration bodies and the two public comparison
definitions were checked against the current source and are unchanged.
Both unchanged consumers `KoszulFibreLinearDescent` and `RationalTermHomComparison`
also compile against the packet without warnings (5.9 and 57.2 seconds). Their
temporary check copies are excluded from delivery.

The relocation and consumer inventory are recorded in
`coord/changes/F2-scalar-localization-coefficient-module.md`.

Repaired the return on head `1db3d114173`: added the omitted
`Sheaf.CategoryTheory.KoszulFibreLinearDescent` consumer to the change record's
`## Users`, recording its unchanged use of `scalarLocalizationCoefficientLinear`
through the public re-export. Refreshed the inventory to include all six downstream
modules and their current claim status. Rebased the two node copies on the current
source, preserving newer review and audit metadata.

Repaired the landing return on head `38284f10586`. The change record remains at
`coord/changes/F2-scalar-localization-coefficient-module.md` in this packet.
`tools/batch_land.py` maps reviewer fixes for change records by the suffix
`.change.md`: any further reviewer correction must therefore be named
`F2-scalar-localization-coefficient-module.change.md` in the fix directory.
The rejected fix filename lacked that suffix; the delivered record itself was
present. Refreshed the record's consumer inventory against the current source.
The delivery tool rebases this packet onto current `sheaf-dag` before pushing.
The five-module packet compiles on the server without warnings; the item takes
30.9 seconds. Both original holes remain closed and no holes were added.
The current unchanged consumers `RationalTermHomComparison` and
`KoszulFibreLinearDescent` also compile against the packet without warnings
(55.9 and 5.6 seconds). Their check copies stay outside the delivery's `lean/` tree.

## Proved and sorry left

Closed both original holes:

- `CategoryTheory.scalarLocalization_exact`.
- `CategoryTheory.scalarLocalization_derivedHom`.

There are zero remaining holes in the item, zero holes added elsewhere, and zero
split-off statements. The new coefficient module and the three adapted telescope
modules also contain zero holes. The proof uses existing declared dependencies;
this delivery does not claim to close their remaining holes.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.

The direct proof no longer needs `lem-pur-derived-change-of-rings`,
`lem-pur-sheaf-ring-derived-coefficient-adjunction`,
`lem-pc-sites-module-sheafification-tensor`, or
`lem-weil-pbc-ringed-site-module-sheafification-exact`. Ordinary exact adjunction
localization replaces the K-flat derived-adjunction route; sheafification-flatness
and the change-of-rings/tensor comparison replace the planned exactness argument.
The obsolete top-level `tool_uses` approvals removed are
`lem-pur-sheaf-ring-derived-coefficient-adjunction`,
`lem-pur-derived-change-of-rings`, and
`lem-pc-sites-module-sheafification-tensor`.

`lem-weil-pbc-exact-functor-derived-functor` is no longer a direct proof dependency,
but remains part of the statement's exact-functor interface. No module is withdrawn:
other consumers and dependencies can still need these modules.

The refreshed DAG's `lem-weil-pbc-scalar-localization-sheaf-exact` and
`def-weil-exact-derived-adjunction` are also unnecessary as direct proof dependencies:
the item proves exactness and constructs the localized ordinary adjunction directly.
These nodes and their modules remain available to other consumers.

## Where the brief, the DAG or earlier work was wrong

The proposed K-flat coefficient-adjunction construction is unnecessary for these
already exact functors: Mathlib's localization of an ordinary adjunction supplies
the required derived adjunction and its normalized unit. The original placement of
coefficient definitions in the Hom module created a circular dependency with the
existing telescope proof. Their relocation resolves that structural issue without
changing any mathematical definition or statement. No disputed statement was found.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
