## What changed

Proved `SheafOfModules.torAmplitude_iff_exists_bounded_flat_model` with its original
signature and all public imports unchanged. The proof compares the live tensor with
categorical derived tensor using `wfSiteDerivedTensor_first`, then applies the proved
source `DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat`. Its construction
uses the same bounded flat resolution, flat-opcycles criterion, and lower truncation
as the original plan. Site object and morphism universes stay independent.

Added the proved theorem
`SheafOfModules.nonempty_monoidalClosed_independentCoefficients` to the unclaimed
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`. It exposes existence
of its already constructed private closed structure, without exporting private data
or changing any existing signature, definition body, or instance. The private
`monoidalClosed_kfi` changes from `@[instance_reducible]` to
`@[no_expose, irreducible]` to keep the adjunction implementation behind that API
and prevent reduction during elaboration. Its existing blueprint
node is `lem-pc-sheaf-modules-tensor-closed`. The new public import supplies the type
in this theorem's signature. Change record:
`coord/changes/M5-independent-closed-tensor-api.md`.

Both modules compile together through `lcompile.py --all` against the current server
build: the supporting module took 24.8 seconds and the item 12.4 seconds after the
irreducibility repair. The proof also shares graded tensor and derived monoidal
instances explicitly. Mathematical data and construction are unchanged. Earlier dry
runs passed compilation and preflight but deferred timed-out axiom probes to merge;
the final delivery reruns these checks. Independent review checks consumer and
signature effects.

## Proved and sorry left

Closed 1 of 1 holes:
`SheafOfModules.torAmplitude_iff_exists_bounded_flat_model`
(node `lem-sp-ringed-site-tor-flat-model`). Added 0 holes; split off 0 holes.
No `sorry` remains in either delivered module. The new closed-structure theorem is proved.
The existing `SheafOfModules.wfSiteDerivedTensor_first` is a stated dependency still
containing `sorry`; it is unchanged and no new assumption is introduced.

## No longer needed

Removed these proof imports:

- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`
- `Sheaf.Algebra.Homology.KFlat`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
  (the current name of the former `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`)
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `Sheaf.Algebra.Homology.BoundedFlatReplacement`
- `Sheaf.Algebra.Homology.SiteFlatOpcyclesTorCriterion`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The item no longer directly needs nodes `lem-pur-quasi-iso-cone-acyclic`,
`lem-pc-tensor-mapping-cone-iso`, `lem-pc-bounded-above-flat-kflat-site`,
`lem-pc-kflat-bounded-flat-replacement`, `lem-weil-pbc-site-flat-opcycles-tor-criterion`,
`lem-weil-pbc-site-derived-tensor-descent`, or `def-pc-tensor-complex-sheaves`.
The source generic flat-model theorem already proves the bounded K-flatness,
flat replacement, and opcycles/truncation steps. The live first-variable tensor
comparison already states the cone-based computation. The abstract derived category,
K-flat predicate, flatness, closed tensor, and t-structure nodes remain needed.

Removed obsolete tool approvals for `lem-weil-pbc-site-derived-tensor-descent`,
`lem-pc-bounded-above-flat-kflat-site`, `lem-pc-kflat-bounded-flat-replacement`, and
`lem-weil-pbc-site-flat-opcycles-tor-criterion`. These are direct dependency removals;
shared/public dependencies may continue to reach some of the modules transitively.
No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The closed tensor construction `monoidalClosed_kfi` packages the internal-Hom
adjunction. Concealing its implementation with `@[no_expose, irreducible]` and exposing the
proved existence proposition supplies the interface needed by the generic argument. The
completed packet compiles below the unchanged per-file limit. A later uncached compile
exposed repeated derived-tensor instance reconstruction; naming the graded tensor and derived-monoidal instances alone did not reliably
meet the limit. Making the closed structure irreducible produced a clean 12.4-second
compile without profiling or altered limits. The source library
already contains the full categorical flat-model argument. The specialized site replacement and opcycles
interfaces equate site universes and therefore do not directly fit this item's
signature; using the existing generic proof avoids rewriting them. The private
independent-universe closed structure only needed a proved public existence API.

Consumer check: the unchanged `DiagramKFlatReplacements` fails with a duplicate
`SheafOfModules.IsFlat` import against both the published baseline and the delivered
overlay. This is not caused by the closed-structure repair. The unchanged
`RingedInternalHomExactRestriction` exceeded 60 seconds against the overlay; the
same 60-second timeout occurs against the published baseline. Neither consumer is changed in this delivery.

No statement changes, new nodes, hollow definitions, or new axioms.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
