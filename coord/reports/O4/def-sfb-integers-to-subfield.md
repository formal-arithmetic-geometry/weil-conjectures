## Worker report

Recorded `existing: true` for
`AlgebraicGeometry.ProEtale.padicIntegersToPadicSubfield` in
`WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`.
No new module or declaration is needed. The complete published source was read with
`scompile.py --source WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`:
the older local slopmaster2 checkout does not contain that module. The current declaration is
an `abbrev`, although the older audit describes it as a `def`; the recorded signature follows
the current source verbatim. There is no repair note for this item.

The blueprint sources read were `def-sfb-integers-to-subfield.md` and its proof in
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/` under
`sk-prop-sfb-qlbar-colimit-x/`, together with the point-inclusion definition under
`sk-thm-sfb-rationalization-comparison/`. The published definition says exactly what these
sources and the DAG item say.

Hypotheses and clauses:

- A prime ℓ is `(ℓ : ℕ) [Fact ℓ.Prime]` in the surrounding variable command.
- A finite subextension E of the algebraic closure of ℚ_ℓ is
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)`. Its definition in
  `WeilConjectures.CategoryTheory.RingObjects.EllAdic` is the subtype of
  `IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)` satisfying `FiniteDimensional ℚ_[ℓ] E`.
  Thus both the specified embedding and finiteness are retained.
- An arbitrary scheme is `(X : Scheme.{u})`; no noetherian, nonempty, finite-type, or
  quasi-compact hypothesis is imposed. The universe `u` is explicitly declared upstream.
- The ring of integers is the existing `PadicAlgCl.integers ℓ E.1` with its restricted
  topology, used by `Profinite.padicIntegersRingObj ℓ E.1`. Its construction was read in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`.
- The specified point map a is exactly
  `padicIntegersRingObjToContinuousMapRingObj ℓ E`, not an arbitrary ring map. Its body
  forgets the condensed ring inclusion to abelian sheaves. That inclusion is
  `continuousMapRingSheafMap (PadicAlgCl.integers ℓ E.1).subtype continuous_subtype_val`;
  on profinite test objects it postcomposes continuous functions with the inclusion.
- The formula φ = p_X^*(a) is the actual body
  `(upperStarFromPoint X).map (padicIntegersRingObjToContinuousMapRingObj ℓ E)`.
  The recorded dependency `sfbPullbackFromPoint X` unfolds to `upperStarFromPoint X`.
- The source is exactly
  `condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X`, namely O_{E,X}.
  The target is exactly
  `condensedRingObj (Profinite.continuousMapRingObj E.1) X`, namely E_X.
  Both are the recorded dependency's existing pulled-back coefficient construction.
- Being a morphism of ring objects is the inferred
  `IsMonHom (padicIntegersToPadicSubfield X ℓ E)`. Mathlib's
  `CategoryTheory.Functor.map.instIsMonHom` transports the specified point-map instance.
  `Functor.monObjObj` gives the unit and multiplication on precisely these objects;
  `Functor.mapMon` bundles this same morphism. The ambient category is
  `Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}` throughout.

Dependency declarations read and used:

- `sk-def-sfb-pullback-from-point`:
  `Sheaf.AlgebraicGeometry.ProEtalePointPullback`,
  `AlgebraicGeometry.ProEtale.sfbPullbackFromPoint` and its specification;
  the alias is exactly `upperStarFromPoint` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
- `def-sfb-integers-to-subfield-point`: its closed slopmaster2 audit supplies
  `AlgebraicGeometry.ProEtale.padicIntegersRingObjToContinuousMapRingObj` in
  `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`.
  Its full definition, docstring and `IsMonHom` instance were read. It needs no new record.
- `sk-def-sfb-pulled-back-coefficients`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`,
  `condensedRingObj` and `isCommMonObj_condensedRingObj`.
  Mathlib's `CategoryTheory.Functor.monObjObj`, `mapMon` and `map.instIsMonHom`
  were read in `Mathlib.CategoryTheory.Monoidal.Mon`.

Edge cases checked: the empty scheme is allowed by the unrestricted scheme binder;
E = ℚ_ℓ is the bottom finite intermediate field and is allowed; every prime, including 2,
is allowed. No positive-degree-extension restriction is imposed. Empty profinite test
objects cause no difficulty for the continuous-function inclusion. Scheme and site
universes are exactly those of the published dependencies, with coefficients in
`Ab.{u + 1}`; no equality of site object and morphism universes is added.

Searches made using `msearch.py N4 def-sfb-integers-to-subfield`:

- LeanFinder: "Pull back the inclusion of the ring of integers of a finite p-adic subfield
  into the field to ring objects on the pro-etale site of a scheme". Eight hits, including
  `BDeRhamPlus`, `BDeRham`, `Tilt`, `PreTilt`, and unrelated scheme declarations; no match.
- Loogle: `CategoryTheory.Functor.mapMon, CategoryTheory.Functor.mapMon_map_hom`.
  One hit, `CategoryTheory.Functor.mapMon_map_hom`, providing the generic underlying-map
  formula, not the project-specific construction.
- LeanSearch: "The inverse image of the inclusion of p-adic integers into a finite p-adic
  field is a morphism of ring objects on the pro-etale site of a scheme". Eight hits,
  including `PadicInt.Coe.ringHom`, `PadicInt.algebraMap_apply`,
  `PadicInt.isOpenEmbedding_coe` and `WittVector.toPadicInt`; no whole-item match.
- Mathlib grep: `padicIntegersToPadicSubfield|padicIntegersRingObjToContinuousMapRingObj|
  def mapMon|map.instIsMonHom` in `CategoryTheory/Monoidal`. Five hits in `Mon.lean`,
  giving only general monoidal machinery.
- `rg -n` for `padicIntegersToPadicSubfield`,
  `padicIntegersRingObjToContinuousMapRingObj` and the item id in the local upstream
  `WeilConjectures` and shared `lean` trees found no definition there. The explicit
  source lookup through `scompile.py --source` found the exact published definition.
  The same search in `dag/lean_names_upstream.json` found no entry. The item's audit and
  blueprint both name this declaration, and the current published source confirms it.

Validation: `scompile.py N4 def-sfb-integers-to-subfield scratchpad/Check.lean` compiled
cleanly against the published sources. The scratch file explicitly binds every universe
and variable and sets `autoImplicit false`. It checks the full types of both inclusions,
infers `IsMonHom` for the pulled-back inclusion, checks by definitional equality that the
formula uses `sfbPullbackFromPoint`, and checks by definitional equality that its bundled
map is `mapMon.map` between the two recorded `coefficientRing` objects. These are scratch
checks only; no theorem or proof is delivered. The delivery wrapper also checks the
recorded existing declaration in its own compile probe.

No statement correction, disputed statement, missing notion, or dependency repair was
needed. Only the item's `lean` field changes.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
