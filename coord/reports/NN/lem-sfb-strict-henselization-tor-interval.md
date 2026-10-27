## Worker report

The module `Sheaf.RingTheory.StrictHenselizationTorInterval` states
`DerivedCategory.torAmplitudeIn_iff_strictHenselization`, with its sole proof `sorry`.
The node changes only in `lean`. There are no new definitions, extra nodes,
dependency repairs, statement corrections, or disputed statements.

Source read: `literature/stacks-project/flat.tex`, Tag 0DK0,
`lemma-tor-amplitude-up-down-henselization`, statement and proof (lines 243–312).
The node is exactly the equivalence (1) with (3) at the closed point of Spec R;
its five proof steps are carried in the declaration's docstring.

Hypothesis and clause correspondence:

- Local commutative R: `(R : Type u) [CommRing R] [IsLocalRing R]`.
- Its residue field k: the canonical `IsLocalRing.ResidueField R`, with no
  separately chosen field or unidentified residue-field isomorphism.
- A separable closure K of k: `(K : Type u) [Field K]`,
  `[Algebra (IsLocalRing.ResidueField R) K]` and
  `[IsSepClosure (IsLocalRing.ResidueField R) K]`. Mathlib's class requires
  separable closedness of K and separability over k; separability implies
  algebraicity, so this is the stated separable closure.
- The structural R-action on K is `[Algebra R K]` and
  `[IsScalarTower R (IsLocalRing.ResidueField R) K]`; the tower says this is
  the residue quotient followed by the chosen field embedding.
- The strict henselization is `(B : Type u) [CommRing B] [Algebra R B]`
  with `_presentation : Algebra.StrictHenselizationPresentationIn.{u, u} R K B`.
  This is the recorded universal pointed-etale colimit presentation, with
  its specified algebra identification, not an arbitrary strictly henselian algebra.
- Unbounded derived categories: `[HasDerivedCategory.{u} (ModuleCat.{u} R)]`
  and the analogous B binder choose the localizations in the stated size
  convention. Their existence is standard for module categories; they impose
  no condition on the rings or the complexes. All rings and modules are in a
  common arbitrary universe u, matching the dependency's common-universe
  convention. There is no independent smaller universe for test modules.
- Arbitrary L over B: `(L : DerivedCategory (ModuleCat.{u} B))`. There is no
  boundedness, pseudo-coherence, finite generation, or descent datum on L.
- The integers and their ordering: `(a b : ℤ) (_hab : a ≤ b)`.
- Clause (1): `torAmplitudeIn (ModuleCat.{u} R) a b
  ((ModuleCat.restrictScalars.{u} (algebraMap R B)).mapDerivedCategory.obj L)`.
  The scalar restriction is the exact canonical module restriction along
  the structural algebra map, descended to unbounded derived categories.
- Clause (2): `torAmplitudeIn (ModuleCat.{u} B) a b L`.
- Equivalence, with the original order of the two clauses: `↔`.

The public upstream definition `DerivedCategory.torAmplitudeIn` was read in
`WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`: it is
`∀ F : C, homologyConcentratedIn a b (M ⊗ (singleFunctor C 0).obj F)`.
Thus the tests are exactly every degree-zero module. Its tensor is the K-flat
derived tensor, with the derived monoidal structure fixed by localization,
not an arbitrary monoidal structure. `homologyConcentratedIn` is the canonical
t-structure's `IsGE a ∧ IsLE b`; `DerivedCategory.isGE_iff` and `isLE_iff`
identify this with vanishing of all homology objects below a and above b.
Consequently this predicate renders both full vanishing clauses, including
all integer degrees outside the inclusive interval.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q` (def-weil-abstract-derived-category).
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`:
  `CategoryTheory.MorphismProperty.kFlat` (def-pc-module-kflat-complex).
  The derived tensor uses the existing K-flat localization framework; no
  replacement predicate or tensor is defined in this module.
- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`:
  `IsSepClosure.exists_intermediateField_mem` (def-pd-separable-closure),
  whose docstring explicitly identifies the underlying notion with Mathlib's
  `IsSepClosure`; the class definition in Mathlib was also read.
- `Sheaf.RingTheory.StrictHenselizationPresentationIn`:
  `Algebra.StrictHenselizationPresentationIn` (def-sc-ring-strict-henselization).
- `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`:
  `DerivedCategory.torAmplitudeIn` and the imported
  `DerivedCategory.homologyConcentratedIn`.
- `WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange`:
  the existing exact derived restriction interface. Its specialized abbrev
  `ModuleCat.derivedRestrictScalars` is definitionally the
  `(ModuleCat.restrictScalars f).mapDerivedCategory` used here.

All recorded proof-dependency modules are imported privately, with their
current source signatures and proof docstrings read:
`WeilConjectures.Algebra.Homology.TorAmplitudeFlatModel`
(`DerivedCategory.module_torAmplitudeIn_iff_exists_flat_model`),
`Sheaf.RingTheory.StrictHenselizationModuleFlatness`
(`Module.flat_iff_strictHenselization`),
`Sheaf.Algebra.Homology.SubcategoryLeftResolution`
(`CochainComplex.exists_subcategory_left_resolution`),
`WeilConjectures.Algebra.Homology.BoundedFlatKFlat`
(`CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat`), and
`WeilConjectures.Algebra.Homology.FlatOpcyclesTorCriterion`
(`Module.Flat.opcycles_of_exactAt`). The definition dependencies that also
occur in `proof_deps` retain their public imports.

Edge cases checked before writing: L = 0 makes both predicates hold;
a = b is the single-degree flat-model case, with both endpoints retained;
negative a and b are unrestricted integers; already strictly henselian R
reduces the equivalence to scalar restriction along an algebra isomorphism.
Arbitrary rank modules and non-Noetherian local rings are included. A complex
not descending along R to B is included since L is bound directly in D(B).
No boundedness is assumed: only either side of the equivalence implies it.
There is no empty indexing set, chosen resolution, or finite-rank restriction
in the signature. The zero ring is excluded precisely by the source's local
ring with residue field hypothesis, not by an additional assumption.

Searches executed on 2026-10-24 using the prescribed msearch.py wrapper:

- LeanFinder: "A complex over the strict henselization of a local ring has the
  same Tor amplitude over the local ring and over its strict henselization".
  Eight hits, concerning formal smoothness, HenselianLocalRing, and unramified
  ring maps; none gives this derived interval equivalence.
- Loogle: "DerivedCategory.torAmplitudeIn, ModuleCat.restrictScalars".
  Zero hits; diagnostic `unknown identifier 'DerivedCategory.torAmplitudeIn'`
  because this is a project declaration rather than a Mathlib declaration.
  The project source was read directly instead.
- Mathlib grep: `(henseli[sz]|Henseli[sz]).*(Tor|amplitude)|(Tor|amplitude).*(henseli[sz]|Henseli[sz])`.
  Zero hits.
- Local `rg` for that same expression over `lean/WeilConjectures` and
  `lean/Sheaf` found only unrelated strict-local log-chart first Tor and
  cohomological-dimension files. Searching the exact item id found no Lean
  attachment. Searching `dag/lean_names_upstream.json` and both source roots
  for `torAmplitudeIn_iff_strictHenselization` found no collision. A broader
  `torAmplitudeIn` / derived-scalar-restriction search located the reused
  upstream interfaces above.

Validation: prescribed scompile.py compiled both the module-mode sandbox
and the library-named file cleanly, 8.7 s and 1.7 s respectively; no errors
or warnings were printed. `set_option autoImplicit false` and explicit
`universe u` ensure every variable and universe is bound. Delivery dry-run
and final delivery are run after writing this report.

## Second reading by NN

This is the dispatcher's single-worker delivery; no separate agent was
started. The maintainer supplies the independent review. The worker's final
rereading checked the source and actual signature clause by clause: the
strict-henselization presentation is the recorded one; the same L is used
on both sides; restriction is along `algebraMap R B`; every module in the
common universe is tested in degree zero; the interval endpoints and its
ordering are preserved; no descent, boundedness or finiteness condition was
added. No mismatch was found and no statement correction was made.
