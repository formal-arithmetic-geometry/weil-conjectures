## Worker report

The module `lean/Sheaf/AlgebraicGeometry/SerreCriterionAffineness.lean` states
`AlgebraicGeometry.Scheme.isAffine_of_finiteType_ideal_h1_zero`, with proof `sorry`.
No definitions, extra nodes, dependency replacements, or statement corrections are needed.

Hypothesis and conclusion correspondence:
- “Let X be a scheme”: `(X : Scheme.{u})`, for an explicitly bound arbitrary universe u.
- “X is quasi-compact”: `[CompactSpace X]`, compactness of the underlying scheme space.
- “X is quasi-separated”: `[QuasiSeparatedSpace X]`, quasi-compact intersections of
  quasi-compact opens. Neither hypothesis imposes separatedness or a Noetherian condition.
- “for every quasi-coherent sheaf of ideals I ⊆ O_X”: `∀ I : X.IdealSheafData`.
  Mathlib's compatible affine-local ideal data encode precisely quasi-coherent ideals;
  the source module `IdealSheaf.Module` realizes this as the actual submodule `I.toModules`,
  the kernel of O_X → (i_I)_* O_{V(I)}, with inclusion `I.toModulesι` and the stated
  affine-sections identification. No additional quasi-coherence hypothesis is necessary.
- “of finite type”: `I.toModules.IsFiniteType →`, using the same Mathlib finite-type
  predicate as the dependency pqf-def-coherent; this is finite type, not coherence or
  finite presentation.
- “H^1(X,I)=0”: `IsZero ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I.toModules)`.
  This is zero as an object of ModuleCat, equivalent to the cohomology module vanishing.
- “Then X is affine”: `IsAffine X`, equivalent to X being isomorphic to Spec of a ring.

Dependencies read and used:
- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `.Hom`; full signatures and docstrings read.
- pqf-def-coherent: `Sheaf.AlgebraicGeometry.Coherent`, declaration
  `AlgebraicGeometry.RingedSpace.IsCoherent`, whose module explicitly identifies the
  quasi-coherent and finite-type clauses with Mathlib's
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`. Only the latter
  is needed explicitly, because IdealSheafData already encodes quasi-coherence.
- pqf-def-cohomology: `Sheaf.Paper.PQFCohomology`, declaration
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`; its cohomology functors are
  `RingedSpace.moduleCohomology`, from `Sheaf.Topology.RingedSpaceModuleCohomology`.
  Their full definitions and docstrings were read; this is module-valued derived global
  sections, not the source's abelian-sheaf Ext cohomology.
- Ideal modules: `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`,
  `AlgebraicGeometry.Scheme.IdealSheafData.toModules` (full construction read).

Source checked: https://stacks.math.columbia.edu/tag/01XG, Lemma 30.3.2.
It agrees with the node hypothesis by hypothesis. The local literature/stacks-project
checkout is absent on this machine, so the cited primary source was opened online.
The theorem docstring carries both proof steps of the node: directed unions of finite-type
subideals and cohomology commuting with those colimits, then the quasi-compact criterion 01XF.

Edge cases checked before drafting: the empty scheme is allowed (affine as Spec of the zero
ring); the zero ideal and unit ideal are both quantified over; there is no nonempty or
nonzero restriction, no base field or characteristic condition, and no Noetherian or
finite-presentation hypothesis. On an affine scheme all quasi-coherent ideals have vanishing
positive cohomology, consistent with the statement. Quasi-separatedness does not require
separatedness. Universes are explicitly bound and the ideals live in the scheme universe.

Searches (actual service calls recorded in searches.jsonl):
- LeanFinder: “A quasi compact quasi separated scheme is affine if first cohomology
  vanishes for all finite type quasi coherent ideals”: eight hits on quasi-affineness,
  quasi-separatedness and affine-limit results, none the cohomological criterion.
- Loogle: `AlgebraicGeometry.IsAffine, AlgebraicGeometry.Scheme`: twelve hits on affineness
  and its elementary properties; none the criterion.
- msearch grep: `serre|Serre|isAffine_of.*[hH]` in Mathlib/AlgebraicGeometry: twenty-five
  hits on affineness under morphisms/limits, none the cohomological criterion.
- LeanSearch: “Serre affineness cohomology ideals”: service unavailable, Internal Server Error.
- rg in WeilConjectures and lean/Sheaf: `serre|Serre|pqf-lem-serre-criterion` found Serre
  duality, vanishing, and ring-theoretic criteria; no affineness criterion or duplicate name.
- rg for `toModules` located the existing ideal-module construction in the source; rg for
  `class IsFiniteType` and `class IsQuasicoherent` located Mathlib's definitions.

No statement dispute or node fault found. Server compilation and delivery preflight are
run with the prescribed tools; the second reading is reserved for the independent reader.

## Second reading by C1

Node statement checklist against `SerreCriterionAffineness.lean`:

- The scheme object is `(X : Scheme.{u})`, with `u` explicitly bound.
- Quasi-compactness is the typeclass hypothesis `[CompactSpace X]`.
- Quasi-separatedness is `[QuasiSeparatedSpace X]`.
- The quantified object is `I : X.IdealSheafData`, Mathlib's quasi-coherent ideal-sheaf data for `X`; its associated O_X-module is `I.toModules`.
- Finite type is the implication hypothesis `I.toModules.IsFiniteType`.
- First cohomology vanishing is `IsZero ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I.toModules)`.
- The conclusion is `IsAffine X`.

The quantifier and implication order agrees with the node: for every ideal datum, finite type implies vanishing, followed by affineness. No field, characteristic, Noetherian, separatedness, finite-presentation, or nonemptiness assumptions occur. Empty and zero schemes, zero and unit ideals, and `n = 0` cases are not excluded; the only index is the literal natural number `1`. The ideal data and module cohomology use the same scheme universe `u`.

I read the dependency records and declarations: `AlgebraicGeometry.Scheme` from Mathlib, `AlgebraicGeometry.RingedSpace.IsCoherent` from `Sheaf.AlgebraicGeometry.Coherent`, and `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages` from `Sheaf.Paper.PQFCohomology`; the latter records `RingedSpace.moduleCohomology`, whose definition was also checked. I read the existing `Scheme.IdealSheafData.toModules` construction in `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`; it is the kernel ideal sheaf and is not a private replacement. Searches recorded in `searches.jsonl` (LeanFinder, Loogle, grep/msearch, LeanSearch, and repository `rg`) found no existing Serre affineness criterion. The Stacks source Tag 01XG was checked directly and has exactly the three hypotheses and affine conclusion rendered above.

No mismatch was found, so no source, statement, dependency, or module repair was necessary. The module compiles cleanly with the prescribed compiler; its only proof is the required `sorry`.
