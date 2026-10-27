## Worker report

The module `Sheaf.AlgebraicGeometry.MaximalPointBlowupGeneratedCohomology` states
`AlgebraicGeometry.subsingleton_moduleCohomology_one_maximalPointBlowup_of_generated`.
Its sole proof is `sorry`, as required for stage 2. No definition, new node,
dependency repair, or mathematical statement correction is needed.

Source read: `literature/stacks-project/resolve.tex`, lemma-cohomology-of-blowup,
Tag 0AGS, lines 568–658, especially clause (3) and its globally generated paragraph.
The source explicitly permits arbitrary quasi-coherent modules and arbitrary sets
of global generators. The item is the globally generated case, not the additional
case where F(1) is globally generated. The latest blueprint unit
`sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` was also read; this
node is an internal principalization prerequisite, not that unit's statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `(A : Type u) [CommRing A] [IsRegularLocalRing A]` is the regular local ring
  (A,m). Mathlib's class includes localness, Noetherianity and equality of the
  maximal ideal's minimal number of generators with the Krull dimension.
- `hdim : ringKrullDim A = 2` is precisely dimension two, in `WithBot ℕ∞`.
- `IsLocalRing.residue A : A →+* ResidueField A` is the canonical quotient by m.
  Consequently `(Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))).ker`
  is the quasi-coherent maximal-ideal sheaf on Spec A, with its reduced closed
  point scheme structure. Mathlib's `IsLocalRing.ker_residue` identifies the
  ring kernel with m, and `Scheme.Hom.ker_of_isAffine` identifies the ideal sheaf
  kernel with the ring kernel on the affine base. `.blowup` is exactly the
  recorded global blowup, not an arbitrary scheme or a separately chosen model.
  The map b is implicit in this canonical blowup, whose `.blowupMap` is b; it
  does not occur separately in the hypothesis or conclusion.
- `F : (...).ker.blowup.Modules` is an O_Y-module on precisely that Y.
- `[F.IsQuasicoherent]` is quasi-coherence alone. In particular the recorded
  dependency's conjunction `IsQuasiCoherentFiniteType` is not imposed: its
  module publicly exposes Mathlib's exact quasi-coherence class.
- `hgen : Epi (F.freeHomEquiv.symm (id : F.sections → F.sections))` is the
  canonical evaluation epimorphism. `SheafOfModules.free` is the coproduct of
  structure modules indexed by `F.sections`; `freeHomEquiv.symm` sends each
  basis generator to the corresponding section. `F.sections` is the family of
  compatible sections on every open, canonically the sections on the terminal
  open Y, so this is precisely the index Γ(Y,F) in the node. Epimorphism means
  surjectivity as a sheaf morphism, not surjectivity on every open's sections.
- `Subsingleton ((RingedSpace.moduleCohomology Y.toRingedSpace 1).obj F)` is
  H¹(Y,F)=0. This cohomology is the right-derived global sections in O_Y-modules
  required by the node, not abelian-sheaf Ext or a new Cech cohomology definition.
  The cohomology object is a module and already has zero, so `Subsingleton` is
  exactly vanishing.

Dependency declarations read and used:

- `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`, whose
  public imports provide Mathlib `IsRegularLocalRing`. The node's ring clause
  is explicitly its `mathlib_match` in `Mathlib.RingTheory.RegularLocalRing.Defs`.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`.
- `def-nagata-global-blowup`: `WeilConjectures.Blowup.Gluing`,
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup`; its full signature and
  gluing-data definition were read.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`, publicly
  exposing `SheafOfModules.IsQuasicoherent` (all three node clauses are
  exposed by the current dependency module, and only its first clause is needed).
- `def-sc-ringed-space-module-cohomology`:
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`,
  `AlgebraicGeometry.RingedSpace.moduleCohomology`.
- Added existing, already recorded statement dependency
  `def-weil-pbc-generating-sections`:
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`,
  `SheafOfModules.GeneratingSections`, whose `epi` field uses exactly the
  `freeHomEquiv.symm` interface used here. The canonical all-sections family
  is specified directly; no second global-generation definition is introduced.

The proof docstring reproduces all five DAG steps: specializing the chart
package; splitting overlap Laurent coefficients; identifying sections of the
free sheaf on the affines; lifting and splitting coefficients of F; computing
Cech degree one. Every already-stated proof dependency is imported privately,
including the Mathlib spectrum-dimension, restriction and tilde interfaces.
`lem-sfb-point-blowup-local-chart-package` has no recorded Lean declaration
in the read DAG; it is needed only for the postponed proof and no fake interface
is supplied or assumed in the statement. No other proof import was omitted.

Edge cases checked before writing:

- No finite-generation, finite presentation or coherence assumption occurs.
  Infinitely many global sections are allowed: the index is their entire type.
- The zero module satisfies the evaluation epimorphism condition and has zero
  H¹; using all sections also includes its zero section without choosing a
  nonempty set of generators as an extra assumption.
- No choice of parameters, algebraically closed residue field, excellence,
  characteristic restriction, or equicharacteristic restriction occurs.
- Dimension zero and one, including the degenerate field blowup, are excluded
  by exactly the stated dimension-two hypothesis, not by an added domain
  assumption. The domain property is a consequence used only in the proof.
- `universe u` and `A : Type u` cover every ring universe. The scheme, module
  values, global-section index and module cohomology all use that universe;
  no unrelated test-object universe or finite index is imposed.
- Evaluation is sheaf-surjective, which is essential: globally generated does
  not mean the evaluation map is sectionwise surjective on every open.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "A globally generated quasi coherent module on the
  blowup of the maximal ideal of a two dimensional regular local ring has zero
  first Zariski cohomology"`: eight hits on cotangent H1, tilde stalks and qcqs
  localization; no blowup vanishing theorem.
- `msearch.py ... loogle '"blowup"'`: zero hits.
- `msearch.py ... leansearch "A globally generated quasi coherent module on a
  regular surface maximal ideal blowup has vanishing first cohomology"`: eight
  cotangent, quasi-coherence and module-freeness hits; no matching theorem.
- `msearch.py ... grep 'blowup|globallyGenerated|globally_generated'
  AlgebraicGeometry`: zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for global generation and
  evaluation found the existing Mathlib free/generating-section interface used
  throughout the project, and separate etale global-generation predicates.
  Those etale predicates describe a different coefficient sheaf and site.
- `rg` for this node id in `lean/WeilConjectures`: no declaration. The chosen
  theorem name also has no hit in either library or `dag/lean_names_upstream.json`.
- `rg` over `dag/nodes` for global generation found the existing
  `def-weil-pbc-generating-sections`, which is reused and added to `stmt_deps`.
  `tools/blueprint_refs.py search 'globally generated'` returned only the four
  etale/coefficient global-generation nodes, not this vanishing theorem.
- Read the existing `localSurfaceMaximalBlowupCenter` construction in
  `Sheaf.AlgebraicGeometry.LocalSurfaceMaximalBlowupGeometry`: its body is the
  exact residue-map kernel expression used directly here. No duplicate helper
  definition is introduced.

The module compiled cleanly with `scompile.py` against the live server build
(sandbox 2.4 seconds; module 2.5 seconds). The final dependency-import adjustment
is checked again by the prescribed dry run and delivery.

## Second reading by Q02

On a second pass I reopened the node, source and final theorem signature.
The dispatcher forbids starting another agent; this is this worker's second
reading, with the independent review left to the maintainer. The main potential
mismatches were checked explicitly: finite-type quasi-coherence versus arbitrary
quasi-coherence, arbitrary free epimorphism versus the specified canonical
all-sections evaluation, and abelian-sheaf versus module-sheaf cohomology.
The final file uses respectively `[F.IsQuasicoherent]`, `freeHomEquiv.symm id`,
and `RingedSpace.moduleCohomology`, so none of these mismatches remains.
The centre is the reduced maximal-ideal closed point via the canonical residue
map, the dimension equality is exactly two, and vanishing is the entire H¹
module being a subsingleton. No statement correction or disputed clause remains.
