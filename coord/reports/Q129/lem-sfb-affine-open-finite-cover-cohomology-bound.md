## Worker report

The module `Sheaf.AlgebraicGeometry.AffineOpenFiniteCoverCohomologyBound` states
`AlgebraicGeometry.subsingleton_moduleCohomology_of_affine_open_finite_cover`.
Its sole theorem has proof `sorry`; no definitions, extra hypotheses, dependency
repairs, new nodes, or statement corrections are introduced.

Clause-by-clause correspondence:

- An affine scheme Y: `(Y : Scheme.{u}) [IsAffine Y]`.
- Its arbitrary open subscheme U: `(U : Y.Opens)`, with induced scheme `U.toScheme`.
- A nonnegative integer s: `(s : ℕ)`. Naturals encode exactly the nonnegative
  integers used for the finite cover size and for right-derived functor degrees.
- A cover by s opens of U: `(V : Fin s → U.toScheme.Opens)` and
  `(hcover : iSup V = ⊤)`. The indices 0 through s-1 relabel 1 through s.
- Every member is affine: `(hV : ∀ i : Fin s, IsAffineOpen (V i))`.
- An arbitrary quasi-coherent O_U-module: `(F : U.toScheme.Modules)
  [F.IsQuasicoherent]`. There is no finite-type or coherence hypothesis.
- Every integer p at least s: `(p : ℕ) (hp : s ≤ p)`. Since s is nonnegative,
  this covers exactly the stated range, including degree zero when s=0.
- H^p(U,F)=0: `Subsingleton ((RingedSpace.moduleCohomology
  U.toScheme.toRingedSpace p).obj F)`. This is the vanishing of the underlying
  module, equivalently the zero cohomology group; the module has a zero element.
- The empty cover is included: `Fin 0` is empty and its supremum is bottom;
  `hcover` forces U to be empty. There is no nonempty-index binder.
- No field, Noetherian, finite-type, minimal-cover, nonempty-open, or positive-degree
  hypotheses occur.

Statement dependencies read and used:

- `def-pc-scheme`: Mathlib.AlgebraicGeometry.Scheme, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom`; affineness and affine opens from
  Mathlib.AlgebraicGeometry.AffineScheme, `IsAffine` and `IsAffineOpen`.
  `Scheme.Opens.toScheme` is the actual restriction scheme, as defined in
  Mathlib.AlgebraicGeometry.Restrict.
- `pqf-def-coherent`: the recorded Sheaf.AlgebraicGeometry.CoherentFiniteType
  publicly exposes Mathlib's `SheafOfModules.IsQuasicoherent`. This predicate is
  used directly, rather than the stronger `IsQuasiCoherentFiniteType` conjunction.
  `Scheme.Modules` is Mathlib's category of sheaves of modules.
- `def-sc-ringed-space-module-cohomology`:
  WeilConjectures.Topology.RingedSpaceModuleCohomology,
  `AlgebraicGeometry.RingedSpace.moduleCohomology`, whose data is the right-derived
  functor of `RingedSpace.globalSectionsFunctor` on module sheaves.

All stated proof dependencies are imported with ordinary, non-public imports:
Sheaf.CategoryTheory.RingedSiteModules (`ringedSiteModules`),
Mathlib.AlgebraicGeometry.Morphisms.Proper (`IsProper`, `IsSeparated`),
Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion (`IsClosedImmersion`),
Mathlib.AlgebraicGeometry.Morphisms.Affine (`isAffineHom_diagonal_iff`),
Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction (the recorded
tensor-pullback interface), WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
(`Scheme.Modules.isQuasicoherent_pullback`),
WeilConjectures.AlgebraicGeometry.OpenRestrictionModuleCohomology
(`nonempty_openRestriction_moduleCohomology_iso`),
WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
(`subsingleton_openModuleCohomology_of_isAffineOpen`), and
WeilConjectures.Topology.ModuleMayerVietoris (`RingedSpace.module_mayerVietoris`).
The statement-dependency modules already import the scheme and cohomology
definitions also listed among proof dependencies. The full five-step DAG proof
is supplied in the theorem docstring, following coherent.tex lines 590-627.

Edge cases checked by reading the statement and the source proof:
s=0,p=0 forces empty U and vanishing of all sections, hence of all degrees;
s=1,p=1 is affine vanishing; s=2,p=2 is the Mayer--Vietoris induction step with
degree-one intersection cohomology. Repeated or empty cover members, nonminimal
covers, U empty with a positive cover size, Y=Spec(0), F=0, and U=Y are admitted.
No independent small universe for test schemes or covers is introduced: `u` is
explicit, and `Fin s` enumerates any finite family of the specified size.

Searches performed on 2026-10-24:

- msearch.py LeanFinder: "Quasi coherent cohomology vanishes in degrees at least
  the size of a finite affine open cover". Eight hits, including
  `QuasicoherentData.coversTop`, eventual-zero sections on limits, and
  `CategoryTheory.Sheaf.H`; none state this module-cohomology bound.
- msearch.py Loogle: `"cohomology", "affine"`. Zero hits.
- msearch.py grep of Mathlib:
  `(affine|Affine).*(cohomolog|Cohomolog)|(cohomolog|Cohomolog).*(affine|Affine)`.
  Zero hits.
- msearch.py LeanSearch: "Quasi coherent module cohomology vanishes above the
  number of affine opens of a finite cover". Eight hits concerning
  quasi-coherence definitions and quasi-compact covers; no exact theorem.
- rg of lean/WeilConjectures and lean/Sheaf for finite-cover bounds, affine
  cohomology, and the exact node/declaration names. The exact node and proposed
  declaration have no match. Related declarations inspected in full:
  `Scheme.Modules.subsingleton_H_of_card_le` in
  WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Vanishing requires a
  nonempty finite set and concerns an abelian sheaf's cohomology; the private
  `finite_affine_cover_cohomology_bound` in
  WeilConjectures.AlgebraicGeometry.ProjectiveTwistFiniteCohomology uses
  `Scheme.Modules.H`, also abelian-sheaf cohomology. Neither is the exact public
  right-derived module-cohomology statement including the empty cover. Other
  matches concern étale cohomology or unrelated finiteness theorems.

Validation: prescribed scompile.py compiled the delivered file in sandbox and
library module modes, both cleanly (4.4 and 4.3 seconds). No warnings were emitted.
No mathematical statement fault or unresolved dispute was found.

## Second reading by Q129

A separate second pass by this worker reopened the node and the final module;
no other agent was started, as the dispatcher explicitly prohibits that.
The maintainer supplies the independent review. This pass checked that the open
family lives on U, that F is an O_U-module rather than a module on the ambient Y,
and that the conclusion is the recorded module cohomology rather than
`Scheme.Modules.H` or `Sheaf.H`. It checked the binder `[F.IsQuasicoherent]`
against the dependency's public predicate, without adding finite type, and
checked s≤p rather than s<p. `Fin s` and `iSup V = ⊤` retain the empty cover;
no index nonemptiness or p>0 slips in. Every variable and universe is explicitly
bound. All five proof steps and the needed proof imports are present. No mismatch
was found and no signature change was necessary after compilation.
