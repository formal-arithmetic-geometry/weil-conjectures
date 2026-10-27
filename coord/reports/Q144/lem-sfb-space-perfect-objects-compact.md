## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpacePerfectObjectsCompact` states
`AlgebraicGeometry.AlgebraicSpace.perfectObjects_compact`, with its only proof `sorry`.
The node statement is unchanged. There are no new definitions, new nodes, dependency
repairs, or statement faults. Source read: `literature/stacks-project/spaces-perfect.tex`,
Tag 09M8, `proposition-compact-is-perfect`, including its first proof paragraph; and
`section-spell-out`. The theorem docstring carries all six steps of the accepted DAG proof.

Hypothesis and clause correspondence:

- The size convention is the explicitly declared `universe u w`: schemes, section rings,
  module carriers, and coproduct index sets use `u`; derived localization morphisms use
  independent `w`. No equality between these universes is imposed. The standard small
  affine model has site object and morphism universes `u`, so applying perfectness at
  `.{u, u, u, w}` uses that model rather than identifying universes of the original site.
- The scheme S and algebraic space X over S are `{S : Scheme.{u}} (X : AlgebraicSpace S)`.
  Their existing definition includes the small etale site and regular-functions sheaf.
- Module sheaves and the unbounded derived category are the existing `X.SmallModules`
  and `X.DerivedModules`, under `[HasDerivedCategory.{w} X.SmallModules]`. This is the
  specified small affine ringed-model presentation of the same original module topos,
  via `X.smallModuleEquivalence`; no different coefficient ring or lift is substituted.
- The category C_X is precisely `X.DerivedQCoh`, the full subcategory defined by
  `X.derivedQCohProperty`. That predicate asks for `SheafOfModules.IsQuasicoherent` of
  every integer cohomology sheaf after the inverse model equivalence. Thus it is
  D_QCoh of the existing module category, rather than the derived category of QCoh.
- Quasi-compactness of |X| is `(hqc : CompactSpace (Point X.obj.obj))`, with the recorded
  point topology; this is the finite-subcover condition without a nonempty assumption.
- Quasi-separatedness is `(hqs : IsAbsolutelyQuasiSeparated X)`. Its full signature is
  the affine-test criterion: for all affine S-schemes U,V and maps h_U,h_V to X, their
  sheaf fibre product has compact point space. The definition's source is Tag 0AHR,
  where this is equivalent to quasi-compactness of the absolute diagonal. In particular
  S is not assumed quasi-separated and the relative diagonal alone is not substituted.
- An arbitrary ambient object is `(P : X.DerivedModules)`. Its perfectness hypothesis is
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
  X.smallStructureSheaf P`. The recorded predicate uses a representative which locally
  admits bounded complexes with degreewise finite-free retractions. Ranks and bounds
  can vary between covering objects; no global strict-perfect representative is assumed.
- The first conclusion is `hP : X.derivedQCohProperty P`, explicitly proving that the
  same ambient P has quasi-coherent cohomology. It is not assumed in the hypotheses.
- The next conclusion is `hcoprod : HasCoproducts.{u} X.DerivedQCoh`. Coproducts in C_X
  are supplied by the theorem, not assumed. This packages the coproduct existence used
  in the node and its proof step 1.
- The final conclusion is `@IsCompactObject.{u} X.DerivedQCoh _ _ hcoprod ⟨P, hP⟩`.
  The existing definition quantifies over every `I : Type u` and `E : I → C_X` and
  asserts `Function.Bijective` of `DirectSum.toAddMonoid` built from
  `Preadditive.rightComp K (Sigma.ι E i)`. This is exactly the canonical direct sum
  of Hom groups to Hom into the coproduct. Both the coproduct and Hom sets are those
  of C_X; no compactness in the whole ambient derived category is asserted.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`, its
  `EtaleSite`, `etaleTopology`, `structureSheaf`, and `Modules` (inherited through the
  recorded small-model calculus).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent abbreviation of Mathlib `SheafOfModules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `AlgebraicSpace.QCoh`
  and the retained Mathlib predicate `SheafOfModules.IsQuasicoherent` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory` (through the derived-module calculus).
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`,
  `IsLocallyStrictPerfectComplexOfUniverses`, and the recorded
  `StrictPerfectCoefficientRepresentationOfUniverses` interface. The item uses the
  predicate for an arbitrary derived object, not a choice of one bounded local model.
- `WeilConjectures.CategoryTheory.CompactObject`: `CategoryTheory.IsCompactObject`;
  the old example module under Sheaf is withdrawn, so the upstream declaration is used.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`:
  `AlgebraicSpace.DerivedModules`, `derivedQCohProperty`, `DerivedQCoh`;
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`:
  `SmallModules`, `smallStructureSheaf`, `smallModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `AlgebraicSpace.IsAbsolutelyQuasiSeparated`; its imported
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology` supplies `Point`'s topology.

The two already landed nodes `def-sfb-space-derived-module-calculus` and
`def-sfb-space-absolute-quasi-separated` are added to stmt_deps under the standing
permission to cite landed notions. The remaining stmt_deps are retained verbatim.
All stated proof-dependency modules are imported non-publicly; for the Mathlib
long-exact-sequence dependency its recorded `Mathlib.Algebra.Homology.HomologySequence`
module is imported. The three currently unstated proof dependencies
`lem-sfb-space-qcoh-kernels-colimits`, `lem-sfb-space-qcoh-extension-closed`, and
`lem-sfb-space-zeroth-hypercohomology-coproducts` have no module to import. Their
mathematical roles are preserved in the theorem docstring. They are not needed to
elaborate this stage-2 statement and are not silently assumed as hypotheses.

Edge cases checked before writing: empty space, zero perfect object, empty index set,
finite coproducts, unbounded E_i, covers with varying local bounds/ranks, arbitrary base
scheme including a non-quasi-separated S, and independent localization universe w.
There is no nonempty hypothesis on X or I and no boundedness hypothesis on the E_i.
The empty Hom direct sum and Hom to the zero coproduct are both zero groups, agreeing
with the required bijection. The zero local model is a bounded finite-free retract.

Searches for an existing statement (2026-10-24):

- `msearch.py leanfinder`, query “Perfect objects on quasi compact quasi separated
  algebraic spaces are compact in the derived category of quasi coherent modules”:
  8 results, all scheme/topological compactness statements, no derived-object result.
- `msearch.py leansearch`, query “A perfect complex on a quasi compact quasi separated
  algebraic space is compact in the category of complexes with quasi coherent cohomology”:
  8 results, scheme compactness/diagonal lemmas and a small-localized-Hom result;
  none is the algebraic-space perfect-to-compact assertion.
- `msearch.py loogle`, query `IsCompactObject`: zero results, unknown Mathlib identifier.
  Direct reading located the project's upstream definition and it is used unchanged.
- `msearch.py grep`, query `perfect.*compact|compact.*perfect`: zero Mathlib hits.
- `rg -n 'perfect.*compact|compact.*perfect|perfect_objects_compact'` in the named
  project algebraic-geometry directories: scheme compactness results, compact perfect
  generators and the weak-generator consumer, but no theorem for each perfect object
  of an algebraic space. `grep -rn 'lem-sfb-space-perfect-objects-compact'` in
  `lean/WeilConjectures` returned no declaration.
- `rg` for `DerivedQCoh`, `IsPerfectOnRingedSiteOfUniverses`, and
  `IsAbsolutelyQuasiSeparated` located the existing definitions above. DAG searches
  located their owning definition nodes. No definition was copied.

Validation: prescribed `scompile.py` compiled the delivered module in both sandbox and
library contexts on the server, with no errors and no unexpected warnings.

## Second reading by Q144

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
