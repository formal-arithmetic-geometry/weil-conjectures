## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.space_picard_obstruction_natural`
in `Sheaf.AlgebraicGeometry.SpacePicardObstructionNatural`. Its proof is `sorry`.
The two supporting definition modules retain actual rings, ideals, line-class quotients,
units, chart restrictions, exact-sequence classes and ordinary tensor pullback.
No existing statement, target, proof plan or definition is changed. The item's only
changes are its Lean record and added statement dependencies. No statement correction
or STATEMENT-DISPUTED flag is needed.

Clause-by-clause correspondence:

- Base scheme and algebraic spaces: `{S : Scheme.{u}}` and `X X' Y Y' : AlgebraicSpace S`.
  The reduced spaces in the node are called `X` and `Y` in Lean, and the thickened
  spaces `X'` and `Y'`.
- Square-zero closed immersion: `IsSpaceFirstOrderThickening i` and similarly `j`.
  This is the recorded scheme-test predicate, requiring first-order closed immersions
  after every scheme base change. A square-zero kernel already has full support;
  no additional topological condition is assumed.
- The actual ideal and its quotient module action: `T : ThickeningSiteModel i` and
  `I : SquareZeroIdeal T`, whose natural injective inclusion has image the actual
  quotient kernel, has square-zero products, and satisfies the quotient scalar law.
  The theorem first supplies these presentations and their units sequence for every
  thickening. It also supplies a units sequence for every specified such presentation;
  callers do not have to assume its existence.
- Quasi-coherence: `I.obj.IsQuasicoherent`, using the recorded Mathlib predicate via
  `AlgebraicSpaceQuasiCoherentModule`. On the affine etale scheme slices this is the
  module-associated-sheaf condition in the node. The first clause supplies a QC ideal;
  all assertions about specified ideals retain their stated QC hypothesis. Same for K.
- Picard group: the existing `RingedSitePicard.Pic X.smallStructureSheaf` is the
  quotient of actual rank-one line modules by module isomorphism, not ring Picard
  groups or H1 renamed as Picard. The quantified `c X : Comparison.{u,u} ...` supplies
  its tensor group law and generator-extension-normalized additive H1 equivalence.
  Its defining `IsComparison` fixes both the zero line and tensor addition.
- Etale module and additive cohomology: the existing small affine etale ringed model
  is equivalent by literal restriction to the original small etale ringed site.
  `picardIdeal I` is `SheafOfModules.toSheaf` applied to `smallModuleRestriction I.obj`.
  `Sheaf.H (picardIdeal I) 2` is the existing global Ext cohomology
  Ext^2(constant integers, additive ideal), hence right derived global sections.
  All section and coefficient universes remain u; no lift, scheme restriction, or
  imposed equality between distinct universes occurs.
- Canonical obstruction homomorphism: `E.obstruction (c X)` is an `AddMonoidHom`
  from the existing Picard quotient with the tensor group law to that H2. Its data
  are the explicit composite of `c.comparison.toAddMonoidHom` and Yoneda
  `E.exact.extClass.postcomp ...`. `E.inclusion_value` fixes j to 1+j;
  `E.projection_value` fixes the actual quotient. Thus neither boundary nor sign
  is arbitrary, and no choice from bare existence is used to define its data.
- Kernel equals image: for every representative `M : Line X.smallStructureSheaf`,
  `E.obstruction (c X) (lineClass M) = 0` iff there is a line N on X' with
  `Nonempty ((smallModuleTensorPullback i).obj N.val ≅ M.val)`.
  Every class has a representative, so this is exactly the stated kernel-image
  equality, expressed without inventing a second Picard pullback map.
- Arbitrary square: `h : Y ⟶ X`, `h' : Y' ⟶ X'` and `j ≫ h' = h ≫ i`.
  There is no `IsPullback`, `Flat`, smoothness, finite-type, Noetherian or
  separatedness hypothesis.
- Canonical module coefficient map h-star I to K: the theorem supplies the unique
  `β : (moduleTensorPullback h).obj I.obj ⟶ K.obj` satisfying
  `IsPicardModuleIdealMap`. On every compatible lifted chart its ideal inclusion
  sends a local tensor a tensor m to r times the pullback of I(m), for every lift
  r of a. Square-zero K makes this independent of the lift. These are the original
  recorded module tensor functor and its recorded unit-normalized tensor sections.
- Additive inverse-image form of that map: `P : PicardAbInverse h` has an exact
  additive inverse image adjoint to the fixed fibre-product direct image. Its
  integer comparison preserves 1 on every compatible chart. The unique α satisfies
  `IsPicardIdealMap`, namely the same actual pullback of included ideal functions
  on every compatible lifted chart. Hence α and β are the additive and tensor-adjoint
  forms of the same structural coefficient map; neither is freely chosen.
- Pullback on H2: `Sheaf.H.map α 2 (P.cohomology (picardIdeal I) 2 ...)`.
  `P.cohomology` is exact-functor transport on Ext precomposed with the
  section-1-normalized integer isomorphism. This is the canonical derived global
  sections pullback followed by the specified coefficient map.
- Naturality for every line: for every M there is a line N whose underlying module
  is isomorphic to `(smallModuleTensorPullback h).obj M.val`, and the final equality
  is `E'.obstruction (c Y) (lineClass N) = H2(α)(h-star(E.obstruction ... M))`.
  Since classes are the isomorphism quotient, it applies to every representative
  of the pulled-back line. E and E' are universally quantified presentations of
  the fixed normalized units sequence, so the result does not depend on choosing
  one presentation or resolution.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `structureSheaf`, `Modules`, `IsLineModule` and their chart definitions.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`; imported as the node's scheme-line dependency.
  Space lines use their recorded space/ringed-site definitions, not this scheme
  predicate applied to a space.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`: `SmallEtaleModel`,
  `smallEtaleInclusion`, `smallStructureSheaf`, `smallModuleRestriction`,
  `smallModuleEquivalence`, with their actual regular-function signatures.
- `Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData`: `ThickeningSiteModel`,
  `IsSpaceFirstOrderThickening`; `SpaceSquareZeroStalkData`: `SquareZeroIdeal`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleChart`,
  `moduleTensorPullback`, `moduleTensorSection`, `moduleTensorAdjunction`;
  `SpaceDerivedTensorPullback`: the existing `smallModuleTensorPullback`.
- `Sheaf.CategoryTheory.Sites.RingedSitePicardData`: `Line`, `Pic`, `lineClass`,
  `Comparison`, `IsComparison`, `units`, `integers`, `integerOne`, and the
  existing `RingedSitePicard.pullback` formula used as the model of our specialized
  exact-functor Ext pullback.
- `Sheaf.CategoryTheory.Sites.RingedSitePicardH1Natural`: `picard_h1_natural`,
  whose full signature and generator/structural-map normalization were read.
- `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap` publicly retains the enlarged
  site declarations in `EnlargedEtaleRingedSite`: `enlargedRestriction`,
  `enlargedDirectImage`, `enlargedChartLift`, and restriction comparisons.
- `AlgebraicSpaceQuasiCoherentModule` and `AlgebraicSpaceQuasiCoherentAlgebra`:
  Mathlib's `SheafOfModules.IsQuasicoherent` and the existing `commStructureSheaf`.
- Existing Mathlib `Sheaf.H`, `Sheaf.H.map`, `Ext.postcomp`, `Ext.precomp`,
  `Functor.mapExtAddHom`, `ShortComplex.ShortExact.extClass`, and
  `hasExt_of_enoughInjectives` provide the homological constructions.

The stated proof dependencies are imported: `SiteCoveringAxioms`,
`HorseshoeDeltaFunctor`, `RingedSitePicardH1Natural`, `SiteCohomologyPullback`,
and the enough-injectives Mathlib module. The enlarged site model is already public
through the supporting module. `lem-sfb-space-first-order-ringed-description` has
no Lean record or Mathlib match in the read repository, so there is no recorded
module to import. It is needed only for the postponed proof. The theorem explicitly
states existence of its normalized thickening/ideal presentations as part of this
node's units construction; it does not hypothesize that unstated result.

Sources checked: Stacks `spaces-more-morphisms.tex`,
`lemma-picard-group-first-order-thickening` (0DNM), including the exact sequence
and proof using 1+j; `spaces-properties.tex`, `lemma-functoriality-etale-site`
(03G2), `remark-explain-equivalence` (03H7); `sites-cohomology.tex`,
`lemma-h1-invertible` (040E). No change to the source statement is necessary.

Edge cases checked mathematically before finalizing the signature:

- Empty spaces and zero ideals remain allowed. Units and line classes are their
  actual sheaf definitions; no nonempty or positive-rank-global-sections binder
  excludes the empty site/space. For a zero ideal the obstruction target is zero
  and the kernel criterion gives restriction-surjectivity.
- Identity thickenings are allowed. The units sequence and both coefficient
  normalizations reduce to their identity/zero-ideal formulas.
- Any characteristic is allowed, including characteristic 2. The inverse 1-j
  and multiplication law use J squared zero and no integer inversion.
- The vertical map can be nonflat, and the square need not be Cartesian. Exactness
  in `PicardAbInverse` concerns abelian inverse image, never module tensor pullback.
- Lifting quotient units is only locally surjective. `PicardUnitsSequence.exact`
  is sheaf short exactness, not global section-surjectivity.
- Arbitrary QC ideals and all line classes are retained; no finite-generation,
  affine-space, projective or base-field restrictions occur.

Searches performed with the prescribed `msearch.py` wrapper for NJ and this item:

- LeanFinder: square-zero algebraic-space Picard obstruction natural for arbitrary
  pullback; 8 hits, chiefly `Algebra.Extension.H1Cotangent.map` and cotangent maps.
  None is the sheaf Picard obstruction theorem.
- Loogle: `"Pic", "Exact"`; 3 hits: two `Submodule`/ring Picard exactness results
  and path homotopy quotient exactness. None applies to algebraic-space line sheaves.
- LeanSearch: connecting map from Picard of a ringed site to H2 square-zero ideal;
  8 hits, group cohomology and ring cotangent naturality, not this assertion.
- Mathlib grep: `square.?zero.*Pic|Pic.*square.?zero|obstruction` in
  AlgebraicGeometry; 0 hits. Further `picardAb|PicardUnitsSequence|picardIdeal|
  square.?zero.*units|units.*square.?zero`; 0 hits. The site-functor query
  `sheafAdjunctionContinuous|mapExtAddHom|unitsToPic|Picard` in CategoryTheory/Sites
  gives 6 generic adjunction references, reused at the general level.
- Upstream/project rg by theorem id and Picard/obstruction names finds only scheme
  square-zero obstruction files, generic `RingedSitePicardData`/H1 naturality and
  the downstream `AbelianPicardInfinitesimalLift` docstring. The latter imports
  no obstruction theorem and is not a declaration match. Source Gm transport and
  Picard obstruction declarations apply only to schemes and their Zariski modules.
- Supporting-notion LeanSearch and LeanFinder queries, exact result names, dates
  and verdicts are recorded separately in each new node's `mathlib_searches`.
- DAG grep and `blueprint_refs.py search` found no node for either new specialized
  presentation. `Picard obstruction` and `units sequence` each give zero blueprint
  matches. Existing square-zero ideal/site and generic Picard nodes are reused.

Validation: all three modules compiled separately in dependency order through
`scompile.py NJ lem-sfb-space-picard-obstruction-natural`. No errors or warnings
remain (the permitted sorry warning aside). No global build or direct Git command
was run. The dry-run and delivery results are recorded below when complete.

## New nodes

`def-sfb-space-picard-abelian-pullback` owns
`Sheaf.AlgebraicGeometry.SpacePicardAbelianPullback`. It supplies abelian restriction
through the existing two bases, the actual fibre-product direct image, its chart
projection, and exact inverse-image presentations with the integer-1 normalization.
It specializes the generic Ext pullback formula to these actual space sites.
The single postponed comparison theorem is `picardAbRestriction_equivalences`;
its source and full compatible-family proof are in its docstring and its assertion
is included explicitly in this definition node. The Ext instance uses Mathlib's
existing theorem directly. The adjoint and integer isomorphism remain presentation
data: no arbitrary functor is chosen to define pullback.

`def-sfb-space-picard-obstruction-data` owns
`Sheaf.AlgebraicGeometry.SpacePicardObstructionData`. It supplies the additive ideal,
transported thick ring, chart-normalized units-sequence presentation, explicit Yoneda
obstruction homomorphism and the additive/tensor coefficient-map predicates. Source:
Stacks 0DNM, its actual 1+j units sequence, with 040E and 03D7. It reuses all existing
space, ideal, Picard and tensor definitions. Its module contains no postponed proof
or data chosen from an existence statement. The supporting searches found no existing
space specialization; the scheme-only square-zero obstruction module is not a match.

## Second reading by NJ

The dispatcher worker reopened the node, all three modules, and the new node records
for a separate clause-by-clause rereading; no other worker or sub-agent was started.
The maintainer's independent review remains the independent reading of this delivery.

The rereading checked the direction of every map: source is the thicker X', reduced
X; verticals go from Y to X; the square equation is j then h' equals h then i;
cohomology goes from X to Y. The units boundary goes from H1 of reduced units to H2
of the ideal, and Yoneda composition is in that order. The Picard comparison fixes
the tensor law, and all lines are represented by the existing quotient.

A possible omission in the initial draft was that only the additive inverse-image
coefficient map was visible. This was repaired before delivery by adding the actual
module map β with the local-tensor formula `IsPicardModuleIdealMap`. The same regular-
function formula fixes α, so the final H2 map is precisely the coefficient map of the
node. The rereading also checked that the theorem asserts existence of site models,
QC ideals, units presentations and line pullbacks: none is an additional hypothesis.
The units sequence is local exactness, so nonliftable global units cause no defect.

The new nodes were read against the existing small-model, thickening and Picard
signatures. Their helpers do not define a new Picard quotient, module tensor functor,
ideal or cohomology theory. The added dependency list records these existing notions.
No mathematical mismatch or statement correction remains.

Dry-run result: `deliver2.py NJ lem-sfb-space-picard-obstruction-natural --no-push`
printed `OK (dry run): commit d1d195dcc95 passes the preflight and compiles; nothing pushed`.
The packet contains exactly the three modules, the item and two new definition nodes,
and this report.
