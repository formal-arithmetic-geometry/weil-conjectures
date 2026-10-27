## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianSpaceFiniteAffineDescent` states
`AlgebraicGeometry.AlgebraicSpace.exists_affine_of_noetherian_finite_surjective`, with
one postponed theorem and no definitions or other proof obligations. The statement is
Stacks Project, Spaces Cohomology, Tag 07VP,
`lemma-image-affine-finite-morphism-affine-Noetherian`, read in the local TeX source.
The source assumes exactly finite, surjective, affine source and Noetherian target.

Clause-by-clause correspondence:

- A scheme S: `{S : Scheme.{u}}`.
- An algebraic space X over S: `(X : AlgebraicSpace S)`, using the recorded fppf-sheaf
  full subcategory with representable diagonal and an étale surjective scheme atlas.
- X locally Noetherian: `hln : ∀ T : X.EtaleSite,
  IsLocallyNoetherian (X.etaleForget.obj T)`. This standard étale-local formulation is
  equivalent to a locally Noetherian étale atlas: pull its charts back to each étale
  scheme over X and descend local Noetherianity étale locally. Conversely it applies
  to every chart of the existing atlas. It is also the formulation used by the recorded
  coherent-filtered-union proof dependency; no Noetherianity of S is imposed.
- X quasi-compact: `hqc : CompactSpace (Point X.obj.obj)`, meaning every open cover of
  the atlas-topologized field-point space has a finite subcover, not a Hausdorff condition.
- X quasi-separated: `hqs : IsAbsolutelyQuasiSeparated X`. The landed definition uses
  the Stacks 0AHR affine-test criterion for the absolute diagonal, valid over arbitrary S.
  The item gains the already landed definition node `def-sfb-space-absolute-quasi-separated`
  in stmt_deps; there is no new definition node and no statement correction.
- An affine scheme Y over S: `(Y : Over S) [IsAffine Y.left]`.
- Its morphism f to X: `(f : yoneda.obj Y ⟶ X.obj.obj)`, a natural transformation on
  schemes over S, so both it and the conclusion respect the specified base.
- Finiteness on every scheme test: `hfin : IsRepresentableWith
  (fun _ _ p ↦ IsFinite p.left) f`. Expanding the recorded definition gives for every
  test `T : Over S` and `h_T → X` a representing scheme U, projection p and an actual
  pullback square, with the Mathlib finite scheme morphism predicate on p.left.
- Surjectivity on field-valued point classes: `hsurj : pointImage f = Set.univ`.
  The existing pointImage is defined using field-valued representatives and the existing
  quotient Point, rather than pointwise surjectivity on scheme sections.
- X is represented by an affine scheme over S: `∃ T : Over S, IsAffine T.left ∧
  Nonempty (yoneda.obj T ≅ X.obj.obj)`. The isomorphism is in presheaves on Sch/S;
  it gives exactly representability over S. It does not assert that T → S is affine.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `AlgebraicSpace.EtaleSite`, `etaleForget`.
  These are reached through the public absolute-quasi-separatedness import.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `AlgebraicSpace.pointImage`,
  `pointTopologicalSpace`, using Point and schemePointMap from AlgebraicSpacePointClasses.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `AlgebraicSpace.IsAbsolutelyQuasiSeparated` (the added landed statement dependency).

Plain proof imports follow every already stated proof dependency: SiteCoveringAxioms,
FullLongExactSequence, ModuleSheavesColimitsForgetful, GrothendieckSheafification,
ClosedImmersion, EtaleAffineQcoherentULift, SchemeZariskiEtaleQuasiCoherentEquivalence,
and AlgebraicSpaceCoherentFilteredUnion. The other proof dependencies have no Lean record
in the read clone and introduce no notions needed to state this theorem: finite-cover
structure-support, affine-ideal-projection, noetherian-coherent-support, affine-cohomology,
coherent-devissage, cohomology-filtered-colimit and Serre-affineness. Their imports remain
for maintenance to add when those nodes are stated. The theorem docstring carries all
8 proof steps, including the zero/summand check, image-ideal issue and Zariski–étale bridge.

Edge cases checked: no nonemptiness of X or Y is required, so the empty scheme and zero
ring are included; a surjection from empty Y can only cover the empty point space. No
reducedness, separation, connectedness, characteristic, field, or Noetherianity of the
base is assumed. All schemes use the algebraic-space framework universe u, and point
classes naturally live in u+1; no universe equality or extra smallness restriction is
added. Absolute quasi-separatedness is essential over non-quasi-separated base schemes.
The representing object is existential data, not a definition chosen from sorry.

Searches (the actual msearch invocations are logged by the launcher):

- LeanFinder: “A Noetherian algebraic space with a finite surjective morphism from an
  affine scheme is represented by an affine scheme”: 8 hits, all scheme results including
  IsFinite.toIsAffineHom, IsNoetherian and IsAffine; no exact algebraic-space theorem.
- Loogle: `AlgebraicGeometry.AlgebraicSpace, AlgebraicGeometry.IsFinite`: zero hits,
  unknown AlgebraicGeometry.AlgebraicSpace (the search index does not contain this
  project's space framework).
- Mathlib grep via msearch: `Noetherian|finite.*surject|affine.*descent` in
  AlgebraicGeometry: 25 hits on schemes, no algebraic-space affineness descent theorem.
- LeanSearch: “finite surjective morphism from an affine scheme to a Noetherian algebraic
  space implies affine target”: 8 hits on scheme affine properties and IsFinite, no match.
- Direct rg in lean/WeilConjectures and lean/Sheaf for Noetherian predicates, finite/affine
  descent, `07VP`, and the proposed declaration name: no matching theorem; the space
  locally Noetherian hypotheses are already written inline in coherent-module statements.
  The search found the landed absolute quasi-separatedness definition, which is reused.
- Direct rg for the item id in lean/WeilConjectures: no hits.

No disputed statement or dependency-interface defect was found. The withdrawn example
Sheaf/CategoryTheory/CompactObject.lean was read together with its node; the node now
points to the actual upstream CompactObject module, whose module header was also read.

## Second reading by Q124

I reread the node, Stacks 07VP, the dependency definitions and the completed signature
in a separate pass. This is a self-check: the dispatcher explicitly forbids starting
other agents; the maintainer's independent review is still required. S and X use the
recorded category; hln, hqc and hqs render exactly the three constituents of Noetherianity.
The affine Y and f are over S. hfin quantifies over every scheme base change and retains
its representing pullback; hsurj is precisely surjectivity on the recorded point classes.
The conclusion retains both affineness and representation over S. The absolute rather
than relative quasi-separatedness predicate was deliberately checked against 0AHR so
that a non-quasi-separated S is allowed. No clause, hypothesis or edge case was dropped.
The only additional node field change is adding the landed absolute-quasi-separatedness
definition to stmt_deps, as authorized. No signature mismatch or correction was needed.

Validation: the supplied file is compiled individually with scompile.py, followed by
both prescribed deliver2.py dry-run and delivery checks. Only the expected sorry warning
is allowed; the theorem proof is exactly sorry.
