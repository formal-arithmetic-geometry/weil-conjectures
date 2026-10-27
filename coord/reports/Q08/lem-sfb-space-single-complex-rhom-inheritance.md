## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceSingleComplexRHomInheritance`
states Tag 0DKI(2) for algebraic spaces and the canonical geometric-stalk condition.
The only theorem is
`AlgebraicGeometry.AlgebraicSpace.SingleComplex.singleComplexRHomInheritance`;
its entire proof is `sorry`. Two helper definitions expose the actual evaluation
transpose and its composite with the specified coefficient map. Their bodies
contain real categorical maps, with no postponed data or new existence assertion.
The node changes only in `lean`; its statement, dependencies and accepted proof
are unchanged. No new node or dependency repair is needed.

Sources read: `spaces-perfect.tex`, lemma-single-complex-base-change-condition-inherited
(Tag 0DKI), equation-bc and lemma-single-complex-base-change-condition (0DKG), and
lemma-quasi-coherence-internal-hom (0A8A); `sites-cohomology.tex`,
remark-prepare-fancy-base-change (08JF). The latest blueprint unit
`sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images
proof were also read. This is the recorded supporting prerequisite, not a change
to that unit's statement or route. No statement fault or dispute was found.

Hypotheses and clauses:

| Node text | Lean rendering |
| --- | --- |
| Size convention, base scheme S | Explicit `universe u w`, `{S : Scheme.{u}}`, and `[∀ Z : AlgebraicSpace S, HasDerivedCategory.{w} Z.SmallModules]`. These binders use the already fixed small affine etale model; no extra equality of site universes is imposed. |
| Algebraic spaces with small etale structure sheaves and module categories | `{X X' Y Y' : AlgebraicSpace S}`; `SmallModules`, `smallStructureSheaf`, and their recorded unbounded `DerivedModules`. |
| f, g, projections h, f', and X' a fibre product | `(f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (h : X' ⟶ X)` and `(sq : IsPullback h f' f g)`. This includes every choice of fibre product with its projections. |
| K and K' have quasi-coherent cohomology | `(K : X.DerivedQCoh) (K' : X'.DerivedQCoh)`; their ambient objects are `K.obj` and `K'.obj`. This is the full subcategory of objects with quasi-coherent cohomology, not a derived category of the abelian category QCoh. |
| phi: Lh*K to K' | `(φ : (derivedPullback h).obj K.obj ⟶ K'.obj)`; `derivedPullback` is the recorded total left derived tensor pullback with flat-term K-flat coordinates. |
| Every geometric point and integer degree has invertible canonical beta_phi | `(h_stalk : StalkCondition f f' g h sq K.obj K'.obj φ)`. The existing definition quantifies over all geometric points, integer degrees and representative coordinates. Its canonical comparison uses the same rings R,A,B,C, the same tensor ring A tensor_R B, and the specified normalized pullback-stalk map. |
| Every perfect P, etale locally bounded finite-free retracts | `(P : X.DerivedModules)` and `hP : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u,u,u,w} X.smallStructureSheaf P`. The recorded predicate uses covering sieves and local bounded strictly perfect packages, not a global strictly perfect representative. |
| J = RHom(P,K) | `X.derivedHom.obj (op P, K.obj)`. |
| J' = RHom(Lh*P,K') | `X'.derivedHom.obj (op ((derivedPullback h).obj P), K'.obj)`. |
| J and J' have quasi-coherent cohomology | The first two conjuncts are `X.derivedQCohProperty J` and `X'.derivedQCohProperty J'`. |
| First arrow in psi is the evaluation transpose | `rhomPullbackComparison h P K.obj` applies `X'.derivedDualityModel.closed.transpose` to `(derivedTensorComparison h).inv.app (J,P) ≫ (derivedPullback h).map (X.derivedDualityModel.closed.evaluation P K.obj)`. Thus its uncurried map is precisely pulled-back evaluation after the inverse tensor comparison. |
| Second arrow is RHom(1,phi) | `rhomCoefficientMap h P K.obj K'.obj φ` composes the first arrow with `X'.derivedHom.map (Prod.mkHom (𝟙 (op ((derivedPullback h).obj P))) φ)`. |
| Every beta_psi is invertible | The final conjunct is `StalkCondition f f' g h sq J J' (rhomCoefficientMap h P K.obj K'.obj φ)`, using the identical definition as the hypothesis. |
| No qc, qs, bounds, flatness or direct-image assertion | No such binder or conclusion occurs. Both K and K' are arbitrary unbounded objects of the indicated full subcategories. |

The statement dependencies were opened and read, including their recorded signatures
and docstrings. The relevant declarations and modules are:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  its small etale site and structure sheaf. The size-convention node is explicitly
  a metatheoretic convention, with no declaration to import.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently the existing `SheafOfModules` category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicGeometry.AlgebraicSpace.QCoh`, based on `SheafOfModules.IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleDirectImageModel`, `moduleTensorPullback`, `moduleTensorAdjunction`.
  The ordinary functors are reused through the existing small-model transport.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses` and its local strict-perfect
  packages. The hP binder is exactly this recorded predicate.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` publicly re-exports
  `CategoryTheory.derivedInternalHomOfUniverses`, which is the definition used by
  `X.derivedHom`. The ordinary-module abbreviation is not substituted for sheaf Hom.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSingleComplexStalkCondition`:
  `AlgebraicGeometry.AlgebraicSpace.SingleComplex.StalkCondition`, `comparison`,
  and its `Coordinates` and geometric-stalk models.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`. The statement uses Mathlib's `IsPullback`.
- Existing public interfaces inherited through the preceding imports are
  `AlgebraicSpace.DerivedQCoh`, `derivedQCohProperty`, `derivedHom`,
  `derivedDualityModel` in `AlgebraicSpaceDerivedModules`; `derivedPullback` and
  `tensor` in `AlgebraicSpaceDerivedPullbackModels`; and
  `derivedTensorComparison` in `AlgebraicSpacePullbackTensorComparison`.
  The latter is directly public-imported because the helper definition uses it.
  It is pinned by its ordinary tensor and K-flat representative formulas.

All stated proof dependencies are imported without `public`, except the stalk
condition, which is also a statement dependency. Their declarations were read:
`SheafOfModules.strictPerfectRingedPullbackModel`,
`CategoryTheory.ringedSitePerfectDuality`,
`AlgebraicGeometry.AlgebraicSpace.pseudoCoherent_rhom_quasiCoherent`,
`CategoryTheory.RingedDerivedComparisons.ringedPerfectInternalHomPullback`,
`CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`,
`AlgebraicGeometry.AlgebraicSpace.SingleComplex.singleComplexTensorInheritance`,
and `CategoryTheory.ringedDerived_closed_symmetric_monoidal`.
The theorem docstring carries all five accepted proof steps, including the
restriction/pullback identification, canonical-map equality by uncurrying, and
the naturality square on beta. No proof dependency is dropped.

The generic `ringedPullbackHomComparison` in
`Sheaf.Paper.RingedPullbackHomEvaluationComparison` was also read. It takes an
`AdjointLift`, whereas this statement uses the already fixed algebraic-space
`derivedPullback` and `derivedTensorComparison`. The helper specializes its
evaluation-transpose formula to these existing maps directly; it does not choose
an unrelated lift, internal Hom, tensor or comparison. It is a helper for the
canonical map explicitly introduced in this item's statement, as allowed by the
missing-helper rule, rather than a new independent mathematical notion.

Edge cases checked before writing: P = 0 gives zero Homs; P = O recovers the
given coefficient map under the canonical unit comparisons; shifts of P give
the same all-integer-degree condition. Local bounds and ranks may vary on the
perfectness cover. Non-flat h is allowed because the pullback and tensors are
derived. K and K' may be unbounded in both directions. Empty X' makes the
pointwise condition vacuous while its quasi-coherence clause remains meaningful.
There is no surjectivity, nonemptiness, quasi-compactness or separation assumption.

Searches performed using `msearch.py`:

- LeanFinder: “The geometric stalk base change condition is stable under derived
  internal Hom from a perfect complex”: eight results on stability of scheme
  morphism properties, including `SurjectiveOnStalks`, flatness and smoothness;
  none states this derived internal-Hom inheritance theorem.
- Loogle: `DerivedCategory, "Hom"`: twelve hits in DerivedCategory.Basic on
  localization, shifts, additivity and homotopy invariance; no matching theorem.
- Mathlib grep: `single.?complex.*base.?change|rhom.*inherit` in CategoryTheory:
  zero hits. An additional grep with internal-Hom pullback terms found no match.
- Direct project searches in `lean/WeilConjectures` and `lean/Sheaf` for the item
  id and `singleComplex.*(Hom|RHom)|rhom.*[Ii]nherit` found only unrelated open
  pullback normalizations; no declaration of this theorem. Searches for all three
  proposed declaration names in the upstream-name index, Mathlib and both project
  roots found none. Existing tensor inheritance and generic Hom pullback were
  inspected and reused as described above.

Validation: `scompile.py Q08 lem-sfb-space-single-complex-rhom-inheritance` compiled
the actual module on the server both as a sandbox file and at its library module
path (2.6 and 2.5 seconds); no error or unexpected warning. All variables and
universes are explicitly bound; the file sets `autoImplicit false`. The only
postponed proof belongs to the item's named theorem. All lines are at most
100 characters, and the node is unchanged outside its new `lean` record.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
