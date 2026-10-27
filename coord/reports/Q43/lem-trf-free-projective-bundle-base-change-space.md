## Worker report

The module `Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace` states
`AlgebraicGeometry.RelativeProjectiveSpace.existsUnique_freeProjectiveBundleBaseChangeSpace`.
Its sole theorem has proof `by sorry`. Three transparent helper definitions express the
normalization of this same comparison; they introduce no replacement symmetric algebra,
relative Proj, projective space, or arbitrary comparison morphism.
The DAG statement and all dependency sets are unchanged. No statement fault or
STATEMENT-DISPUTED flag was found. No new nodes or dependency repairs are needed.

Clause-by-clause correspondence:

- An arbitrary scheme is `(S : Scheme.{u})`; no affine, separated, quasi-compact,
  Noetherian, or field hypothesis is imposed. The nonnegative integer is `(r : ℕ)`.
- The specified free module with its ordered basis is the recorded
  `RelativeProjectiveSpace.freeModule S r`. Its actual symmetric algebra and symmetric
  grading are `RelativeProjectiveSpace.algebra S r`, whose specification fixes the
  constructed symmetric algebra, its monomial pieces, and their inclusion maps.
  `RelativeProjectiveSpace.scheme S r` and `π S r` are the node's relative Proj and p.
- The target is `ProjectiveSpace (ULift.{u} (Fin (r + 1))) S`, the recorded fibre-product
  definition, with structural first projection `ProjectiveSpace ... S ↘ S`. ULift merely
  places the same finite ordered coordinates in the scheme universe; `i.down` retains
  their labels. The integral coefficient ring is similarly `ULift.{u} ℤ`, as in the
  existing projective-space definition. Its polynomial grading is total degree.
- `∃! θ : scheme S r ≅ ProjectiveSpace ... S` supplies the canonical scheme isomorphism.
  Uniqueness is relative to all the displayed normalizations, not uniqueness among
  arbitrary isomorphisms over S (which would be false). The first conjunct is exactly
  `θ.hom ≫ ... ↘ S = π S r`, i.e. q composed with theta equals p.
- For EVERY affine open `V : S.affineOpens`, the second conjunct requires
  `IsIntegralProjComparison S r V (affineToIntegral S r θ V)`.
  The helper `affineToIntegral` is the actual composite of the inverse recorded
  relative-Proj affine restriction isomorphism, the inverse-image open inclusion,
  theta, and `ProjectiveSpace.toProjInt`; it is not a free parameter.
- `integralPolynomialMap` extends the coefficients from lifted integers into Γ(S,V),
  keeps each ordered variable (through `i.down`), and applies the RECORDED
  `affinePolynomialEquiv S r V`. That equivalence is oriented polynomial-to-symmetric
  algebra: its inverse is precisely the node's alpha sending iota(e_i) to T_i.
  The existing equivalence's specification fixes both coefficients and generators;
  `affinePolynomial_homogeneous` identifies its grading with symmetric degree.
- `IsIntegralProjComparison` requires a graded homomorphism psi whose UNDERLYING RING
  MAP equals this explicitly constructed `integralPolynomialMap`, and an irrelevant
  ideal witness, with the local integral projection equal to `Proj.map psi hpsi`.
  Thus it specifies the canonical Proj comparison, including its map on every
  homogeneous localization; it does not only assert an abstract local isomorphism.
  Together with the fixed map to V, the integral projection determines the map into
  V times_SpecZ Proj Z[T] by the fibre-product universal property. The irrelevant-ideal
  witness and gradedness are CONCLUSIONS, not additional assumptions on S or its algebra.
  The helper's body installs Mathlib's precise total-degree grading via a `letI`;
  there is no local notation or file-local instance, and no let binder in the theorem.
- For every pair of nested affine opens and every proof `h : W ≤ V`, the third conjunct
  says `(algebra S r).localTransition h ≫ affineToIntegral ... V =
  affineToIntegral ... W`: the local scheme comparisons agree with base restriction.
- The last conjunct says that section restriction conjugated by the canonical affine
  polynomial equivalences is EXACTLY `MvPolynomial.map` of the structural coefficient
  restriction. This map fixes every variable, including for the identity restriction.
  Quantification over all polynomials includes scalars, variables and all degrees.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`:
  `AlgebraicGeometry.exists_quasiCoherentSymmetricAlgebra` (the quasi-coherent symmetric
  sheaf and affine-section comparison, through the recorded free-space construction).
- `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`:
  `SymmetricAlgebra.graded_by_tensor_images` (symmetric degree; proof import).
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`:
  `Scheme.GradedAlgebraData.relProj`, `relProjHom`, `relProjRestrictIso`,
  `relProjRestrictIso_hom_naturality`, `relProjι_relProjHom`.
  The sheaf-input bridge is the recorded `Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction`:
  `RelativeProjAlgebra.affineData`, `realization`, and its canonical `RelativeProjData`
  restriction interface. These are imported through RelativeProjectiveSpace.
- `Sheaf.AlgebraicGeometry.RelativeProjectiveSpace`: `freeModule`, `algebra`, `algebra_eq`,
  `construction`, `scheme`, `π`, `coordinate`, `existsUnique_affinePolynomialEquiv`,
  `affinePolynomialEquiv`, `affinePolynomial_homogeneous`. The actual existing section
  rings, gradings, restriction maps, and local transitions are retained throughout.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace`,
  `ProjectiveSpace.toProjInt`, and its `over` instance. Its definition uses
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd` from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- Proof dependencies: `Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension`,
  `AlgebraicGeometry.lem_nagata_affine_proj_scalar_extension`;
  `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis`, `SymmetricAlgebra.equivMvPolynomial`
  and `equivMvPolynomial_ι_apply`; `Mathlib.AlgebraicGeometry.AffineScheme`,
  `Scheme.isBasis_affineOpens`; `Mathlib.AlgebraicGeometry.Gluing`,
  `Scheme.Cover.glueMorphisms`, `ι_glueMorphisms`, `hom_ext`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`, `IsOpenImmersion`;
  `WeilConjectures.AlgebraicGeometry.RelativeProj.Universal` for chart-preserving
  realization uniqueness. Proof-only imports are non-public. The statement imports
  expose the recorded dependency constructions, rather than duplicating them.

Source checks: read the local Stacks constructions.tex definition-projective-space
(Tag 01NF), its following identification paragraph, and lemma-relative-proj-base-change
(Tag 01O3), as well as morphisms.tex lemma-projective-over-quasi-projective-is-H-projective
(Tag 087S), whose finite-generators argument uses P(O_S^n) = P_S^(n-1).
Read the current `literature/blueprint/latest` ancestor statement/proof
`lem-trf-local-term-locality`; this is a supporting node, not a changed blueprint unit.
Read the entire assigned five-step proof and preserved it as the theorem's proof docstring.

Edge cases checked mathematically before finalization: r=0 gives one variable and P^0_S;
no r>0 restriction occurs. The empty base scheme and empty affine opens are included.
Zero affine rings are allowed: their Proj charts are empty, so no false injectivity or
nonzero-coordinate assertion occurs. Arbitrary characteristic, nilpotents and nonreduced
bases are included. Nonaffine intersections are handled by affine refinements in the
proof, with no separatedness hypothesis. Identity restrictions are included. The
canonical-polynomial normalization rules out projective coordinate automorphisms,
so the uniqueness quantifier is valid. The finite nonempty coordinate set Fin(r+1)
exactly matches the item; no empty-coordinate case is silently discarded.

Searches (the msearch tool records the actual outputs):

- msearch leanfinder: "Relative Proj of the symmetric algebra of a finite free sheaf is
  canonically isomorphic over the base to projective space obtained by base change from
  the integers". Eight results: Proj.toSpec_base_isIso, projIsoSpec,
  Proj.pullbackAwayιIso, Proj.isIso_toSpec, projIsoSpecTopComponent,
  Proj.toSpec_base_apply_eq, Proj.pullbackAwayιIso_hom_awayι,
  ProjIsoSpecTopComponent.toSpec_fromSpec. All concern ordinary Proj/localization;
  none gives this relative symmetric-sheaf comparison.
- msearch loogle: `AlgebraicGeometry.Proj, MvPolynomial`: zero hits.
- msearch grep: `relativeProj|RelativeProjectiveSpace|freeProjectiveBundle`, restricted
  to Mathlib AlgebraicGeometry: zero hits.
- msearch leansearch: "Relative Proj of the symmetric algebra of a finite free sheaf is
  projective space over the base scheme": eight hits (linear projectivization notation,
  Proj, Proj notation, Projectivization.Subspace, ProjectiveSpectrum.mk, Proj.toSpecZero,
  Proj.ext, SymmetricAlgebra.instModuleFree); none matches.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for free/projective/relative projective
  comparisons and the node id: no existing declaration of this node. Inspected
  `SymmetricProjFreeComparison`: it is a conditional theorem about compatibility of a
  supplied normalized tautological quotient, not this unconditional canonical iso with
  affine normalization. `GloballyGeneratedProjectiveBundle` is its H-projectivity
  consumer; `Compactification.ProjectiveSpace` concerns affine charts into the
  base-change space; `VectorProjectiveFrameModel` compares local free-frame models
  to the relative-Proj interface. None states the current node.

Validation: scompile.py compiled the complete module cleanly in sandbox and library
forms (7.2 s and 3.3 s). The first attempt had supplied positional arguments to
Mathlib's implicit-argument gradedAlgebra; corrected to named arguments after reading
its declaration. All binders and universe levels are explicit, and the final module
has one sorry, on the assigned theorem only.

## Second reading by Q43

Worker self-check after reopening the full node and module: the only parameters are
S and r, so no hypothesis was added. Source and target use the two recorded distinct
interfaces. Checked the orientation of affinePolynomialEquiv (polynomial TO symmetric)
and of Proj.map (contravariant), the orientation of restrictionIso.inv, and the
structural morphism equation. The existential graded map is fixed by an equality of
ring maps; it cannot replace the canonical comparison by an arbitrary map. The
restriction equation uses section restriction W≤V in the correct contravariant direction
and coefficientwise polynomial restriction V→W. The local comparisons determine both
projections, so no local-isomorphism clause was lost. The helper definitions are real
terms and no definition data is sorry. No mathematical mismatch remained and no node
correction was made. The independent delivery review is performed by the maintainer,
as specified in the dispatch brief; no other agent was started.
