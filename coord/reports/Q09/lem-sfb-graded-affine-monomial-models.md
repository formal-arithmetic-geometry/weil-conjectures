## Worker report

The module `Sheaf.AlgebraicGeometry.GradedAffineMonomialModels` states
`AlgebraicGeometry.graded_affine_monomial_models`, with its proof `sorry`. No
mathematical theorem is proved. The item's statement and all dependency records
remain unchanged. There is no statement dispute or dependency-interface defect.

The helper declarations belong to this node's monomial construction:
`GradedSheafAlgebra.sectionMonomial` recursively multiplies the chosen degree-one
sections, starting with the actual structural unit; `gradedModuleMonomialIndex`
is the finite type of a generator, its complementary degree bounded by d, and a
word of that degree; `GradedSheafModule.sectionMonomial` applies the given graded
action and transports along the index's degree equality. These contain real data,
not choices from unproved existence statements. Words of length d on Fin r have
exactly the same values as exponent-vector monomials of total degree d: counting
each letter gives its exponent, and commutativity identifies all word orders.
Thus repetitions in this finite indexing do not change any generating family.

`sectionsGenerateOn` expresses the given family's generation using the recorded
`SheafOfModules.GeneratingSections` on `F.over U`. Its bijection of index types
forces precisely the prescribed family; evaluation at the terminal over-object
forces its actual sections on U. Naturality determines all their restrictions.
It does not replace generation by sectionwise surjectivity on arbitrary opens.
`gradedAffineSectionSum` abbreviates Mathlib's algebraic `DirectSum` of the
actual homogeneous section modules, with its existing addition and base action.
`affineMonomialResidueIso` is the explicit composite of `residueFieldCongr`, the
canonical affine open immersion's `residueFieldMap`, and `Spec.residueFieldIso`.
No arbitrary residue-field map or abstract substitute for a stalk is introduced.

Hypothesis-by-hypothesis translation:

- The scheme S is `(S : Scheme.{u})`; quasi-compactness is `[CompactSpace S]`,
  and local Noetherianity is `[IsLocallyNoetherian S]`. There is no separation,
  nonemptiness, characteristic or dimension assumption.
- The homogeneous sheaves are `B L : ℕ → S.Modules`; their graded algebra and
  module structures are the recorded `A : GradedSheafAlgebra B` and
  `M : GradedSheafModule A L`.
- `hB` and `hL` assert Mathlib's `IsQuasicoherent` for every homogeneous piece.
- The structural equality B_0=O_S is `hzero : IsIso A.unit`; it is the given
  structural unit, not an unrelated isomorphism.
- Coherence of B_1 is `hone : RingedSpace.IsCoherent S.toRingedSpace (B 1)`.
  This is the finite-type-and-finite-type-kernel predicate, not merely the
  conjunction of quasi-coherence and finite type.
- Degree-one generation is `hgen : A.IsGeneratedInDegreeOne`; local finite
  homogeneous module generation is `hM : M.IsLocallyFinitelyGenerated`, with
  arbitrary nonnegative degrees and the exact local spanning condition.

Conclusion clause-by-clause translation:

- `n : ℕ`, `U : Fin n → S.Opens`, `hU : ∀ i, IsAffineOpen (U i)` and
  `(⨆ i, U i) = ⊤` give the finite affine open cover. Each ring A_i is the
  actual `Γ(S, U i)`; `hU i` provides its canonical Spec chart. The next
  conjunct explicitly asserts `IsNoetherianRing Γ(S, U i)` for every chart.
- `r t : Fin n → ℕ` give the lengths of the lists. `x i` is a list in
  `(B 1)(U i)`, `b i j : ℕ` is the degree of a module generator, and `e i j`
  is in `(L (b i j))(U i)`. They are chosen once, before quantifying over d.
- For every d, the first `sectionsGenerateOn` is the degree-d word/monomial
  family of x_i; the second is the family of x_i^alpha e_i,j satisfying
  |alpha|+b_i,j=d. The complementary degree k is bounded by d, so this is a
  finite family. `ULift.{u}` supplies the index universe required by the
  existing sheaf-generators interface without restricting the scheme universe.
- The next two `Submodule.span Γ(S, U i) ... = ⊤` conjuncts say that exactly
  these same monomial families span the modules of affine sections, degree
  by degree. The final conjunct explicitly states `Module.Finite` for L_d(U_i).
- `gradedAffineSectionSum B (U i)` and `gradedAffineSectionSum L (U i)` are
  C_i and M_i. The existential `c`, `a`, `m` supplies their ring, A_i-algebra,
  and C_i-module structures. `c.toAddCommGroup` is forced to be the existing
  direct-sum additive structure and `a.toSMul` the existing A_i action.
  The homogeneous multiplication, algebra-map and action formulas force the
  operations to extend the given A.mul, A.unit and M.act. They determine
  the canonical structures by additivity and finite support; these are not
  unrelated structures chosen to make generation true. `Algebra.adjoin` of
  the actual degree-one inclusions equals top, and `Submodule.span` over C_i
  of the actual degree-b_i,j inclusions of e_i,j equals top.
- For every d and every s in U_i, the last `Nonempty (... ≅ ...)` is an
  isomorphism in `ModuleCat (S.residueField s)`. Its source extends scalars
  from the actual `(RingedSpace.moduleStalkFunctor S.toRingedSpace s).obj
  (L d)` along the actual residue map. Its target extends scalars from
  `(L d)(U_i)` over A_i to `(hU i).primeIdealOf s`'s `Ideal.ResidueField`,
  then restricts scalars along `affineMonomialResidueIso`. This is exactly
  the stated kappa(s)-linear comparison using the canonical residue-field
  identification. `ModuleCat.extendScalars` places the scalar tensor factor
  first; tensor commutativity gives the displayed order in the node.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, its
  `component_noetherian`, and the affine-cover characterization.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, without a Hausdorff condition.
- `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`:
  `GradedSheafAlgebra` and `GradedSheafModule`, including all operation signatures
  and unit/associativity/restriction laws.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes the recorded
  `WeilConjectures.AlgebraicGeometry.Coherent` predicate `RingedSpace.IsCoherent`,
  and Mathlib's `SheafOfModules.IsQuasicoherent` and `IsFiniteType`. The auxiliary
  `IsQuasiCoherentFiniteType` is not substituted for coherence.
- `Sheaf.AlgebraicGeometry.GradedSheafGeneration`:
  `GradedSheafAlgebra.IsGeneratedInDegreeOne` and
  `GradedSheafModule.IsLocallyFinitelyGenerated`.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `RingedSpace.moduleStalkFunctor`, with its actual additive presheaf stalk and
  canonical local-ring module structure.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`:
  `SheafOfModules.GeneratingSections`, its `I`, `s`, and `epi` fields.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `residue`,
  `residueFieldCongr`, `Hom.residueFieldMap`, and `Scheme.Spec.residueFieldIso`.
  The latter is constructed from `Spec.stalkIso`; its algebra-map compatibility
  is `Spec.algebraMap_residueFieldIso_inv`.

The header also imports the recorded modules for every stated proof dependency:
`AffineScheme` (affine basis and affine stalk localization),
`AffineFiniteTypeGeneratingSections` (`affine_finiteType_generatingSections`),
`Modules.Sheaf` and `Modules.Tilde` (restriction and quasi-coherence, tilde-free
modules), `Modules.QuasiCoherentCokernelImage` (`quasiCoherent_cokernel_image`),
`Morphisms.AffineModuleGermLocalization` (`Scheme.isLocalizedModule_affine_germ`),
and `TensorProduct.Defs`. The theorem docstring contains the node's six proof
steps, including the explicit inverse on residue fibres.

Edge cases checked before finalizing the statement:

- For the empty scheme take n=0; no nonempty cover index is imposed.
- r_i=0 is allowed. Fin 0 → Fin 0 contains the empty word; for d>0 there
  are no words with letters in Fin 0. The degree-zero monomial is the unit.
- t_i=0 gives an empty module monomial family in every degree, forcing exactly
  the zero homogeneous modules by its span/top conditions.
- A generator with b_i,j>d contributes no index; b_i,j=d contributes exactly
  the empty word. No assumption bounds generator degrees uniformly in advance.
- Zero rings and zero sheaves are allowed. A chart with no points makes its
  fibre comparison vacuous, as in the source. No field characteristic is fixed.
- The sums are algebraic direct sums of sections. No equality of global
  sections with a sheaf coproduct, nor affine-section surjectivity on nonaffine
  subopens, is assumed.

Searches for existing statements/definitions:

- `msearch.py ... leanfinder` with query "Finite affine open monomial models
  for a graded quasi coherent sheaf algebra and finitely generated graded module"
  returned 8 hits, principally `Proj.affineOpenCover`, Proj basic-open results,
  and `SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType`. None
  supplies the node's simultaneous monomial sheaf/section/fibre conclusions.
- `msearch.py ... loogle` with `SheafOfModules.IsQuasicoherent, Module.Finite`
  returned 0 hits.
- `msearch.py ... leansearch` with query "A graded quasicoherent module over a
  standard graded sheaf algebra has finite affine monomial generators in each
  degree and its fibre is the tensor product of affine sections with the residue
  field" returned 8 hits on homogeneous generators, finite sheaf presentations
  and quasi-finite algebra fibres; no exact theorem.
- `msearch.py ... grep` with
  `(graded|homogeneous).*(affine|monomial)|(affine|monomial).*(graded|homogeneous)`
  returned Proj and polynomial homogeneous-monomial lemmas; no sheaf model theorem.
- `rg` of the same pattern in `lean/WeilConjectures` and `lean/Sheaf`, followed
  by searches for `GradedSheafAlgebra`, `GradedSheafModule` and section-total
  constructions, located the recorded graded interfaces and the separate
  `GradedSheafAlgebra.exists_total`. That theorem concerns a sheaf coproduct
  and sheafification, not this algebraic direct sum of sections, so it was not
  substituted. `GradedFibreHilbertFunctionsFinite` is a consumer, not a match.
- `grep -rn lem-sfb-graded-affine-monomial-models lean/WeilConjectures` found
  no declaration. Searches of the proposed declaration names in Mathlib, the
  upstream Lean, `lean/Sheaf`, and `dag/lean_names_upstream.json` found no clash.

The node source was read in `literature/stacks-project/algebra.tex`,
`lemma-graded-module-fg` (00K0), and `schemes.tex`, `lemma-spec-sheaves`
(01HV, especially clauses 2, 6 and 7) and `lemma-quasi-coherent-affine` (01IA).
The old example's Sheaf module is withdrawn; its node now records
`WeilConjectures.CategoryTheory.CompactObject`, which was read as well.

Validation: `scompile.py` compiled the completed module on the server with no
errors or warnings. `deliver2.py Q09 lem-sfb-graded-affine-monomial-models --no-push`
reported OK at dry-run commit `6d353ef52b1`: preflight passed and the module
compiled. The only node-field change is `lean`; the one postponed proof is
`graded_affine_monomial_models`. No diagnostic commands or over-width lines remain.

## Second reading by Q09

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
