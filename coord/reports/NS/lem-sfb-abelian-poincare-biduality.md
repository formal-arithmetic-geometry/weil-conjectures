## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.PoincareBiduality` states
`AlgebraicGeometry.IsAbelianVariety.poincare_biduality`. Its sole theorem has proof
`sorry`. Six auxiliary definitions unpack the Poincare comparisons and their
rigidifications using existing module inverse-image functors; none has postponed
data or a postponed proof. They belong to this node's evaluation/dual-map notion
and are all listed in `lean.declarations`.

This is the stage-2 handoff of the stage-1 split independently accepted on
2026-10-24. The current queue lists the item at stage 2 and the node has no Lean
record. The earlier BLOCKED ending concerned reopening a reviewed stage-1 split;
`coord/brief-stage2.md` §0 explicitly distinguishes this from writing its Lean
statement. The accepted statement, seven proof steps, dependencies, and review
stamp are retained without modification. Only `lean` changes in the node copy.

### Hypotheses and clauses

- The base is an arbitrary field: `{k : Type u} [Field k]`. There is no
  perfectness, algebraic-closedness, separability, characteristic-zero, or
  invertibility hypothesis. All schemes and groups are over `Spec (.of k)`.
- An abelian variety is `A : Over (Spec (.of k))` with `[GrpObj A]` and
  `[IsAbelianVariety A]`. The latter is the upstream proper/smooth/connected
  predicate, not a replacement definition. The second conjunct repeats these
  same hypotheses for both `A` and `B`.
- The two chosen normalized dual data are
  `D : AbelianDualPoincareDatum A` and
  `E : AbelianDualPoincareDatum D.dual`. Their actual dual objects, Poincare
  modules, group instances, and rigidifications come from that recorded datum.
  The theorem quantifies over every such choice.
- The factor switch is `(β_ D.dual A).hom`, the Cartesian symmetry from
  `D.dual ⊗ A` to `A ⊗ D.dual`. Products are products in the category over the
  field, hence fibre products over k, not products of underlying spaces.
- The first conjunct asserts
  `∃! delta : A ≅ E.dual, IsMonHom delta.hom ∧
  IsAbelianPoincareEvaluation D E delta.hom` for every A and both dual data.
  `A ≅ E.dual` is an isomorphism over k, and `IsMonHom` makes it a group-scheme
  isomorphism. The inverse is a homomorphism by Mathlib's instance for the
  inverse of a monoid-homomorphism isomorphism. Uniqueness is uniqueness of
  the isomorphism, not just uniqueness of its map on points.
- `IsAbelianPoincareEvaluation` includes an actual isomorphism
  `i : pullback (D.dual ◁ delta).left E.poincare ≅
  pullback (β_ D.dual A).hom.left D.poincare`.
  This is precisely `(1 × delta)^* P_D ≅ s^* P_A` on `D × A`.
- Both identity axes are included. `abelianIdentityAxis D.dual A` is `0_D × A`;
  `poincareOtherIdentityAxis D.dual A` is `D × 0_A`. The two final equations
  in the evaluation predicate require the restriction of this same `i.hom`
  to preserve both axis trivializations, through canonical composition,
  equality, and unit comparisons. `hA`, `hE`, `hD` are existential proofs of
  the actual commuting-square equalities, not extra input maps or hypotheses.
- The recorded datum supplies its first-axis rigidification, but only existence
  of a trivialization on the other axis. The predicate therefore quantifies
  second-axis trivializations `rD` and `rE` and requires
  `PoincareAxesAgreeAtOrigin D rD` and
  `PoincareAxesAgreeAtOrigin E rE`. This compares their restrictions at the
  origin with the specified first-axis rigidification using `pullbackComp`,
  `pullbackCongr`, `mapIso`, and `pullbackObjUnitIso`. It fixes the scalar
  normalization; no independently chosen rigidification is added to the data.
- All inverse images are the existing `Scheme.Modules.pullback` on modules,
  exactly as in `AbelianDualPoincareDatum`. This is the extension-of-scalars
  inverse image of module sheaves, not just inverse image of underlying
  abelian sheaves. The recorded tensor-pullback module is publicly imported;
  no second pullback functor is constructed. The auxiliary base-change
  definition composes only existing canonical isomorphisms.
- For B the corresponding data are `F : AbelianDualPoincareDatum B` and
  `G : AbelianDualPoincareDatum F.dual`. The map `f : A ⟶ B` is required to
  satisfy `IsMonHom f`, the recorded notion of group-scheme homomorphism.
- The second conjunct asserts the existence of
  `fDual : F.dual ⟶ D.dual`, its `IsMonHom` property, and
  `∀ g, ClassifiesAbelianDualHom D F f g ↔ g = fDual`.
  Thus the map is uniquely characterized among all scheme morphisms by its
  classifying family, rather than being an arbitrary homomorphism.
- `ClassifiesAbelianDualHom D F f g` is an isomorphism
  `(1_A × g)^*P_A ≅ (f × 1)^*P_B` whose restriction to `0_A × F.dual`
  respects the pulled-back specified rigidification. Its square equality
  expresses `f(0_A) = 0_B` on the actual axis. The pulled-back trivialization
  is formed explicitly by `poincareRigidificationBaseChange`.
- The existence and uniqueness characterization of
  `fDoubleDual : E.dual ⟶ G.dual` uses
  `ClassifiesAbelianDualHom G E fDual g`. Here the source of `fDual` is
  `F.dual` with dual datum G, and its target is `D.dual` with dual datum E;
  this gives exactly the second dual and its correct variance.
- Finally, for every pair of group isomorphisms `deltaA`, `deltaB` satisfying
  the evaluation predicates, the conclusion is
  `deltaA.hom ≫ fDoubleDual = f ≫ deltaB.hom`, i.e.
  `f^{vee vee} delta_A = delta_B f`. The first conjunct provides the unique
  evaluation isomorphisms for A and B, so the conditional formulation of the
  naturality square is not vacuous and makes no extra assumption.

### Dependency declarations read and used

- `def-weil-field`: `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-sc-abelian-variety`:
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`,
  `AlgebraicGeometry.IsAbelianVariety` (proper, smooth, connected).
- `def-sfb-abelian-dual-poincare-datum`:
  `Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum`,
  `AlgebraicGeometry.AbelianDualPoincareDatum`, `abelianIdentityAxis`, and
  `abelianRigidificationPullback`. The full structure and docstrings were
  read: its representing property includes every rigidified fibrewise
  algebraically trivial invertible family, and its other axis is `Nonempty`.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` in
  `Mathlib.CategoryTheory.Monoidal.Grp`, `CategoryTheory.IsMonHom` in
  `Mathlib.CategoryTheory.Monoidal.Mon`; the intended Over specialization
  and group-inverse instance are as documented in the publicly imported
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`,
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction` and its
  imported tensor construction. The chosen Poincare datum itself uses
  `AlgebraicGeometry.Scheme.Modules.pullback` from
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`; this interface is retained.
  `pullbackComp` and `pullbackCongr` are Mathlib's comparisons, and
  `pullbackObjUnitIso` is already exposed by the datum's imports.

Recorded, available proof-dependency modules are imported privately:
`GlobalSectionsProper`, `AbelianVariety.Basic`, `AbelianVariety.Projective`,
`AbelianVariety.Isogeny`, `AbelianVariety.Rigidity`,
`Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso`,
`Mathlib.AlgebraicGeometry.Morphisms.Finite`, `ModulePullbackTensor`, `Regular`,
and `Sheaf.AlgebraicGeometry.RegularNormalDecomposition`.
`LineAlgebraicEquivalence` and `TensorPullback` are already imported through
public statement dependencies. The three statement-only proof prerequisites
`lem-sfb-abelian-field-extension`, `lem-sfb-ample-line-polarization-isogeny`,
and `lem-sfb-dual-isogeny-degree` have no module record and cannot yet be
imported. They are not needed to type the statement; none is silently assumed.
The docstring preserves all seven accepted proof steps, including finite-flat
rank and generic-field cancellation rather than geometric-point counting.

### Edge cases and statement checks

- Dimension-zero abelian varieties (the trivial group): the products and axes
  still exist, both normalizations restrict to the same one-dimensional line,
  and the unique evaluation isomorphism is included. No positive-dimension
  binder appears.
- The identity homomorphism and the zero homomorphism are both allowed. Their
  duals classify respectively the same family and the rigidified trivial
  family. The naturality equation has the stated covariant second dual.
- Positive characteristic, inseparable isogenies, and imperfect fields remain
  in scope. No geometric-point bijection is substituted for a scheme
  isomorphism. The proof sketch uses equal finite-flat ranks on generic fields.
- Chosen Poincare sheaves may have differently scaled specified first-axis
  rigidifications. The second-axis normalization is compared at the origin
  to that actual rigidification; no scalar is silently fixed in advance.
- Equality of maps is equality in `Over (Spec (.of k))`; no reduction to
  rational points, closed points, or reduced test schemes occurs.
- All universes and all variables are explicit, with `autoImplicit` and
  `relaxedAutoImplicit` both false. Scheme/product and coefficient universes
  match the recorded datum; there is no additional universe equality.
- The empty scheme is not an abelian variety, already because of the identity
  section over a field. No artificial nonemptiness hypothesis is added.

### Searches

All searches used the prescribed `msearch.py` wrapper or read-only ripgrep.

- LeanFinder: “The evaluation isomorphism of an abelian variety with its
  double dual defined by the Poincare bundle is natural in homomorphisms”.
  Eight results, including `Module.Dual.eval_naturality`,
  `Module.Dual.eval_comp_comp_evalEquiv_eq`, `CharacterModule.dual_comp`,
  and categorical evaluation formulas. Their signatures concern linear maps,
  characters, or unrelated evaluation adjunctions, not abelian varieties.
- LeanSearch: “An abelian variety over any field is naturally isomorphic to
  its double dual by the Poincare line bundle”. Eight results: character
  double-dual equivalences, reflexive modules, fractional ideals, and
  annihilators. No abelian-variety statement.
- Loogle: `"Poincare"`: zero hits.
- Mathlib grep: `bidual|doubleDual|Poincare` in `AlgebraicGeometry`: zero hits.
- Project grep: `bidual|doubleDual|dualAbelian` and the item tag under
  `lean/WeilConjectures` and `lean/Sheaf`; no evaluation/dual-variety declaration.
  Upstream hits about biduals of modules and unrelated Verdier duality were
  inspected and rejected as different statements.
- The existing `DualPoincareDatum` and `PolarizationCalculus` files were read.
  The latter states polarization calculations over algebraically closed
  fields; it neither states biduality nor supplies this naturality theorem.
  It is therefore not a replacement for the assigned arbitrary-field node.
- Helper-name and rigidification/axis searches across the project found the
  existing `abelianRigidificationPullback`, which is used. The cubical-line
  `pullbackRigidification` is specialized to its cubical datum, rather than
  a Poincare comparison across a specified square. No copy of that notion
  is made.

Source read locally: Milne AV, I §8 pp.36–40, the paragraph after Lemma 8.8,
the biduality part of Theorem 8.9, and I §9 p.41 for the dual map. The theorem
asserts only biduality, not the unrestricted four-condition equivalence of
printed Theorem 8.9. No STATEMENT-DISPUTED issue or statement correction.

### Validation

The delivered module was checked individually through `scompile.py` in module
mode, both as the sandbox file and under its real module name. It compiles
cleanly with no errors or unexpected warnings. An initial type-check caught
untyped field notation on identity arrows and a reversed pair of data in the
second dual predicate; both were corrected before the successful compile.
No global build, source-repository edit, or direct Git mutation was performed.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
