## Worker report

The module `Sheaf.RingTheory.RelativeGlobalCompleteIntersectionColimitDescent` states
`Algebra.exists_eventually_relativeGlobalCompleteIntersection`, with its proof left `sorry`.
Its helper `Algebra.relativeGlobalCompleteIntersectionBaseChangeCondition` is a transparent
scalar-action adapter for the already recorded complete-intersection predicate. It constructs
no new notion: after installing `ρ.toAlgebra`, it applies
`Algebra.IsRelativeGlobalCompleteIntersection` to Mathlib's tensor of the identity and `φ₀`.
The helper belongs to the canonical-map interface of this item and is listed in
`lean.declarations`. Its data contains no postponed proof.

Clause-by-clause correspondence:

- The directed set is `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]`. The fixed
  `i₀ : I` supplies nonemptiness, so an extra Nonempty hypothesis is unnecessary.
- The directed ring system is `F : I ⥤ CommRingCat.{u}`. Its colimit is `colimit F` and
  its structural map at `i₀` is `(colimit.ι F i₀).hom`. The index has the rings' universe.
  Existence of this colimit is provided by Mathlib's ring-colimit instances, not an extra
  hypothesis. Using the chosen colimit is the definition dependency's convention and
  represents any specified colimit by its unique compatible isomorphism.
- `B₀ : Type w`, `C₀ : Type x`, their CommRing instances, and their Algebra instances over
  `F.obj i₀` are precisely the two arbitrary commutative base algebras. Their universes
  are independent of each other and of the ring system's universe.
- `φ₀ : B₀ →ₐ[F.obj i₀] C₀` says that the initial map respects the base.
  `hfp : φ₀.toRingHom.FinitePresentation` is finite presentation of this map alone.
  There is no finite-presentation or finite-type assumption on either original base algebra.
- Unfolding the adapter in `hci` gives the exact map
  `(TensorProduct.map (Algebra.ofId S S) φ₀).toRingHom`, with `S = colimit F` and its
  canonical `F.obj i₀` action. Mathlib's `map_tmul` sends `r ⊗ b` to `r ⊗ φ₀ b`.
  Its source and target are therefore precisely `B` and `C` of the node.
- The recorded ring-map predicate existentially quantifies finite variable and equation
  counts, relations, and an isomorphism of algebras with that quotient. For every prime
  with nonzero fibre it asserts `c ≤ n` and topological Krull dimension `n - c`.
  Thus it renders the entire explanatory presentation/fibre clause, including the
  negative-expected-dimension case, using the dependency's exact definition.
- `∃ (i : I) (hi : i₀ ≤ i)` gives a stage at least the initial one.
  `∀ (j : I) (hij : i ≤ j)` includes every later stage and the stage itself.
  Applying the adapter to `(F.map (homOfLE (hi.trans hij))).hom` installs exactly the
  structural map `Rᵢ₀ → Rⱼ`; its tensors are `Bⱼ` and `Cⱼ` and its map is `1 ⊗ φ₀`.
  No arbitrary stage maps or algebra structures are quantified over.

Statement dependencies used:

- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.colimit` and
  `colimit.ι` (def-weil-pbc-category-colimit); existence from
  `Mathlib.Algebra.Category.Ring.Colimits`.
- `Mathlib.RingTheory.FinitePresentation`: `RingHom.FinitePresentation`, defined by
  `Algebra.FinitePresentation` for the specified map's algebra structure
  (def-weil-pbc-finitely-presented-algebra).
- `WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation`:
  imports `Algebra.IsRelativeGlobalCompleteIntersection` and supplies
  `Algebra.IsRelativeGlobalCompleteIntersectionPresentation`, both declarations of
  def-weil-pbc-relative-global-complete-intersection.
- `Mathlib.RingTheory.TensorProduct.Maps`: `Algebra.TensorProduct.map`, used for
  the precise induced map, and `Algebra.TensorProduct.cancelBaseChange` in the proof plan.

Available proof-dependency modules are imported without `public`:
`Sheaf.Paper.NoetherianApproximation`
(`Algebra.exists_finiteType_subring_relativeGlobalCompleteIntersection`),
`Sheaf.Paper.RelativeGlobalCompleteIntersectionBaseChange`
(`Algebra.relativeGlobalCompleteIntersection_baseChange`), and
`WeilConjectures.RingTheory.FinitePresentationModelStage`
(`RingHom.exists_finitePresentation_model_stage`). The remaining proof dependencies
are the statement dependencies or Mathlib's `Algebra.FinitePresentation.of_finiteType`
and `Algebra.TensorProduct.cancelBaseChange`, already covered by the imports.
The docstring reproduces all four proof steps and tracks compatibility with `φ₀`.

Edge cases checked by reading the definitions: the index cannot be empty because of `i₀`;
preorders need not be antisymmetric. A singleton index and `j = i` are included. Zero
rings and zero fibres require no Nontrivial assumption; the fibre condition is vacuous
on a zero quotient. The predicate also handles `n = 0`, `c = 0`, and `c > n` without
truncated-subtraction errors. Initial algebras can be of infinite type over the initial
base. No flatness, characteristic, Noetherian, or nonzero-ring assumption is introduced.
No statement fault or correction was needed.

Searches made on 2026-10-24:

- msearch LeanFinder: "Relative global complete intersection algebra maps descend along a
  directed colimit of rings" returned eight hits including finite-presentation
  factorization, CodescendsAlong, and standard smoothness; no exact statement.
- msearch Loogle: `"CompleteIntersection"` returned zero hits.
- msearch grep, Mathlib/RingTheory: `CompleteIntersection|relativeGlobal.*colimit`
  returned zero hits.
- msearch LeanSearch: "Relative global complete intersections descend along directed
  colimits of base rings" returned eight hits about ring colimits and morphism descent;
  no complete-intersection descent theorem.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for colimit/stage complete-intersection
  names found no exact theorem. Searching the item id in the upstream source found none.
  The related upstream complete-intersection modules concern fibres, localization,
  flatness and equation counts, not colimit descent. The existing colimit-flatness and
  model-stage modules were read for their canonical tensor-map interfaces.
- rg of both proposed names in Mathlib, upstream, Sheaf, and
  `dag/lean_names_upstream.json` found no collisions.

Validation: scompile.py compiled the module in sandbox and library mode, both clean.
The final dry run recompiles the final signature after removal of the redundant
HasColimit binder, as required by coord/STATE.md's filtered-ring-colimit convention.

## Second reading by Q34

I reopened the node and reread the completed file, following the scalar-action adapter
through its body. This is a second pass by the assigned dispatcher worker; no additional
agent was started, in accordance with the brief. The maintainer supplies the independent
review. The checks above match every hypothesis and both quantifiers in the conclusion.
The important map check is that `map (Algebra.ofId S S) φ₀` fixes the left tensor factor
and applies the original algebra homomorphism to the right one. At a stage the base
homomorphism is the composite inequality `hi.trans hij`, not an independently chosen map.
The presentation predicate is reused via its recorded ring-map form because this node
quantifies over the existence of a presentation, rather than fixing equations. On this
pass I removed the redundant HasColimit instance binder; no mathematical statement changed.
