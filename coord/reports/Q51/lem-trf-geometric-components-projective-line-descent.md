## Worker report

Item: `lem-trf-geometric-components-projective-line-descent`.
Module: `Sheaf.AlgebraicGeometry.GeometricComponentsProjectiveLineDescent`.

The module states the node in three named theorems, all with `sorry` proofs:
`AlgebraicGeometry.geometric_components_baseChange`,
`AlgebraicGeometry.reduced_component_projectiveLine_iff`, and
`AlgebraicGeometry.reduced_component_projectiveLine_iso_descends`.
It introduces no definitions, extra nodes, or dependency repairs. The natural-language
statement and the DAG dependencies are unchanged. Sources read: Stacks `varieties.tex`,
lemma-bijection-irreducible-components (038F); `limits.tex`,
lemma-descend-finite-presentation (01ZM), especially clauses (2)--(3); and `algebra.tex`,
theorem-nullstellensatz (00FV).

Hypotheses and object identifications:

- The two algebraically closed fields are `(k L : Type u) [Field k] [IsAlgClosed k]
  [Field L] [IsAlgClosed L]`. The inclusion/field extension is `[Algebra k L]`,
  with its canonical injective `algebraMap k L`. No algebraicity of `L/k` is assumed.
- The finite-type scheme is `(C : Scheme.{u}) (f : C ⟶ Spec (.of k))`
  with `[LocallyOfFiniteType f] [QuasiCompact f]`. These are precisely the two
  constituents in the finite-type node's recorded interface. There is no separatedness,
  smoothness, dimension, properness, reducedness, or nonemptiness assumption on `C`.
- A component in the first theorem is `T : TopologicalSpace.Closeds C` with
  `(T : Set C) ∈ irreducibleComponents C`. Components are closed; hence passing to
  `Closeds C` excludes none. Its reduced induced scheme and immersion are exactly
  `(Scheme.IdealSheafData.vanishingIdeal T).subscheme` and `.subschemeι`.
- In the other two theorems the same component scheme is represented by
  `(R : Scheme.{u}) (i : R ⟶ C) [IsClosedImmersion i] [IsReduced R]` and
  `hi : Set.range i ∈ irreducibleComponents C`. This is the uniqueness characterization
  in `reduced_induced_closed_subscheme`: such an `i` is uniquely isomorphic over `C`
  to the canonical reduced induced scheme on its image. These binders describe the
  component's chosen scheme structure; they impose no extra condition on `C` or on
  which component is allowed. Conversely the canonical construction satisfies them.
- Every universe is explicitly bound. Fields, schemes, subalgebras and their spectra
  share the ambient scheme universe; no independent smaller universe of test objects
  or unbound implicit is introduced. `set_option autoImplicit false` checks this.
- `ProjectiveLine S` is the existing abbreviation
  `ProjectiveSpace (ULift.{u} (Fin 2)) S`, not a newly defined model. The existing
  `ProjectiveLine.TwistData` declaration in `TransitionUnits` uses this same scheme.
  Its coordinate index has exactly two elements in the ambient universe.

Clauses of the first theorem:

- `C_L` is `pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))`, and
  `π : C_L ⟶ C` is its `pullback.fst`.
- The component bijection is `Set.BijOn (Set.preimage π)
  (irreducibleComponents C) (irreducibleComponents C_L)`.
- The component's scalar extension is written as the iterated fibre product
  `pullback i_T π`, canonically `R ×_k L` by pullback pasting. Its projection to `R`
  is `pullback.fst i_T π`. `IsReduced`, `IrreducibleSpace`, and `Surjective` give,
  respectively, reducedness, nonempty irreducibility, and surjectivity of this projection.
- For every closed `D` whose underlying set is `π ⁻¹' T`, the equality
  `(pullback.snd i_T π).ker = Scheme.IdealSheafData.vanishingIdeal D`
  identifies the scheme structure, not merely the support. Base change makes this
  second projection a closed immersion. Its kernel ideal is exactly the canonical
  ideal cutting out the reduced induced component on `D`. Together with the preceding
  `Set.BijOn`, this gives the bijection of reduced component schemes claimed by the node.

Projective-line and prescribed-descent clauses:

- Direct scalar extension of a representative `i : R ⟶ C` is
  `pullback (i ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k L)))`.
  Its structure morphism is the second projection. This is canonically the same
  scalar extension used in the first theorem.
- `reduced_component_projectiveLine_iff` states the exact equivalence between
  `Nonempty (Over.mk (R_L → Spec L) ≅ Over.mk (ProjectiveLine (Spec L) → Spec L))`
  and the analogous `Over Spec k` isomorphism for `R`. Thus the isomorphisms are over
  the specified fields, not bare scheme isomorphisms or arbitrary changes of scalars.
- The final theorem quantifies over the actual `e : R_L ≅ P¹_L` in `Over Spec L`.
  It produces `A : Subalgebra k L`, `A.FG`, and an actual isomorphism
  `a : R_A ≅ P¹_A` in `Over Spec A`. Each `Iso` includes its inverse and both
  inverse identities; no mere maps or unproved choice of inverse are substituted.
- The two equations for `r : R_L ⟶ R_A` specify its composite with each pullback
  projection: identity on `R`, and the spectrum map of `A.val` on the base. By
  `pullback.hom_ext`, these determine exactly one map. This is a characterization of
  the canonical transition map, not a free comparison morphism.
- The next two equations are `e.hom.left ≫ P(A.val) = r ≫ a.hom.left` and
  `e.inv.left ≫ r = P(A.val) ≫ a.inv.left`. `P(A.val)` is the existing
  `ProjectiveSpace.map (ULift.{u} (Fin 2)) (Spec.map (CommRingCat.ofHom A.val.toRingHom))`.
  `ProjectiveSpace.isPullback_map` makes that square cartesian, so the equations say
  exactly that base change of BOTH prescribed finite-stage maps is `e` and `e⁻¹`.
- The maximal ideal is `m : Ideal A` with `m.IsMaximal`. The statement retains the
  actual residue algebra isomorphism `q : (A ⧸ m) ≃ₐ[k] k`, not an abstract field
  isomorphism that could change the `k`-structure.
- The quotient point used in specialization is explicitly the spectrum map of
  `q.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk m)`.
- The theorem produces `b : R ≅ P¹_k` in `Over Spec k`. Both projections of
  `s : R ⟶ R_A` are specified: its first is `𝟙 R` and its second is the structural
  map of `R` followed by that quotient point. This again uniquely determines the
  canonical specialization map. The final two equations say that `b` and `b⁻¹`
  are the specializations of `a` and `a⁻¹`, using the same quotient point and the
  existing projective-space base-change map.
- There is deliberately no equation identifying the scalar extension of `b` with `e`.
  This preserves the node's explicit distinction between descent to `A` of the
  prescribed isomorphism and existence of a possibly different `k`-isomorphism.

Dependency declarations used (all signatures and docstrings read):

- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`:
  `AlgebraicGeometry.ProjectiveSpace`, `.ProjectiveLine`, `.ProjectiveSpace.map`,
  and `.ProjectiveSpace.isPullback_map`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`:
  `AlgebraicGeometry.ProjectiveLine.TwistData`, which confirms the standard-chart
  projective line is the existing base-change model.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`,
  with the actual `vanishingIdeal`, `subscheme`, `subschemeι` and kernel interfaces.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` and `algebraMap`.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` and `.Basic`:
  the recorded closure interface and `IsAlgClosed`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`,
  `isClosed_of_mem_irreducibleComponents`, and `IrreducibleSpace`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, and the universal property.
- `Mathlib.AlgebraicGeometry.Over`: the `Over` formulation of field-linear
  scheme isomorphisms. Standard `Subalgebra.FG`, `Ideal.IsMaximal`, quotient rings
  and `AlgEquiv` supply the finite-stage and rational-specialization objects.

The module imports the stated proof dependencies as ordinary imports: finitely generated
subalgebra union, subset geometric irreducibility, product-component bijection, geometric
reducedness test, field-tensor irreducibility, projective standard charts, affine-transition
spreading out, and the Mathlib affine/Noetherian/faithfully-flat/maximal-ideal/residue-field
interfaces. Their proof roles are recorded step by step in the declaration docstrings.

Edge cases checked before writing and again against the final signatures:

- Empty `C`: no irreducible component exists, so the first theorem gives the empty
  bijection and vacuous component assertions. The other statements have no `i` with
  the required component image. No accidental `Nonempty C` binder appears.
- Nonreduced `C`: its components use the reduced induced structure. No assumption
  incorrectly makes `C` itself reduced.
- Nonseparated finite-type schemes: no separatedness premise is introduced. Closed
  components remain finite type over a Noetherian field and hence finitely presented
  via quasi-compactness and local Noetherian quasi-separatedness.
- `L = k` and arbitrary characteristic: all spectra and maps are defined, and all
  claimed assertions retain their ordinary identity-extension interpretations.
- Transcendental extension and an automorphism with coefficients outside `k`: the
  finite subalgebra may contain these coefficients and denominators. Specialization
  may change the automorphism, as the statement permits. It never asserts that the
  original isomorphism descends all the way to `k`.
- Zero subalgebra/zero quotient: a unital subalgebra of the field `L` is nontrivial;
  `m.IsMaximal` and the explicit quotient equivalence ensure the specialization has
  precisely residue field `k`. No arbitrary residue-field identification is hidden.

Searches for an existing exact statement:

- `msearch.py`, LeanFinder: "Reduced irreducible components under an extension of
  algebraically closed fields and descent of an isomorphism with the projective line".
  Eight results, including Weierstrass point comparison, `projIsoSpecTopComponent`,
  the Proj valuative criterion and `Scheme.SpecToEquivOfField`; no exact statement.
- `msearch.py`, Loogle: "irreducibleComponents, IsAlgClosed, ProjectiveSpace".
  No results; Loogle does not know the project-specific `ProjectiveSpace` name.
  Retried with "irreducibleComponents": twelve relevant topological declarations,
  including the definition and preimage/image component lemmas, but no reduced
  component scheme theorem or projective-line isomorphism descent.
- `msearch.py`, Mathlib grep in `AlgebraicGeometry`:
  "projectiveLine.*descent|geometric.*components|components.*baseChange".
  Only `GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents`;
  it does not state this theorem.
- Direct `rg` in `WeilConjectures` and `Sheaf`: item id and the three proposed
  declaration names gave no matches. Concept searches for components, projective
  line and descent found component predicates, the semistable-marked consumer and
  the valuation geometric-component theorem. The latter gives a related component
  statement over valuation residue fields, but not descent of a prescribed
  projective-line isomorphism; none is an exact existing statement for this node.
- The upstream declaration-name index also has none of the proposed names.

Validation: the module was compiled through `scompile.py` in module mode, both as
sandbox and named library module, with no errors or warnings. All three theorems
remain `sorry`, as required at stage 2. No mathematical fault or statement correction
was found. The delivery dry run is recorded by the delivery tool.

## Second reading by Q51

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
