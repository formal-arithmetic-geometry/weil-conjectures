## Worker report

The module `Sheaf.AlgebraicGeometry.RationalFixedSpaceBaseChange` defines
`AlgebraicGeometry.RationalRepresentation.fixedSpace` and states
`AlgebraicGeometry.RationalRepresentation.fixedSpace_baseChange`, with `sorry` as its
only theorem proof. This repair uses the now-landed definition node for the existing
NaturalRepresentation structure; there is no mathematical statement correction or Lean change.
The fixed-space construction is introduced by this item's own
statement and belongs to this item's module.

The existing `NaturalRepresentation` interface, read in
`Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`, is used for both the
input and the restricted representation. The same module's `finite_dictionary` states
that, for finite-dimensional V, these natural actions correspond to actual group-scheme
homomorphisms to `GeneralLinearGroup (FiniteIndex V) k`, with the point action specified
in a chosen finite basis. Its `FiniteIndex` and `finiteBasis` include dimension zero.
Consequently a natural representation here means precisely the rational representation
in the node, including its rationality conclusion, rather than just a representation
of the abstract group G(k). The landed existing:true definition node
`def-sfb-rational-natural-representation` owns the plain structure and is cited in
`stmt_deps`. The proof_deps list is restored exactly to the base, as the latest return
requires. No theorem or choice from it occurs in the signature.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`.
- The k-scheme is `{G : Scheme.{u}} [G.Over (Spec (.of k))]`; its group structure is
  `[GrpObj (G.asOver (Spec (.of k)))]`, its affineness is `[IsAffine G]`, and finite type
  is `[LocallyOfFiniteType (G ↘ Spec (.of k))] [QuasiCompact (G ↘ Spec (.of k))]`.
- The closed subgroup scheme is `{H : Over (Spec (.of k))} [GrpObj H]` with
  `(i : H ⟶ G.asOver (Spec (.of k))) [IsClosedSubgroupScheme i]`. The recorded class
  includes `IsSubgroupScheme`, hence the group-homomorphism and pointwise-injectivity
  requirements, and the closed-immersion requirement on `i.left`.
- The finite-dimensional vector space is `{V : Type u} [AddCommGroup V] [Module k V]`
  with `[FiniteDimensional k V]` on the theorem. The rational representation is
  `(r : NaturalRepresentation (k := k) G V)`, using the existing equivalent encoding.
- `fixedSpace r i` is an actual submodule, constructed as the infimum over every bundled
  commutative k-algebra B and h in H(B) of the kernel of
  `(r.action B (h ≫ i) - id) ∘ (v ↦ 1 ⊗ v)`. Thus its membership condition is exactly
  the defining universally quantified fixed-vector equation of the node. Bundling the
  test algebras with `CommAlgCat` records their ring and algebra structures without
  inserting any new mathematical hypothesis.
- For every `(A : Type u) [CommRing A] [Algebra k A]`, the first conjunct asserts
  `Function.Injective ((fixedSpace r i).subtype.baseChange A)`. This is the natural
  tensor inclusion A tensor V^H to A tensor V.
- The range equivalence, for every `w : A ⊗[k] V`, identifies its image exactly with
  the fixed elements after every `(B : Type u) [CommRing B] [Algebra k B]` and every
  compatible map `(α : A →ₐ[k] B)`, and for every `(h : points H B)`. The vector's
  extension is the canonical `α.toLinearMap.rTensor V w`, and the subgroup action is
  `r.action B (h ≫ i)`. Giving α is exactly giving the further A-algebra structure
  compatible with k, as in the displayed formula in the node.
- The second conjunct is conditional on `IsNormalSubgroupScheme i`; normality is not
  imposed on the base-change assertion. It gives
  `s : NaturalRepresentation (k := k) G (fixedSpace r i)` and specifies that every
  `s.action A g` agrees with `r.action A g` after the injective tensor inclusion. Since
  these are linear automorphisms, this also asserts preservation of the whole tensor
  image and its inverse, not just preservation on k-points. Naturality is a field of
  `NaturalRepresentation`. Its finite-dimensional dictionary gives the rational
  group-scheme representation on the actual fixed subspace.
- The final clause `∀ A ... (h : points H A), s.action A (h ≫ i) = 1` says H acts
  trivially over every algebra. No choice of an unrelated restricted representation
  can satisfy the specified intertwining equation: the tensor inclusion is injective.
- The tensor convention is A tensor V, as in the shared representation interface and
  Mathlib's `LinearMap.baseChange`. `TensorProduct.comm k V A` identifies this with
  the node's V tensor A; under it 1 tensor v becomes v tensor 1. The same symmetry
  identifies the inclusion, scalar extension map, fixed-vector equation and restriction.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, specialized to
  `Over (Spec (.of k))` (def-sc-group-scheme).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms and
  `AlgebraicGeometry.Spec` (def-pc-scheme, def-weil-affine-spectrum).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`
  (def-weil-finite-type-morphism).
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme`,
  `IsNormalSubgroupScheme` (def-sc-group-scheme-subgroup). Their full signatures
  quantify over every test algebra in the common scheme universe.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes`, publicly exposed by the dictionary:
  the recorded general-linear-group node reuses the upstream
  `AlgebraicGeometry.GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv` in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`. Read these signatures
  and the dependency record's note: GL is reused upstream; the new special-linear
  construction is not needed here. `GeneralLinearGroup.RationalHom`, defined in
  `.GeneralLinear.Lie`, is a genuine scheme morphism, with `IsMonHom` for its group law.
- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`: `FiniteDimensional` is `Module.Finite`
  (def-weil-finite-dimensional-subspace). Submodules inherit this condition.
- `Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`:
  `AlgebraicGeometry.RationalRepresentation.NaturalRepresentation`, `finite_dictionary`,
  `FiniteIndex`, `finiteBasis`. The plain structure is now owned by
  def-sfb-rational-natural-representation; finite_dictionary and the other results
  provide the mathematical interpretation described by that module. The latest return
  requires leaving the base proof_deps unchanged, so that theorem is not added to the DAG.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring`: `points`, `points.map`,
  the shared scheme-point interface used in the dictionary.
- Proof-plan imports: `Mathlib.LinearAlgebra.Basis.VectorSpace`
  (`Module.Free.of_divisionRing`); `Mathlib.LinearAlgebra.FreeModule.Basic`
  (`Module.Free`); `Mathlib.LinearAlgebra.TensorProduct.Tower` and `.Map`
  (`TensorProduct`, `LinearMap.baseChange`, `LinearMap.rTensor`);
  `Mathlib.RingTheory.TensorProduct.Maps` and its basic dependency (the commutative
  algebra tensor-product/pushout operations). These are the recorded Mathlib leaves
  of the theorem's proof dependencies. The complete seven-step natural-language proof
  is in the theorem docstring; none is proved in this stage.

Source checked directly in the local Milne PDF using pdftotext: Proposition 4.31 on
printed p.96 gives precisely the universal further-algebra criterion and its basis-of-A
coefficient proof; Proposition 4.33 identifies the fixed space with the universal-point
kernel; Lemma 5.15 on printed p.102 uses the normality conjugation computation over each
further algebra. The statement agrees with these sources.

Edge cases checked before writing and on rereading:

- V=0 and V^H=0: the definition is the zero submodule and all tensor spaces are zero.
  `NaturalRepresentation` has its unique possible automorphisms; `finite_dictionary`
  explicitly handles the empty basis and GL(0)=Spec k. No nonzero or positive-dimension
  assumption occurs.
- A=0: arbitrary commutative rings include the zero ring. A tensor V=0, the tensor
  inclusion has zero source and target and is injective. Compatible further algebras
  are zero rings as well. No `Nontrivial A` assumption is added.
- A=k, H=1 and H=G recover respectively the original fixed-vector condition, the whole
  vector space and the full invariant subspace. Normality is needed only for restriction.
- Infinite-dimensional A and algebras with nilpotents are allowed; there is no finite,
  reduced, smooth, connected, perfect-field or characteristic hypothesis.
- Universes are explicitly bound. The field, schemes, vector space and all test
  algebras use the same arbitrary universe u, as in the recorded scheme-point and
  natural-representation interfaces. In particular test-algebra quantifiers cannot
  be accidentally vacuous because of a smaller independent universe.

Searches for existing statements and notions (2026-10-24):

- `msearch.py ... leanfinder "Rational fixed vectors of an affine group scheme commute
  with arbitrary algebra base change and normal subgroup invariants are a rational
  subrepresentation"`: 8 hits, including `Rep.toInvariants`, `Representation.toInvariants`
  and `Representation.le_comap_invariants`. These concern a single abstract group and
  do not give the rational, universal further-algebra statement.
- `msearch.py ... leansearch "Rational representations affine group scheme invariants
  arbitrary algebra scalar extension"`: 8 hits, none stating the item.
- `msearch.py ... loogle "Representation.invariants"`: 12 hits; the abstract-group
  invariant submodule and normal-subgroup restriction have no all-algebra comparison.
- `msearch.py ... grep "invariants.*baseChange|baseChange.*invariants"
  RepresentationTheory`: no hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf`, for rational representations,
  RationalRepresentation, rationalFixed, fixedSpace and invariant declarations:
  found the shared natural-representation dictionary, the separate basis-coordinate
  `IsInvariantRationalSubspace`, and abstract continuous-group fixedSpace constructions;
  none is this rational fixed subspace or its base-change theorem. Used the dictionary.
- `grep -rn "lem-sfb-rational-fixed-space-base-change" lean/WeilConjectures`: no hits.
  Search of `dag/lean_names_upstream.json` for the delivered names found no collision.
  DAG searches found the item and its parent normal-subgroup-kernel use, not an existing
  declaration of this statement. The return identifies the missing definition-node
  ownership, supplied without adding any Lean code in this repair.

Compilation: prescribed `scompile.py Q84 lem-sfb-rational-fixed-space-base-change` ran
both sandbox and library module checks successfully, with no errors or warnings.

## Repair of return 80bf2f5c1e34

H7/b: restored proof_deps exactly to the ten entries of the current main branch and
the list specified in the return. The accepted proof steps are unchanged, and the
restored proof_deps is exactly the union of their uses. The item differs from main
only in lean and stmt_deps; stmt_deps is the base list plus
`def-sfb-rational-natural-representation`. The Lean file and lean record are unchanged
from the returned delivery, as requested. The earlier lean.note's sentence about the
dictionary being in proof_deps is superseded by this repair; the return explicitly
requested preserving that record. The mathematical statement is unchanged.

Race resolved: `def-sfb-rational-natural-representation` has landed from Q91, with
existing:true ownership of `NaturalRepresentation` and `genericPoint` in
`Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`. I read its current
record and the structure's action/naturality fields. Its existing definition is the
same one used by this module. Removed Q84's duplicate node file from the sandbox and
retained the statement citation to the landed node. No definition node is delivered.

H11 from the earlier return remains repaired by the clause-by-clause second reading
below. No independent agents were started.

## Second reading by Q84

This is my own second reading; the dispatcher forbids starting other agents. The
maintainer supplies the independent review. I compared the unchanged Lean file with
the returned head and checked the current live definition and DAG ownership.

- Field: `{k : Type u} [Field k]`.
- Affine group scheme over k: `{G : Scheme.{u}} [G.Over (Spec (.of k))]`,
  `[GrpObj (G.asOver (Spec (.of k)))]` and `[IsAffine G]`.
- Finite type: `[LocallyOfFiniteType (G ↘ Spec (.of k))]` and
  `[QuasiCompact (G ↘ Spec (.of k))]`.
- Closed subgroup: `{H : Over (Spec (.of k))} [GrpObj H]`,
  `(i : H ⟶ G.asOver (Spec (.of k))) [IsClosedSubgroupScheme i]`.
- Vector space and finite dimension: `{V : Type u} [AddCommGroup V] [Module k V]`
  and `[FiniteDimensional k V]`.
- Rational representation: `(r : NaturalRepresentation (k := k) G V)`. The signature
  uses the plain structure owned by the now-landed definition node. Finite-dimensional
  equivalence with scheme homomorphisms is supplied in the proof by finite_dictionary.
- Definition of V^H: `fixedSpace r i := ⨅ (B : CommAlgCat.{u} k) (h : points H B),
  LinearMap.ker (((r.action B (h ≫ i)).toLinearMap.restrictScalars k - LinearMap.id) ∘ₗ
  TensorProduct.mk k B V 1)`. This imposes precisely every required fixed-vector equation.
- Every scalar algebra: `∀ (A : Type u) [CommRing A] [Algebra k A]`.
- Injective natural inclusion: `Function.Injective ((fixedSpace r i).subtype.baseChange A)`.
- Exact image, in both directions: for every `w : A ⊗[k] V`,
  `w ∈ LinearMap.range ((fixedSpace r i).subtype.baseChange A) ↔` the universally
  quantified fixed-vector condition that follows.
- Every further algebra and every subgroup point: `∀ (B : Type u) [CommRing B]
  [Algebra k B] (α : A →ₐ[k] B) (h : points H B)`.
- Fixedness after extension: `r.action B (h ≫ i) (α.toLinearMap.rTensor V w) =
  α.toLinearMap.rTensor V w`.
- Normality is conditional: `IsNormalSubgroupScheme i →`; it does not constrain the
  preceding base-change assertion.
- Restricted rational representation: `∃ s : NaturalRepresentation (k := k) G
  (fixedSpace r i)`. Finite-dimensionality of a subspace and finite_dictionary give
  its rational group-scheme interpretation.
- Preservation and the actual restriction: for every A, g and w,
  `(fixedSpace r i).subtype.baseChange A (s.action A g w) =
  r.action A g ((fixedSpace r i).subtype.baseChange A w)`. This pins the restriction
  by injectivity; automorphisms for g and its inverse give preservation of the image.
- Trivial H-action: `∀ (A : Type u) [CommRing A] [Algebra k A] (h : points H A),
  s.action A (h ≫ i) = 1`.
- GL(V)(A) is the automorphism group appearing in `NaturalRepresentation.action`.
  `finite_dictionary` uses the actual existing GL scheme and includes its empty basis,
  so V=0 gives GL(0)=Spec k. No nonzero or positive-dimension hypothesis appears.
- The node's V tensor A convention corresponds to A tensor V throughout by
  `TensorProduct.comm`; the inclusion, scalar-extension map and action equations
  use the shared natural-representation convention consistently.
- Definition-node reading: `structure NaturalRepresentation` has exactly the action
  group homomorphisms and the displayed naturality equation. It is a real plain
  structure with no theorem choice or postponed data. The landed node states both fields,
  uses the same arbitrary universe u, and imposes neither finite dimension nor finite type.

V=0, V^H=0, H=1, H=G, A=0, infinite-dimensional A and nonreduced H/test algebras
remain covered. No mathematical mismatch or disputed statement remains. The only
changes from the returned delivery are restoration of the base proof_deps, removal
of the duplicate definition-node file after its landing, and this report, as requested.
