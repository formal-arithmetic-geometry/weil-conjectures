## Worker report

The module `Sheaf.AlgebraicGeometry.DiagonalizableHomFamilyRigidity` states
`AlgebraicGeometry.diagonalizable_hom_family_rigidity`, with its only proof `sorry`.
There are no new definitions and no proved assertions. The node statement is unchanged.
The sole additional statement dependency is the already landed
`def-sfb-diagonalizable-group`, whose exact Hopf-spectrum construction is reused.

I read the complete node and all seven original statement dependencies, their recorded
declarations and docstrings, the landed diagonalizable-group node and module, and the
four proof dependency interfaces. I read Milne's Theorem 12.36, printed pp.243--244,
and Remark 12.43, p.245 directly in the local PDF. The theorem is precisely the
algebraically closed, affine specialization stated by the node. There is no node fault
or statement dispute and no statement correction.

The hypothesis and conclusion correspondence is as follows:

| Node clause | Lean rendering |
| --- | --- |
| F is an algebraically closed field | `(F : Type u) [Field F] [IsAlgClosed F]` |
| D₁ and D₂ are F-group schemes | `(D₁ D₂ : Grp (Over (Spec (.of F))))`; `Grp` supplies each `GrpObj` |
| Both group schemes are affine | `[IsAffine D₁.X.left] [IsAffine D₂.X.left]` |
| Both are of finite type over F | `LocallyOfFiniteType` and `QuasiCompact` on each `Dᵢ.X.hom` |
| M₁ and M₂ are finitely generated abelian groups | `(M₁ M₂ : Type u) [AddCommGroup M₁] [AddCommGroup M₂] [AddGroup.FG M₁] [AddGroup.FG M₂]` |
| There exists a group-scheme isomorphism Dᵢ ≅ Spec F[Mᵢ] | `hDᵢ : Nonempty (Dᵢ ≅ diagonalizableGroup F Mᵢ)`, an isomorphism in `Grp (Over (Spec F))`, so it preserves the group structure |
| The specified basis, multiplication, coproduct, counit, inverse on F[Mᵢ] | The existing `diagonalizableGroup` is `hopfSpec` of `CommHopfAlgCat.of F (AddMonoidAlgebra F Mᵢ)`, using exactly those canonical operations |
| X is an affine F-scheme with structure morphism | `(X : Over (Spec (.of F))) [IsAffine X.left]`, with structure morphism `X.hom` |
| X is connected and of finite type | `[ConnectedSpace X.left] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]` |
| x₀ : Spec F → X is an F-point | `(x₀ : 𝟙_ (Over (Spec (.of F))) ⟶ X)`; the tensor unit is definitionally `Over.mk (𝟙 (Spec (.of F)))` |
| φ : X ×_F D₁ → D₂ is an F-morphism | `(φ : X ⊗ D₁.X ⟶ D₂.X)`; the cartesian tensor in `Over` is the actual scheme fibre product |
| A is any commutative F-algebra | `∀ (A : Type u) [CommRing A] [Algebra F A]` in `hφ`, with no reducedness, domain, or finite type restriction |
| x ∈ X(A) | `x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F A))) ⟶ X` |
| d ↦ φ(x,d) is a group homomorphism D₁(A) → D₂(A) | An existential `f : (Spec A ⟶ D₁.X) →* (Spec A ⟶ D₂.X)`, with `∀ d, f d = lift x d ≫ φ`; here each hom-set is in `Over` and its group law is the canonical one induced by `GrpObj` |
| Naturally under change of A | Each evaluation is pairing of scheme morphisms followed by φ. Precomposition by `Spec` of an F-algebra map commutes with this pairing and composition. This is intrinsic naturality of the displayed map, rather than an extra arbitrary family of maps. The equality specifying every value of `f` uniquely determines each homomorphism |
| φ at x₀ uses the base-changed point x₀,A | `lift (toUnit D₁.X ≫ x₀) (𝟙 D₁.X) ≫ φ` is the F-morphism D₁ → D₂; its value on d is φ(x₀,A,d) since `d ≫ toUnit D₁.X` is the unique map Spec A → Spec F |
| φ = φ_x₀ ∘ pr_D₁ as F-morphisms | `φ = snd X D₁.X ≫ (lift (toUnit D₁.X ≫ x₀) (𝟙 D₁.X) ≫ φ)` |
| No smoothness or reducedness of X,D₁,D₂ required | No `Smooth`, `IsReduced`, or analogous hypotheses occur |

All universes and variables are explicitly bound, with `autoImplicit false`. The common
universe `u` is the one for schemes, the base field, the finitely generated character
groups and the test algebras. Test algebras do not have a separate potentially smaller
universe. In particular the universal test algebras B[M₁ ⊕ M₁] and B used in the proof
are available. Larger common universes cover arbitrary size choices by the usual lifts.

Dependency declarations reused:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the component of
  `def-weil-algebraic-closure` actually used here; no choice of algebraic closure is needed.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, and its category of
  multiplication-preserving morphisms, giving the exact recorded group-scheme notion.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `CategoryTheory.Hom.group`, the
  canonical group structure on the represented point sets. `MonoidHom` between these
  groups is a group homomorphism, since preservation of inverses follows from its axioms.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Over`: the bundled category `CategoryTheory.Over`
  realizes the structure morphism and F-morphisms of `def-weil-scheme-over-base`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`, exactly the two
  components of finite type recorded by `def-weil-finite-type-morphism`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including nonemptiness.
- `Sheaf.AlgebraicGeometry.DiagonalizableGroup`: `AlgebraicGeometry.diagonalizableGroup`.
  Its full declaration and canonical Hopf operations were read; it needs no interface repair.
- Proof imports: `WeilConjectures.Mathlib.AlgebraicGeometry.Scheme`, providing
  `AlgebraicGeometry.Scheme.connectedSpace_iff_isIdempotentElem`;
  `Mathlib.RingTheory.TensorProduct.Maps` (and its Basic import), providing
  `Algebra.TensorProduct.productMap`, inclusions, multiplication and extensionality;
  `Mathlib.AlgebraicGeometry.Pullbacks`, providing `AlgebraicGeometry.pullbackSpecIso`.
  The spectrum dependency is already publicly available. No proof import cycle occurs.

Edge cases checked against the coefficient proof:

- A trivial character group on either side is allowed: no positive rank or nontriviality
  hypothesis appears. Torsion groups are allowed by `AddCommGroup` and `AddGroup.FG`.
- Positive characteristic and nonreduced μ_p are retained by the canonical Hopf construction.
- X = Spec(F[ε]/ε²) is connected and permitted: the proof only uses the absence of
  nontrivial idempotents, never an integral-domain or reducedness assumption.
- X empty is excluded by `ConnectedSpace`, as in the recorded definition; it would
  also admit no x₀. X = Spec F is included and the conclusion specializes correctly.
- A = the zero F-algebra is allowed by `[CommRing A] [Algebra F A]`; all its point sets
  consist of the unique morphism from the empty scheme, so the hypothesis is meaningful.
- A disconnected parameter X = Spec(F × F) could choose different homomorphisms on
  its components; this is exactly why the connectedness assumption is necessary.
- Homomorphisms are required on all A-points. Tests only on F-points would lose the
  intended infinitesimal cases, and are not used in this signature.

Searches for an existing statement (full tool results are in sandbox `searches.jsonl`):

- `msearch.py ... leanfinder "A connected family of homomorphisms between diagonalizable
  group schemes is constant"`: eight results about connected categories, affine limits,
  or diagonal morphisms; none states this theorem.
- `msearch.py ... leansearch "Homomorphisms of diagonalizable group schemes parametrized
  by a connected scheme are constant"`: eight results about scheme morphisms,
  continuous diagonal maps and representations; none states the theorem.
- `msearch.py ... loogle "GrpObj, IsMonHom"`: unqualified identifier unavailable.
  Corrected to `"CategoryTheory.GrpObj, CategoryTheory.IsMonHom"`: twelve results
  supplying the group-object API, not family rigidity.
- `msearch.py ... grep "diagonaliz|rigidity" AlgebraicGeometry`: no Mathlib hits.
- `rg` over `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry` for diagonalizability, rigidity and homomorphism
  families: no exact theorem; the existing `DiagonalizableGroup.lean` supplies the
  precise diagonalizable-group construction. Other rigidity results concern abelian
  varieties or nilpotent lifting, not this connected-family assertion.
- `rg` for the item id in `lean/WeilConjectures`: no hit. Searching the proposed
  declaration name in Mathlib, WeilConjectures and Sheaf: no hit. Searching
  `dag/lean_names_upstream.json` for rigidity/families: no exact statement attachment.
- Read `dag/nodes/sec-six-functors-basics/def-sfb-diagonalizable-group.json` and
  its recorded module. Reuse that landed node; no new definition node is necessary.

Validation: `scompile.py Q13 lem-sfb-diagonalizable-hom-family-rigidity` compiled
the delivered file in both sandbox and library module contexts successfully
(4.3 s and 8.7 s). No error or unexpected warning was printed.

## Second reading by Q13

I reopened the node and completed Lean file for a separate clause-by-clause pass.
The dispatcher forbids starting another worker; this is the worker's second reading,
with the maintainer's independent review to follow delivery.

I checked that the diagonalizability hypotheses are isomorphisms of group objects,
not merely isomorphisms of their underlying schemes. I checked the actual `Over`
cartesian tensor construction: its unit is Spec F with identity structure map and its
tensor is the scheme fibre product, so both x₀ and the conclusion have the correct
domains. I read the existing point-set group structure and checked that the specified
monoid homomorphism is exactly `d ↦ lift x d ≫ φ`, with naturality forced by this formula.
I checked that the conclusion first projects to D₁ and then evaluates at x₀, with the
composition order matching φ_x₀ ∘ pr_D₁. Every original hypothesis and every clause
is matched in the table above; none is omitted or strengthened. The original node is
unchanged apart from its Lean record and adding the landed definition dependency.
The docstring carries all four proof steps, including the universal nonreduced test
algebra, identity test, coefficient argument, and equality of scheme morphisms.
No mismatch was found in this pass and no source correction was needed.
