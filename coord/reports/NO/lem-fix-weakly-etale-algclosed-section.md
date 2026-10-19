## Worker report

This delivery records the exact existing declaration
`AlgebraicGeometry.exists_comp_eq_id_of_weaklyEtale` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`, lines 81–100
of the source checkout. The same signature, docstring and proof were read using
`scompile.py --source WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`.
No module is added and no theorem or definition is restated. The node already carried
an attachment to this theorem; this delivery supplies the complete stage-2 Lean record.
Only `lean` changes in the copied node, including retaining the existing node status.

The existing signature is:

```lean
theorem exists_comp_eq_id_of_weaklyEtale {K : Type u} [Field K] [IsAlgClosed K] {V : Scheme.{u}}
    (f : V ⟶ Spec (.of K)) [WeaklyEtale f] (v : V) :
    ∃ σ : Spec (.of K) ⟶ V, σ ≫ f = 𝟙 _
```

Every hypothesis and clause corresponds as follows:

- The algebraically closed field Ω is `K : Type u` with `[Field K] [IsAlgClosed K]`.
  No fixed base field or chosen algebraic closure is required by the node.
- The arbitrary scheme Z is `V : Scheme.{u}`. It is not required to be affine,
  quasi-compact, connected, reduced by a separate hypothesis, or of finite type.
- The morphism q is `(f : V ⟶ Spec (.of K))`.
- Weakly étale is `[WeaklyEtale f]`, Mathlib's flatness of f and its diagonal.
- Nonemptiness of the underlying topological space is the point argument `(v : V)`:
  Mathlib coerces a scheme to its underlying point type. Giving any witness of
  `Nonempty V` supplies this argument. Conversely such an argument witnesses
  nonemptiness; there is no chosen-point condition on the resulting section.
- The section s is the existential `σ : Spec (.of K) ⟶ V`.
- The identity q ∘ s = id is `σ ≫ f = 𝟙 _`, with diagrammatic composition.
  There is no extra requirement that σ pass through the supplied v.

Dependency declarations read, including their full definitions and docstrings:

- `def-weil-algebraic-closure`: its `mathlib_match` explicitly identifies
  `IsAlgClosed` in `Mathlib.FieldTheory.IsAlgClosed.Basic` for the part used here.
  That class states that every polynomial splits; its docstring and `exists_root`
  give equivalence with having roots for all nonconstant polynomials. The same
  dependency also names `AlgebraicClosure` and `IsAlgClosure`, which are not needed
  because this statement starts with an arbitrary algebraically closed field.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`
  in `Mathlib.AlgebraicGeometry.Scheme`; schemes are locally affine locally ringed
  spaces, with morphisms of locally ringed spaces. Its `CoeSort` is the point type.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`; `Spec (.of K)` uses the actual spectrum.
- `def-weil-weakly-etale-morphism`: its `mathlib_match` is
  `AlgebraicGeometry.WeaklyEtale` in
  `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`, whose two fields are
  `Flat f` and `Flat (pullback.diagonal f)`.

Source and proof check: read `literature/stacks-project/proetale.tex`,
`lemma-geometric-lift-to-cover` (Tag 0F6C). Its proof uses surjectivity of the cover
and separable algebraic residue extensions of weakly étale maps. For a nonempty
scheme over an algebraically closed field, such residue fields equal the base,
giving a rational point and hence a section. The existing theorem implements the
same existence argument through an affine neighbourhood of a source point:
its nonzero weakly étale coordinate algebra has a K-algebra map to K by
`Algebra.WeaklyEtale.nonempty_algHom_of_isAlgClosed`; applying Spec and the open
immersion gives σ and functoriality proves the composite identity. That helper's
signature and proof were also read. The node's `proof` is empty; no postponed
proof or additional DAG interface is introduced.

Edge cases checked: an empty Z has no point argument, exactly as excluded by the
node. The theorem imposes no characteristic restriction, no finite-type condition,
and covers non-affine and non-quasi-compact sources by choosing one affine open.
For Z = Spec K and q the identity, the identity is a section. Disconnected sources
need only one point; no uniqueness or section through every supplied point is
asserted. The field and schemes use the common arbitrary universe u required by
Mathlib's category of schemes, matching the project's size convention.

Searches performed on 2026-10-17:

- `msearch.py ... leanfinder "nonempty weakly etale scheme over an algebraically
  closed field admits a section"`: eight Mathlib hits, including finite-type
  étale algebra results; none state the arbitrary weakly étale scheme result.
- `msearch.py ... loogle "AlgebraicGeometry.exists_comp_eq_id_of_weaklyEtale,
  IsAlgClosed"`: no hits; upstream-only identifier unknown to Mathlib search.
- `msearch.py ... leansearch "A nonempty weakly etale scheme over an algebraically
  closed field has a section"`: eight hits, including Scheme and étale results;
  no exact Mathlib theorem.
- `msearch.py ... grep "WeaklyEtale|exists_comp_eq_id_of_weaklyEtale"
  AlgebraicGeometry/Morphisms`: five hits, the WeaklyEtale class and its basic API.
- `rg` of `exists_comp_eq_id_of_weaklyEtale|nonempty_algHom_of_isAlgClosed` in
  the source `WeilConjectures` tree: found the exact theorem and its algebraic
  input, with consumers in AlgClosedFieldSite and the adic stalk modules.
- `rg` of the item id in that tree: no blueprint-id annotation, but the name and
  signature above establish the exact match.
- `rg` of `exists_comp_eq_id_of_weaklyEtale|weakly.*[Ss]ection|[Ss]ection.*weakly`
  in `lean/Sheaf`: only unrelated weakly contractible section results; no duplicate.

No statement correction, missing notion, unusable dependency, or
STATEMENT-DISPUTED issue was found. The current source resolves the existing
upstream declaration, so no additional module is appropriate under the one-notion rule.

Validation is through the prescribed `scompile.py` existing-declaration probe and
`deliver2.py --no-push` preflight, followed by `deliver2.py` delivery.

The explicit `scompile.py` probe passed both sandbox and library compilation, with
no warnings. Its printed type matches the recorded signature, and `#print axioms`
reports exactly `[propext, Classical.choice, Quot.sound]`, with no sorry axiom.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
