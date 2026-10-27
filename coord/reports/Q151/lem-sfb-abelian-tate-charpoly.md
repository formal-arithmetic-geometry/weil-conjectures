## Worker report

The delivery states `lem-sfb-abelian-tate-charpoly` in
`Sheaf.AlgebraicGeometry.AbelianVariety.RationalTateCharpoly`, with main declaration
`AlgebraicGeometry.IsAbelianVariety.existsUnique_rational_tate_charpoly`.
The only changes to the item are its `lean` record and the addition of the new
canonical-action definition node to `stmt_deps`. The mathematical statement,
proof, proof dependencies, source and status are unchanged.

Hypotheses and clauses, individually:

- The field `k` is `{k : Type u} [Field k]`, with explicit universe `u`.
  Algebraic closedness is `[IsAlgClosed k]`, not an assumption about a chosen
  algebraic closure of a smaller field.
- The abelian variety over `k` is `A : Over (Spec (.of k))` with `[GrpObj A]`
  and `[IsAbelianVariety A]`. These are the recorded notions; properness,
  smoothness and connectedness are the fields of that existing class.
- The dimension `g` is the existing `IsAbelianVariety.dim A`.
  `IsAbelianVariety.topologicalKrullDim_eq` identifies its natural-number value
  with `topologicalKrullDim A.left`. No independent dimension or finiteness
  hypothesis is added.
- `End_k(A)` uses `Additive (Grp.mk A ⟶ Grp.mk A)`. A morphism between these
  group objects is precisely a scheme morphism over `k` compatible with the
  group structure. Its addition is pointwise addition from the commutative
  group-scheme structure, using Mathlib's `Grp` group-object and Hom instances.
  This excludes translations and arbitrary scheme endomorphisms. The tensor
  product is the existing Mathlib tensor product over `ℤ`, with `ℚ` on the
  right as in the item. The theorem uses the underlying additive tensor space
  of the composition algebra, and does not introduce another multiplication
  or depend on a multiplication convention.
- The quantified rational endomorphism is `(f : RationalEndomorphisms A)`.
  This abbreviation is the actual tensor product, not a fraction chosen with
  an unproved existence assertion or a freely supplied representation.
- Existence of `P_u ∈ ℚ[X]` is `∃ P : Polynomial ℚ`.
  Monicity is `P.Monic`; the precise degree is `P.natDegree = 2 * dim A`.
  A monic polynomial over `ℚ` is nonzero, so natural degree is its actual degree.
- Every allowable prime is covered by
  `∀ (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k)`.
  Coefficient extension is `P.map (algebraMap ℚ ℚ_[ℓ])`.
  Its equality to the determinant polynomial is the equality to
  `rationalEndomorphismTateCharpoly A ℓ hℓ f`.
  This helper is exactly `LinearMap.charpoly` of the canonical rational action
  on the recorded `rationalTateModule ℓ A`. Mathlib's `LinearMap.charpoly` uses
  `det(X I - T)` in any basis. Its finite-dimensional instance is obtained
  internally from `nonempty_linearEquiv_rationalTateModule`; it is not a
  hypothesis imposed on the caller. Changing that instance does not change
  the mathematical polynomial.
- Uniqueness is the next explicit conjunct: for every `Q : Polynomial ℚ`
  that is monic, has degree `2 * dim A`, and has all the same Tate realizations,
  `Q = P`. It is uniqueness among the polynomials described in the main clause,
  without requiring the competing polynomial to satisfy the subsequent
  integrality or dimension-zero properties.
- Integral endomorphisms are exactly the image of the map `a ↦ a ⊗ₜ[ℤ] 1`.
  The clause is
  `(∃ a : Additive (Grp.mk A ⟶ Grp.mk A), f = a ⊗ₜ[ℤ] (1 : ℚ)) →
   ∀ n : ℕ, ∃ z : ℤ, P.coeff n = (z : ℚ)`.
  Thus every coefficient lies in `ℤ`; no assumption that `f` is an isogeny is
  made. This is equivalent to having an integer-coefficient polynomial mapping
  to `P`, and does not merely assert that its values at integers are integers.
- The final explicit clause `(dim A = 0 → P = 1)` retains `g = 0`.

The main theorem and the named additivity theorem have `sorry` proofs only.
Their docstrings contain the source and full natural-language proof plans.
Definitions contain actual data; the action is a tensor-product lift of a
specified bilinear map. There are no unspecified maps or Nonempty choices
of representations.

Dependency declarations used, with source signatures/docstrings read:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the algebraically
  closed clause of def-weil-algebraic-closure).
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`:
  `IsAbelianVariety`, `IsAbelianVariety.dim`,
  `IsAbelianVariety.topologicalKrullDim_eq` (def-sc-abelian-variety and its
  existing dimension convention).
- `Mathlib.CategoryTheory.Monoidal.Grp` and
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `GrpObj`, `Grp`,
  `Hom.group`, `Hom.commGroup`, and the group-object structure on `Grp.mk A`.
  These implement the group-scheme and group-homomorphism terminology of
  def-sc-group-scheme. `IsAbelianVariety.isCommMonObj`, in upstream
  `AbelianVariety.Basic`, provides commutativity.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule`:
  `tateModule`, `rationalTateModule`, `rationalTateModuleMap` and
  `nonempty_linearEquiv_rationalTateModule`. The node sk-def-av-tate has no
  `lean` record, but its closed upstream audit names this module. I read its
  definitions and componentwise-action docstrings in the actual source.
  The rational action reuses that integral action, with no duplicate Tate module.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and `Basic`:
  `TensorProduct`, `TensorProduct.lift` (def-weil-pbc-module-tensor-product).
  The new action also uses `LinearMap.restrictScalars₁₂`, `compl₁₂`,
  `LinearMap.lsmul` and `AddMonoidHom.toIntLinearMap` to construct the balanced
  bilinear extension using existing APIs.
- `Mathlib.NumberTheory.Padics.PadicNumbers`: `Padic` with notation `ℚ_[ℓ]`
  and its rational algebra map (def-weil-l-adic-numbers).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, as represented by
  the recorded dimension theorem above (def-kun-topological-krull-dimension).
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`; `Polynomial.Monic`,
  `natDegree`, `map`, `coeff` render the polynomial clauses.
- `Mathlib.LinearAlgebra.Charpoly.Basic`: `LinearMap.charpoly`, whose matrix
  definition is precisely the requested determinant polynomial
  (def-weil-characteristic-polynomial). `LinearMap.det`, in
  `Mathlib.LinearAlgebra.Determinant`, is the recorded determinant notion;
  no second determinant is defined.

Public imports expose the statement dependencies. Plain proof imports include
`Sheaf.RingTheory.MultiplicativePolynomialNorm`,
`Sheaf.NumberTheory.Padics.RootProductRigidity`,
`WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable` and
`Mathlib.RingTheory.Localization.BaseChange`. Their recorded declarations and
proof docstrings were read. The Tate rank theorem and Cayley--Hamilton and
charpoly-degree facts are already available through the statement imports.
The geometric Hom-finiteness, degree-polynomial, degree-multiplicativity and
Tate-valuation proof nodes have no published Lean bindings in the read clone;
there is no module to import for them yet. Their steps remain in the proof
plan, and are not replaced by assumptions.

Edge cases checked:

- Dimension zero: no `Nontrivial` assumption on the endomorphism algebra;
  the tensor space and Tate vector space can be zero. The polynomial is `1`,
  monic of degree zero, including at the unique endomorphism.
- The zero endomorphism and non-isogenies are allowed. No invertibility or
  nonzero-determinant hypothesis occurs.
- Positive characteristic, including 2 and 3, is covered; characteristic zero
  allows every prime. At least one of 2 and 3 is allowable for uniqueness.
- A denominator may be divisible by the characteristic of `k`. Scalars are
  inverted only in `ℚ`/`ℚ_[ℓ]`, never in `k`; denominators divisible by `ℓ`
  are also valid in the rational Tate space.
- Integral endomorphisms are the full group-scheme endomorphism image;
  rational endomorphisms with genuinely nonintegral coefficients are not
  incorrectly required to have integer characteristic coefficients.
- Arbitrary field universe `u` is explicit; all geometric source objects use
  the upstream `Over (Spec (.of k))` convention and no extra universe equality.

Searches for an existing statement and its missing action:

- `msearch.py ... leanfinder` with “The characteristic polynomial of a rational
  endomorphism of an abelian variety on its rational Tate module is rational
  and independent of ell”: eight hits, headed by `LinearMap.polyCharpolyAux`
  and its specialization lemmas; none proves rationality of a Tate action.
- `msearch.py ... loogle 'LinearMap.charpoly, TensorProduct.lift'`: zero hits.
- `msearch.py ... grep 'TateModule|abelian.variety|rationalEndomorphism'`:
  zero Mathlib hits.
- The action-specific LeanSearch, LeanFinder, Loogle and grep searches are
  recorded in full by query and returned declaration names in the new node's
  `mathlib_searches`. They found generic endomorphism/tensor APIs, not this
  rational geometric action.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for rational endomorphisms,
  tensor endomorphisms, rational Tate action and characteristic polynomials
  found only the upstream integral `rationalTateModuleMap` and unrelated
  statements. Searching `lem-sfb-abelian-tate-charpoly` in upstream sources
  found no attached declaration. A full-name search in Mathlib, both project
  source roots, and `dag/lean_names_upstream.json` found none of the new names.
- DAG searches for `End.*otimes`, rational endomorphisms, and endomorphism
  algebra found consumers (degree-polynomial, polarization, and this item),
  not a definition node for this action. `tools/blueprint_refs.py search
  'rational endomorphism'` returned zero nodes. The ancestor command returned
  `blueprint.from.node = None`, retained as JSON null in the new node.

The paper was read locally using pdftotext: printed pp.43--52, especially
Theorem 10.9, Remark 10.11 and Proposition 10.20. No statement correction or
STATEMENT-DISPUTED flag is needed. The historical CompactObject example is
now a withdrawn module; I followed the current module/public-import/exposed
section rules from the standing brief and live statement modules instead.

## New nodes

`def-sfb-rational-abelian-endomorphism-action` defines the actual tensor space
of rational group-scheme endomorphisms and the canonical rational extension of
the upstream integral Tate action. Its source is Milne I section 10,
pp.43--47. The module is
`Sheaf.AlgebraicGeometry.AbelianVariety.RationalEndomorphismAction`.
`RationalEndomorphisms` abbreviates the existing group-object Hom additive
space tensor `ℚ`; `rationalTateModuleMap_add` records the additivity needed
for the construction, with a coordinatewise proof docstring;
`integralEndomorphismTateAction` bundles the given integral action as an
integer-linear map; `rationalEndomorphismTateAction` is `TensorProduct.lift`
of `(a,q) ↦ (q : ℚ_[ℓ]) • rationalTateModuleMap a`.
Thus its value on every pure tensor is specified by real data. This definition
node explicitly includes the additivity assertion that its named postponed
well-definedness theorem states. Searches listed above found no earlier
canonical rational-action declaration or owning definition node. The geometric
Tate module itself is reused, not redefined. The main module's charpoly helper
only applies the existing characteristic polynomial to this action, using the
existing rank theorem to supply the finite-dimensional instance.

## Second reading by Q151

This is the author's second reading, not an independent worker review; the
prompt reserves independent review for the maintainer and prohibits spawning
other agents. I reopened the node statement and both delivered files and
checked every hypothesis/clause against the mapping above.

The rational vector-space endomorphism really acts on the recorded geometric
Tate module; its integral map takes the underlying `IsMonHom` morphism of a
bundled group-scheme endomorphism. The tensor lift explicitly uses the rational
embedding into `ℚ_[ℓ]` and scalar multiplication, so no arbitrary action is
introduced. The characteristic polynomial helper adds no finite-dimensional
hypothesis. During this reading I made uniqueness explicit among all monic
polynomials of the prescribed degree satisfying the realizations, separately
from the coefficient and dimension-zero conclusions. Integral coefficients
are expressed coefficientwise, and the zero-dimensional implication is present.
All variables and universes are bound; the old statement and proof are intact.

Validation: both delivered modules compiled separately through scompile.py.
The first dry run required the current schema field `import_flags` on the new
node; I added the empty list, matching the live definition-node schema.
