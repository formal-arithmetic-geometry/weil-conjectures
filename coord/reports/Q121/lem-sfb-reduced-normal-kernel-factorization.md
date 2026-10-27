## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.ReducedNormalKernelFactorization`
states `AlgebraicGeometry.reduced_normal_kernel_factorization`, with one `sorry`
and no new definitions or additional lemmas. The node's natural-language statement,
statement dependencies, proof and proof dependencies are unchanged.

### Hypotheses and clauses

- Algebraically closed field: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Group schemes and homomorphism: `H J : Grp (Over (Spec (.of k)))`, `q : H ⟶ J`.
  The bundled objects use the recorded `GrpObj` and morphisms use `IsMonHom`.
- Affine, smooth and connected H and J: `IsAffine _.X.left`, `Smooth _.X.hom`,
  and `ConnectedSpace _.X.left`, separately for each group.
- Finite type H and J: `LocallyOfFiniteType _.X.hom` and `QuasiCompact _.X.hom`.
- Faithful flatness of q: `[Flat q.hom.hom.left] [Surjective q.hom.hom.left]`.
  These are the geometric flatness and surjectivity conditions, equivalent to
  faithful flatness of the coordinate map for these affine schemes.
- N is the scheme-theoretic kernel: the first `IsPullback` square has edges
  `i.hom.hom`, `toUnit N.X`, `q.hom.hom`, and `η[J.X]`. This is precisely the
  pullback defining `GrpObj.ker`; it specifies N up to its unique kernel isomorphism,
  with its actual inclusion i. No arbitrary subgroup or merely pointwise kernel is used.
- L is the reduction of N: `e : L.X.left ≅ N.X.left.nilradical.subscheme` and
  `r.hom.hom.left = e.hom ≫ N.X.left.nilradical.subschemeι`. The inclusion r
  makes this identification one over N, and hence over k. The group operations
  on L are part of the existential group object and r is a group homomorphism;
  they are not assumed in the hypotheses or chosen from an existence axiom.
- L smooth, closed, normal in H: `Smooth L.X.hom`,
  `IsClosedSubgroupScheme (r ≫ i).hom.hom`, and
  `IsNormalSubgroupScheme (r ≫ i).hom.hom`.
- P smooth, connected, affine and finite type: the five displayed geometric
  predicates on P, with finite type expressed as locally finite type plus QC.
- P is H/L as the specified fppf coset sheafification: `IsFppfGroupQuotient (r ≫ i) a`.
  The existing definition includes fppf local surjectivity, the represented sheaf,
  the coset coequalizer and its sheafification universal property. Its torsor
  isomorphism has projections `(h,l) ↦ h` and `(h,l) ↦ h·i(r(l))`, exactly the
  node's `(h,l) ↦ (h,hl)`, not an unspecified isomorphism.
- a smooth faithfully flat finitely presented: `Smooth`, `Flat`, `Surjective`,
  `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated` on its scheme map.
  The last three together state finite presentation, not just local presentation.
- b a finite faithfully flat radicial homomorphism: `b : P ⟶ J` and
  `IsFinite`, `Flat`, `Surjective`, `UniversallyInjective` on its scheme map.
  Universal injectivity is exactly the dependency node's radicial condition.
- q equals b composed with a: `a ≫ b = q` (Lean's composition is left-to-right).
- ker b = N/L: K with inclusion j is specified by the second kernel `IsPullback`
  square; `IsFppfGroupQuotient r c` makes this same K the quotient N/L;
  `i ≫ a = c ≫ j` retains the canonical induced map. Thus the assertion identifies
  the actual embedded kernel and the actual quotient map, not just abstract groups.
- Conditional A-action: universally quantify A with exactly the same affine,
  smooth, connected, finite-type hypotheses, followed by `ModObj A.X H.X` and
  `ModObj A.X J.X`. These are morphism-valued internal group actions over k,
  not actions solely on k-points. The two multiplicativity hypotheses hold for
  every test scheme T and all its points t,x,y; `IsModHom A.X q.hom.hom` is q's
  equivariance. Group action inverses make every t-action invertible, so
  multiplicativity expresses action by group automorphisms (unit and inverse
  preservation follow for group homomorphisms).
- A preserves L and descends to P: existential `ModObj A.X L.X` and
  `ModObj A.X P.X`, multiplicative on every test scheme. `IsModHom` for the
  closed inclusion `r ≫ i` gives scheme-theoretic preservation, and `IsModHom`
  for a and b gives both required equivariances. The inverse action gives
  equality of the subgroup, rather than just one-sided containment.
- No connectedness hypothesis is imposed on N or L, nor smoothness on N.
  No characteristic restriction or faithfulness of any action is imposed.

All variables and the universe u are explicitly bound; `autoImplicit` is false.
Schemes, coefficients, actions and test schemes use the same u as the existing
quotient presentation. No independent small test universe makes a condition vacuous.
The two existential kernel presentations are ordinary universal-property encodings
of the kernels, equivalent to using the chosen pullbacks, and add no hypothesis.
There are no data definitions using `sorry`, local instances, local notations,
statement lets, or proof-bearing casts.

### Dependency declarations

The full signatures and docstrings of the statement dependencies were read from
the node records and the local Mathlib/upstream sources. The compact-object example
module is now withdrawn (it contains no declarations); the active quotient module
supplies the current module-mode and docstring example.

- `def-weil-field`: Field.
- `def-weil-algebraic-closure`: Mathlib/FieldTheory/IsAlgClosed/AlgebraicClosure.lean — AlgebraicClosure.
- `def-sc-group-scheme`: Mathlib.CategoryTheory.Monoidal.Grp — CategoryTheory.GrpObj.
- `def-sbc-smooth-morphisms`: Mathlib.AlgebraicGeometry.Morphisms.Smooth — AlgebraicGeometry.Smooth.
- `def-weil-connected-scheme`: Mathlib/Topology/Connected/Basic.lean — ConnectedSpace.
- `def-weil-finite-type-morphism`: Mathlib.AlgebraicGeometry.Morphisms.FiniteType — AlgebraicGeometry.LocallyOfFiniteType.
- `def-pc-reduced-scheme`: Mathlib.AlgebraicGeometry.Properties — AlgebraicGeometry.IsReduced.
- `def-sc-group-scheme-subgroup`: WeilConjectures.AlgebraicGeometry.GroupScheme.Defs — AlgebraicGeometry.IsSubgroupScheme.
- `def-weil-pbc-scheme-reduction`: Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme — AlgebraicGeometry.Scheme.IdealSheafData.subscheme.
- `def-sfb-fppf-group-quotient-presentation`: Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry — AlgebraicGeometry.IsFppfGroupQuotient.
- `def-weil-radicial-morphism`: Mathlib/AlgebraicGeometry/Morphisms/UniversallyInjective.lean — AlgebraicGeometry.UniversallyInjective.
- `def-weil-flat-morphism`: Mathlib.AlgebraicGeometry.Morphisms.Flat — AlgebraicGeometry.Flat.
- `def-sbc-locally-finite-presentation`: Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation — AlgebraicGeometry.LocallyOfFinitePresentation.
- `def-pc-fibre-product`: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback — CategoryTheory.Limits.pullback.
- `def-weil-finite-integral-morphism`: Mathlib.AlgebraicGeometry.Morphisms.Finite — AlgebraicGeometry.IsFinite.

The additional action notions are the existing `CategoryTheory.ModObj`,
`CategoryTheory.IsModHom`, and Hom-type `MulAction`, read in
`Mathlib.CategoryTheory.Monoidal.Mod` and `.Cartesian.Mod`; no competing action
notion is defined. All recorded proof dependency modules are imported (including
Mathlib matches). The two proof dependencies
`lem-sfb-faithfully-flat-group-quotient-universal` and
`lem-sfb-nested-homogeneous-quotient-geometry` have no Lean/module record or Mathlib
match on the read base, so there is no module to import yet. They are proof-only
prerequisites, not missing objects for this statement; their names and uses remain
in the ten-step proof docstring and unchanged DAG proof.

### Edge cases and sources

Checked before writing: q an isomorphism gives trivial N and L and a,b
isomorphisms; J the trivial group gives N=L=H, P=1; Frobenius on Ga or Gm in
characteristic p gives nonreduced kernel and trivial reduced kernel, with a an
isomorphism and b Frobenius. The map x ↦ x^(p*n) on Gm with n prime to p gives
disconnected L = mu_n and finite radicial b, so no connectedness of L was inserted.
In characteristic zero reduced kernels give b an isomorphism. Trivial A and
nonfaithful actions are included. Empty groups cannot occur because group objects
have an identity section. Normality is necessary for reducing an arbitrary subgroup,
but here N is a kernel; it is not a hypothesis silently imposed on an arbitrary N.

Read Milne's local PDF: printed pp.18–20 (Proposition 1.38, Corollary 1.39),
pp.23–24 (kernel fibre product and exactness, Proposition 1.62), pp.100–105
(quotient universal property and affine normal quotients), and p.122 (Exercises
5-5 and 5-6). The node already supplies the needed normal-kernel restriction
for Exercise 5-6. No statement correction or dispute is needed.

### Searches and validation

- `msearch.py leanfinder`: "A faithfully flat homomorphism of smooth connected
  affine algebraic groups over an algebraically closed field factors through the
  quotient by its reduced kernel as a smooth torsor followed by a finite radicial map".
  Eight hits concerned smooth algebra descent or general faithful flatness;
  none states this group-scheme factorization.
- `msearch.py loogle`: `"GrpObj", "ker"`. Eight unrelated commutator lemmas;
  no reduced-kernel factorization.
- `msearch.py grep`: `reduced.*[Kk]ernel|[Kk]ernel.*reduced|[Rr]adicial`,
  restricted to `AlgebraicGeometry/Group`: zero hits.
- `msearch.py leansearch`: "The reduced kernel of a smooth affine group
  homomorphism gives a smooth quotient followed by a finite universally injective
  homomorphism". Eight abstract group kernel/quotient or ring quotient hits;
  no scheme-theoretic factorization.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `reduced_normal_kernel`, and `ReducedNormalKernel`: no existing statement.
- Project and Mathlib searches for actions found the existing internal `ModObj`
  and `IsModHom` interfaces. Existing `IsFppfGroupQuotient` was read and reused
  directly, including its canonical torsor coordinates and sheafification clause.
- `dag/lean_names_upstream.json` has no `reduced_normal_kernel_factorization`.
- First `scompile.py` run passed sandbox and library compilation with no unexpected
  warnings (6.4 s and 2.4 s). Final imports are checked again by the dry run.

## Second reading by Q121

A fresh second pass by this dispatcher worker read the node and the complete
module together; no additional agent was started, as the assignment prohibits it.
The maintainer's independent review will read this delivery.

Rechecked all hypotheses and clauses against the list above: the two group
structures and actual q; field and geometric hypotheses; N's identity fibre;
L's nilradical subscheme with its actual inclusion; smooth closed normal L;
the quotient's geometry, coset sheafification, torsor coordinates, smoothness
and full finite presentation; finite faithfully flat universally injective b;
composition equality; the embedded kernel N/L with its canonical map; and the
scheme-valued automorphism actions preserving L and making a,b equivariant.
The statement includes no connectedness or smoothness restriction on N and no
connectedness restriction on L. The two action multiplicativity conditions imply
unit preservation because their values lie in groups, and inversion in A makes
them automorphisms. Existential action instances are scoped to the clauses in
which the compiler uses them. No mismatch was found. During the import pass,
explicit statement dependency imports and recorded Mathlib proof-module imports
were added; the theorem signature did not change.
