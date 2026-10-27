## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTorsionHomParameter` states
`AlgebraicGeometry.finite_torsion_hom_parameter`, with its proof exactly `sorry`.
Three explicit helpers define the node's constant parameter scheme, evaluation of
its family on algebra-valued points, and its homomorphism condition. They belong
to the owning notion and are recorded in `lean.declarations`; none contains a sorry
or chooses unspecified data. No statement correction or dependency repair is needed.
The only change to the existing JSON node is its `lean` field.

Clause-by-clause correspondence:

- The field is `(k : Type u) [Field k]`; `n >= 1` is `(n : ℕ) [NeZero n]`.
  The nonnegative integers `r,s` are natural-number binders, with no positivity
  assumptions. All universes and variables are bound explicitly; autoImplicit is false.
- `H = (μ_n)^r` is `∏ᶜ fun _ : Fin r ↦ StandardGroupSchemes.roots k n`.
  `T = G_m^s` is `∏ᶜ fun _ : Fin s ↦ StandardGroupSchemes.multiplicative k`.
  These are categorical products in `Over (Spec (.of k))`, hence fibre products
  over k. Their points are tuples, with the pointwise product of the recorded
  group structures. Empty products are terminal objects, hence the trivial group.
- The label set `M` is `Fin s → Fin r → ZMod n`, canonically the stated matrices
  (curried functions on the product of index sets). It is finite because n is
  nonzero. `finiteTorsionParameterScheme` is the coproduct, indexed by M, of
  `Over.mk (𝟙 (Spec (.of k)))`. Colimits in this over category have the underlying
  scheme coproduct and its canonical structure morphism, so this is exactly C.
- An arbitrary k-scheme is `X : Over (Spec (.of k))`. The left side of the
  equivalence is its k-morphisms to C. The right side is the subtype of actual
  k-morphisms `φ : X ⨯ H ⟶ T` satisfying `IsFiniteTorsionFamily φ`.
- The predicate quantifies over every `A : Type u` with `[CommRing A] [Algebra k A]`
  and every `x : StandardGroupSchemes.affine k A ⟶ X`. This is exactly
  `x ∈ Hom_k(Spec A,X)`; no field, domain, reducedness or finite-type condition
  is put on A or X. A tuple h consists of maps `Spec A ⟶ μ_n`.
  `finiteTorsionFamilyValue` pairs x with `Pi.lift h`, composes with φ, and takes
  the j-th target projection. The predicate says this sends the identity tuple
  to the identity and sends every product h*h' to the product of the values,
  coordinate by coordinate. This is precisely a group homomorphism H(A) → T(A).
  Inverses follow from identity and multiplication. Naturality in A is intrinsic:
  precomposition with the Spec morphism of an algebra homomorphism commutes with
  product pairing, coordinate projection and φ. No independently chosen point map
  or naturality assumption is substituted for a scheme morphism.
- The existential `e : ∀ X, ... ≃ ...` states bijectivity simultaneously for every X.
  Its first conjunct is naturality for every `g : X' ⟶ X` and every `f : X ⟶ C`:
  `(e X' (g ≫ f)).val = prod.map g (𝟙 _) ≫ (e X f).val`.
  This equality of actual family morphisms gives both directions of naturality
  because each e X is an equivalence; no affine restriction is imposed on g.
- The second conjunct identifies the component label by the exact equation
  `x ≫ f = Over.homMk (affine k A).hom ≫ Sigma.ι ... m`.
  On that component it quantifies over EVERY integer matrix a with
  `∀ j i, (a j i : ZMod n) = m j i`. The j-th family value equals the product
  `List.ofFn (fun i ↦ (h i ≫ rootsInclusion k n) ^ (a j i)) |>.prod`.
  Thus h is viewed in G_m through the recorded roots inclusion, negative powers
  use its genuine group structure, and every lift gives the same value.
  The finite list order is the order of `Fin r`; in this commutative group this
  is the stated product. Quantifying over all affine-algebra-valued points also
  identifies the morphism on each component, not just its geometric points.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-sc-gm-ga`: `Sheaf.AlgebraicGeometry.StandardGroupSchemes`, declarations
  `affine`, `rootsIdeal`, `rootsAlgebra`, `rootsCoordinate`, `roots`, `rootsGroup`,
  `multiplicative`, `multiplicativeGroup`, `rootsCoordinateUnit`, `rootsQuotient`,
  and `rootsInclusion`. The quotient is k[t]/(t^n-1); the inclusion is Spec of
  its Laurent coordinate substitution. Its group laws are the declared Hopf laws.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, `IsMonHom`, and `Hom.group`;
  modules `Mathlib.CategoryTheory.Monoidal.Grp` and
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp` (the latter supplies the scoped
  group on point sets). No alternate group-scheme definition is introduced.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and its projections,
  in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`. The product
  construction in the category over Spec k gives these fibre products; `prod.lift`
  and `Pi.lift` express their universal maps.
- `def-weil-scheme-over-base`: `Scheme.Over` / `Scheme.Hom.IsOver`, read in
  `Mathlib.AlgebraicGeometry.Over`, and the equivalent bundled `CategoryTheory.Over`,
  `Over.Hom`, `Over.mk`, `Over.homMk`, read in the Mathlib Over sources.
- `def-weil-pbc-algebra-hom-quotient`: Mathlib `Algebra`, `AlgHom` and
  `Ideal.Quotient` (the existing roots construction uses its quotient algebra).

The plain proof imports retain the recorded proof plan: affine spectra/pullbacks,
commutative tensor-product maps, open base change, prime-spectrum idempotents,
`Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen`,
`WeilConjectures.AlgebraicGeometry.SchemeClopenIdempotent`, and the affine-target
adjunction. The theorem docstring explains all eight DAG proof steps, including
universal algebra-valued points, orthogonal coefficient idempotents, gluing on
possibly nonaffine overlaps, inverse construction and arbitrary-base naturality.

Edge cases checked before writing:

- `s = 0`: M is a singleton, T terminal, the hom predicate and coordinate formula
  have no j, and both represented sets are singleton sets.
- `r = 0`: H terminal and M singleton; identity preservation forces the family's
  coordinates to be 1, exactly the empty list product in the formula.
- `n = 1`: ZMod 1 has one element and μ_1 is the trivial group. All integer lifts
  are allowed; each roots-valued point becomes the identity in G_m.
- Empty X: the two morphism sets are singletons and the formula has no nonempty
  affine test points; the zero algebra is included and has its unique point.
- Characteristic p dividing n: there is no invertibility or reducedness assumption.
  Testing on all commutative algebras includes infinitesimal roots; the coefficient
  proof uses idempotents over arbitrary rings, never the domain-only group-like theorem.
- Disconnected and nonreduced parameter rings, such as k×k and k[ε]/ε², are allowed.
- Schemes and test algebras are in the same universe u as k. There is no independent
  smaller test universe and no object/morphism-universe equality imposed on a site.

Searches made (2026-10-24):

- `msearch.py ... leanfinder`: “Families of homomorphisms from powers of roots of
  unity group schemes to split tori are represented by a finite constant scheme”.
  Eight hits, on cyclotomic characters and abstract finite-abelian duality; none
  represents the stated scheme families over arbitrary parameter rings.
- `msearch.py ... leansearch`: “finite constant scheme representing homomorphisms
  from roots of unity to a torus”. Eight hits on cyclotomic characters, abstract
  roots-of-unity duality, IsFinite and MulChar.finite; no exact statement.
- `msearch.py ... loogle '"GrpObj", "Pi"'`: zero hits.
- `msearch.py ... grep 'torsionHom|homParameter|CartierDual|characterScheme'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `torsionHom|homParameter|CartierDual|finite.torsion.hom|characterScheme`:
  only unrelated derived torsion-homology, high-genus Hom and Kummer normalization
  modules; no exact statement. The required grep of the item id in
  `lean/WeilConjectures` found no declaration.
- Further name/concept search found existing `MultiplicativeType.splitTorus` and
  `RingGroupSchemes.splitTorus`. These are recursive bundled split-torus objects,
  not this parameter construction. This module defines no competing split torus:
  it uses Mathlib products directly, with the StandardGroupSchemes factors.
  Searches for all four new full declaration names in the two project roots found
  no collision. All three non-theorem helpers concern this very node's notion.

Source checked: the local Milne PDF, Lemma 12.35 and Theorem 12.36 at printed p.243,
with the node's explicit finite split character-label proof from Lemma 12.4.
No STATEMENT-DISPUTED flag and no node fault.

Validation: `scompile.py Q77 lem-sfb-finite-torsion-hom-parameter <module>`
succeeded for sandbox and library module names (13.9 s and 16.9 s respectively),
with no error or non-sorry warning. The sole postponed theorem is
`AlgebraicGeometry.finite_torsion_hom_parameter`.

## Second reading by Q77

I reread the node, the complete module and its elaborated successful compile as a
separate checking pass. The dispatcher explicitly forbids starting another agent;
this section records a self-check and does not claim an independent worker reading.
The maintainer's independent delivery review remains to be performed.

The field, positive n, zero-allowed ranks, exact roots and multiplicative schemes,
finite matrix-indexed coproduct, all k-schemes, all algebra-valued points, identity
and multiplication equations, naturality under every k-morphism and monomial formula
for every integer lift are all present as mapped above. In particular, no
prime-to-characteristic condition or connectedness condition slipped into the statement.
The formula uses the genuine recorded roots inclusion and genuine point group law.
The zero-rank and empty-scheme cases survive the binders. No mismatch was found and
no source statement, dependency statement or proof plan was changed.
