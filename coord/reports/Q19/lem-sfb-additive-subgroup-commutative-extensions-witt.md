## Worker report

The module `Sheaf.AlgebraicGeometry.AdditiveSubgroupCommutativeExtensionsWitt`
states `AlgebraicGeometry.StandardGroupSchemes.additive_subgroup_commutative_extensions_witt`.
Its only declaration is this theorem, with `sorry` as the entire proof. It defines
no new objects and changes only the item's `lean` record. The declaration docstring
contains all six accepted proof steps, including the bounded-degree lift for
nonreduced subgroups and the finite Witt-sum correction.

Source read: Milne, Algebraic Groups (2017), Proposition 15.27 and display (113),
printed pp.316–317. It states that every commutative extension of an algebraic
subgroup of the additive group by the additive group is pulled back from W₂.
The node's perfect-field hypothesis is retained exactly. The local compact-object
example has been withdrawn and contains only its withdrawal notice; the module
therefore follows the current module-mode header convention of the recorded Witt
and standard-group-scheme dependencies.

Hypotheses and clauses, individually:

- A field k: `(k : Type u) [Field k]`, using the recorded Mathlib `Field`.
- Positive prime characteristic p: `(p : ℕ) [Fact p.Prime] [CharP k p]`.
  The fact includes p>0 and permits precisely p=2 as well as all other primes.
- Perfectness in the node's stated sense: `hperfect : ∀ x : k, ∃ y : k, y ^ p = x`.
  This states the given p-th-root condition directly, without algebraic closure.
- The k-group schemes Q and E: `Q E : Over (Spec (.of k))`, with `[GrpObj Q]`
  and `[GrpObj E]`. `Over` morphisms are k-morphisms throughout.
- Commutativity: `[IsCommMonObj Q] [IsCommMonObj E]`, using their actual group laws.
- Affineness: `[IsAffine Q.left] [IsAffine E.left]`.
- Finite type: `[LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]` and the same two
  assumptions for E.hom, exactly the recorded finite-type conjunction.
- The specified closed subgroup embedding: `ι : Q ⟶ additive k` with
  `[IsClosedSubgroupScheme ι]`. This is the upstream subgroup class, including
  the homomorphism, injectivity on every algebra-valued point, and closed immersion.
- The arrows of the extension: `i : additive k ⟶ E` and `q : E ⟶ Q`, with
  `[IsMonHom i] [IsMonHom q]`.
- Scheme-theoretic kernel identification: `hkernel : ∃ e : additive k ≅ GrpObj.ker q,
  e.hom ≫ GrpObj.kerι q = i`. This identifies the actual pullback kernel and its
  inclusion, rather than imposing only exactness on rational points. Because i is
  a homomorphism and the kernel inclusion is monic, this identification also
  preserves group operations. It implies that i is the required closed immersion.
- Faithful flatness of q: `[Flat q.left] [Surjective q.left]`.
- Finite presentation of q: `[LocallyOfFinitePresentation q.left]`,
  `[QuasiCompact q.left] [QuasiSeparated q.left]`, the usual global conjunction.
  All are properties of q as a scheme morphism, not just its k-points.
- W₂, τ and j are exactly `LengthTwoWitt.scheme k p`,
  `LengthTwoWitt.truncation k p`, and `LengthTwoWitt.inclusion k p`, supplied by
  `lem-sfb-length-two-witt-extension-verschiebung` with the specified polynomial law.
- Existence of h: `∃ h : Q ⟶ additive k, ... IsMonHom h ...`.
- Existence of the second-projection homomorphism: `a : E ⟶ LengthTwoWitt.scheme k p`
  with `IsMonHom a`.
- The isomorphism: `e : E ≅ pullback h (LengthTwoWitt.truncation k p)` is an
  isomorphism in the category of k-schemes. Its two components are specified by
  `e.hom ≫ pullback.fst ... = q` and `e.hom ≫ pullback.snd ... = a`.
  These equations plus `IsMonHom q` and `IsMonHom a` express exactly preservation
  of the induced pullback group law: compare the unit or multiplication after
  each projection, and use the pullback's uniqueness. Hence e is a group-scheme
  isomorphism, with group-homomorphic inverse, not merely an arbitrary scheme
  isomorphism. This avoids introducing another definition of the pullback group.
- Identity on the quotient Q is the first-projection equality above.
- Identity on the kernel Gₐ is `i ≫ a = LengthTwoWitt.inclusion k p`, together with
  the first-projection equality: the two projections of e∘i are the zero map to Q
  and the specified j, exactly the canonical pullback kernel inclusion. Thus the
  kernel automorphism is the identity, rather than an unspecified scalar.
- The explicitly requested square is `a ≫ LengthTwoWitt.truncation k p = q ≫ h`.
- The zero h is allowed: no nonzero, mono, surjectivity, degree, or nontriviality
  condition occurs on h. No smoothness or connectedness assumption occurs on Q/E.

Statement-dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (Mathlib match, no Lean
  record needed).
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsClosedSubgroupScheme`, in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, including its parent
  `IsSubgroupScheme` and `IsMonHom` fields.
- `def-sc-gm-ga`: `AlgebraicGeometry.StandardGroupSchemes.additive` and its actual
  `additiveGroup`, in `Sheaf.AlgebraicGeometry.StandardGroupSchemes` (publicly
  imported through the recorded Witt module).
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, `IsCommMonObj`, `IsMonHom`,
  `Mathlib.CategoryTheory.Monoidal.Grp` / `.Mon`; actual `GrpObj.ker` and `kerι`
  from `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`, exposed
  through the recorded group-scheme module.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `lem-sfb-length-two-witt-extension-verschiebung`: `LengthTwoWitt.scheme`,
  `group`, `inclusion`, `truncation`, `extension`, in
  `Sheaf.AlgebraicGeometry.LengthTwoWittExtensionVerschiebung`. The signatures
  and docstrings specify the actual two-coordinate group law, kernel, and maps.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
  Its universal property applies in `Over (Spec k)` as in schemes.

The already recorded proof dependencies are imported privately:
`AlgebraicGeometry.Spec` (`Mathlib.AlgebraicGeometry.Scheme`), `MvPolynomial`
(`Mathlib.Algebra.MvPolynomial.Basic`),
`StandardGroupSchemes.exists_additiveSubgroup_polynomial_quotient`
(`Sheaf.AlgebraicGeometry.AdditiveSubgroupPolynomialQuotient`),
`AdjoinRoot.powerBasis'` (`Mathlib.RingTheory.AdjoinRoot`), and
`MvPolynomial.symmetric_polynomial_cocycle_normal_form`
(`Sheaf.RingTheory.SymmetricPolynomialCocycleNormalForm`).
`lem-sfb-additive-affine-torsor-section` has no Lean record or Mathlib match yet;
there is no module to import for this proof-only prerequisite. The exact node
and its role remain in the proof docstring. It is not a prerequisite to typing
this statement and no replacement theorem or assumption is introduced.

Edge cases checked mathematically before drafting:

- Split extension: h=0 gives Q × ker(τ), hence Q × Gₐ with the specified inclusion;
  the formula a(t,x)=j(t) gives all conclusion equations.
- Trivial subgroup Q: the kernel identification identifies E with Gₐ; the same
  h=0 case works and the subgroup need not have positive dimension.
- Q=Gₐ: no properness hypothesis is imposed on ι.
- Infinitesimal Q such as αₚ: no reducedness, smoothness, or rational-point-only
  exactness assumption excludes it; the pullback and kernel are schemes.
- Characteristic two is permitted; no oddness or sign restriction was introduced.
- Arbitrary field universe u: Q/E are schemes in the same geometric universe as
  Spec k and the recorded affine line; no independent smaller test-algebra
  universe can make exactness vacuous. All variables and universes are explicit,
  with `autoImplicit false` in the delivered module.
- The empty scheme cannot be a group object over nonempty Spec k, so no artificial
  nonemptiness assumption is needed.

Searches for an existing statement (2026-10-24; raw wrapper outputs are saved by
msearch in sandbox `searches.jsonl`):

- LeanFinder: “Commutative extensions of closed subgroups of the additive group
  scheme by the additive group are pullbacks of the length two Witt extension
  over a perfect field”. Eight hits, all Witt isocrystals and their structures;
  none states this group-scheme extension classification.
- Loogle: `"WittVector", "pullback"`. Zero hits.
- Mathlib grep via msearch: `Witt.*extension|extension.*Witt|symmetric.*cocycle`.
  Zero hits.
- LeanSearch: “Every commutative extension of a closed subgroup scheme of the
  additive group by the additive group over a perfect field is a pullback of the
  length two Witt vector extension”. Eight hits; `AddGroupExtension`, abstract
  equivalences, Witt rings and isocrystals are not this scheme-theoretic theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` with the above expression, plus
  `commutative.*extensions` and the exact node id: the Witt extension itself and
  the symmetric polynomial normal form exist; the classification theorem does not.
- Exact-id / proposed-name searches of `dag/lean_names_upstream.json`,
  `lean/WeilConjectures` and `lean/Sheaf` returned no declarations with this theorem.

No statement correction, dependency repair, new notion, or disputed statement
was needed.

## Second reading by Q19

Final self-check against the opened node and source: the hypothesis and clause
mapping above was reread after drafting. The isomorphism is explicitly over k;
its two homomorphic components force preservation of the pullback group law.
The kernel equality uses the given i and the fixed j, not an arbitrary
identification; the quotient projection is the given q. Perfectness, finite
presentation, the zero-map case, and nonreduced subgroups are retained. No
mismatch or correction was found. This is a self-check: the dispatcher prohibits
starting another worker, and the maintainer supplies the independent review.
