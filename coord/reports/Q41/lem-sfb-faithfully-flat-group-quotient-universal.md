## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.FaithfullyFlatQuotientUniversal`
states `AlgebraicGeometry.existsUnique_hom_of_faithfullyFlat_of_trivial_on_kernel`.
Its only theorem has proof `sorry`. No definitions or helper nodes are needed.
The original node is unchanged except for `lean`.

Source read: Milne, Algebraic Groups (2017), Theorem 5.13 (printed p.101),
Definition 5.5 (printed p.99), and Proposition 5.43 (printed p.109) in the local PDF.
Theorem 5.13 says exactly that a homomorphism whose kernel contains the kernel
of a quotient map factors uniquely through that quotient; Definition 5.5 says
quotient maps are faithfully flat. The DAG spells out an fpqc descent proof;
the declaration docstring includes all five steps and their cited nodes.

Hypothesis and clause correspondence:

- A field F: `{F : Type u} [Field F]`, using def-weil-field's Mathlib match `Field`.
- G, Q, H are F-schemes: `G Q H : Over (Spec (.of F))`. All morphisms between
  them are over Spec F, so F-linearity is built into their types.
- Group-scheme structures: `[GrpObj G] [GrpObj Q] [GrpObj H]`.
- Affineness: `[IsAffine G.left] [IsAffine Q.left] [IsAffine H.left]`.
- Each group has finite type over F: for each of G, Q, H, the two binders
  `[LocallyOfFiniteType _.hom] [QuasiCompact _.hom]` are precisely the dependency
  node's finite-type conjunction, on the structure morphism.
- q is a group-scheme homomorphism: `(q : G ⟶ Q) [IsMonHom q]`.
- Its coordinate map is faithfully flat: `(hq : q.left.appTop.hom.FaithfullyFlat)`.
  `q.left` is the actual scheme map; `appTop` pulls back global functions from
  Q to G. Mathlib's `RingHom.FaithfullyFlat` installs this very ring map as
  the algebra structure and requires `Module.FaithfullyFlat`. Flatness gives
  exact extension of scalars and faithful flatness detects zero modules
  (`Module.FaithfullyFlat.lTensor_reflects_triviality`). No unrelated algebra
  structure or arbitrary replacement map is quantified over. This follows the
  same canonical-coordinate-map encoding as the landed consumer
  `commutative_multiplicativeType_extension`.
- N and i: `GrpObj.ker q` and `GrpObj.kerι q`, the recorded fibre-product kernel
  and its first projection. These are not independently supplied objects/maps.
- Every homomorphism u: `(u : G ⟶ H) [IsMonHom u]`.
- Triviality on the kernel: `hu : GrpObj.kerι q ≫ u =
  toUnit (GrpObj.ker q) ≫ η[H]`. `toUnit` is the unique map to the terminal
  object of the over-category, namely Spec F, and `η[H]` is H's identity section.
  This is equality of morphisms in Over (Spec F), not equality of rational points.
  By affine Yoneda it is equivalently equality on every commutative F-algebra,
  including nonreduced algebras. The node's explanatory equivalence is implemented
  by choosing the actual morphism equality as the hypothesis.
- Existence of a homomorphism v: `∃! v : Q ⟶ H, IsMonHom v ∧ ...`.
- Its factorization equation: `q ≫ v = u`, i.e. u = v ∘ q with Lean's composition
  convention. Uniqueness quantifies over the predicate containing both
  homomorphism preservation and this equation, so it is uniqueness among group
  homomorphisms, exactly as requested, not uniqueness among arbitrary scheme maps.
- No smoothness, connectedness, commutativity, reducedness, perfectness, or
  restriction on the characteristic appears. No extra conclusion is asserted.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and `Grp`;
  `Mathlib.CategoryTheory.Monoidal.Mon`: `CategoryTheory.IsMonHom`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: documented specialization
  of those declarations to Over (Spec F), exactly as def-sc-group-scheme records.
  Its public import
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp` supplies
  `CategoryTheory.GrpObj.ker`, `kerι`, and their pullback interfaces. The full
  definitions/docstrings were read: `ker f = pullback f η[H]`, with `kerι` its fst.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, with `QuasiCompact` from its imports,
  as def-weil-finite-type-morphism records. Both class signatures/docstrings read.
- `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`, and
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`.

Plain imports retain every recorded proof dependency's defining module:
`Mathlib.AlgebraicGeometry.Morphisms.Flat` (affine flatness),
`Mathlib.AlgebraicGeometry.Sites.Fpqc` (fpqc covers, axioms, representable descent),
`Mathlib.AlgebraicGeometry.AffineScheme` (affine basic opens),
`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` (the recorded affine-ideal lemma),
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra` (surjective spectrum),
`Mathlib.RingTheory.Spectrum.Prime.Topology` (principal-open basis/compactness), and
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (fibre products).
The scheme definitions and basic-open pullback declarations are already publicly
imported through the group-scheme dependency, which is also a proof dependency.

Edge cases checked mathematically before writing: q = identity gives v = u;
Q trivial makes its kernel all of G, forcing u trivial; trivial H gives the unique
trivial homomorphism. In characteristic p the Frobenius G_a → G_a has infinitesimal
kernel alpha_p: its inclusion is the actual fibre-product inclusion, so hu does not
collapse to the vacuous condition on alpha_p(F). Power maps on G_m allow nontrivial
finite kernels, including nonreduced mu_p. Disconnected affine finite-type groups
are permitted. Empty group schemes cannot carry an identity section over a field;
this is intrinsic to GrpObj, not an added nonemptiness assumption. The universe u
is explicitly bound, and there is no test-algebra universe whose size could make
a hypothesis vacuous.

Searches actually run for this assignment:

- msearch.py, leanfinder: "A homomorphism of affine group schemes killing the
  kernel of a faithfully flat quotient factors uniquely through the quotient".
  Eight hits, including Scheme.Hom.liftQuotient, its two composition lemmas,
  faithfully-flat ring descent lemmas, Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine,
  formally-unramified lift uniqueness and AlgHom.liftOfSurjective_comp. None states
  the group-scheme quotient universal property. liftQuotient factors a map INTO
  a closed subscheme rather than THROUGH a faithfully flat quotient.
- msearch.py, loogle: "GrpObj.ker, IsMonHom, FaithfullyFlat": unknown identifier
  GrpObj.ker, zero hits; this upstream kernel is not indexed by public Loogle.
  Follow-up loogle query `"FaithfullyFlat"` returned twelve Module.FaithfullyFlat
  declarations, including toFlat and tensor detection of triviality, no match.
- msearch.py, grep: `quotient|factor|FaithfullyFlat` in AlgebraicGeometry/Group:
  three hits in Abelian.lean and Affine.lean, none the target statement.
- rg in both lean/WeilConjectures and lean/Sheaf for faithfully-flat group
  quotient/factorization names and `existsUnique.*ker`: no existing statement.
  The landed CommutativeMultiplicativeTypeExtension, ConnectedExtension and
  AffineCommutativeExtensionPushout modules mention this DAG node in proof plans
  and need it; they do not state it. The upstream ring quotient helpers concern
  ideals, not affine group quotients.
- grep -rn of the item id in lean/WeilConjectures: no matches.
- Exact proposed full declaration name searched in Mathlib, WeilConjectures,
  Sheaf and dag/lean_names_upstream.json: no match.

No statement dispute or statement correction. The source.place field retains the
base node's reference to printed p.107 for Proposition 5.43; the actual PDF puts
that proposition on p.109, already noted in the node's reviewed record. The
mathematical statement depends directly on 5.13 and 5.5, not that page number.

Validation: the prescribed scompile.py compiled the file in both sandbox and
library module names cleanly (1.7 seconds each). Every theorem proof is `sorry`;
no proofs or definition data were supplied in this stage-2 delivery.

## Second reading by Q41

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
