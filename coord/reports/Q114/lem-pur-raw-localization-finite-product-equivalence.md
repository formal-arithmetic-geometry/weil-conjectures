## Worker report

The module `Sheaf.CategoryTheory.RawLocalizationFiniteProductEquivalence` states
`CategoryTheory.rawLocalization_finiteProduct_equivalence`, with one `sorry` and no
new definitions. The node is unchanged except for `lean`.

Source read: main-20261015 blueprint, sec-six-functors-basics/sk-def-purity-conv/
def-pur-section-invariant.md, final assertion that the section invariant is invertible.
As the accepted node and its proof_origin specify, the finite-clopen scalar comparison
is an agent subargument, rather than a theorem asserted verbatim in that blueprint.
The theorem docstring follows all six accepted proof steps and their dependencies.

Hypotheses, matched with the node:

- Commutative ring and its element: `(R : Type r) [CommRing R] (t : R)`;
  the coefficient ring S is exactly `Localization.Away t` throughout.
- A and all B_i are R-linear categories, without additivity of objects assumed:
  `Category.{v}`, `Preadditive`, and `Linear R` instances for A and each B_i.
  All object types use the common universe u; all component morphisms use v;
  r and the index universe w are independent and explicit. These fit in a common
  larger universe as in the node; no equality of coefficient and Hom universes is imposed.
- Finite, possibly empty I: `(I : Type w) [Fintype I]`. There is no Nonempty binder.
  The decidable equality used by the finite tensor isomorphism is classical, scoped
  to this declaration with `open Classical in`, rather than an added hypothesis.
- The functors r_i: `(F : ∀ i : I, A ⥤ B i)` with component `Additive` and
  `Functor.Linear R` instances. Their assembled functor is exactly `Functor.pi' F`,
  and `[(Functor.pi' F).IsEquivalence]` is the given integral equivalence.

Conclusions, in the order of the Lean conjunction:

- `∃ E : ScalarLocalization R A t ≌ (∀ i, ScalarLocalization R (B i) t)`
  gives the equivalence of precisely the recorded raw localizations. Objects are
  the existing single-field wrappers for original objects. No completion appears.
- Forward S-linearity is `Additive ∧ Linear (Localization.Away t)` for every
  `E.functor ⋙ Pi.eval ... i`. Product Hom modules are componentwise, so this is
  exactly S-linearity into the product. Mathlib does not supply a pointwise
  Preadditive/Linear category instance for this Pi category; no arbitrary structure
  is supplied as a hypothesis or chosen as data.
- Inverse S-linearity is stated explicitly by the addition and scalar equations
  for `E.inverse.map`, where the inputs `f g : ∀ i, L i ⟶ M i` carry precisely
  their ordinary pointwise module structures. Thus the inverse is linear as well.
- The object formula is `E.functor.obj ⟨K⟩ i = ScalarLocalization.mk ((F i).obj K)`.
- The pure-tensor arrow formula is the HEq between `E.functor.map (a ⊗ₜ f)`
  and `fun i ↦ a ⊗ₜ (F i).map f`. HEq accounts only for object types identified
  by the preceding object equality; it does not remove the formula. Component
  additivity/linearity supplies the additive extension to all tensors.
- The Hom clause supplies an integral linear isomorphism h with
  `h f = fun i ↦ (F i).map f`. For every tensor z the localized Hom map is
  `TensorProduct.piRight ... (h.toLinearMap.baseChange (Localization.Away t) z)`.
  `piRight` is an S-linear equivalence with pure tensor formula
  `a ⊗ (h_i) ↦ (a ⊗ h_i)_i`. The recorded scalar localization and baseChange use
  scalar-first tensors; applying TensorProduct.comm converts this clause exactly
  to the node's Hom-first formula and `TensorProduct.piLeft`. Both factors are
  isomorphisms: h is a LinearEquiv and scalar extension preserves its inverse.
- For every localized tuple L, the next clause gives an integral K, integral
  `α i : (F i).obj K ≅ (L i).obj`, and localized
  `β i : E.functor.obj ⟨K⟩ i ≅ L i`. Both β.hom and β.inv are specified to be
  one tensored with the corresponding integral arrow, using HEq for the same
  object-identification reason. This is the requested integral representative
  and the requested choice of localized component isomorphisms.
- `IsEmpty I → Nonempty A ∧ ...` asserts existence of an integral object,
  `Subsingleton (K ⟶ M)` for every integral Hom module, and `Subsingleton`
  for every localized Hom set. For a module, subsingleton means the zero module;
  the zero morphism ensures these Hom sets are nonempty and hence singletons.

Dependency declarations read and used:

- def-weil-linear-category: `CategoryTheory.Linear`, Mathlib.CategoryTheory.Linear.Basic,
  lines 46-62; with Category and Preadditive as its record specifies.
- def-weil-linear-functor: `CategoryTheory.Functor.Linear` and `mapLinearMap`,
  Mathlib.CategoryTheory.Linear.LinearFunctor, lines 35-38 and 100-107;
  `Functor.Additive` supplies preservation of addition.
- def-weil-linear-scalar-localization: `CategoryTheory.ScalarLocalization`,
  `ScalarLocalization.mk`, `category`, `preadditive`, and `linear`, from
  Sheaf.CategoryTheory.ScalarLocalization. Read the entire module, including
  composition_tmul and localization. Its Hom is S tensor Hom, its identity is
  one tensor identity, and its objects wrap exactly the original objects.
- Proof dependencies are already covered by these imports and Mathlib imports:
  `Equivalence.fullyFaithfulFunctor`, `Equivalence.mk`, and `Functor.asEquivalence`
  (Mathlib.CategoryTheory.Equivalence); `LinearMap.baseChange`
  (Mathlib.LinearAlgebra.TensorProduct.Tower, lines 657-694); and
  `TensorProduct.piLeft`/`piRight` (Mathlib.LinearAlgebra.TensorProduct.Pi,
  lines 54-118). The finite tensor comparison uses piRight because of the
  dependency's scalar-first convention. No dependency interface is replaced.

Edge cases checked before writing: I empty, I a singleton, t a unit, t zero,
and the zero ring. The empty case does not assume an object of A in advance:
it derives one from the integral equivalence. For t zero or the zero ring,
S is zero, so every localized Hom is a singleton; the product and the same
integral object representatives still give the claimed equivalence. For a unit,
tensoring preserves the integral comparison. No field, nonzero-ring,
idempotent-completeness or additive-category assumptions occur.

Searches actually run:

- msearch leanfinder: "Raw scalar localization of a linear category preserves finite
  product equivalences with tensor Hom comparison": eight hits about localization
  at morphism classes and shift linearity; none states the raw tensor-Hom comparison.
- msearch loogle: "TensorProduct.piLeft, CategoryTheory.Equivalence": zero hits.
- msearch grep: "ScalarLocalization|scalarLocalization", CategoryTheory: zero hits.
- msearch leansearch: "Scalar extension tensor morphisms of linear categories
  preserves finite product equivalences": eight hits about module-category scalar
  extension and finite presentation, including ModuleCat.extendScalars;
  none states this result for arbitrary linear categories.
- rg in lean/WeilConjectures and lean/Sheaf for ScalarLocalization,
  scalarLocalization, raw product, finite product/product equivalence and piRight:
  the existing raw construction and semilinear extension interfaces occur, but
  no finite product equivalence statement. In particular SemilinearScalarLocalization
  treats individual semilinear functors, not this tensor/product Hom isomorphism.
- grep for this exact node id in lean/WeilConjectures: no matches.
- rg of Mathlib Linear/Preadditive and project modules for Pi-category linear
  instances: no suitable pointwise instance. Read Mathlib.CategoryTheory.Pi.Basic
  for the canonical category, projections, and Functor.pi' rather than copying them.

Validation: scompile.py compiled the initial statement in sandbox and library modes;
it reported only a style warning for `open scoped Classical`. This was repaired
by declaration-scoped `open Classical in`; the final compile and delivery dry run
are recorded below. All variables and universes are explicit. No statement fault,
statement correction, new node or dependency module was needed.

## Second reading by Q114

This is a second pass by the assigned worker, not a claim of a separate agent's
review; the dispatcher forbids starting other agents and the maintainer supplies
independent review. I reopened the accepted JSON statement and the final Lean
module and matched each of its hypotheses and clauses above. In particular I
checked that E has the raw product codomain, not the localization of the product;
that both forward and inverse linearity are asserted; that the Hom isomorphism
is tied to the actual F.map, rather than an unspecified isomorphism; that both
arrows of each integral component isomorphism are tensored with one; and that
the empty case asserts Nonempty A as well as both Hom vanishing statements.
The scalar-first tensor convention is exactly that of the recorded dependency,
so it requires no correction. The second pass found no mathematical mismatch.
The only change following compilation was scoping Classical to the theorem,
which removes the warning without adding decidability assumptions.

Final explicit scompile.py validation: sandbox mode passed in 13.0 s and the
library module passed in 6.4 s, both with no diagnostics. A local read-only check
of the delivery found no Lean lines over 100 characters and confirmed that the
only changed field of the existing node is `lean`.
