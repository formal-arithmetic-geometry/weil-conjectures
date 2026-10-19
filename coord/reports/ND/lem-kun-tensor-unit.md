## Worker report

Existing declarations, no new module: `AlgebraicGeometry.Etale.derivedTensorRightUnitor`
and `AlgebraicGeometry.Etale.derivedTensorLeftUnitor` in
`WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`. Read both complete signatures,
docstrings and definitions. They return the canonical monoidal unit isomorphisms (`ρ_ K`
and `λ_ K`), not an unspecified isomorphism. The two declarations jointly say exactly
lem-kun-tensor-unit; recording them avoids duplicating either statement.

Hypotheses and clauses:

- Scheme T: specialize the explicit `X : Scheme.{u}` binder to T.
- Commutative coefficient ring Λ: take `Λ : Type (u + 1)` and `[CommRing Λ]`, and
  specialize the coefficient category A to `ModuleCat.{u + 1} Λ`. All the general
  coefficient-category hypotheses are library instances for this category, so there
  are no additional mathematical assumptions.
- Arbitrary E in D(T_et, Λ): `K : DerivedCategory
  (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`. This is the unbounded category,
  with no restriction on E.
- Right constraint E tensor Λ_T → E is an isomorphism: the `.hom` of
  `derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) T E`. Its source is
  `((derivedTensor A T).obj E).obj (𝟙_ _)`, and its target is E.
- Left constraint Λ_T tensor E → E is an isomorphism: the `.hom` of
  `derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) T E`. Its source is
  `((derivedTensor A T).obj (𝟙_ _)).obj E`, and its target is E.
- The unit `𝟙_ _` is the constant coefficient sheaf in degree zero; the upstream
  `constantComplex` definition in `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`
  is precisely this object. The TensorStructure docstrings explicitly identify it.

Dependencies read and used:

- def-kun-derived-tensor: `AlgebraicGeometry.Etale.derivedTensor` in
  `WeilConjectures.SixFunctors.Etale.Derived.Tensor`; its body is `curriedTensor _`
  on the K-flat-derived monoidal category. The existing constraints use this very functor.
- def-kun-constant-sheaf: `CategoryTheory.Functor.mapHomologicalComplex` in
  `Mathlib.Algebra.Homology.Additive`, specialized to `constantSheaf` as the node's
  record specifies. Read that signature and docstring, and the sheafification definition
  of `CategoryTheory.constantSheaf` in `Mathlib.CategoryTheory.Sites.ConstantSheaf`.
  The constant coefficient complex in degree zero is the tensor unit above.
- def-weil-pbc-etale-sheaves: read the current published source of
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves` using `scompile.py --source`.
  Its recorded declaration `AlgebraicGeometry.Scheme.IsLocallyConstantEtaleSheafOfSets`
  concerns a different clause of this mixed dependency. Its record explicitly permits
  the `Sheaf T.smallEtaleTopology (ModuleCat Λ)` encoding used here; no new predicate
  or sheaf category is introduced.

Edge cases: empty T, zero ring Λ, E = 0, and unbounded E are all allowed by these
signatures. No reducedness, connectedness, flatness of E, boundedness, or invertibility
of integers is required. Universe u is arbitrary, with coefficient and section values
in u+1, following the existing small-etale-site convention.

Searches (2026-10-15):

- msearch LeanSearch: "The derived tensor product of sheaves with the coefficient ring
  has left and right unit isomorphisms". Service unavailable: Internal Server Error.
- msearch LeanFinder: "The derived tensor product of etale sheaves with the constant
  coefficient ring has canonical left and right unit isomorphisms". Eight hits on
  formally etale algebras and Kahler differentials, no relevant match.
- msearch Loogle: `MonoidalCategory.leftUnitor, MonoidalCategory.rightUnitor`.
  Unknown identifier `MonoidalCategory.leftUnitor`; no hits.
- msearch grep `leftUnitor|rightUnitor` under Mathlib CategoryTheory/Monoidal:
  25 displayed hits, generic coherence and subcategory infrastructure.
- rg `lem-kun-tensor-unit|derivedTensor.*[Uu]nit|[Uu]nit.*derivedTensor` over upstream
  WeilConjectures and project lean/Sheaf found the exact two upstream declarations
  in TensorStructure, together with their uses in purity and duality. No duplicate
  project declaration was found. Read the complete TensorStructure module.

Validation: scratch/Check.lean specializes both existing declarations and checks
`IsIso` for their canonical forward maps, using only inferred instances. It is a
compilation probe, not a delivered module. The delivery dry run also checks both
recorded existing declarations. No statement correction or disputed clause.

## Second reading by ND

Read the item JSON, all three statement-dependency JSON records, the blueprint
item and derived-tensor definition, Stacks sites-modules.tex section
`section-tensor-product` (03EK), and both complete upstream unitor definitions
with their enclosing variables. The source assumes a site and a sheaf of rings;
it adds no finiteness, characteristic, or geometric restriction here.

Object/hypothesis/conclusion checklist, in the order of the node:

- Scheme T: upstream `(X : Scheme.{u})`, specialized to T. Pass: arbitrary scheme.
- Commutative ring Λ: specialize A to `ModuleCat.{u + 1} Λ`, with
  `Λ : Type (u + 1)` and `[CommRing Λ]`. Pass: the enclosing Abelian,
  Grothendieck, symmetric monoidal closed, monoidal preadditive and functorial
  flat-resolution hypotheses are inferred library instances, not assumptions on
  Λ. The scratch specialization compiled without additional hypotheses.
- E in the unbounded D(T_et,Λ): the explicit `K : DerivedCategory
  (Sheaf X.smallEtaleTopology A)` binder. Pass: no boundedness or flatness of E.
  The mixed def-weil-pbc-etale-sheaves record explicitly authorizes this
  ModuleCat-valued encoding; its primary locally-constant predicate is not
  being mistaken for the category. Read its published module using
  `scompile.py --source WeilConjectures.AlgebraicGeometry.EtaleSheaves`.
- Constant coefficient sheaf in degree zero: `𝟙_ _` in both sources. Pass:
  Coefficients.constantComplex is this unit. Independently checked the
  construction: Mathlib Sites.Monoidal's Sheaf.monoidalCategory localizes the
  presheaf monoidal category through presheafToSheaf, and constantSheaf is
  Functor.const followed by presheafToSheaf. Its unit is therefore the constant
  Λ-module sheaf. Mathlib Homology.Monoidal.tensorUnit is `(single C c 0).obj
  (𝟙_ C)`; the upstream derived monoidal construction localizes the homotopy
  category and its unit comparison is invertible (DerivedCategory.isIso_ε_Qh).
  This is precisely that sheaf placed in degree zero up to canonical comparison.
  Read mapHomologicalComplex: it maps terms and differentials termwise, as the
  def-kun-constant-sheaf dependency prescribes.
- Right canonical map E tensor Λ_T → E is invertible:
  `derivedTensorRightUnitor A T E : ((derivedTensor A T).obj E).obj (𝟙_ _) ≅ E`.
  Pass: its body is `ρ_ E`; its forward map is the canonical constraint.
- Left canonical map Λ_T tensor E → E is invertible:
  `derivedTensorLeftUnitor A T E : ((derivedTensor A T).obj (𝟙_ _)).obj E ≅ E`.
  Pass: its body is `λ_ E`, not a choice of an unspecified isomorphism.
  Both declarations together supply exactly the two clauses. Returning Iso
  supplies the inverse of these specified canonical maps and imposes no
  stronger mathematical conclusion. Quantifier order is T, Λ, then arbitrary E
  after the indicated specialization.
- Tensor in both clauses: exactly the recorded def-kun-derived-tensor
  `Etale.derivedTensor`, whose implementation is the K-flat-derived curried
  monoidal tensor. Read its complete signature and construction documentation.
  Pass: neither the underived tensor nor a private copy is substituted.

Edge cases: T empty, Λ the zero ring, E zero, and arbitrary unbounded E are
included. There is no index set or n parameter to restrict; the unit sits at
n = 0 with arbitrary other degrees in E. All characteristics are admitted.
The universe u is arbitrary; Λ and section values use the dependency's u+1
size convention. Small rings may be lifted to this universe; no algebraic
restriction or equality of independent site universes is added.

Independent searches: msearch Loogle `CategoryTheory.MonoidalCategory, _ ≅ _`
returned the generic leftUnitorNatIso/rightUnitorNatIso and coherence maps;
msearch LeanFinder "Tensoring an unbounded complex of etale module sheaves
with the constant coefficient sheaf in degree zero is canonically the original
complex" returned HomologicalComplex.leftUnitor' and ordinary tensor-unit
infrastructure, plus irrelevant differential/condensed hits. The worker's
LeanSearch attempt is recorded above as unavailable. Independently rg-searched
`derivedTensorLeftUnitor|derivedTensorRightUnitor|constantSheaf.*[Uu]nit|tensorUnit.*constant`
in upstream WeilConjectures, project lean/Sheaf and Mathlib Sites: the two exact
upstream declarations and their applications are present; no new module is
needed. Read the full TensorStructure module rather than relying on names.

No mismatch found; no Lean or node changes. The recorded primary signature is
verbatim, including its explicit K binder, and declarations lists both clauses.
There are no new nodes, dependency modules, hollow definitions or new proofs.
H8/H9 obligations for newly written declarations do not apply to this existing
record; the node retains the complete three-step ordinary-unit/K-flat proof.
The upstream definitions are concrete canonical unitors. All explicit variables
and universes in their signatures are bound by the enclosing declarations.

Validation: reran the existing scratch/Check.lean via scompile.py with its
absolute path. Sandbox and library checks both passed cleanly (2.1 s each),
confirming both specialized canonical forward maps have IsIso with inferred
instances. No delivered Lean files require compilation.
