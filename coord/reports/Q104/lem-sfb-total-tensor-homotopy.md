## Worker report

Recorded existing declarations, without a new Lean module. The previous partial `lean`
record already named the two upstream homotopy instances but lacked its module,
primary declaration, statement, date, author and `existing` fields. This delivery
completes that record and also lists the complex-category instance. No mathematical
statement, dependency list, proof or other node field is changed. No repair note for
this item is present.

Source read: current blueprint main-20261015,
`sec-proetale-coefficients/sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`,
including its references to the tensor product on K(C) and its constraints. Read the
entire upstream module
`WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal`, including all
its ambient variables and its bifunctor, associator, unitor and coherence constructions.
The source printed by `scompile.py --source` agrees with the local source. Read the
Mathlib total tensor and signs and the upstream bifunctor-homotopy construction too.

Hypotheses and clauses, individually:

- An arbitrary abelian C: `C : Type u`, `[Category.{v} C]`, `[Abelian C]`. Object and
  morphism universes remain independent. `Abelian` supplies the preadditivity and
  zero object required by the existing instances.
- The specified monoidal structure: `[MonoidalCategory C]`; additivity in both
  variables: `[MonoidalPreadditive C]`. Its instances give `(curriedTensor C).Additive`
  and `((curriedTensor C).obj X).Additive` for every X. No symmetry or closedness is used.
- All small colimits and preservation by tensoring on either side give, in particular,
  `[HasColimitsOfSize.{0,0} C]` and
  `[∀ X, PreservesColimitsOfSize.{0,0} ((curriedTensor C).obj X)]` and the analogous
  assumption on `(curriedTensor C).flip.obj X`. These are exactly the hypotheses used
  in the successful specialization check. They infer the binary graded coproducts,
  triple preservation, quadruple extensionality and empty-colimit preservation
  required by the upstream instance, as well as the `HasMapBifunctor` family.
  Thus no additional tensor hypotheses have been inserted. The general upstream
  result asks only for the particular colimits needed here; its specialization
  under the node's all-small-colimits hypotheses is immediate by instance inference.
- Unbounded cochain complexes: specialize `c` to `ComplexShape.up ℤ`, obtaining
  `CochainComplex C ℤ`. There is no boundedness or nonnegative-index assumption.
- The specified direct-sum tensor: `HomologicalComplex.tensorObj` is the total
  complex `mapBifunctor` for `curriedTensor C`. Its summands are indexed by p+q=n;
  `ιTensorObj` is the inclusion of `X.X p ⊗ Y.X q`. This is precisely the binary
  tensor used by the recorded `PreservesTotalTensorKFlatQuasiIso` dependency module,
  rather than another K-flat or derived tensor construction.
- The differential is `mapBifunctor.d_eq`, the sum of `D₁` and `D₂`.
  `d₁_eq'` and `d₂_eq'` give the two summand formulas. In
  `ComplexShapeSigns.lean:155–190`, the cochain sign instance has `π(p,q)=p+q`,
  `ε₁=1` and `ε₂=Int.negOnePow p`. This is d(x) tensor y plus
  (-1)^p x tensor d(y), including negative p.
- The complex monoidal structure is `HomologicalComplex.monoidalCategory` in
  `Mathlib.Algebra.Homology.Monoidal:340`. Its `monoidalCategoryStruct` uses this
  `tensorObj`, `tensorHom`, associator and unitors. The unit `tensorUnit C c`
  is `(single C c 0).obj (𝟙_ C)`, exactly the unit concentrated in degree zero.
- The complex associator is `mapBifunctorAssociator (curriedAssociatorNatIso C)`;
  its underlying graded associator identifies the two iterated coproducts indexed
  by triples with fixed total degree, using the associator of C. The unitors use
  `tensorUnitIso` and the corresponding graded unitors. Thus the chosen structure
  is the one the node specifies, not merely an existential monoidal structure.
- K(C) is Mathlib's `HomotopyCategory C (ComplexShape.up ℤ)`, the quotient by
  `homotopic`, defined as `Nonempty (Homotopy f g)`. In `Homotopy.lean:126–129`,
  `hom i j` vanishes unless j+1=i and `comm` is
  `f.f i = dNext i hom + prevD i hom + g.f i`. Set h^n=`hom n (n-1)`:
  this is f^n-g^n = h^(n+1) after d_X plus d_Y after h^n, exactly the node's
  formula (the two summands commute in the additive Hom group).
- Tensor passes to classes: the upstream `bifunctor` is
  `(curriedTensor C).bifunctorMapHomotopyCategory c c c`. The latter is a genuine
  `Quotient.lift₂`, using `mapBifunctorMapHomotopy₁` and
  `mapBifunctorMapHomotopy₂` to respect homotopy in each variable.
- Its monoidal structure is
  `HomotopyCategory.MonoidalCategory.instMonoidalCategory` at lines 235–237.
  It is assembled from that bifunctor, `unit`, `associator`, `leftUnitor`,
  `rightUnitor`, `pentagon` and `triangle` via `MonoidalCategory.ofBifunctor`.
- The quotient is strong monoidal by
  `HomotopyCategory.MonoidalCategory.instMonoidalHomologicalComplexQuotient_weilConjectures`
  at lines 240–246 (the elaborated name of the source's anonymous instance).
  It uses `Functor.CoreMonoidal.toMonoidal` with `εIso := Iso.refl _` and
  `μIso _ _ := Iso.refl _`, and verifies the three coherence equations. Hence its
  unit and tensor comparisons are isomorphisms, as required by the strong-monoidal
  dependency, with the specified construction rather than arbitrary comparisons.
- The quotient associator is explicitly the image of the complex associator by
  `associator_hom_app_app_app`; likewise `leftUnitor_hom_app` and
  `rightUnitor_hom_app` identify the unitors with the quotient images. The upstream
  `pentagon` and `triangle` prove the required identities by applying the quotient
  to the corresponding complex identities. These are also fields of the resulting
  `MonoidalCategory` instance.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic:112`, with `hasZeroObject` and the finite
  biproduct theorem at lines 274–284.
- `def-weil-abstract-derived-category`: `DerivedCategory` and `HasDerivedCategory`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic:74–95`. This node uses its cochain
  complexes and homotopy category, not the localization or a derived-category size
  assumption; the underlying complex and quotient definitions were read directly.
- `def-sfb-preserves-kflat-quasi-iso`:
  `Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso`, including the full
  signatures and docstrings of `CochainComplex.IsKFlatForTotalTensor`,
  `CategoryTheory.Functor.PreservesTotalTensorKFlatQuasiIso`, and its exact-functor
  theorem. The shared tensor is Mathlib's `tensorObj`/`tensorHom`; the present node
  needs none of the dependency's extra functor data or K-flat tests.
- `def-sfb-monoidal-category`: `CategoryTheory.MonoidalCategory`,
  `Mathlib.CategoryTheory.Monoidal.Category:162–210`, and its data structure at
  lines 87–107. This supplies the specified associator orientation and coherence.
- `def-sfb-strong-monoidal-functor`: `CategoryTheory.Functor.CoreMonoidal`,
  `Mathlib.CategoryTheory.Monoidal.Functor:620–651`, and `toMonoidal`, the exact
  interface used by the quotient instance.

Edge cases checked by inspecting the constructions: zero complexes; the unit in
exactly degree zero; complexes supported in any positive or negative degree;
negative-degree parity; unbounded inputs with infinitely many pairs in a total
degree; and distinct object/morphism universes. The colimits are coproducts, never
products. Empty contributions and off-zero components of the single complex are
zero objects. Nothing requires tensor exactness, K-flatness of the inputs, a
braiding, a nonzero object, or a boundedness condition. There is no statement fault
or disputed assertion.

Searches actually run with `msearch.py Q104 lem-sfb-total-tensor-homotopy`:

- LeanFinder: "The signed direct sum total tensor product of cochain complexes
  descends to a monoidal structure on their homotopy category and its quotient
  functor is strong monoidal." Eight hits, led by
  `HomologicalComplex.monoidalCategory`, `monoidalCategoryStruct`, `HasTensor`,
  and tensor-unit instances; no complete Mathlib homotopy descent.
- Loogle: `HomotopyCategory.MonoidalCategory.instMonoidalCategory`.
  Zero hits; unknown identifier in the service's Mathlib index. The declaration
  does exist in the upstream project, confirmed by the source and compiler.
- Grep: `monoidalCategory|MonoidalCategory|quotient`, under
  `Algebra/Homology/HomotopyCategory`. Twenty-five hits on quotient operations,
  not a Mathlib homotopy monoidal instance.
- LeanSearch: "Tensor product of cochain complexes descends to the homotopy
  category, with a strong monoidal quotient functor." Eight hits including
  `HomotopyCategory.quotient`, `HomotopyCategory`, and
  `HomologicalComplex.tensorObj`; no complete homotopy monoidal result.
- Direct `rg` in `WeilConjectures` for the item id: no hits. Direct search in
  the upstream homotopy monoidal module located the construction and the two
  instances at lines 235 and 240. The existing partial node record and audit
  identified the elaborated name of the latter.
- Direct `rg` of `lean/Sheaf` for the item id, quotient instance and homotopy
  monoidal types found consumers such as `ScalarExtensionDerivedRestriction`,
  not a competing definition of this general structure. A search of
  `dag/lean_names_upstream.json` for the two names had no hits; the current source
  and compiled checks provide the binding.

Validation: a scratch file outside `lean/`, compiled with `scompile.py`, imports
only the upstream homotopy monoidal module and the abelian and monoidal-preadditive
Mathlib modules. With independent u and v and precisely the colimit/preservation
assumptions above, all three `inferInstance` checks succeed: complexes monoidal,
homotopy category monoidal, and quotient strong monoidal. Both upstream homotopy
instances have exactly the allowed axiom set `propext`, `Classical.choice`,
`Quot.sound`. The scratch file introduces no declarations in the delivery.
The required dry run additionally checks all three recorded declarations in the
published library.

## Second reading by Q104

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
