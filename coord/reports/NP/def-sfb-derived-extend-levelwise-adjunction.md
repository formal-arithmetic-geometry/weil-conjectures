## Worker report

Recorded the exact existing declaration
`CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction` in
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars` with
`existing: true`. No new module or theorem is delivered. Only the item's `lean`
field changes. The definition and its full surrounding variable binders were
read in the local live source and independently retrieved from the server with
`scompile.py --source WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`.
The source declaration is at lines 197–202 of the current file.

The node and its proof were compared with the main-20261015 blueprint files
`sec-proetale-coefficients/sk-def-sfb-derived-extension-of-scalars/def-sfb-derived-extend-levelwise-adjunction.md`
and its `.proof.md`, as well as the unit's `_section.md`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The category C is `{C : Type u} [Category.{v} C]`, with independent object and
  morphism universes. No equality of the two universes is imposed.
- Abelian and Grothendieck abelian are `[Abelian C]` and
  `[IsGrothendieckAbelian.{v} C]`.
- Closed symmetric monoidal is `[MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C]`.
- Tensor additive in each variable is `[MonoidalPreadditive C]`.
- Functorial flat resolutions are `[Abelian.HasFunctorialFlatResolution C]`.
- The commutative ring objects are `{R S : C} [MonObj R] [MonObj S]
  [IsCommMonObj R] [IsCommMonObj S]`. These are the paper's commutative monoid
  objects in the additive monoidal category, as in the recorded dependencies.
- The morphism of ring objects is `(φ : R ⟶ S) [IsMonHom φ]`.
- Derived extension `S ⊗ᴸ_R -` is `(Mod.extendScalars φ).leftDerivedFunctor`.
  `extendScalars` is the existing relative-coequalizer construction, with S
  acting on the first factor, and the left derived functor uses K-flat
  resolutions on the unbounded derived category.
- Termwise restriction `D(Res φ)` is `(Mod.comap φ).mapDerivedCategory`.
  Mathlib's `Mod.comap` keeps the object and morphism unchanged and restricts
  the action along φ. Exactness supplies the induced derived-category functor.
- The displayed adjunction is exactly
  `(Mod.extendScalars φ).leftDerivedFunctor ⊣ (Mod.comap φ).mapDerivedCategory`,
  between `DerivedCategory (Mod C R)` and `DerivedCategory (Mod C S)`.
  The declaration supplies actual adjunction data, rather than an arbitrary
  choice from existence. There are no flatness assumptions on S and no
  boundedness restrictions on complexes.

All three recorded statement dependencies were read in full, including the
Lean signatures and declaration/module docstrings. They use the same module
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`:

- `lem-sfb-extend-scalars-kflat`:
  `CategoryTheory.Mod.preservesKFlatQuasiIso`, providing preservation on
  K-flat complexes for the left derived functor.
- `def-sfb-derived-extend-restrict-adjunction`:
  `CategoryTheory.Mod.derivedExtendRestrictAdjunction`.
- `def-sfb-derived-restrict-levelwise`:
  `CategoryTheory.Mod.rightDerivedComapIsoMapDerivedCategory`.

The existing definition's body is exactly
`(derivedExtendRestrictAdjunction φ).ofNatIsoRight
(rightDerivedComapIsoMapDerivedCategory φ)`. This uses the recorded
adjunction and canonical comparison without an interface repair. It implements
all three proof steps: obtain L(Ext) ⊣ R(Res); obtain the canonical comparison
ρ; transport the Hom equivalence by postcomposition with ρ. Mathlib's
`Adjunction.homEquiv_ofNatIsoRight_apply` and
`Adjunction.homEquiv_ofNatIsoRight_symm_apply` give the forward map and inverse
specified by step 3. The unit and counit of the transport are the displayed
ones in that step.

Edge cases checked: φ = identity is explicitly specialized in the compiled
probe. Zero objects and a zero scalar object require no nonzero hypothesis;
the construction and Hom-equivalence transport remain meaningful. A nonflat
scalar quotient, such as Z → Z/n, is not excluded by any binder; it is handled
by the left derived functor. All complexes are unbounded, including the zero
complex. There is no index-set, characteristic, or boundedness restriction.
These latter edge cases were checked by reading the hypotheses/construction,
not by claiming separate concrete Lean instantiations.

Searches made with `msearch.py NP def-sfb-derived-extend-levelwise-adjunction`:

- LeanFinder query: "Derived extension of scalars for module objects is left
  adjoint to termwise restriction of scalars on unbounded derived categories".
  Eight hits: ordinary ModuleCat adjunctions and generic derived-category
  machinery; none gives this module-object construction.
- Loogle query: `CategoryTheory.Adjunction.ofNatIsoRight`. Five hits give the
  generic transport and its unit, counit, and Hom-equivalence formulas.
- Mathlib grep query:
  `derivedExtendMapDerivedCategoryAdjunction|derivedExtendRestrictAdjunction|ofNatIsoRight`
  in `CategoryTheory`. Thirteen hits concern generic adjunction transport;
  none is the module-object derived adjunction.
- LeanSearch query: "Derived extension of scalars is left adjoint to exact
  restriction applied termwise on unbounded derived categories". Eight hits
  concern ordinary ModuleCat scalar change; no exact Mathlib match.
- `rg` of `lean/WeilConjectures` found the exact existing declaration in
  `CategoryTheory/ModuleObjects/DerivedExtendScalars.lean:200`, as well as both
  dependencies. `grep -rn` for the node id there found no literal blueprint
  annotation. The exact declaration name has no entry in the local
  `dag/lean_names_upstream.json` index; the live source and server probe supply
  the current authoritative interface.
- `rg` of `lean/Sheaf` found existing consumers of this exact upstream name,
  including coefficient-completion and scalar-pullback modules. No duplicate
  statement is needed.

Validation: the sandbox-only `scratch/ExistingProbe.lean` imports the recorded
module, prints all four full types, and directly uses the existing adjunction
under every ambient hypothesis with `autoImplicit false`, for arbitrary φ
and the identity. `scompile.py` passed both its sandbox and library checks
(5.9 s and 5.8 s), with no errors or warnings. The scratch probe is not a
library module and is not delivered. The delivery wrapper additionally
compiles its own existing-declaration check.

No statement correction, disputed statement, new node, dependency repair,
or new proof is needed. The maintainer's independent review is the second
reading required by the current dispatcher brief.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
