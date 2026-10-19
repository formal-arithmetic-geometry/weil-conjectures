## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleGeneratorEpimorphism` states
`AlgebraicGeometry.Scheme.exists_constructible_generator_epimorphism`, with its entire
proof `sorry`. It introduces no definitions and no additional theorem. The mathematical
node and its dependencies are unchanged; only its `lean` record is added.

The previous worker's stale-assignment diagnosis confused stages: Q130's ledger entry
records a reviewed stage-1 split, with `reviewed` and no `lean` or `reviewed_lean` record.
This delivery supplies the previously absent stage-2 statement; it does not split the
node again or redeliver Q130's split. No repair note is present for this item.

Source read: `literature/stacks-project/etale-cohomology.tex`, Lemma
`lemma-category-constructible-modules`, Tag 095N, lines 12412--12466, especially its
finite-subfamily argument. The node applies that argument to the composite of an
arbitrary free cover of M with the given epimorphism p. Its complete six-step proof,
including the finite-disjoint-union identification, is transcribed in the docstring.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| X is a scheme | `(X : Scheme.{u})` |
| X is Noetherian, explicitly quasi-compact and locally Noetherian | `[CompactSpace X] [IsLocallyNoetherian X]` |
| A is a finite commutative ring | `(A : Type (u + 1)) [CommRing A] [Finite A]` |
| M and C are sheaves of A-modules on the small etale site | `{M C : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}` |
| p is an arbitrary epimorphism M to C | `(p : M ⟶ C) [Epi p]` |
| C is constructible | `(hC : IsConstructibleEtaleModuleSheaf C)` |
| There are finitely many etale morphisms u_i:U_i to X | `∃ (n : ℕ) (U : Fin n → X.Etale)`; `(U i).hom` is etale by the defining property of `X.Etale` |
| Every u_i is separated | `∀ i, IsSeparated (U i).hom ∧ ...` |
| Every u_i has finite type | `LocallyOfFiniteType (U i).hom ∧ QuasiCompact (U i).hom`, exactly the recorded conjunction |
| A_U is the constant rank-one module sheaf over A_U | `(constantSheaf (U i).left.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)` |
| (u_i)_! is the specified etale extension by zero | `(Etale.etaleLowerShriek (ModuleCat.{u + 1} A) (U i).hom inferInstance).obj` applied to that constant module sheaf |
| The source is the finite direct sum of these extensions | `∐ fun i : Fin n ↦ ...`, the coproduct in the abelian category of module-valued sheaves |
| e maps this sum to M | `∃ e : (∐ ...) ⟶ M, ...` |
| p composed with e is an epimorphism | `Epi (e ≫ p)` |
| The finite sum can be combined over the finite disjoint union | The actual scheme coproduct is `∐ fun i : Fin n ↦ (U i).left`; its structure map is exactly `Sigma.desc (fun i : Fin n ↦ (U i).hom)`. The statement supplies its etaleness, separatedness and finite type, and `Nonempty` of an isomorphism from the finite sum to the extension of the rank-one constant module sheaf along this map. Transporting e by this isomorphism gives the same epimorphic composite from the combined source. |

No affineness restriction is imposed on the witnesses: although the proof selects affine
objects, the statement allows every separated etale finite-type family, as the node says.
No constructibility or finite-generation assumption is imposed on M. No flatness, torsion,
nonzero ring, nonempty base, nonempty index set, or characteristic assumption is added.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale` and
  `AlgebraicGeometry.Scheme.Etale`, used through the site and lower-shriek imports.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` (transitively public).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `AlgebraicGeometry.IsSeparated`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`, exactly the recorded
  dependency interface with constructible parts and finite constant values.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: recorded sheaf-category convention.
  In accordance with that node's note, the constructible material uses module-valued
  sheaves, not the alternative `SheafOfModules` encoding.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`:
  `AlgebraicGeometry.Etale.etaleLowerShriek` with its full coefficient category,
  morphism and proof of etaleness arguments; it sheafifies the sum-over-lifts presheaf.
- `Mathlib.AlgebraicGeometry.Limits`: scheme coproducts, with `Sigma.desc`;
  `CategoryTheory.Limits.Sigma` supplies the sum and its universal property.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape`: the existing
  colimit instances for the module-valued sheaf category. No local instance is introduced.
- `def-weil-pbc-scheme-conventions` has a convention record and no declaration/module;
  its named Mathlib properties are used directly.

Recorded proof-dependency modules are imported without `public` for the future proof.
For `lem-weil-pbc-constructible-module-finite-stalks`, the existing
`Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteStalks` counterpart is imported:
its `constructibleModule_finite_geometric_stalk` uses the recorded side-project
constructibility predicate. The upstream counterpart imports the distinct, duplicate
`WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`; importing both
would collide. No upstream declaration is copied or redefined. Mathlib proof leaves
(separatedness, qcqs permanence, spectrality, exact stalks and coproducts) are present
in the existing import closure. No import cycle is introduced.

Edge cases checked mathematically before drafting:

- Empty X: the sheaf category is trivial; n = 0 and the empty scheme coproduct are allowed.
- C = 0: the empty family has zero-to-C epic composite, with no requirement that e be epic.
- Zero coefficient ring: no nontriviality condition is present; the module category is trivial.
- n = 0: both the empty sheaf sum and the empty scheme coproduct are defined, and the
  rank-one extension from the empty scheme is the zero sheaf. The combined-map clauses
  remain meaningful and true.
- M arbitrary, including infinitely generated/nonconstructible M: only C is assumed
  constructible, and only e followed by p is required to be epic.
- p an isomorphism: the usual finite generator cover of C transports to M.
- Universes: `X : Scheme.{u}` and coefficients/module values in `Type (u + 1)` use the
  established constructible-module convention. The finite index `Fin n` is small in
  every site universe and includes every finite family up to reindexing.

Searches performed (all returned no exact statement):

- `msearch.py` LeanFinder: "An epimorphism onto a constructible etale module sheaf on a
  Noetherian scheme is lifted by a finite sum of extension by zero constant rank one
  sheaves". Eight hits, including `SheafOfModules.GeneratingSections.ofEpi`, `.ofEpi_I`,
  `.opEpi_comp` and `generatorsOfIsCokernelFree`; these are generic generating-section
  results and do not give finite etale rank-one generators lifting an arbitrary p.
- `msearch.py` Loogle: `SheafOfModules.GeneratingSections.epi`. One generic hit, which
  does not select a finite etale family or lift through an arbitrary p.
- `msearch.py` grep, subdirectory `AlgebraicGeometry`:
  `constructible.*epi|epi.*constructible|finite.*generator`. Zero hits.
- `msearch.py` LeanSearch: "Every epimorphism of etale module sheaves onto a constructible
  sheaf is covered by a finite sum of etale extension by zero constant sheaves".
  Eight hits: generic sheaf local surjectivity and generating-section statements,
  including `CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`; no exact match.
- `rg` of the upstream project and `lean/Sheaf`:
  `generator.*epi|Generator.*Epi|finite.*[Ee]pimorph|constructible.*[Gg]enerator|etaleLowerShriek.*constant|∐.*etaleLowerShriek|etaleLowerShriek.*∐`.
  Read the closest results: `ConstructibleSheaf/FreeLifting.lean` and
  `SixFunctors/Etale/Derived/Finiteness/FlatModel.lean`. Their generic
  `liftsAlongEpi_of_exists_epi_sigma_freeYoneda` requires a generator hypothesis and
  concludes an abstract lifting property; `liftsAlongEpi_flat_isConstructibleSheaf`
  concludes a flat constructible cover and does not retain the specified sum.
- Read `Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteEpimorphism`:
  `exists_affine_free_etale_epimorphism` covers F itself and has no arbitrary p/lift.
- Searched the item id in the upstream project: no occurrence. Searched the new full
  declaration name and module name in Mathlib, the upstream project, `lean/Sheaf` and
  `dag/lean_names_upstream.json`: no occurrence.

Validation: `scompile.py NU lem-trf-constructible-generator-epimorphism` compiled
`Sheaf.AlgebraicGeometry.ConstructibleGeneratorEpimorphism` successfully, without errors
or warnings. There are no new nodes, no dependency-record repairs, no statement
correction and no unresolved statement dispute. The only postponed proof is the named
theorem belonging to this DAG node.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
