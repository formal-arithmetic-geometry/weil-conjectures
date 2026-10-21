## Worker report

Repair of returned immutable head c8ca66406d02, group NZ, item
lem-sfb-kflat-scalar-comparison-normalization. Module:
`Sheaf.Paper.KFlatScalarComparisonNormalization`; namespace:
`SheafOfModules.ScalarPullback`.

The first required saved-packet dry run printed
`OK (dry run): commit 9af99e5f4af passes the preflight and compiles; nothing pushed`.
That mechanical success did not resolve the maintainer's H3 finding. The packet
has therefore been substantively repaired before delivery.

### Returned points repaired

1. Removed `pasteAction`, `mate_composition`, and `mate_identity`. Those generic
   mate facts did not assert the geometric scalar-comparison clauses.
2. `a_h` is now a definition. `action_existsUnique` specifies its unique ordinary
   restriction/action isomorphism by its complete underlying-section equation.
   Choosing from this unique characterization postpones only the proof of
   linearity/existence; it does not choose an arbitrary map.
3. `aD_h` is a definition, obtained by the existing exact-functor localization
   `Functor.mapDerivedCategoryNatIso` and the canonical derived composition isos.
   It does not choose a derived square. `θ_h` is the definition
   `mate dY dX (aD_h IA IB ring_compat leftExact).hom`.
4. `θ_composition` concerns two actual composable geometric inverse images
   `Lg` and `Lf`, with right adjoints `Rg`, `Rf` and geometric adjunctions
   `adjg`, `adjf`. The composite has right adjoint `Rf ⋙ Rg` and an arbitrary
   chosen inverse image `Lh` with its adjunction `adjh`. The canonical
   inverse-image composition map `Lg ⋙ Lf ≅ Lh` is exactly
   `(adjg.comp adjf).leftAdjointUniq adjh`. The independent algebraic
   presentations `IhA` and `IhB` are compared with the iterated presentations.
   `ringA` and `ringB` identify the ring comparison along this canonical
   isomorphism with `Lf.map IgR.ringUnderlying.hom ≫ IfR.ringUnderlying.hom`.
   The conclusion provides `cA` and `cB` and fixes each on every underlying
   section by `IhR.moduleUnderlying.inv ∘ canonicalComposition ∘
   Lf(IgR.moduleUnderlying.hom) ∘ IfR.moduleUnderlying.hom`. Thus these are the canonical module composition
   maps, rather than arbitrary comparison isomorphisms.
   `compositionDerived` uses the existing exact-functor comparison to localize
   these same maps. Transporting `θ_h` with those maps is asserted equal to
   the composite of `θ_f` whiskered by `g_A` and `θ_g` whiskered by `f_B`,
   including all functor associators. This is precisely
   θ_gf = (f_B* θ_g) ∘ (θ_f g_A*).
5. `θ_identity` uses the actual identity inverse image of the sheaf topos and
   identity ring identifications. Its conclusion supplies module identifications
   `iA` and `iB`, fixed by the underlying-sheaf maps. After their canonical
   exact localization and `mapDerivedCategoryIdIso`, it identifies `θ_h` with
   the identity of the model's derived scalar-extension functor, using unitors.
6. Replaced the former extra statement dependency
   `lem-pur-derived-change-of-rings` by the live owning definition node
   `def-sfb-derived-change-of-rings-cochain-model`. The existence theorem
   remains in `proof_deps` and is still available through its imported module.
   `def-weil-pbc-algebraic-inverse-image` remains an added statement dependency.
   No other non-Lean node field was changed; the packet was refreshed from the
   current read-only node before applying these dependency additions.

### Hypotheses and clauses

- Small sites: `C D : Type u`, `[Category.{u} C]`, `[Category.{u} D]`, and
  `J`, `K`. The corresponding abelian sheafification structures are explicit.
  Module universe is `u`; the ordinary derived localization Hom universe `w`
  is independent. The composition theorem uses three sites of the same kind.
- A morphism of topoi: `L`, `R`, `adj : L ⊣ R`, `[PreservesFiniteLimits L]`.
  No site morphism, points, or topological-space presentation is required.
- Ring sheaves and map: `AY BY AX BX`, `φY`, `φX`. The recorded algebraic
  inverse images `IA` and `IB` identify the X rings with inverse images of
  the Y rings; `ring_compat` identifies the coefficient map as well.
- Module categories, inverse images and restriction: `Modules` specializes the
  recorded `ringedSiteModules`, `IA.modules`, `IB.modules`, and `restriction`
  specializes Mathlib's `restrictScalars`. No replacement module category,
  tensor product, or scalar restriction is introduced.
- Ordinary unbounded derived categories and scalar extension: the four
  `HasDerivedCategory.{w}` binders and the recorded models `mY`, `mX`.
  Their existing `E`, `T`, `ε` are the ordinary extension, universal derived
  extension, and canonical cochain counit. The theorem asserts the required
  additive/exactness structures existentially; these are not flatness assumptions.
- The ordinary B-linear balanced comparison is
  `χ : mY.E ⋙ IB.modules ≅ IA.modules ⋙ mX.E`. Being a module natural
  isomorphism supplies B-linearity and invertibility. The generalized-pairing
  equation, quantified over every test sheaf `Z` and triple `(b,x,z)`, fixes it
  to inverse image of the balanced coequalizer map. `pure` uses the existing
  presheaf balanced tensor, sheafification, and model object identification.
  Inverse image is never identified with sectionwise evaluation.
- Ordinary unit preservation is the equation with `aY.unit`, the defined
  `a_h`, `restriction φX`, `χ`, and `aX.unit`.
  `AdjunctionNormalized` fixes those ordinary units to insertion of 1 and
  their derived units to the canonical cochain formulas on K-flat models.
- The canonical action map is fixed pointwise in the main theorem, and its
  derived map is fixed there on every `DerivedCategory.Q.obj H` by the
  termwise action map and exact-localization factorization isomorphisms.
  Both refer to the actual definitions `a_h` and `aD_h`.
- The representative clause quantifies over every cochain complex `P` with
  `IsKFlatIndependentCoefficients P` and `IsFlatOnSite (P.X n)` for every
  integer n. Its equation compares the defined `θ_h` with Q of χ inverse
  under the two model counits and exact inverse-image factorization maps.
  Invertibility of the X counit is asserted; the Y counit computation is
  part of the recorded model.
- Global invertibility is `IsIso (θ_h IA IB ring_compat inferInstance dY dX)`
  on the entire ordinary unbounded derived category.
- Composition and identity are the geometric companion statements described
  above, with all canonical ring/module identifications specified. Their
  contextual exactness witnesses are precisely the structures provided by
  the main theorem, and their dZ/dY/dX are the scalar adjunctions for the
  existing cochain models. No flatness or boundedness is imposed.

### Dependency declarations used

- `Sheaf.CategoryTheory.RingedToposMorphism`:
  `CategoryTheory.RingedToposMorphism`; its geometric portion is unbundled
  because this statement uses transported ring sheaves.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and its imported tensor interface;
  ordinary scalar tensors are `changeOfRings` and `changeOfRingsPresheaf`
  from `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.mateEquiv`.
- `Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses`:
  `SheafOfModules.AlgebraicInverseImageOfUniverses`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryNatIso`, `Functor.mapDerivedCategoryCompIso`,
  `Functor.mapDerivedCategoryIdIso`; Mathlib `Adjunction.comp` and
  `Adjunction.leftAdjointUniq` fix the topos composition identification. Their
  full signatures and factorization
  docstrings were read for the repair; the new definitions use these APIs.
- Proof imports retain the recorded K-flat resolution, geometric inverse-image
  exactness, geometric module construction, algebraic inverse-image tensor
  comparison, and preservation of flat-term K-flat complexes by ringed pullback.

### Edge cases and searches

Mathematical edge checks: zero rings, zero scalar extension, zero and unbounded
complexes, empty sites/degenerate topoi, identity inverse image, identity
coefficient map, and a non-flat coefficient map such as ℤ → ℤ/n.
All remain allowed. Composition uses arbitrary algebraic presentations of the
canonical composite, not an equality of their module functors; identity similarly
allows a presentation other than the literal identity module functor.

Retained searches recorded in the saved packet/search log:

- leanfinder: "Geometric inverse image commutes with derived scalar extension
  and the comparison equals the adjunction mate on K-flat representatives";
  eight derived-adjunction hits, no normalized sheaf-ring comparison.
- leansearch: "The inverse image comparison for derived change of rings is
  the scalar adjunction mate of restriction of scalars on K-flat representatives";
  ordinary scalar-adjunction/pseudofunctor hits, no exact match.
- loogle: `SheafOfModules.pullback, CategoryTheory.conjugateEquiv`;
  `conjugateEquiv_pullbackId_hom` and `conjugateEquiv_pullbackComp_inv`,
  which concern ordinary continuous-site pullback rather than this statement.
- msearch grep for K-flat scalar/mate and derived scalar/coequalizer patterns;
  no normalized comparison match. Project/upstream rg found specialized étale
  constant-coefficient comparison modules, not the arbitrary ring-sheaf statement.

Repair searches actually run in this attempt:

- msearch grep `scalar.*comparison|θ_composition|action_existsUnique`: 0 hits.
- rg of both library trees for those patterns: specialized scalar/tensor
  comparison modules, no duplicate of these declarations.
- rg for `mapDerivedCategoryNatIso`, `mapDerivedCategoryCompIso`, and
  `mapDerivedCategoryIdIso`: located their existing upstream ExactFunctor API,
  which is reused rather than reconstructed.
- Read the current node and its owning cochain-model definition node, both
  inverse-image and cochain-model source interfaces, the blueprint's full
  det-prop-scalar-six-pullback proof (1), and Mathlib's mate/localization APIs.

There are no new nodes, dependency modules, mathematical statement correction,
or disputed statement. The four postponed named theorems are
`action_existsUnique`, `kflat_scalar_comparison_normalization`,
`θ_composition`, and `θ_identity`; each carries the owning node ID, source,
and a natural-language proof. Definitions have explicit data; the only choice
is from a unique, specified action map. No sub-agent was started.

## Second reading by NZ

This is the resumed worker's self-check, not the maintainer's independent review.
Read the repaired file against every clause of the current node and the source
blueprint. The comparison is B-linear and invertible, preserves the ordinary
unit, is identified with its specified inverse mate on flat-term K-flat models,
and is globally invertible without assuming coefficient flatness or boundedness.
The former generic composition/identity statements have been removed. The new
statements refer to the defined θ_h at actual geometric inverse images, including
the composite and identity, and specify the canonical ring and underlying-module
identifications used in the equations. This supplies precisely the equation
needed by det-prop-scalar-six-pullback step 2. The transparent aliases `InverseImage`, `inverseModules`, `inverseRing`, and
`inverseUnderlying` specialize the recorded inverse-image interface and projections,
so that its six sheaf-composition instances are elaborated once rather than
repeated at every projection. They introduce no independent notion. All
variables/universes are explicit.

## Validation

The repaired file is being compiled only through the prescribed scompile.py
wrapper, under its unchanged 60-second limit. Final results are appended below.

Initial compiler diagnostics led to explicit sheafification binders on the derived
helpers and transparent aliases of the existing inverse-image projections. The
aliases avoid repeated synthesis of the six inherited sheaf-composition structures.
No time limit was raised; no mathematical hypothesis was added. A profiling
scratch file was used only for diagnosis; no profiling option is in the delivery.
The compiler then diagnosed the docstring/include ordering; moved the include
command before its theorem docstring and wrapped the remaining long lines.

Final clean scompile.py completed successfully: sandbox 23.1 s and library module
19.5 s, with no errors or warnings. Static self-check confirmed all four theorem
proofs are sorry, no definition contains sorry, all Lean lines are at most 100
characters, autoImplicit is false, and lean.statement is the main signature
verbatim. Compared against the current read-only node, only lean and the two
already-recorded statement-dependency additions differ. The existence theorem
remains a proof dependency. The final dry run follows this compile.

Final required deliver2.py --no-push printed:
`OK (dry run): commit 6e3a9a56a0a passes the preflight and compiles; nothing pushed`.
The repaired statement and metadata passed server preflight and per-file compilation.
