## Worker report

The module `Sheaf.Algebra.Homology.ScalarAdjunctionUnitCoefficientNormalization` states
`SheafOfModules.ScalarAdjunctionNormalization.scalarAdjunctionUnitCoefficientNormalization`.
Its single postponed proof is `sorry`. The conclusion is `Nonempty (Normalization J n M)`;
this structure spells out every asserted formula and supplies the adjunctions, rather than
assuming their existence or their normalizations. No definition chooses data from this
existence assertion. The explicit helpers only specialize existing notions and construct
the actual coefficient quotient.

Hypothesis and clause correspondence:

- A small site is represented by `{C : Type u} [Category.{v} C]`, its
  `J : GrothendieckTopology C`, and `[EssentiallySmall.{r} C]`. This uses the Grothendieck
  topology/sheaf part of the recorded site convention. `[HasTerminal C]` supplies the final
  object. The explicit sheafification, locally bijective equivalence and sheaf-composition
  instances are the standard infrastructure for these module categories on a small site.
- `n : ℕ` and `hn : 1 ≤ n` retain the positive-integer hypothesis, including `n = 1`.
- `integers J` and `residues J n` are exactly `constantSheaf J CommRingCat` applied to
  `ULift ℤ` and `ULift (ZMod n)`. The size lift changes neither ring. `quotient J n` is the
  image of `Int.castRingHom (ZMod n)` under the existing lifted-ring and constant-sheaf
  functors. It is not an unspecified homomorphism.
- `IntegerModules` and `ResidueModules` transparently use `ringedSiteModules` and its
  underlying `SheafOfModules` category. An abelian sheaf is represented as its integer-ring
  module sheaf, as in the statement. `DerivedCategory`, with independent selected Hom
  universes `wZ` and `wR`, is the cohomological unbounded derived category.
- `M : DerivedChangeOfRingsCochainModel (quotient J n)` is the recorded presentation of
  `E` and `Lq`: `M.E`, `M.obj_eq` and `M.map_eq` prescribe the actual sheafified scalar
  extension, and `M.T`, `M.ε`, `M.universal` and `M.computes` prescribe its universal left
  derived pair and K-flat resolution comparison. The result holds for every such
  presentation. This parameter adds no mathematical assumption; the dependency supplies it.
- `restriction J n` is exactly the recorded `SheafOfModules.restrictScalars` along the
  underlying ring-sheaf quotient. `restriction_limits` and `restriction_colimits` assert
  exactness. `restriction_rightDerived` asserts that the termwise factorization computes
  its right derived functor, with `mapDerivedCategoryFactors.inv` as comparison.
- `ordinary` supplies `E ⊣ Res`. `ordinary_forward` is `f ↦ (x ↦ f(x ⊗ 1))`;
  `ordinary_inverse` is `g ↦ (x ⊗ a ↦ a g(x))`. The project writes the scalar first,
  `a ⊗ x`. Both formulas evaluate after `toSheafify`; object-identification casts come
  from `M.obj_eq`. The inverse formula explicitly uses the residue-module scalar action.
- `derived` supplies `Lq ⊣ Res_D`. `derived_hom` is the canonical Hom formula of
  `new-derived-adjunction-compatibility` pulled back to complexes, with `M.ε` and the
  canonical restriction factorization. It fixes which adjunction is intended, rather
  than permitting an arbitrary adjunction on the same two functors. K-flat representatives
  determine the unit, and resolutions and naturality determine it everywhere.
- `kflat_unit` quantifies over every K-flat complex using the recorded
  `IsKFlatIndependentCoefficients`. Its left side is `η ≫ Res(M.ε)`, followed by the
  canonical comparison to localized termwise restriction. Its right side is localization
  of the ordinary termwise unit. `M.computes P hP` makes `M.ε.app P` precisely the
  isomorphism `c_P` in the node. The ordinary formulas give `x ↦ x ⊗ 1` degree by degree.
- `unit_shift` quantifies over all `k : ℤ`. `Adjunction.LeftAdjointCommShift.iso` gives
  the comparison induced by the derived adjunction from exact restriction. The existing
  `Adjunction.CommShift.CompatibilityUnit` expands to the node's equation with both
  canonical shift comparisons inserted. The corresponding coherent shift structure is
  Mathlib's `Adjunction.leftAdjointCommShift`.
- `integer_kflat` asserts K-flatness of the actual `CochainComplex.singleFunctor _ 0`
  of `integerUnit`, the rank-one integer-ring module sheaf.
- `coefficient` is `∃! e : Lq(Z[0]) ≅ R[0], ...`, with the prescribed adjunct equal to
  `(DerivedCategory.singleFunctor _ 0).map (coefficientQuotient J n)`. The helper
  `coefficientQuotient` is the integer-linear map carrying `1` to `1`; its scalar action
  is through the actual constant quotient, hence its sectionwise map is the quotient.
  `mapDerivedCategorySingleFunctor` inserts exactly the canonical single/restriction
  identification. Uniqueness is among every isomorphism with this adjunct.
- `reduction` applies to every normalized coefficient isomorphism `e`, every `F`, `T` and
  `p : F ⟶ Res(T)`. `hp₀` and `IsColimit (CokernelCofork.ofπ p hp₀)` express exactly
  that `p` is a cokernel of multiplication by `n`, encoded by `n • 𝟙 F`.
- Its arbitrary isomorphism `a : Lq(F[0]) ≅ T[0]` has exactly the required normalization,
  with the same canonical single/restriction comparison. It quantifies over every
  `s : Z ⟶ F`. The first conclusion is `∃! t : R ⟶ T, q ≫ Res(t) = s ≫ p`, so uniqueness
  concerns the ordinary reduction equation alone. The second conclusion applies to every
  map satisfying that equation and says
  `t[0] = e.inv ≫ M.T.map s[0] ≫ a.hom`. In the paper's composition order this is
  `t[0] = a Lq(s[0]) e⁻¹`.
- There is no flatness assumption on the residue ring, on `F`, or on the terms of a
  K-flat complex. All comparisons are the canonical localization and single-complex
  comparisons, not freely chosen isomorphisms.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` and its documented Grothendieck-topology
  sheaf convention.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and `DerivedCategory.singleFunctor`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and its public tensor/change-of-rings API.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Sheaf.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility`:
  `exists_derived_adjunction_compatibility` (the proof plan and the displayed canonical
  Hom formula).
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.

The stated proof dependencies are imported for stage 3: ordinary coefficient adjunction
(`SheafOfModules.sheafRingCoefficientOrdinaryAdjunction`), exact derived functor
(`CategoryTheory.Functor.exactFunctor_derivedFunctor`), termwise/homotopy adjunction
(`CategoryTheory.Adjunction.mapHomologicalComplex` and `.mapHomotopyCategory`), derived
Hom comparison (`SheafOfModules.sheafRingDerivedHomComparison`), shift compatibility
(`CategoryTheory.Adjunction.CommShift.CompatibilityUnit` and
`CategoryTheory.Adjunction.LeftAdjointCommShift.iso`), tensor universal property
(`SheafOfModules.tensor_bilinear_universal`), K-flat resolutions
(`CochainComplex.exists_isKFlatResolutionIndependentCoefficients`), and the pre-derived
Hom theorem (`CategoryTheory.preDerivedAdjunctionGeneral`). Their recorded signatures
and source docstrings were read. The module docstring and theorem docstring cite the
blueprint and Stacks sources and give all nine steps of the node's proof.

Edge cases checked before writing: `n = 1` gives the zero residue ring and zero residue
modules, with the asserted unique coefficient isomorphism and reduction consistent;
`n > 1` does not require the false assertion that `Z/n` is flat over `Z`; `s = 0`,
`F = 0`, and `T = 0` preserve the equations and uniqueness. Both positive and negative
shifts, including zero, are quantified. A site with a final object is nonempty, as in the
node; a topology with degenerate sheaves causes no problem. No assertion of sectionwise
surjectivity of a sheaf cokernel or global pure-tensor representation is used.
The object, morphism, coefficient and two localization universes remain separate.

Searches for an existing statement:

- `msearch.py leanfinder`: “Derived scalar extension restriction adjunction unit on K flat
  sheaf complexes and normalized integer to ZMod coefficient quotient”. Eight hits were
  ordinary `ModuleCat` adjunctions and their units; no complete sheaf-derived statement.
- `msearch.py leansearch`: “Derived extension restriction adjunction on sheaf modules with
  coefficient unit quotient normalization”. Eight hits included ordinary module extension,
  sheaf pullback adjunctions and module sheafification; no complete statement.
- `msearch.py loogle`: `CategoryTheory.Adjunction.derived_unit,
  ModuleCat.extendRestrictScalarsAdj_unit_app_apply`: zero hits.
- `msearch.py grep` in `CategoryTheory`: `derived_unit|derivedη_fac_app|leftAdjointCommShift`.
  Six hits in the abstract derived-adjunction and shift-adjunction files, providing parts
  of the API but not this coefficient-normalization statement.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  the item id, `scalarAdjunction`, coefficient-unit/integer-sheaf terms, constant ring
  sheaves, and `unitHomEquiv`. Found general coefficient, cyclic quotient, tensor and
  normalization modules, and Mathlib's canonical rank-one module `unit`/`unitHomEquiv`.
  Read and reused the latter. The specialized integral-adic and constant-module-valued
  reductions use different objects or restricted site universes; none states this node.

No statement correction, new DAG node, unusable dependency, or disputed statement was found.
All original node fields outside `lean` are preserved. Compilation and delivery checks
are performed with the prescribed server wrappers.

Validation: `scompile.py` compiled both the sandbox and final module cleanly, with no
warnings (55.1 s and 47.3 s respectively, within the unchanged 60 s limit).
`deliver2.py --no-push` reported OK: the packet passed the server preflight and compiled.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
