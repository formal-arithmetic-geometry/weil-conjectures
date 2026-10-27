## Worker report

The delivery states the unchanged node in one module,
`Sheaf.AlgebraicGeometry.PerfectScalarChangeModel`. Its primary theorem
`AlgebraicGeometry.ProEtale.sfbPerfectScalarChangeModel` is the two displayed
isomorphisms in the new coefficient derived category on every specified chart.
The companion `sfbPerfectScalarChangeModels` states all finite projectivity,
finite-free retract, flatness, and K-flatness clauses, without any ambient derived
object or cover. Specializing it to `X = 𝒰.X i` gives those clauses on every chart.
Both proofs are `sorry`; the three complex constructions contain real data.
There are no new nodes, dependency repairs, or statement changes.

Source read: the current `literature/blueprint/latest/blueprint/` copy of
`sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-ctf.proof.md`,
paragraph (2), including the displayed scalar-change formula. The node's seven
proof steps are carried into the theorem docstrings, including the general
ringed-site restriction and tensor inputs. The whole node and its statement
dependencies' records were read before writing.

Hypothesis and clause correspondence:

- Arbitrary commutative condensed rings are `Λ Λ' : Sheaf (coherentTopology
  Profinite.{u}) Ab.{u + 1}`, each with `MonObj` and `IsCommMonObj`. The arbitrary
  ring morphism is `a : Λ ⟶ Λ'` with `IsMonHom a`. No topological presentation,
  admissibility, flatness, characteristic, or Noetherian hypothesis appears.
- The scalar rings R and R' are the recorded `scalarRingObj Λ` and
  `scalarRingObj Λ'`, literally sections at the one-point profinite set, with the
  existing lax-monoidal ring structures. `scalarSections.map a` is their induced
  ring map. Scalar modules use the dependency's internal-module encoding
  `Mod Ab (scalarRingObj Λ)`, equivalent to ordinary R-modules.
- Every scheme S is `S : Scheme.{u}`; its coefficient module category is
  `Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u+1}) (condensedRingObj Λ S)`.
  These internal module sheaves encode precisely sheaves with sectionwise
  coefficient action and linear maps. This is the same published coefficient
  framework used by the recorded local-model and coefficient-change nodes.
- P is an object of the ordinary `DerivedCategory` of that category. Its derived
  coefficient change is `(Mod.extendScalars (coefficientMap a S)).leftDerivedFunctor.obj P`.
  This is the general unbounded left derived extension, which requires no flat
  coefficient map; the flat-only upstream `derivedPullIso` is not used.
- The specified pro-etale cover is `𝒰 : Scheme.Cover.{u}
  Scheme.proetalePrecoverage S`. This keeps the actual covering condition rather
  than assuming an arbitrary jointly surjective family. The chart maps are `𝒰.f i`.
- The specified scalar complexes are `C i`. Boundedness is `hb`, giving two
  integer bounds and `IsStrictlyGE`/`IsStrictlyLE` for each chart. Bounds need not
  be uniform over the cover. Finite projectivity is `hp`: each term is a retract
  of `Mod.finiteFree (scalarRingObj Λ) n` for some natural n. A finitely generated
  projective module has exactly such a splitting; conversely a finite-free
  retract is finite and projective. This writes the termwise hypothesis rather
  than merely assuming an isomorphic perfect derived object.
- The specified isomorphisms are `e i`, from the levelwise derived chart pullback
  `(CondensedRing.upperStar Λ (𝒰.f i)).mapDerivedCategory.obj P` to
  `DerivedCategory.Q.obj (sfbScalarModelComplex (𝒰.X i) (C i))`.
- `sfbScalarModelComplex` applies precisely the recorded
  `finiteConstantScalarExtension Λ X` degree by degree. That functor is
  `scalarConstant X` on scalar modules followed by extension along the canonical
  `scalarCoefficientHom Λ X`; thus scalar tensors really mean constant sheaves,
  not an arbitrary condensed scalar module. Its zero-morphism preservation is
  obtained from the existing adjunction and finite-colimit instances inside the
  definition, with no postponed proof or extra assumption.
- `sfbScalarChangedComplex a C` is ordinary termwise `Mod.extendScalars` along
  `scalarSections.map a`, namely R' tensor_R C. The first three conjuncts of
  `sfbPerfectScalarChangeModels` state its boundedness and finite projectivity.
- The next conjunct asserts, in each degree, finite-free retractions and
  `ObjectProperty.flat` for both the old coefficient model and the new scalar
  model. This recorded flatness predicate says tensor on either side is exact;
  by the existing symmetry it is equivalent to the node's right-tensor exactness.
- The last two conjuncts assert `(HomologicalComplex.quasiIso _ (.up ℤ)).kFlat`
  for both coefficient complexes. This is the exported K-flat predicate of
  `def-pc-kflat-complex`, for the actual total tensor on internal module complexes.
- `sfbExtendedScalarModelComplex a X C` is the ordinary, uncompleted complex
  Λ'_X tensor_{Λ_X} (Λ_X tensor_R C). The main theorem's first `Nonempty (… ≅ …)`
  identifies the restricted derived extension with its derived-category image.
  The second identifies that image with the derived image of
  `sfbScalarModelComplex X (sfbScalarChangedComplex a C)`, namely
  Λ'_X tensor_{R'} (R' tensor_R C). Both isomorphisms live in D(Λ'_X), retaining
  the new coefficient action.
- The companion theorem universally quantifies X and the bounded scalar complex
  without any P, cover, or local presentation hypothesis. This supplies exactly
  the final cover-independent assertion. All coefficient maps remain arbitrary.

Recorded declarations used:

- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`:
  `AlgebraicGeometry.ProEtale.scalarSections`, `scalarRingObj`, `scalarConstant`,
  `scalarCoefficientHom`, `finiteConstantScalarExtension`, and their existing
  monoidal/ring-hom structures. No copy of these notions is introduced.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `upperStarFromPoint`, and
  `pointUpperStarLowerStarAdjunction`; the coefficient rings are actual pullbacks.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `coefficientMap`; its general extension uses the publicly imported
  `CategoryTheory.Mod.extendScalars` and `Functor.leftDerivedFunctor`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.upperStar`; exact chart pullback uses `mapDerivedCategory`.
- Mathlib `AlgebraicGeometry.Scheme.ProEt`, `Scheme.ProEt.topology`,
  `Scheme.proetalePrecoverage`, `Scheme.Cover`, `DerivedCategory`, and
  `DerivedCategory.Q` supply the site, actual covers, and ordinary localization.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex` was read in full. Our specified bounded
  projective representatives use its defining boundedness and term conditions;
  they are not replaced by its weaker existential choice of representative.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite` exports the existing
  `CategoryTheory.ObjectProperty.flat`, suitable for the internal-module encoding;
  `IsFlatOnSite` itself is the intrinsic SheafOfModules presentation of the same
  exact-tensor notion.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` exports the existing
  `CategoryTheory.MorphismProperty.kFlat`, suitable for these internal-module
  complexes. Its ringed-site-only predicate is not copied or misapplied.
- `Mathlib.Algebra.Module.Projective`: `Module.Projective` and its split-free
  characterization justify the explicit finite-free retract form; Mathlib
  `CategoryTheory.Retract` and `Mod.finiteFree` are used directly.

Every recorded proof-dependency module is imported, directly or by the public
statement import closure: coefficient sections localization, the point pullback
composition isomorphism, coefficient compatibility, projective modules, sheaf
tensor, flatness, bounded-above-flat K-flatness, K-flat resolutions, ordinary
derived change of rings, K-flat chart restriction, and localized tensor
restriction. These imports are the unchanged seven-step proof plan for stage 3.

Edge cases checked before writing and on rereading:

- Nonflat Z/4 → F_2 and arbitrary nonflat constant-to-coefficient maps are allowed:
  finite-free splitting, not exactness of scalar extension, proves the claim.
- Zero target ring and zero scalar complex are included. `Fin 0` gives the
  zero finite-free object; no nonzero rank or nontrivial-ring assumption occurs.
- A zero complex admits bounds in either order; no inequality l ≤ h is added.
- Empty scheme and empty cover are allowed; the main chart assertion then has
  no indices, while the independent scalar-model theorem still states its claim.
- There is no uniform boundedness or rank assumption across the cover or degrees.
- `Scheme.{u}` retains its small pro-etale site with object universe u+1 and
  morphism universe u; coefficient abelian groups and scalar modules use u+1.
  No equality between site object and morphism universes is imposed.

Searches performed:

- `msearch.py … leanfinder "Bounded finite projective scalar complexes for
  condensed coefficients remain K-flat under arbitrary coefficient change"`:
  8 hits, including `Module.Flat.of_projective`, ordinary module tensor exactness,
  and flat scalar extension. None states the condensed coefficient local-model
  calculation or all its clauses.
- `msearch.py … loogle "Module.Projective.tensorProduct, Module.Finite.base_change"`:
  0 hits. Separately read `Module.Projective.tensorProduct` and the split-free
  characterization in the actual Mathlib source.
- `msearch.py … grep "IsFiniteProjective|finiteProjective|perfectScalar|scalar.*[Kk]Flat"`:
  0 hits in Mathlib.
- `rg` in project `lean/WeilConjectures` and `lean/Sheaf`, for finite-projective,
  scalar/perfect, and the new declaration names; the node id was also searched
  in `lean/WeilConjectures`. The exact item and new names have no prior declaration.
  Related results are fixed-coefficient, adic/completed, etale, or pullback models;
  none is the arbitrary condensed coefficient statement. In particular the
  upstream flat-change derived comparison was inspected and excluded.

No mathematical dispute or node correction was found. No direct Git operation,
library write, local compiler invocation, or global build was performed.

Validation: `scompile.py Q35 lem-sfb-perfect-scalar-change-model` compiled the
complete delivered file, both the sandbox and its actual library module name,
with exit code 0 and no warnings. The wrapper's first phase included a long
server wait; the actual library-module phase reported 13.3 seconds.

## Second reading by Q35

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
