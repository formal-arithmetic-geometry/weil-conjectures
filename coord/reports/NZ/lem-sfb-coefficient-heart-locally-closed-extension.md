## Worker report

The module `Sheaf.Paper.CoefficientHeartLocallyClosedExtension` states
`AlgebraicGeometry.ProEtale.coefficientHeart_locallyClosedExtension` with one `sorry`.
It introduces no definitions, helper nodes, dependency repairs, or statement corrections.
The item's node changes only in `lean`. The existing locally closed extension is reused.

The previous worker's reported live-wins refusal concerned the stage-1 split, reviewed by
Q79. That review does not supply a Lean statement: the current node has no `lean` record.
This packet states the already reviewed split; it does not re-split or change its proof.
There is no released repair note and no stage-2 return for this item in the read clone.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Noetherian scheme X, meaning locally Noetherian and quasi-compact | `(X : Scheme.{u}) [IsNoetherian X]`; Mathlib's class extends `IsLocallyNoetherian X` and `CompactSpace X`. |
| Arbitrary commutative condensed ring | `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `[MonObj Λ] [IsCommMonObj Λ]`. This is the unbundled form of the recorded `Profinite.CondensedRing`, not just a topological, finite, or field coefficient ring. |
| Internal modules over the pulled-back coefficients on every small pro-etale site | `Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)`, and the corresponding expression at X. The actual existing functors use the same expression at `a.image`. |
| Every open, closed or locally closed subscheme is Noetherian | `∀ (T : Scheme.{u}) (b : T ⟶ X), IsImmersion b → IsNoetherian T`. Open and closed immersions are special cases of `IsImmersion`; its definition is closed immersion into an open subscheme. |
| Such a subscheme has Noetherian underlying topology | `TopologicalSpace.NoetherianSpace T` in that same universal assertion. |
| All its open immersions are quasi-compact | `∀ (V : Scheme.{u}) (j : V ⟶ T), IsOpenImmersion j → QuasiCompact j`. |
| Each such subscheme is quasi-separated | `QuasiSeparatedSpace T`, the scheme quasi-separatedness convention. |
| An arbitrary locally closed immersion a from S | `∀ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)`. |
| a is quasi-compact and quasi-separated | `QuasiCompact a ∧ QuasiSeparated a`. These are conclusions, not extra hypotheses. |
| Canonical scheme-theoretic image is the topological closure | `Set.range a.imageι = closure (Set.range a)`. The image is the actual `a.image = a.ker.subscheme`, retaining its scheme structure. |
| Canonical factorization | `a.toImage ≫ a.imageι = a`. Its factors are the dependency's canonical maps, not existentially chosen maps. |
| Closed factor | `IsClosedImmersion a.imageι`. |
| Open factor | `Exists fun [_hu : IsOpenImmersion a.toImage] ↦ ...`. This existential proof enables the actual open functor's type without imposing openness as an additional hypothesis. |
| u_! and i_* are exact | `PreservesFiniteLimits` and `PreservesFiniteColimits` for each of `CondensedRing.openImmersionLowerShriek Λ a.toImage` and `CondensedRing.lowerStar Λ a.imageι`. |
| Actual a_! is i_* u_!, and is exact | Both exactness properties for `coefficientHeartLocallyClosedExtension Λ a ha`. Its existing definition is exactly the two preceding functors in diagrammatic composition order, using the canonical factorization; no private copy is made. |
| Termwise application | `Exists fun [_hadd : (coefficientHeartLocallyClosedExtension Λ a ha).Additive] ↦ ...` provides the additivity needed by `mapHomologicalComplex (.up ℤ)`. Additivity follows already from exactness and is not an additional assumption. |
| Natural cohomology comparisons for all K and all integer degrees | `∀ n : ℤ, Nonempty (F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor _ (.up ℤ) n ≅ HomologicalComplex.homologyFunctor _ (.up ℤ) n ⋙ F)`, with the full actual F written in the source. This is a natural isomorphism of functors on all cochain complexes, not just separate objectwise isomorphisms. |
| Preserves quasi-isomorphisms | `∀ (K L : CochainComplex ... ℤ) (f : K ⟶ L), QuasiIso f → QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f)`. |
| Induced functor on unbounded derived categories | `∃ D : DerivedCategory (Mod ... S ...) ⥤ DerivedCategory (Mod ... X ...), ...`. |
| Natural localization square | `Nonempty (DerivedCategory.Q ⋙ D ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)`. This is the requested functor isomorphism and includes its normalization on all complexes and maps. |
| Empty schemes and zero complexes | No nonemptiness, nonzero, boundedness, dimension, or rank hypotheses occur. Every integer n and every cochain complex is quantified. |

Dependency declarations read and reused (module names are exact):

| Node(s) | Module and declarations |
| --- | --- |
| `sk-def-sfb-condensed-ring` | `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, the transparent bundled encoding of the ring-object input. |
| `sk-def-sfb-pulled-back-coefficients` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `AlgebraicGeometry.ProEtale.coefficientRing`, its underlying `condensedRingObj`, and commutativity instance. |
| `sk-def-sfb-module-objects` | `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, and `Mod.Hom`. |
| `def-nagata-scheme-theoretic-closure`, `def-nagata-scheme-theoretic-image`, `def-nagata-scheme-image-factor` | `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `AlgebraicGeometry.Scheme.Hom.image`, `imageι`, `toImage`, `toImage_imageι`. |
| `def-sfb-module-open-lower-shriek` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`: `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek` and its finite-limit/finite-colimit instances. |
| `def-sfb-module-lower-star` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`: `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar`, with its specified underlying sheaf and action. |
| `sk-def-sfb-derived-categories` | `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` gives the recorded derived convention interface. Here its ambient categories are the existing Mathlib `DerivedCategory` and `DerivedCategory.Q`; exact descent needs no resolution choices. |
| `def-weil-closed-immersion` | `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`; `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `AlgebraicGeometry.IsImmersion`. |
| `def-weil-open-immersion` | `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`. |
| `pqf-def-locnoeth` | `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`, `IsNoetherian`. |
| `def-weil-pbc-quasi-compact-scheme` | `Mathlib.Topology.Defs.Filter`: `CompactSpace`. |
| `def-sfb-locally-closed-coefficient-extension` | `Sheaf.Paper.CoefficientHeartFiltration`: `AlgebraicGeometry.ProEtale.coefficientHeartLocallyClosedExtension`. |
| `def-weil-finite-type-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`; its quasi-compactness convention is `AlgebraicGeometry.QuasiCompact`. |
| `def-weil-quasi-separated-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `AlgebraicGeometry.QuasiSeparated`. |

All recorded non-Mathlib proof interfaces are imported: `SheafTensor`,
`InternalAbelianSheafModuleEquivalence`, `RingedSiteModules`,
`ProEtaleIdentifiedOpenClosed`, and the coefficient/module functor modules above.
Noetherian geometry and exact-functor homology/localization proof leaves are the
existing Mathlib declarations imported with `Noetherian`, `Immersion`, `Proper`, and
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
The declaration docstring reproduces all seven steps of the node's proof.

Sources inspected: the current blueprint `_section.md` and proof of
`sk-lem-coefficient-heart`, the complete item and its statement dependency records,
the declarations and docstrings of the recorded interfaces, and
`coord/pefw-upstream-framework.md` for the published pro-etale framework.

Edge cases checked: empty X or S, the empty immersion, identity immersion, purely open
and purely closed immersions, nonreduced scheme-theoretic images, arbitrary commutative
condensed coefficients (including the zero ring), zero and unbounded complexes, and
negative, zero and positive cohomology degrees. The image is not replaced by a reduced
closure. The natural functor isomorphism controls morphisms as well as objects.
No edge case forces any additional hypothesis. No statement dispute or node fault found.

Searches made on 2026-10-22:

- `msearch.py ... leansearch "An exact locally closed extension functor on internal condensed coefficient modules on the proetale site preserves cohomology and descends to the unbounded derived category"`: eight hits, including `Functor.preservesHomologyOfExact`, condensed module constructions and Ext; none states the full result.
- `msearch.py ... leanfinder "Exact locally closed extension of condensed coefficient modules via the scheme theoretic image preserves homology and induces the unbounded derived functor"`: eight hits on condensed AB properties, local cohomology, Ext, and `mapDerivedCategoryFactors`; these are partial matches only.
- `msearch.py ... loogle "CategoryTheory.Functor.mapDerivedCategory"`: twelve hits on the existing exact-functor derived construction and comparisons, used instead of duplicating those definitions.
- `msearch.py ... grep "NoetherianSpace|mapDerivedCategoryFactors" AlgebraicGeometry`: ten geometry hits, chiefly `Mathlib.AlgebraicGeometry.Noetherian`; no combined coefficient extension statement.
- `rg -n "coefficientHeartLocallyClosed|locallyClosed.*[Ee]xact|locallyClosed.*[Cc]oefficient|preserves.*lowerStar"` in `lean/WeilConjectures` and `lean/Sheaf`: found the canonical definition in `CoefficientHeartFiltration` and `CoefficientHeartExtensionAssertions` in `CoefficientHeart`. The latter is only a predicate, not a theorem, and omits the geometry and natural homology clauses. `coefficientHeart` itself assumes field coefficients and standing finite-type-over-a-field hypotheses, so it is not this arbitrary-condensed-ring statement.
- `rg -n "lem-sfb-coefficient-heart-locally-closed-extension" lean/WeilConjectures`: no hits.

Validation: `scompile.py NZ lem-sfb-coefficient-heart-locally-closed-extension` compiled
both the sandbox and intended library module names cleanly, in 2.3 and 2.4 seconds.
Every variable and universe is bound explicitly with `autoImplicit false`. Only the
named theorem's proof is postponed. The final module with its explicit dependency
imports also compiled in `deliver2.py --no-push`, which printed
`OK (dry run): commit e26bb3d8c16 passes the preflight and compiles; nothing pushed`.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
