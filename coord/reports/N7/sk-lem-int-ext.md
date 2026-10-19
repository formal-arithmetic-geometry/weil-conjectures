## Worker report

The delivery states `AlgebraicGeometry.ProEtale.integralConstructibleExt` in
`Sheaf.Paper.IntegralConstructibleExt`, with one named theorem whose proof is `sorry`.
It supplies the missing statement dependency `sk-def-sfb-constructible` in
`Sheaf.Paper.CondensedConstantConstructibility`. No natural-language statement, statement
or proof dependency, proof step, target, upstream source or live artifact was changed.

The two clauses are a conjunction, in the order of the node. Their hypotheses and
conclusions are rendered as follows.

- The global finite-field setting is `D : WeilConjectures.FiniteFieldDatum.{u}`:
  its fields include the prime p, q = p^a, the finite field and its fixed algebraic
  closure k. `ℓ : ℕ`, `[Fact ℓ.Prime]` and `_hℓ : ℓ ≠ D.p` give the different
  coefficient prime. `E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)` is a finite
  coefficient extension in the fixed closure, the convention used in the setting.
- `X : Scheme.{u}`, `[X.Over (Spec (.of D.k))]`, `IsSeparated`, `LocallyOfFiniteType`
  and `QuasiCompact` of that structure map are precisely a separated finite-type
  k-scheme. These are the hypotheses assumed throughout the source, not hypotheses
  on the varying second argument.
- The ring object `condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X`
  is p_X^* of the genuine condensed valuation ring. `padicIntegersRingObj` uses
  continuous maps into the valuation ring with the topology induced from the
  fixed algebraic closure. The ambient category is `DerivedCategory` of
  `CategoryTheory.Mod` over this ring object in pro-etale abelian sheaves.
- Clause 1's `C ∈ Dbc` is `constantModelBoundedConstructible ... X C`.
  C is quantified over the full ambient derived category, with this predicate;
  neither derived completeness nor finite Tor amplitude is assumed additionally.
- Every small filtered diagram is quantified as `I : Type (u + 1)`,
  `[SmallCategory I]`, `[IsFiltered I]`, and `K : I ⥤ CochainComplex ... ℤ`.
  The size is the published module-object convention: scheme objects Type (u+1),
  morphisms Type u, coefficients Ab.{u+1}, and index size u+1.
- The common lower bound is exactly
  `∃ b : ℤ, ∀ (i : I) (r : ℤ), r < b → IsZero ((K.obj i).X r)`.
  Thus it is a common termwise lower bound on complexes, as specified explicitly
  in the source's detail `det-lem-int-ext-continuity`, not boundedness depending on i.
- `∀ q : ℤ` retains every shift. `DerivedCategory.Q ⋙ shiftFunctor _ q ⋙
  preadditiveCoyoneda.obj (op C)` is the functor Hom(C,Q(-)[q]) into abelian groups.
  `IsIso (colimit.desc _ (...mapCocone (colimit.cocone K)))` asserts invertibility
  of the canonical map from the colimit of these groups to Hom(C,Q(colim K)[q]).
  Its legs are postcomposition with the shifted images of the actual colimit legs.
- Clause 2 quantifies C and N over module sheaves, with
  `IsConstantModelConstructible ... X C` and the identical condition on N.
  `∃ d : ℤ` occurs after C and before N, so the bound depends only on C.
  `∀ q : ℤ, d < q → Subsingleton (single₀ C ⟶ (single₀ N)⟦q⟧)` says exactly
  Ext^q(C,N)=0, with the source's definition of integer-degree Ext as derived Hom.
  A subsingleton abelian group is the zero group. No extra nonnegativity on d
  or exclusion of negative integer q is imposed.

Dependency declarations read and used:

- `sk-def-sf-setting`: its recorded module
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients` is imported; its full
  `constantComplex`, `DerivedCategoryModule` and Tor-amplitude declarations were read.
  This finite-stage vocabulary is not substituted for integral pro-etale modules.
  The setting's recorded note also names `Sheaf.Paper.FiniteFieldFiber` /
  `WeilConjectures.FiniteFieldDatum` and the coefficient-extension modules.
- `sk-def-sfb-constructible`: supplied by this delivery, using the seven declarations
  listed in its lean.declarations. The theorem uses `IsConstantModelConstructible`
  and `constantModelBoundedConstructible` directly.
- Published framework: `AlgebraicGeometry.ProEtale.condensedRingObj` and
  `upperStarFromPoint` in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`;
  `CondensedRing.upperStar` in its `UpperLowerStar.Defs`; the module category is
  the existing `CategoryTheory.Mod`, not a new encoding. `Profinite.padicIntegersRingObj`
  is from `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`.
- The missing dependency reuses `CategoryTheory.Mod.IsFinitelyPresented` from
  `WeilConjectures.CategoryTheory.ModuleObjects.Free`,
  `AlgebraicGeometry.Scheme.Stratification` from
  `WeilConjectures.ConstructibleSheaf.Defs`, the ordinary `DerivedCategory`,
  `DerivedCategory.TStructure.t.bounded`, `DerivedCategory.homologyFunctor`, and
  `DerivedCategory.finiteTorAmplitude` / `torAmplitudeIn` from
  `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`.
- The proof inputs `det-lem-int-ext-continuity` and `det-lem-int-ext-bound` have no
  Lean records or modules on the read base. Their complete mathematical application
  is in the theorem docstring; no guessed imports or duplicate theorem nodes were added.

Edge cases checked before writing: C=0 gives zero Hom and arbitrary bounds; the
empty scheme permits the zero-stratum stratification (no positive-n restriction);
rank-zero and torsion local models are permitted by a cokernel presentation, so
O_E/π is included and its potentially nonzero Ext^1 is not suppressed. Negative and
zero shifts are included. A filtered category is nonempty by definition, not an
extra accidental omission; empty coproduct-style index sets are irrelevant here.
No uniform lower bound on C is substituted for the stated bound on the varying K_i.
For general schemes the dependency explicitly switches to affine-local
constructibility; for qcqs schemes it requires the finite constructible stratification.
No frontier condition is added to a stratification.

Searches for reuse (2026-10-18):

- `msearch.py ... leanfinder`: "Hom from a bounded constructible integral pro-etale
  complex commutes with filtered colimits of uniformly bounded below complexes;
  constructible Ext uniformly vanishes in high degrees" returned 8 generic
  derived-category fractions / single-functor / support lemmas, no match.
- `msearch.py ... loogle 'CategoryTheory.Abelian.Ext'`: 12 generic Ext declarations,
  including Ext.hom and homEquiv₀, none is either integral constructible assertion.
- `msearch.py ... grep 'Ext.*filtered|filtered.*Ext|constructible.*Ext'`: 5
  unrelated filtered-category, presentability and field-extension hits.
- `msearch.py ... leansearch`: "Constructible modules over a condensed coefficient
  ring locally given by finitely presented modules over its global scalar ring"
  returned 8 hits (CondensedMod, LightCondMod, SheafOfModules finite presentations),
  no exact constant-model constructibility predicate.
- `msearch.py ... leanfinder`: "constructible condensed module finite constant
  scalar presentation pro-etale locally" returned 8 condensed free-module and
  general sheaf-presentation hits, no exact constructibility predicate.
- `rg` in `lean/Sheaf` and `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`
  for the item id, integral Ext/continuity names, constant scalar matrix/local-model
  names and the actual new declaration names found no existing exact declaration.
  The side framework was read in the exact path prescribed by the brief.
  `CondensedSheafExtContinuity` is only the rational E sheaf case;
  `IntegralConstructibleBoundedBelowCompactness` is only coproduct compactness;
  `ContinuousConstructibleModule` concerns continuous coefficient sheaves on
  noetherian schemes and does not define this arbitrary condensed-ring notion.

Validation: both delivered modules compiled separately in dependency order using
`scompile.py N7 sk-lem-int-ext <dependency> <item>`. The final dependency source
and item passed both sandbox and library-name compilation, with no errors or
unexpected warnings, in 2.4 s and 5.0 s respectively. The dependency defines real
predicates and full subcategories and contains no `sorry` or postponed helper.
The only new postponed theorem is the item itself, with its matching existing DAG
node and proof docstring. There is no statement dispute or statement correction.

## Dependency modules

`sk-def-sfb-constructible` has no Lean record or Mathlib match on the read base.
Its source distinguishes constant scalar presentations from arbitrary local finite
presentations: `det-def-sfb-constructible-local-model` explicitly says the converse
fails for a general condensed coefficient ring. Therefore the upstream
`IsConstructibleModuleObject` / `boundedConstructible` cannot supply this dependency.
The new module gives all the dependency's notions, without changing its statement:

- Clause 1 is `HasFiniteConstantLocalModel Λ X M`: choose a pro-etale cover, and
  on each member pull back a globally finitely presented module over Λ on the point.
  `Mod.IsFinitelyPresented Λ P` is an isomorphism with the cokernel of a map
  Λ^m→Λ^n. On the point, each component Λ→Λ of a Λ-linear map is multiplication
  by a global section Λ(*). Conversely a scalar matrix gives this map.
  Since p_X^* is exact, strong monoidal and preserves finite sums and cokernels,
  its module pullback gives precisely Λ_X⊗_{Λ(*)}coker(A). Every finitely presented
  scalar module has such a finite matrix. Thus P here is the condensed extension
  of the finitely presented scalar module, not an arbitrary varying local model.
- Clause 2's finite qcqs stratification is `IsFiniteConstantStratified` using
  `Scheme.Stratification`, whose fields require both locally closed and constructible
  strata, and `CondensedRing.upperStar` for restriction. The affine-local convention
  is `IsConstantModelConstructible`, using `CompactSpace X ∧ QuasiSeparatedSpace X`
  to select the qcqs branch, and every affine open otherwise.
- `ConstantModelConstructible` is Cons as a full subcategory.
  `constantModelBoundedConstructible` is boundedness intersected with the predicate
  on every integer-degree cohomology sheaf; `ConstantModelBoundedConstructible` is Dbc.
- The final Tor-amplitude clause reuses `DerivedCategory.torAmplitudeIn` verbatim
  (tensor with every degree-zero module sheaf and test cohomology in [a,b]);
  `ConstantModelConstructibleFiniteTor` intersects Dbc with the existing
  `DerivedCategory.finiteTorAmplitude` and takes the full subcategory Dctf.

Only this dependency's lean field changes, with the reason recorded in lean.note.
No new definition node is needed: this is the existing statement dependency's own
notion. No other missing prerequisite is assumed or left as data written with sorry.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
