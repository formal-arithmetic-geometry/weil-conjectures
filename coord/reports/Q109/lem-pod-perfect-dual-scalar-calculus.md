## Worker report

The module `Sheaf.Algebra.Homology.PerfectDualScalarCalculus` states
`CochainComplex.PerfectDualScalar.perfect_dual_scalar_calculus`. Its only theorem
proof is `sorry`; there are no new definitions, choices, axioms, private helpers,
instances or local notation. The docstring carries all twelve proof steps and
their dependency names. The natural-language statement is unchanged.

The theorem gives one simultaneous, coordinate-normalized family of chain
precomposition maps `pre`, signed evaluations `ev`, scalar comparisons `beta`,
and derived comparison isomorphisms `delta`. It also records that derived duals
of perfect objects remain perfect. Quantifying over the maps before their
normalizations does not assume a comparison or replace it by an arbitrary map:
the normalizations are conclusions of the same theorem and determine the maps.

### Hypotheses and clause correspondence

- Rings and maps are `R S T : CommRingCat.{u}` and `f : R ⟶ S`, `g : S ⟶ T`.
  Every commutative ring is admitted, including the zero ring. There is no
  flatness, Noetherianity, characteristic or nonzero hypothesis. A common module
  universe is explicit, with the usual small-Hom module derived categories
  `[∀ R, HasDerivedCategory.{u} (ModuleCat.{u} R)]`, as in the existing
  `coefficientDerivedDual` and projective Hom evaluation interfaces. This binder
  specifies the localization and does not assert an additional ring property.
  The arbitrary-localization-size perfectness predicate is specialized to this
  existing module derived category; no new perfectness predicate is defined.
- The cochain object is `P : CochainComplex (ModuleCat.{u} R) ℤ`. Its bounded
  finite-projective hypothesis is exactly `P.IsStrictlyGE a`,
  `P.IsStrictlyLE b`, and
  `∀ n, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n)`.
  Empty support intervals are allowed. The canonical maps themselves are stated
  without imposing finite-projectivity; invertibility and finite-projectivity
  are asserted with precisely these hypotheses.
- `P_S` is `(E f).obj P`, with the recorded termwise extension functor.
  Mathlib writes `S ⊗[R] P`, the symmetry-equivalent scalar-first convention
  explicitly permitted by `def-weil-module-base-change`. Thus the statement's
  `x ⊗ b` is written `b ⊗ₜ[R] x`; the scalar factors have degree zero.
- `P^vee` is the existing expression `moduleHomComplex P (coefficient R)`.
  `coefficient R` is the existing single complex `R[0]`. Its differential is
  Mathlib `HomComplex.δ_hom`, namely `d_N f - (-1)^j f d_P`; here `d_N=0`,
  so it is exactly `-(-1)^j f d_P`. No competing dual complex is constructed.
  The general site Hom dependency is imported, and the landed owning node of
  its ordinary-module encoding is added to `stmt_deps`.
- The first conjunct fixes `pre` by
  `((pre R v).f j z).v p 0 h = v.f p ≫ z.v p 0 h`.
  These are exactly the precomposition coordinates. Coordinates with target
  degree different from zero land in the zero module, so specifying the
  degree-zero target coordinates specifies the full chain map.
- The next conjunct fixes `ev` on every tensor summand by
  `(p*j).negOnePow • (z.v p (p+j) rfl) x`. This is the ordered signed
  evaluation `P tensor P^vee -> R[0]`. It covers every integer degree, including
  the zero components when `p+j != 0`.
- The next conjunct fixes `beta` on pure tensors by
  `beta(a tensor z)(b tensor x) = f.hom(z(x))*a*b`, with `h : p+j=0`.
  It is an actual morphism of cochain complexes, so its type includes
  `d beta = beta d` in every degree, not just invertibility on cohomology.
- The scalar evaluation square uses the canonical
  `mapCochainComplexμIso` and `mapCochainComplexεIso`, the termwise versions
  of the tensor and coefficient-unit comparisons. Together with the two
  coordinate formulas, both paths on `(b tensor x) tensor (a tensor z)`
  have value `(-1)^(p*j) * f.hom(z(x))*a*b`.
- The finite-projective conjunct asserts `IsIso (beta f P)` and explicitly
  asserts `Module.Projective` and `Module.Finite` for every term of `P_S`,
  `P^vee`, and `(P_S)^vee`. Thus the comparison is an isomorphism of complexes,
  not merely a derived isomorphism or a componentwise unspecified equivalence.
- The chain naturality square is
  `(E f).map (pre R v) ≫ beta f P = beta f Q ≫ pre S ((E f).map v)`.
  The derived square quantifies over arbitrary `v : P ⟶ Q` in `D(R)` with
  `IsPerfectRingComplex` for both objects, and uses the existing
  `MonoidalClosed.pre`. Hence it includes every derived morphism, independently
  of chain-map representatives.
- The derived dual is the existing functor `coefficientDerivedDual R`, not a
  new definition. The family `delta` is a family of isomorphisms between
  `B f` of that dual and the dual of `B f`. Its all-morphism naturality square
  is exactly a natural isomorphism on the opposite perfect full subcategory.
- For every bounded finite-projective model the theorem supplies `k` and `l`
  identifying the localized ordinary duals with derived duals. Each is pinned
  by the canonical `DerivedCategory.Q` tensorator, signed evaluation and the
  coefficient-unit map. These are the adjoint-transpose comparisons of the
  projective Hom evaluation dependency. The next equation identifies the
  component of `delta` with `Q.map (beta f P)` through these comparisons and
  the fixed `modelMap`. It quantifies over every representative. Combined with
  all-derived-morphism naturality, this is representative independence,
  including the cocycle for changes among three models. The explicit derived
  evaluation square uses `coherenceData.tensor` and `coherenceData.unit`.
- Identity scalar extension is compared using the actual multiplication
  isomorphism `ModuleCat.extendScalarsId`. The chain identity equation says
  `beta` becomes identity through that multiplication and precomposition.
  The derived identity equation uses the already normalized
  `coherenceData.identity` on the dual and on the original object.
- The chain tower equation uses the actual balanced associator
  `ModuleCat.extendScalarsComp`, mapped termwise. The subsequent pure-tensor
  equation explicitly gives the common value
  `g.hom(f.hom(z(x))) * g.hom(a*b) * c*d`. The direct comparison has this
  value through the associator by the preceding tower equation. The derived
  tower square uses `coherenceData.comp`, with the correct contravariant
  direction on the comparison for the original object. Its evaluation version
  is the same equation composed with the signed evaluation square.
- Localization uses `ModuleCat.localizedModuleFunctor U`, the genuine fraction
  localization (with Mathlib's universe-preserving `Shrink`). For arbitrary,
  possibly unbounded `P Q` and a quasi-isomorphism `v`, the theorem asserts
  `QuasiIso` after this termwise localization; no projectivity or boundedness
  is used in this clause.
- The final conjunct gives a *natural isomorphism* `l` from scalar extension
  to fraction localization, normalized on every `1 tensor x` by
  `localizedModuleMkLinearMap`. It then gives `eta`, the localized dual map,
  with the exact equality
  `eta P = l.inv.app(P^vee) ≫ beta_{Localization U/R,P} ≫ pre(l.inv.app P)`.
  This identifies the canonical localized dual map with `beta`, rather than
  just asserting that some localization isomorphism exists. Its last formula
  is the fraction calculation `(z/s)(x/t) = z(x)/(s*t)`, using the actual
  `IsLocalizedModule.mk'` and `IsLocalization.mk'` constructors. The `@id`
  annotations only expose the definitional module types for instance search.
- All preceding equations quantify simultaneously over *every* ring map,
  including localization maps and induced maps between localized rings.
  Therefore they apply over those rings as well. Comparing the two towers
  `R -> S -> Localization(f(U))` and
  `R -> Localization(U) -> Localization(f(U))`, whose composites agree,
  gives exactly localization of `beta_f`. The same tower comparison and the
  evaluation/naturality squares identify the localized equations with those
  constructed over the localized rings. Thus the general formulas, the exact
  fraction identification and the tower equations include the final
  localization-compatibility clause; it is not replaced by a bare preservation
  assertion.

### Dependency declarations read and used

- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, its full bounded finite-projective
  model predicate with an independent localization universe.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `LinearMap.baseChange`,
  `TensorProduct`, `TensorProduct.mk`, and
  `TensorProduct.AlgebraTensorModule.distribBaseChange`.
- `WeilConjectures.Algebra.Homology.HomComplex`:
  `CategoryTheory.homComplex`, `homComplexFunctor`, `homComplex_exists`;
  its product projections and signed differential were read in full.
- `WeilConjectures.Algebra.Homology.ModuleHomComplex`:
  `CochainComplex.moduleHomComplex`, using Mathlib cochains and `δ_hom`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and the localization `DerivedCategory.Q`.
- `Mathlib.Algebra.Module.Projective`: `Module.Projective` and its lifting
  characterization. `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  the existing total tensor and `HomologicalComplex.ιTensorObj` are used.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`, its
  fraction relation and `IsLocalizedModule.mk'`.
  `Mathlib.Algebra.Category.ModuleCat.Localization` supplies the same
  localization as a functor, its canonical map and exactness instances.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectScalarTensorCoherence`:
  `DerivedCategory.PerfectScalar.E`, `B`, `coefficient`, `modelMap`,
  `coherenceData` and its normalized tensor, unit, identity and tower maps.
- `Sheaf.Paper.CoefficientDuality`: `WeilConjectures.coefficientDerivedDual`.
  This is exactly the already defined contravariant internal-Hom functor.
- Proof interfaces: `Module.dual_projective`, `Module.dual_finite` and
  `Module.instIsReflexiveOfFiniteOfProjective` in
  `Mathlib.LinearAlgebra.Dual.Lemmas`;
  `CochainComplex.IsKProjective.Qh_map_bijective` and
  `CochainComplex.isKProjective_of_projective` in the Mathlib derived/homotopy
  KProjective modules;
  `CochainComplex.projective_hom_evaluation_model` in
  `Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel`;
  `LocalizedModule.map_exact` and `IsLocalizedModule.map_exact` in
  `Mathlib.Algebra.Module.LocalizedModule.Exact`.

The three added statement dependencies are existing landed nodes:
`def-sc-module-total-hom-complex`, `def-sf-coefficient-duality`, and
`lem-sf-perfect-scalar-tensor-coherence`. Their actual recorded declarations
are used in the signature. There are no new nodes or dependency repairs.
The integral-point signed-dual helper was inspected but its owning theorem
has this item in its transitive dependency closure; it is not imported.
Instead the statement uses the owning module Hom construction directly.

### Sources, searches and edge cases

Read the current `literature/blueprint/latest/` proof of
`lem-pod-point-dualizing-complex`, specifically its coefficient-ring Hom
sentence. Also read the Stacks source around 07VI, 0A8H, 00CS and 064B and
all recorded dependency signatures and docstrings. No source correction was
needed and there is no STATEMENT-DISPUTED issue.

Searches used the prescribed `msearch.py Q109 lem-pod-perfect-dual-scalar-calculus`:

- LeanFinder: `dual bounded finite projective cochain complex base change signed
  evaluation localization natural isomorphism`. Eight hits, mainly projective
  resolutions and K-projective lemmas; no package matching the item.
- Loogle: `Module.Dual, LinearMap.baseChange`. One transvection base-change
  hit; not this theorem.
- Mathlib grep: `toDualBaseChange|dualBaseChange|baseChange.*[Dd]ual`.
  Seven hits, including `Module.Dual.baseChange` and `IsBaseChange.toDualBaseChange`.
  The latter requires finite *free* modules and is a module-only result; it
  cannot replace the finite-projective chain/derived statement.
- LeanSearch: `The dual of a bounded complex of finite projective modules
  commutes with scalar extension, naturally with evaluation and localization`.
  Eight hits, including `IsBaseChange.dual`, `Module.Dual.baseChange_baseChange`
  and the finite-projective dual instances. These are ingredients, not the
  signed chain/derived/localization package.
- `rg` of the upstream and Sheaf trees for perfect-dual scalar calculus,
  `dualBaseChange`, `toDualBaseChange`, coefficient duality and module Hom
  into a coefficient complex. The blueprint-id search of upstream returned
  no theorem for this item. Existing project statements mention this node in
  proof plans, but do not state its complete package. These searches found
  and prompted reuse of the existing coefficient-dual functor.

Checked the mathematical cases before and during writing: zero complex;
`R[0]`; an odd shift (evaluation sign is negative); a two-term complex with a
nonzero differential; a nonfree finite-projective summand; a non-flat map
`Z -> Z/2`; identity maps and towers containing an identity; arbitrary negative
cochain degrees; empty support interval; `U={1}`; and `0 in U`, including the
zero ring. The last case gives zero localization and is not excluded.
Localization's quasi-isomorphism clause covers unbounded complexes. No basis,
nonempty support, characteristic or flatness assumption has slipped in.

Compilation uses only the prescribed server `scompile.py`, checking sandbox
and actual module names separately. The developed statement, including the
explicit fraction formula and derived evaluation square, compiled cleanly;
there are no non-sorry warnings. Final dry-run and delivery use `deliver2.py`.

## Second reading by Q109

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
