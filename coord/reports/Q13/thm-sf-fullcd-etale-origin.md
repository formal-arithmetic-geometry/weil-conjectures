## Worker report

The module `lean/Sheaf/AlgebraicGeometry/SfFullcdEtaleOrigin.lean` states
`AlgebraicGeometry.Scheme.sfFullcdEtaleOrigin`, with one `sorry` and no other
new declaration. It states the absolute and arbitrary-base-change vanishing clauses
of `thm-sf-fullcd-etale-origin`. The natural-language docstring contains all four
DAG proof steps. No definition is introduced and no theorem is proved.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Global finite-field datum, algebraic closure k and characteristic prime p0 | `D : WeilConjectures.FiniteFieldDatum.{u}`; `D.k` and `D.p` |
| Prime l different from p0 | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)` |
| Finite extension E/Q_l | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]` |
| Fixed uniformizer, coefficient quotient A_E,n | `Padic.coefficientExtensionRing l E n`, the recorded quotient by powers of the recorded chosen uniformizer |
| Integer n >= 1 | `(n : ℕ) (_hn : 1 ≤ n)`; every positive integer level is covered |
| Natural d | `(d : ℕ)` |
| Finite-type k-schemes Xbar and Y | `(X Y : Scheme.{u})`, their `.Over (Spec (CommRingCat.of D.k))` instances, and both `LocallyOfFiniteType` and `QuasiCompact` instances on their structure arrows |
| dim Xbar <= d | `_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)` |
| Proper finite-type k-morphism p | `(p : X ⟶ Y) [p.IsOver (Spec (CommRingCat.of D.k))] [IsProper p]`; properness already supplies locally finite type and quasi-compactness |
| F is a module sheaf over the constant ring A on X_proet | `F : proEtaleRingModules X (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))` |
| G is an arbitrary etale A-module sheaf | `G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))` |
| Specified isomorphism F ≅ nu*G | `_e : F ≅ (ProEtale.finiteCoefficientIntrinsicComparison X (Padic.coefficientExtensionRing l E n)).obj G` |
| Sheaves placed in degree zero | `(DerivedCategory.singleFunctor _ 0).obj` |
| Finite-level derived direct image | `proEtaleConstantDerivedDirectImage`, the exact underlying ordinary finite-level image also used by the recorded `sfFiniteDerivedDirectImage` |
| Cohomology in every integer r | `DerivedCategory.homologyFunctor _ r` with `(r : ℤ)` |
| Absolute vanishing for r > 2d | First conjunct, `∀ (r : ℤ), (2 * d : ℤ) < r → IsZero ...` |
| Every scheme map V -> Y | Second conjunct, `∀ (V : Scheme.{u}) (v : V ⟶ Y)`; no further instances or conditions on V |
| Xbar_V, g_V and p_V | `pullback p v`, `pullback.fst p v` and `pullback.snd p v` |
| Constant-coefficient pullback g_V*F | `proEtaleConstantModulePullback (pullback.fst p v) (Padic.coefficientExtensionRing l E n) F` |
| Relative vanishing with the same bound | Second conjunct applies `IsZero` to degree-r cohomology of the derived direct image along `pullback.snd p v`, for every r > 2d |
| Both restricted FullCD clauses, including all pro-etale and etale objects | The explicit absolute conjunct and arbitrary-scheme second conjunct specialize to every such site object. F remains the original-source sheaf with its specified origin witness; there is no quantifier over arbitrary sheaves on Xbar_V |

Coefficient and universe conventions: the coefficient ring is in `Type u`, and its
canonical `ULift` supplies fixed-scalar modules in `u+1`. Intrinsic constant-ring
modules use site objects in `u+1`, morphisms in `u`, and module values in `u+1`.
No site universes were equated. The fixed-scalar etale category is the encoding
explicitly authorized by `def-weil-pbc-etale-sheaves`. Its canonical realization
extends constant scalar actions to the constant ring sheaf, so the specified origin
isomorphism is in exactly the same intrinsic category as F and its direct image.
The existing realization construction does not require an extra `Finite` binder;
finiteness at positive coefficient levels is supplied by the recorded theorem for
the later proof. The chosen uniformizer is the one fixed by the dependency, rather
than a second choice.

Dependency declarations read and used (including publicly available constructions
in the recorded dependency interfaces):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, importing
  `Sheaf.NumberTheory.Padics.CoefficientExtension`: `Padic.coefficientExtensionRing`,
  `Padic.coefficientExtensionUniformizer`, `Padic.finite_coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the recorded etale module-sheaf
  convention, using `CategoryTheory.Sheaf`, `Scheme.smallEtaleTopology`, `ModuleCat`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `AlgebraicGeometry.Scheme.proEtaleSiteComparisonModules`, whose left adjoint is
  the `ProEtale.comparisonUpperStar` used by the intrinsic comparison.
- `Sheaf.Paper.SfDerivedDirectImage`: `WeilConjectures.sfFiniteDerivedDirectImage`
  uses `AlgebraicGeometry.Scheme.proEtaleConstantDerivedDirectImage` from its public
  import `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`; the theorem
  applies that same image to F[0] directly, rather than requiring an integral lift.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport` reexports
  `AlgebraicGeometry.Scheme.proEtaleConstantModulePullback` from
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`; the object-level tensor construction
  is used verbatim, matching the FullCD definition.
- `Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension`:
  `AlgebraicGeometry.Scheme.sfFullCohomologicalDimension`; its two displayed formulas
  are used explicitly, with the original-source origin restriction and arbitrary
  scheme base change in the second clause.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`:
  `AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicComparison`, constructed from
  `comparisonUpperStar` and `finiteCoefficientIntrinsicRealization`. This existing
  public interface belongs to `def-weil-pbc-proetale-modules`, now added to stmt_deps
  as an already-landed node. Its statement and recorded `ProEtaleFiniteModules`
  declarations were read; no new node or definition is required.

All stated proof-dependency modules are also imported, without `public`, including
`EtaleDirectImageVanishing`, `ComparisonDirectImage`, `ComparisonPullbackExact`,
`SupportComparisonPullbackCoherence`, `ProEtaleConstantExact`,
`FiniteLevelProEtaleBaseChange`, and `RingedEtaleOriginWitness` in their recorded
`Sheaf` topic directories. The Mathlib proof leaves are imported as well:
`Morphisms.Separated`, `ShortComplex.PreservesHomology`; the padic-number leaf is
already imported by the coefficient definitions. Their precise theorem signatures
were read, including the qcqs hypotheses, bounded-below witness, arbitrary
cartesian square, and exactness/cohomology comparison clauses. No import was omitted
for a cycle or compilation conflict.

Edge cases checked before writing: empty X (Krull dimension bottom is allowed),
empty Y, zero F and G, d=0, n=1, every integer r (including negative r, whose range
condition is false), identity base change, empty V, non-finite-type V and V of larger
dimension than X. The theorem bounds only the original X; it never asserts
`dim (X ×_Y V) ≤ d`. Arbitrarily large, nonconstructible G are included. There is
no l=p case, as explicitly excluded in the node; n=0 is explicitly excluded too.

Searches for an exact existing declaration:

- `msearch.py ... leanfinder "Higher direct images of pro-etale sheaves of etale origin under a proper morphism vanish above twice the dimension uniformly after arbitrary base change"`:
  8 unrelated scheme etale/base-change hits, no matching vanishing theorem.
- `msearch.py ... loogle '"rightDerived", "IsZero"'`: one hit,
  `CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ`; this is vanishing
  on injective inputs, not the required uniform bound.
- `msearch.py ... grep 'FullCD|HasUniformCohomologicalDimensionLE|etale.*[Vv]anishing' AlgebraicGeometry`:
  no Mathlib hits.
- `msearch.py ... leansearch "Proper direct images of etale-origin proetale module sheaves vanish above twice the dimension after arbitrary base change"`:
  8 scheme etale/proper base-change and algebra hits, no matching statement.
- `rg` in the source project's `WeilConjectures` for
  `FullCD|fullcd|fullCD|HasUniformCohomologicalDimensionLE`, and by item id:
  the relevant candidate is
  `AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedLowerStar_comparisonUpperStar`
  in `SixFunctors/ProEtale/ExceptionalAdjoint.lean:210`. Its full signature and
  docstring were read. It quantifies over every etale sheaf on every base-changed
  source, unlike this node, and has general invertible-exponent coefficients and
  a separably closed base. Thus it is not an exact `existing: true` match.
- `rg` over `lean/Sheaf` with the same FullCD pattern found the existing FullCD
  definitions and the distinct `sfFullcdUsedClass`, which includes closure clauses
  and restricts base changes to site objects; neither states this exact theorem.
  `rg` for `sfFullcdEtaleOrigin` in Mathlib, the source library, `lean/Sheaf` and
  `dag/lean_names_upstream.json` found no name collision.
- Read the live source of `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`
  through `scompile.py --source` to confirm the canonical construction. Lean drops
  its unused section-level `Finite` variable from the actual definition, so no
  finiteness argument is needed in its application.

No STATEMENT-DISPUTED flag or new node fault. The reviewed stage-1 arbitrary-base-change
repair is retained verbatim; this delivery does not alter the natural-language
statement, proof or proof dependencies.

Validation: `scompile.py Q13 thm-sf-fullcd-etale-origin <module>` passed in both
sandbox and module-path modes (5.1s and 5.4s), with no errors or warnings.

## Second reading by Q13

I independently opened the corrected node copy, its source place, the module, and
the dependency declarations. The item-by-item reading is:

| Node object or clause | Lean rendering and verdict |
| --- | --- |
| Global datum (k=\overline{\mathbf F}_q), characteristic (p_0) | `D : WeilConjectures.FiniteFieldDatum.{u}` supplies `D.k`, `D.p`, the field, and the algebraic-closure instance; exact. |
| Prime \(\ell\ne p_0\) | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`; exact. |
| Finite extension (E/\mathbf Q_\ell) | `E : Type u` with `Field`, `Algebra (Padic l) E`, and `FiniteDimensional`; exact finite-extension encoding. |
| Chosen uniformizer and (A_{E,n}) | `Padic.coefficientExtensionRing l E n` uses the dependency's single recorded uniformizer; no second choice or arbitrary quotient is introduced. |
| (n\geq1), (d\in\mathbf N) | `(_hn : 1 ≤ n) (d : ℕ)`; exact. |
| Finite-type (k)-schemes \(X,Y\) | `X Y : Scheme.{u}` over `Spec (CommRingCat.of D.k)` with locally-finite-type and quasi-compact structure arrows; this is the recorded finite-type convention. |
| \(\dim X\le d\) | `_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)`; exact. |
| Proper finite-type (p:X\to Y) over (k) | `p : X ⟶ Y`, `[p.IsOver ...]`, `[IsProper p]`; `IsProper` includes separated, universally closed, and locally finite type, so no hypothesis is missing or strengthened. |
| Pro-étale (A)-module sheaf (F) | `F : proEtaleRingModules X (proEtaleConstantRing X (...))`; exact intrinsic constant-ring category. |
| Étale (A)-module sheaf (G) | `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift ...))`; this is the dependency's fixed-scalar étale encoding and is transported canonically by `finiteCoefficientIntrinsicComparison`. |
| Origin isomorphism | `_e : F ≅ (ProEtale.finiteCoefficientIntrinsicComparison X ...).obj G`; exact canonical form of (F\cong\nu_X^*G). |
| Absolute conclusion | `∀ r, 2*d < r → IsZero (homologyFunctor ... (proEtaleConstantDerivedDirectImage p ... (singleFunctor ... F)))`; `IsZero` is the categorical vanishing of the stated cohomology sheaf. |
| Arbitrary base change | `∀ V : Scheme.{u}, v : V ⟶ Y, r : ℤ`; no finite-type, dimension, or other condition on `V`. |
| Base-changed source and maps | `pullback p v`, `pullback.fst p v`, and `pullback.snd p v`; these are the recorded fibre-product construction and projections. |
| Relative conclusion | The same `2*d` bound and `IsZero` for the finite-level derived direct image of `proEtaleConstantModulePullback ... F`; exact. |

The corrected node source is read first: its arbitrary-(V) clause is the reviewed
repair of the blueprint sentence that restricted (V) by a dimension condition.
The sole citer, `thm-sf-fullcd-used-class`, uses only the absolute clause in the
relevant proof step, so its use still holds. No `statement_change` is present in
this delivery and no further correction is needed.

Edge cases checked: empty (X), empty (Y), empty (V), zero (F) or (G),
(d=0), (n=1), negative and zero cohomological degrees (the strict bound is
then false), identity base change, non-finite-type (V), and (V) of larger
dimension than (X). The exclusions (\ell=p_0) and (n=0) are explicit. No
universe is left independent: all schemes, (E), and (V) are in `Type u`,
while the fixed-scalar module values are in `Type (u+1)` via `ULift`.

For H4 I repeated the searches with LeanFinder, LeanSearch, Loogle, and `rg` in
Mathlib, `WeilConjectures`, and `lean/Sheaf`, using queries for FullCD,
etale-origin vanishing, and right-derived `IsZero`. They found only generic
étale/proper morphism facts and the unrelated upstream candidate
`isZero_homology_rightDerivedLowerStar_comparisonUpperStar`; no exact theorem.
I also read the dependency source for `FiniteFieldDatum`, coefficient rings,
finite coefficient modules, the intrinsic comparison, pullback, direct image,
and FullCD. The added `def-weil-pbc-proetale-modules` dependency is the landed
canonical coefficient interface; it supplies the comparison used by `_e`.

No mismatch was found and no Lean or node text was changed during this reading.
The module was recompiled with `scompile.py` after the audit and passed cleanly,
with only the permitted `sorry` declaration warning absent from the compiler output.
