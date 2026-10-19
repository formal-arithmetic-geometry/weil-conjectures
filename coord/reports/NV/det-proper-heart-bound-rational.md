## Worker report

The module `Sheaf.AlgebraicGeometry.ProperHeartBoundRational` states both alternatives of det-proper-heart-bound-rational, as `AlgebraicGeometry.ProEtale.isZero_higherDirectImage_rational_of_isProper` (finite rational coefficients) and `AlgebraicGeometry.ProEtale.isZero_higherDirectImage_padicAlgCl_of_isProper` (algebraic-closure coefficients). Both proofs are exactly `sorry`. No definition, dependency record, natural-language statement or proof route is changed.

Clause-by-clause correspondence (the common binders are repeated in each theorem):

- The prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- A finite subextension E of Qbar_ell over Q_ell is `(E : PadicAlgCl.FiniteIntermediateField ℓ)`. This upstream subtype contains exactly finite intermediate fields, with their induced topology. The Qbar conclusion does not depend on a chosen auxiliary E; universally quantifying an unused E would be redundant, since the degree-one subfield always exists.
- The field k is `(k : Type u) [Field k]`; positive characteristic is `hchar : ringChar k ≠ 0`. For a field, its characteristic is zero or prime; excluding zero is exactly positive characteristic. Difference from ell is `hell : ringChar k ≠ ℓ`.
- X and Y are arbitrary `Scheme.{u}`. Their structures over k are `[X.Over (Spec (.of k))]` and `[Y.Over (Spec (.of k))]`. Each has `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` on its structure morphism. The latter two together say finite type. These are the standing setting, without a new predicate or a chosen compactification hypothesis.
- The named map is `(p : X ⟶ Y)` with `[p.IsOver (Spec (.of k))]` (over k) and `[IsProper p]` (proper).
- The integer d is `(d : ℤ)`. For every point `y : Y`, the expression `Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y` is its canonical algebraic-closure geometric point. `pullback p (...)` is exactly the geometric fibre named by the dependency record, not the ordinary fibre or an arbitrary geometric test object.
- `hd` bounds `topologicalKrullDim` of each geometric fibre by `if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞)`. The codomain of the recorded dimension is {-infinity,0,1,...,+infinity}; for nonnegative d this is its usual bound. For every negative d, dimension ≤ d is equivalent to dimension = bottom, i.e. an empty fibre. Thus the conditional is an exact encoding of an integer bound, including all negative integers, rather than a nonnegative restriction.
- For finite rational coefficients the condensed ring is `Profinite.continuousMapRingObj E`, with ring on X `padicSubfieldRingObj X ℓ E`; the latter unfolds to `condensedRingObj (Profinite.continuousMapRingObj E) X`. For Qbar it is `Profinite.padicAlgClRingObj ℓ`, and the ring on X is `padicAlgClRingObj X ℓ`. Its sections have image in a finite subextension, as required; it is not the larger condensed ring of all continuous maps into the algebraic closure.
- `M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (...)` is an internal module over the pulled-back ring on X. The hypothesis `IsConstantModelConstructible (...) X M` is exactly membership in the recorded Cons full subcategory. It uses finite constant scalar models on constructible locally closed strata, not arbitrary local finite-presentation matrices.
- `DerivedCategory.singleFunctor _ 0` embeds M in degree zero; `(CondensedRing.lowerStar (...) p).rightDerivedFunctor` is Rp_* on internal module objects. In particular it derives the composite with scalar restriction, not the abelian-sheaf functor or a different module pushforward. Its target automatically uses `condensedRingObj (...) Y`, i.e. Lambda_Y.
- `q : ℤ` and `hq : 2 * d + 1 < q` render every degree above 2d+1. `DerivedCategory.homologyFunctor _ q` takes its cohomology sheaf in degree q (the complex shape is cochain). `IsZero` means that module sheaf is zero. No restriction on q or extra conclusion is added.

Dependency declarations read and used:

- sk-def-sfb-constructible: `Sheaf.Paper.CondensedConstantConstructibility`, `AlgebraicGeometry.ProEtale.IsConstantModelConstructible` (and its finite-constant-local-model/stratification definitions). Confirmed against current source using `scompile.py --source` as well as the local shared source.
- sk-def-sfb-module-derived-pushpull: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`, its `derivedUpperStarLowerStarAdjunction` interface and the generic `CategoryTheory.Functor.rightDerivedFunctor` (defined in `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`). The statement uses the generic functor directly, as this node requires. The underived composite is `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar` in `...ModuleObject.UpperLowerStar.Defs`.
- def-sfb-subfield-coefficient-ring: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`, `AlgebraicGeometry.ProEtale.padicSubfieldRingObj`; the underlying condensed ring is the existing `Profinite.continuousMapRingObj` in `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`.
- sk-def-sfb-qlbar-condensed has no lean record, but its closed upstream audit explicitly names `Profinite.padicAlgClCondensedRing` and `Profinite.padicAlgClRingObj`, in `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`. These definitions are reused, with `PadicAlgCl.FiniteIntermediateField` from `...RingObjects.EllAdic`. No duplicate node or definition is added.
- def-weil-proper-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper` (its finite-type formulation follows from universally closed implying quasi-compact).
- def-weil-geometric-fibre: `CategoryTheory.Limits.pullback` in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, instantiated with the exact algebraic-closure geometric point from its record. Residue fields, the canonical residue-field map and scheme pullbacks are supplied by `Mathlib.AlgebraicGeometry.Fiber`; algebraic closure by `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`.
- def-kun-topological-krull-dimension: `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`.
- sk-def-sfb-dc-setting: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`. Its standing scheme/base binders are rendered explicitly; this assertion does not use the chosen compactification, so none is imposed as extra data.
- sk-def-sfb-pulled-back-coefficients: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `AlgebraicGeometry.ProEtale.coefficientRing` / `condensedRingObj` with transported ring structures.

Proof dependencies with recorded declarations, closed upstream audit declarations or Mathlib matches are imported non-publicly. The two unstated proof-only nodes `det-proper-heart-bound-reduction` and `det-proper-heart-bound-lattice` have no available module and are the only such omitted imports. They are still cited in the complete natural-language proof docstrings; neither is needed to type this statement. The resolved stage-1 repair note asks for proof re-splitting with unchanged statement; it is not a released stage-2 interface defect and no withdrawn declaration is rebound.

Edge cases checked mathematically: d < 0 forces empty geometric fibres and then empty X; its higher images vanish in all integer degrees. d = 0 gives exactly q > 1. Empty X and empty Y remain allowed; `hd` over empty Y is vacuous while any map to Y has empty source. Zero M, rank-zero models and empty stratifications are included. E may be Q_ell itself (the bottom intermediate field), and the Qbar ring is the finite-subextension-valued one. The base field need not be perfect, finite or algebraically closed. No dimension assumption on X or Y or nonemptiness assumption is added. Universes agree with the published small pro-etale framework: schemes in Scheme.{u}, site objects in Type (u+1) and coefficients Ab.{u+1}.

Searches for an existing matching statement:

- `msearch.py ... leanfinder "proper pushforward of constructible rational pro-etale sheaves vanishes above twice the geometric fibre dimension plus one"`: eight unrelated hits (scheme-limit section vanishing, etale cancellation, constructible images); no match.
- `msearch.py ... loogle "topologicalKrullDim, DerivedCategory.homologyFunctor"`: zero hits.
- `msearch.py ... grep "proper.*[Bb]ound|[Bb]ound.*proper|cohomologicalDimension"`: 25 generic boundedness/proper metric/topology hits; no matching sheaf-theoretic theorem.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, shared `lean/WeilConjectures` and shared `lean/Sheaf` for `proper.*[Bb]ound|[Bb]ound.*proper|det-proper-heart-bound-rational` and for `isZero.*[Pp]roper|[Pp]roper.*isZero|isLE.*[Pp]roper|[Pp]roper.*isLE|[Hh]eart[Bb]ound`: existing proper torsion etale bounds and bounded-constructibility preservation do not give this rational internal-module bound. No exact match.
- `rg -n det-proper-heart-bound-rational dag/lean_names_upstream.json`: no hit. Direct inspection of ModuleObject/Derived/BoundedConstructible confirms it only asserts preservation, with no explicit 2d+1 estimate.

No STATEMENT-DISPUTED issue, new node, dependency repair or statement correction.

Validation: the first compile identified a missing scheme type annotation on the geometric-fibre expression and a missing `open scoped CategoryTheory.Obj` for transported ring-object instances. Both elaboration issues were repaired without changing the statement. The repaired sandbox and final module path compile successfully; the only reported warning was a 102-character line, subsequently wrapped to 97 characters maximum. The final `deliver2.py Q88 det-proper-heart-bound-rational --no-push` completed successfully: commit 5a801fa5dd passes the server preflight and compiles. No warnings remain after wrapping the overlong line. The dry run staged exactly the item node, its Lean module and this report.

## Second reading by Q88

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
