## Worker report

The module `Sheaf.Paper.ProperOpenBoundaryZero` states
`AlgebraicGeometry.ProEtale.CondensedRing.proper_open_boundary_zero` with `sorry`.
No proof is supplied. Its docstring gives all six DAG proof steps, including the
coefficient-specific proper base-change cases, the finite constant-model argument
for j_!A, its Tor interval, and the final right-adjoint preservation of zero.
The item node changes only in `lean`; no statement correction or new DAG node is needed.

Clause-by-clause correspondence:

- A prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- A field of positive characteristic distinct from ell: `(k : Type u) [Field k]`,
  `[Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`. The characteristic of a field
  is zero or prime, so primality here expresses precisely positive characteristic.
- All schemes and maps over k: `(W Ybar Y Z : Over (Spec (.of k)))`, with r, i, c
  morphisms of this Over category. Their `.left` fields are the scheme maps.
  `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` on every structure map
  express exactly separated finite type, as in the recorded dc-setting interface.
  The fibre product inherits its k-structure and these properties by base change
  and composition; no independent structure on it is assumed.
- Admissible commutative condensed coefficients: Λ is a sheaf of abelian groups on
  coherent Profinite, with `MonObj` and `IsCommMonObj`. The hΛ binder uses the exact
  finite-subextension coefficient specialization defined in this item module below.
  Its finite discrete case includes the zero ring, with an arbitrary ell-power
  annihilator; Z_ell, Q_ell, E, O_E and Qlbar are all present, up to ring-object
  isomorphism. The Qlbar case is `Profinite.padicAlgClRingObj ℓ` rather than the
  larger all-continuous-map sheaf. No coefficient isomorphism is assumed to identify
  these two constructions.
- Proper r: `(r : W ⟶ Ybar) [IsProper r.left]`.
- Quasi-compact open i: `(i : Y ⟶ Ybar) [IsOpenImmersion i.left] [QuasiCompact i.left]`.
- U, j and p: U is literally `pullback r.left i.left`, j is
  `pullback.fst r.left i.left`, and p is its canonical second projection
  `pullback.snd r.left i.left`. The latter is determined and does not occur in
  the conclusion, so it needs no extra binder or tautological conjunct.
- Reduced closed complement c: `(c : Z ⟶ Ybar) [IsClosedImmersion c.left]`
  and `[IsReduced Z.left]`, together with
  `hc : Set.range c.left.base = (Set.range i.left.base)ᶜ`.
  This is the intrinsic characterization of any presentation of the reduced
  closed complement; it does not select an arbitrary closed support or thicken it.
- Every bounded constructible finite-Tor A: the binder
  `A : ConstantModelConstructibleFiniteTor Λ (pullback r.left i.left)` is exactly
  the recorded full subcategory from sk-def-sfb-constructible. It uses finite
  constant scalar models, not merely arbitrary finite-presentation matrices.
- j_! is `(openImmersionLowerShriek Λ (pullback.fst r.left i.left)).mapDerivedCategory`:
  the recorded exact module extension by zero, acting termwise on complexes.
- Rr_* is `moduleObjectDerivedPushforward Λ r.left`; c^* is
  `moduleObjectDerivedPullback Λ c.left`. They are the recorded total derived
  functors of full internal-module pushpull, in ordinary unbounded categories.
- The conclusion is `IsZero` of that target object. In a category with a zero
  object this is equivalent to an isomorphism with zero, in precisely the ambient
  ordinary derived category on Z. No claim about a comparison morphism or any
  localizing closure occurs.

Recorded dependency declarations used:

- sk-def-sfb-dc-setting:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and its
  documented Over/finite-type/separated setting. No compactification choice is
  needed in the displayed target object.
- sk-def-localizing-closure: the unchanged live interface
  `Sheaf.Paper.LocalizingAdmissibleCoefficients`,
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`. Its distinct
  continuous-map compatibility case is retained. The item module owns the narrower
  `AlgebraicGeometry.ProEtale.IsFiniteSubextensionLocalizingAdmissibleCoefficient`,
  which is listed in the item lean.declarations; it does not rebind this dependency.
- sk-def-sfb-qlbar-condensed:
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
  `Profinite.padicAlgClCondensedRing` and `Profinite.padicAlgClRingObj`.
- sk-def-sfb-module-derived-pushpull:
  `Sheaf.Paper.CondensedModuleDerivedPushpull`,
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback` and
  `.moduleObjectDerivedPushforward`.
- sk-def-sfb-module-derived-lower-shriek:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`;
  its compactification composite uses the same exact termwise j_! specialization.
  The actual j_! declaration is `CondensedRing.openImmersionLowerShriek` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`.
- def-pc-fibre-product: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` and its two projections.
- def-weil-open-immersion: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- def-weil-proper-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`.
- def-weil-closed-immersion: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- sk-def-sfb-constructible: `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.ConstantModelConstructibleFiniteTor`.

All recorded statement modules are publicly imported, and all stated proof
modules are privately imported (a statement dependency already public needs no
second import). Mathlib proof leaves use their recorded modules: OpenImmersion,
ClosedImmersion, Proper, FiniteType, QuasiCompact and
Algebra.Homology.ShortComplex.PreservesHomology. There are no omitted proof
imports due to cycles. Recorded signatures and docstrings were read in the shared
Lean sources, including the framework note coord/pefw-upstream-framework.md.

Edge cases checked before writing: empty Y gives empty U and zero extension;
i an isomorphism gives empty Z; empty W and A = 0 give zero targets. A nonreduced
W or Ybar is permitted, while Z is reduced as specified. The auxiliary closed
base change T may be nonreduced and no reducedness of T is imposed. Ell = 2 and
all positive characteristics different from ell are allowed; characteristic zero
is excluded by the actual standing setting. Finite coefficient rings killed by
ell^0 include the zero ring. Tor intervals and cohomological degrees are not
restricted by the theorem. The free universe u keeps the existing site convention
(scheme universe u, sheaf values u+1); no equality of distinct site universes or
extra resolution, density or properness assumptions are introduced.

Searches for an existing statement or exact coefficient interface:

- msearch.py leanfinder, query “Proper pushforward of open extension by zero
  restricts to zero on the closed complement”: 8 hits, concerning extension of
  functions and topological support, with no derived pro-etale module statement.
- msearch.py loogle, query `AlgebraicGeometry.IsProper`: 12 hits, defining properness
  and its permanence instances; no matching vanishing statement.
- msearch.py grep, query `proper.*[Bb]ase[Cc]hange|extensionByZero|lowerShriek`,
  subdirectory AlgebraicGeometry: 25 scheme/base-change hits, no matching theorem.
- rg in lean/WeilConjectures and lean/Sheaf for closedComplement, boundaryZero,
  BoundaryZero, proper/boundary and admissible coefficient names: found the proper
  qcqs refinement theorem in Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryVanishing
  and the continuous-algebraic-closure degree-zero refinement theorem in
  Sheaf.Paper.RefinementBoundaryVanishing. Their assumptions and coefficient/input
  conventions differ, so neither states this node. Read both modules fully.
- rg for `lem-sfb-proper-open-boundary-zero` in lean/WeilConjectures: no match.
- rg for `FiniteSubextensionAdmissible`, `FiniteSubextensionLocalizing` and
  `proper_open_boundary_zero` in both source roots: no existing declarations.
- Read IsFinitenessCoefficient / IsEllAdicFinitenessCoefficient and
  IsNormTopologicalLocalizingAdmissibleCoefficient: the former classes use exact
  presentations rather than ring-object isomorphism classes; the latter uses the
  all-continuous-map closure. Neither supplies the exact finite-subextension specialization used by this item.

Validation after repair: the single delivered module passed scompile.py both as
a sandbox source and as its library module, with no errors or non-sorry warnings.
No statement is disputed. No source statement or dependency graph is changed.

## Returned-delivery repair

Repaired the H13/H4 return on immutable head a7ecdd8ffc52. The saved-packet first
--no-push dry run passed mechanical preflight and compilation (3523e37b1d2), but
that does not resolve the maintainer's ownership objection. This repair does:

- Restores the complete sk-def-localizing-closure node file byte-identical to the
  current live record, including Q90's module, primary declaration and declaration
  list, and the A4 note retaining the continuousMapRingObj (PadicAlgCl ell) case.
- Drops Sheaf/Paper/FiniteSubextensionAdmissibleCoefficients.lean.
- Moves IsFiniteSubextensionLocalizingAdmissibleCoefficient, with identical body
  and docstring, into ProperOpenBoundaryZero.lean in AlgebraicGeometry.ProEtale.
  The item module publicly imports Sheaf.Paper.LocalizingAdmissibleCoefficients.
- Lists that real Prop-valued helper in the item's lean.declarations and explains
  ownership in lean.note. The original compatibility predicate and both
  size-indexed localizing-closure declarations are neither changed nor rebound.

The item's theorem signature, source statement, all hypotheses and conclusion,
edge cases, universes, source/proof docstrings and six-step plan are unchanged.
No dependency module or new definition node is delivered. The one theorem remains
sorry; the helper is defined in full. Its six clauses and all ring objects are
identical to the returned packet. The complete restored dependency JSON was
compared byte-for-byte with live. The helper's docstring and definition were
compared with the returned head's former module and are identical.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
