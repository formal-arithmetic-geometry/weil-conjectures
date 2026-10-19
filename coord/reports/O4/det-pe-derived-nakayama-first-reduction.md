## Worker report

The module `Sheaf.Paper.DerivedNakayamaFirstReduction` states
`AlgebraicGeometry.ProEtale.derived_nakayama_first_reduction`, with its whole proof
`sorry`. It has four conjuncts, corresponding to all clauses of the unchanged node.
The theorem's docstring carries the eight-step proof of the node, including the
strict quotient tower, the signed cone and shift comparisons, descent through
localization, the Roos comparison and augmentation, induction, cone closure and
isomorphism detection. No definition or auxiliary assertion is introduced.

Hypotheses and objects, clause by clause:

- The ambient prime and finite extension are `(l : ℕ) [Fact l.Prime]`,
  `(E : Type u) [Field E] [Algebra (Padic l) E]` and
  `[FiniteDimensional (Padic l) E]`. These are precisely the coefficient data of
  the recorded completion definition, not additional hypotheses on K or X.
- The arbitrary scheme is `(X : Scheme.{u})`. Its category is
  `DerivedCategory (AdicCompletion.Modules l E X)`. Reading `Modules` and `ring`
  shows internal modules over the pullback of the *continuous condensed* integral
  ring, not a constant replacement. All complexes and triangles use this same
  category. There is no restriction on dimension, quasi-compactness,
  quasi-separatedness, residue characteristic, or boundedness.
- `IsDerivedComplete l E X K` is the recorded definition, whose specified
  K-flat augmentation into the Roos complex is invertible after localization.
  This uses the actual canonical map, including its zero nullhomotopy.
- The first premise `IsZero ((AdicCompletion.derivedReduction l E X 0).obj K)`
  says K_1 = 0. The recorded reduction indexes positive powers by n+1, so
  index zero means the quotient by pi, not the quotient by 1.
- The conclusion `∀ n : ℕ, IsZero ((AdicCompletion.derivedReduction l E X n).obj K)`
  says K_m = 0 for every positive m, with m = n+1. Each K_m is in its finite-ring
  derived category. `IsZero K` is the accompanying conclusion K = 0.
- Cone closure is quantified over every `T : Triangle (...)` with
  `T ∈ distTriang (...)`. Completeness of `T.obj₁` and `T.obj₂` implies that of
  `T.obj₃`. This is invariant under the isomorphism specifying a derived cone,
  and covers every morphism and every choice of its distinguished cone triangle.
- Shift closure is `∀ K, IsDerivedComplete ... K → ∀ r : ℤ,
  IsDerivedComplete ... (K⟦r⟧)`. Negative, zero and positive shifts are included.
- For every `(K L : DerivedCategory (...)) (f : K ⟶ L)`, completeness of both
  objects and `IsIso ((AdicCompletion.derivedReduction l E X 0).map f)` imply
  `IsIso f`. The functor's map is the canonical derived extension of scalars of f,
  exactly the node's f tensor^L (O_E/pi)_X; no arbitrary comparison map is assumed.

Dependency declarations used:

- `Sheaf.SixFunctors.ProEtale.DerivedCompletion` (public):
  `AlgebraicGeometry.ProEtale.IsDerivedComplete`,
  `AlgebraicGeometry.ProEtale.AdicCompletion.Modules`, `ring`, `finiteRing`,
  `quotient`, `FiniteDerived` and `derivedReduction`. Full signatures and the
  construction bodies were read in the recorded module. `derivedReduction` is
  `(Mod.extendScalars (quotient ... n)).leftDerivedFunctor` and has codomain
  `FiniteDerived ... n`, the derived category over the actual finite ring.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` (public): `DerivedCategory`
  and its existing additive, zero-object, shift and triangulated structures;
  `DerivedCategory.mem_distTriang_iff` explains the cone formulation.
- Proof-only imports, corresponding to all stated proof dependencies:
  `Sheaf.Paper.DerivedNakayamaResolution` supplies
  `AlgebraicGeometry.ProEtale.DerivedNakayama.derived_nakayama_resolution`;
  `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived` supplies
  `AlgebraicGeometry.Scheme.ProEt.products_derived`;
  `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit` supplies
  `CategoryTheory.IsDerivedLimit` and `IsDerivedLimitTriangle`;
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated` supplies
  `Pretriangulated`, the three triangle-morphism isomorphism criteria, and
  `Pretriangulated.Triangle.isZero₃_iff_isIso₁`;
  `Mathlib.CategoryTheory.Limits.Shapes.Products` supplies categorical products.
  Completion's own module is already a public statement dependency.

Edge cases checked before writing: the zero object, the empty scheme, arbitrary
unbounded complexes, the first positive quotient, all higher quotients, r = 0,
negative shifts, zero morphisms between zero objects, identity morphisms, and
schemes in residue characteristic l. No argument requires l to be invertible on
X. The finite-ring and scheme universes are exactly those of the supplied
continuous-coefficient interface; no new universe equation is imposed.
Vanishing in the finite coefficient category has the usual meaning of an
acyclic finite-coefficient complex, equivalently vanishing after exact restriction
of scalars to the integral category.

Searches (2026-10-18):

- `msearch.py ... leanfinder "A derived complete complex is zero if its first
  reduction is zero, derived completeness is closed under cones and shifts,
  and reduction detects isomorphisms"`: 8 hits, all on derived zero objects,
  t-structure bounds and bounded representatives. No match.
- `msearch.py ... loogle '\"DerivedCategory\", \"complete\"'`: 0 hits.
- `msearch.py ... grep 'derivedComplete|derived.*[Nn]akayama|[Nn]akayama.*derived'`:
  0 Mathlib hits.
- `rg -n 'IsDerivedComplete|derived_nakayama'` in upstream `WeilConjectures`:
  no hits. `grep -rn 'det-pe-derived-nakayama-first-reduction'` in that tree:
  no hits. The name search in `dag/lean_names_upstream.json` also has no match.
- The same concept search in `lean/Sheaf` found the recorded completion and
  resolution interfaces and other completion statements. Inspection of
  `RingTheory/DerivedCompleteProductsTriangles.lean` shows an ordinary ring/module
  statement using a different, ideal-based predicate. Inspection of
  `SixFunctors/ConstructibleTensorCompletion.lean` shows constructible completed
  tensor products with additional qcqs and invertibility hypotheses, rather than
  this unrestricted Nakayama statement. The broader hits in
  `Paper/IntegralHomReduction.lean` and `DerivedCompleteIntegralDetailed.lean`
  give different notions or comparison assertions. None states this item.
- `rg -n -i 'nakayama|first.reduction'` in the side-published upstream
  `WeilConjectures/SixFunctors/ProEtale` framework: no hits. The framework and
  `coord/pefw-upstream-framework.md` were read from the specified shared checkout.
- The proposed full theorem name was searched in `lean/Sheaf`, upstream
  `WeilConjectures`, and `dag/lean_names_upstream.json`: no duplicate.

No statement dispute or correction, missing notion, dependency repair or new node
is needed. Only the item's `lean` field is changed in its node copy.

## Second reading by N4

This section records the worker's own second pass; the dispatcher explicitly
forbids starting other agents, and the maintainer performs the independent review.
With the node and the Lean declaration open, I checked that the first conjunct
has both the universal finite-level vanishing and integral vanishing conclusions;
the second quantifies over distinguished triangles rather than merely chain
cones; the third includes every integer shift; the fourth requires completeness
of both K and L and uses the functor's actual map of f. The prime and extension
binders reproduce those of the completion definition. In particular, quotient
index zero means exponent one throughout, and there is no boundedness or
invertibility premise. No mismatch or node-field correction was found in this
pass. The only postponed proof is the named theorem for this DAG node.

Validation: `scompile.py N4 det-pe-derived-nakayama-first-reduction` passed for
both its sandbox probe (2.2 seconds) and the final library module path (2.4
seconds), with no compiler messages. The initial namespace lookup error for
`Triangle` was repaired by opening `CategoryTheory.Pretriangulated`; no signature
change was needed. A line-width scan found no Lean line over 100 characters.
Comparing the JSON copy to the shared node confirmed that only `lean` differs.
