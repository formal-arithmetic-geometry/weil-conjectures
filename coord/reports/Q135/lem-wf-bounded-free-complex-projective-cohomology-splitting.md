## Worker report

The module `Sheaf.Algebra.Homology.BoundedFreeProjectiveCohomologySplitting` states
`CochainComplex.exists_bounded_free_projective_cohomology_splitting`, with `sorry` as
its only proof. No definitions or other theorems are added. The node changes only
in `lean`; there is no statement correction or disputed statement.

I read the item's statement and eight proof steps, all three statement dependency
nodes and their recorded Mathlib declarations, the compact-object example and its
node record, and the source paragraph in
`literature/blueprint/main-20261015/blueprint/sec-purity-real-sheaves/sk-p-real-rankone/lem-wf-curve-finite-level-pd.proof.md`
(lines 23–32). The docstring gives all eight proof steps, including the descending
induction and the coordinate inverse, contraction, and derived localization step.
There is no repair note for this item.

Hypothesis and clause correspondence:

- The commutative ring is `{R : Type u} [CommRing R]`.
- The integer-indexed cochain complex of R-modules is
  `L : CochainComplex (ModuleCat.{v} R) ℤ`. Its differential-square-zero condition
  is part of Mathlib's complex structure.
- Boundedness is `hbounded`: there exist integers `a,b` such that `L.X i` is a
  zero object whenever `i < a ∨ b < i`. Allowing reversed bounds simply includes
  the zero complex; no interval or nonemptiness restriction is added.
- Having a finite basis in every degree is `hfree`: for every `i` there is an
  `n : ℕ` and a `Module.Basis (Fin n) R (L.X i)`. An arbitrary finite basis can
  be reindexed by `Fin n`, so no chosen bases or constant rank are required.
- The cohomology object is `L.homology i`, Mathlib's abelian-category cohomology
  (kernel modulo image), not an independently supplied family of modules.
- Projectivity of every cohomology module is exactly
  `hprojective : ∀ i : ℤ, Module.Projective R (L.homology i)`.
- The chosen derived-category size is the explicitly bound universe `w` and
  `[HasDerivedCategory.{w} (ModuleCat.{v} R)]`. This is the recorded size-choice
  interface of the dependency, with its standard choice available; it imposes no
  ring or module property. Ring and module universes `u,v` are independent.
- Finite support is the existential `s : Finset ℤ`. The first conjunction says
  that both `H^i(L)` and `image (L.d i (i+1))` are zero outside `s`. Thus it covers
  both cohomology summands and the lower indices of nonzero disks. It does not
  require any summand indexed by `s` to be nonzero.
- The derived isomorphism is `Nonempty (DerivedCategory.Q.obj L ≅ ∐ ...)`.
  Its summand is `(DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
  (L.homology i.1)`, shifted by `-i.1`. This is precisely `H^i(L)[-i]`, with
  cohomological shift convention `K[n]^r = K^(r+n)`.
- The complex isomorphism is the next `Nonempty (L ≅ ...)`, in the category of
  complexes itself. Its first finite coproduct consists of
  `(HomologicalComplex.single (ModuleCat.{v} R) (ComplexShape.up ℤ) i.1).obj
  (L.homology i.1)`, which has the actual cohomology module in degree `i` and
  zero differential. Its second coproduct consists of
  `HomologicalComplex.double (𝟙 (image (L.d i.1 (i.1 + 1)))) ...`, in degrees
  `i,i+1`. The image is exactly `B^(i+1)` up to the usual unique image isomorphism;
  no arbitrary boundary modules are introduced. Mathlib's `double` places the
  specified identity differential between those two terms and zero elsewhere.
  The displayed `rfl` certifies that `i+1` is the successor of `i` in this shape.
  The binary coproduct `⨿` joins the two finite coproducts. In this additive
  category these coproducts are direct sums, with no product-versus-sum change.
- Contractibility is the last clause, for every integer `i`:
  `Nonempty (Homotopy (𝟙 (HomologicalComplex.double ...)) 0)`.
  Mathlib's `Homotopy.hom` has components zero unless they lower degree by one;
  its `comm` equation is `id = dNext h + prevD h + 0`, exactly `id = dh + hd`.
  This covers every disk, including zero disks and those outside `s`.

Dependency declarations used:

- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, declarations `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.singleFunctor`.
  I read the definitions/docstrings at Basic.lean:70–100 and 235–255, the additive
  and shift instances at 140–177, and the cohomology definition
  `HomologicalComplex.homology` at ShortComplex/HomologicalComplex.lean:90.
- `def-weil-pbc-free-module`:
  `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free` and its basis interface
  `Module.Basis`; FreeModule/Basic.lean:42–66 identifies freeness with a basis.
  The node explicitly requires finite bases, rendered by `Fin n`.
- `def-weil-pbc-projective-module`:
  `Mathlib.Algebra.Module.Projective`, `Module.Projective` (Projective.lean:67–76),
  with the lifting property read at 90–105 for the documented proof plan.
  No private projectivity predicate is introduced.

Other existing constructions read and used: `HomologicalComplex.single`
(Single.lean:34–58), `HomologicalComplex.double` (Double.lean:29–90),
`CategoryTheory.Limits.image` (Images.lean:350–361), `Homotopy`
(Homotopy.lean:143–155), the degreewise colimit instances
(HomologicalComplexLimits.lean:141–185), and `ModuleCat.abelian`
(ModuleCat/Abelian.lean:77). The complex abelian-category import supplies finite
coproducts; the triangulated derived-category interface supplies finite coproducts
there. There are no new notions needing nodes or dependency-interface repairs.

Edge cases checked mathematically before drafting:

- Zero complex: the finite set may be empty, both coproducts are zero, and all
  disks have zero underlying boundary module and admit the zero homotopy.
- Zero ring: no `Nontrivial R` is assumed. Empty bases and zero modules are allowed.
- A one-degree complex uses that cohomology singleton and only zero boundary disks.
- A two-term identity complex has zero cohomology and is precisely its boundary
  disk; the identity in upper-to-lower degree contracts it.
- Negative degrees and arbitrary integer bounds are allowed; the shift is `-i`,
  so the cohomology object is placed in degree `i`, including negative `i`.
- Projective boundary/cohomology summands need not be free: for multiplication by
  2 over Z/6, the direct summands are projective and can be nonfree. The statement
  makes no freeness assumption on these summands.
- Multiplication by 2 over Z/4 has nonprojective Z/2 cohomology and is excluded
  by the actual projectivity hypothesis; no splitting of arbitrary complexes is
  asserted.
- No equality between the ring, module, or localization universes is imposed.

Searches performed in this session (all via the prescribed search wrapper):

- LeanFinder query `bounded cochain complex finite free modules projective
  cohomology splitting as cohomology and contractible disks`: eight results,
  including `CochainComplex.isKProjective_of_projective`,
  `CochainComplex.isSplitEpi_to_singleFunctor_obj_of_projective`, and projective
  resolution/K-projectivity facts. None states this complex and derived splitting.
- Loogle query `HomologicalComplex, CategoryTheory.Projective`: three results,
  `HomologicalComplex.instProjectiveXObjSingle`,
  `HomologicalComplex.instProjectiveXExtend`, and
  `CategoryTheory.ProjectiveResolution.instIsIsoFromLeftDerivedZero'Self`.
  None states this decomposition.
- Mathlib grep query
  `(projective.*homology|homology.*projective|split.*complex|complex.*splitting)`
  in `Algebra/Homology`: eighteen hits, mainly short-exact-sequence splittings,
  degreewise split triangles, and K-projective facts, with no exact theorem.
- LeanSearch query `bounded complex projective homology direct sum homology
  contractible two term complexes`: eight results, including
  `HomotopyCategory.isZero_quotient_obj_iff`, homology additivity, and biproduct
  projective-dimension bounds; no exact splitting theorem.
- Direct `rg` for `(cohomology.*split|projective.*cohomology|bounded.*splitting|
  identity.*complex|twoTerm)` in upstream `WeilConjectures` and side `lean/Sheaf`,
  plus the exact item id in upstream: no matching statement. Existing unit-entry
  cancellation modules and two-term homotopy results concern different hypotheses
  and conclusions. I opened `UnitEntrySplits.lean` and the upstream `Double.lean`;
  the latter imports the exact existing Mathlib two-term construction used here.
- Direct `rg` of `dag/lean_names_upstream.json` for the item id and
  `bounded.*free.*complex|cohomology.*splitt`, and a full-name collision search
  across Mathlib, upstream `WeilConjectures`, and side `lean/Sheaf`: no exact
  statement or collision found.

Validation: the first compile caught coproduct notation syntax, which I corrected
to Mathlib's `∐ (fun i : s ↦ ...)`. The final module is checked through the required
`scompile.py` wrapper, followed by the delivery dry run and delivery.

## Second reading by Q135

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
