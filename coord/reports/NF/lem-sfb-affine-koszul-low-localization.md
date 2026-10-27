## Worker report

The module `Sheaf.AlgebraicGeometry.AffineKoszulLowLocalization` states
`AlgebraicGeometry.affine_koszul_low_localization`, with its sole proof `by sorry`.
No definition or auxiliary theorem is introduced. All seven reviewed proof steps are
carried in the theorem docstring. The node statement and proof are preserved verbatim.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- An arbitrary commutative ring is `(A : Type u) [CommRing A]`; there is no nonzero or
  Noetherian assumption. A finite sequence, including length zero, is `(r : ℕ)
  (f : Fin r → A)`.
- The affine scheme Y is `Spec (.of A)`, using `AlgebraicGeometry.Scheme` and `Spec`.
  The open W is `(W : (Spec (.of A)).Opens)` with
  `hW : W = ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)`. Each basic open is exactly
  the set of primes not containing the specified element. Its inclusion j is `W.ι`.
  The W binder and its defining equality only name the node's finite union.
- Zariski structure-sheaf modules use the shared carrier
  `SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)`, and on W the same
  carrier with `W.toScheme.toRingedSpace`. Explicit `HasDerivedCategory` binders
  specify their chosen unbounded derived categories, with independent universes wY
  and wW; no equality of these universes is imposed.
- `(E : schemeDerivedCategory (Spec (.of A)))` and
  `hE : schemeDerivedQCohProperty (Spec (.of A)) E` express exactly membership in
  D_QCoh(O_Y). The integer bound is `(a : ℤ)`.
- The Koszul object in `hvan` is `DerivedCategory.Q.obj` of the termwise image under
  `tilde.functor (.of A)` of `(ExteriorAlgebra.koszulComplex A r f).extend
  ComplexShape.embeddingDownNat`. Thus it is the dependency's actual exterior-algebra
  complex, with chain degree q in cochain degree -q. The explicit zero-preservation
  structure uses `tilde.map_zero`, not a second sheafification construction.
- `hvan : ∀ n : ℤ, n ≤ a → Subsingleton (...⟦-n⟧ ⟶ E)` is precisely vanishing of
  Hom(C_f[-n], E) for every n ≤ a. In the preadditive derived category its Hom type
  has zero, so Subsingleton is equivalent to the Hom group being zero.
- The unit in the conclusion comes from
  `(Scheme.Modules.restrictAdjunction W.ι).ofNatIsoLeft
  (Scheme.Modules.overFunctorEquiv W).symm`, then
  `mapDerivedCategoryRightDerivedAdjunction`. This is a constructed adjunction:
  its left functor is `schemeOpenRestriction ... W` localized, and its right functor
  is definitionally `schemeDerivedDirectImage W.ι`. The latter is the right derived
  functor of `RingedSpace.moduleDirectImage W.ι.toLRSHom.toShHom` by the recorded
  dependency. The typed `@id` fixes the shared sheaf-module category instance rather
  than the different Category instance on the synonym `Scheme.Modules`.
- `IsIso ((DerivedCategory.TStructure.t.truncLE (a - 1)).map (...unit.app E))`
  asserts invertibility in the derived category of the canonical unit after standard
  cohomological truncation at exactly a-1. This specifies the canonical arrow itself,
  not merely the existence of some isomorphism between its endpoints.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty` (and its full-subcategory interpretation).
- `WeilConjectures.AlgebraicGeometry.KoszulComplex`: `ExteriorAlgebra.koszulComplex`,
  its contraction differential `koszulBoundary` and chain-indexing convention.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `schemeDerivedDirectImage`; its expansion through `RingedSpace.derivedModuleDirectImage`
  was read in `RingedSpaceDerivedDirectImage`.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: `DerivedCategory.TStructure.t`;
  `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT`: `TStructure.truncLE`.
- `WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps`:
  `schemeOpenRestriction` and its public exactness/additivity instances. Added the
  already-landed node `def-pc-derived-open-restriction-maps` to stmt_deps to cite this
  existing canonical restriction interface. Its full declaration and docstrings were read.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `Scheme.Modules.restrictAdjunction` and
  `Scheme.Modules.overFunctorEquiv`. The derivation of an exact adjunction uses
  `CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction` from
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `tilde.functor`, `tilde.map_zero`;
  `Mathlib.Algebra.Homology.Embedding.CochainComplex`: `ComplexShape.embeddingDownNat`.

Every already-stated proof dependency's recorded module is imported privately, except
those also serving the statement, which are public imports. The natural-language proof
follows all seven steps: quasi-compact union and supported cone; shifted Hom exactness;
power induction; augmentation factorization; affine cohomology comparison; the long
exact cohomology sequence; and inversion of a quasi-isomorphism roof.

Edge cases checked mathematically before writing:

- r=0: the supremum is the empty open and the empty Koszul complex is A in degree zero.
  The unit goes to zero; the hypothesis kills H^n(E) for n≤a by affine QCoh comparison,
  so its truncation at a-1 is indeed invertible. No inhabitant of Fin r is used.
- A=0: its spectrum and open are empty; module sheaves and derived objects vanish.
- A unit among the f_i: W=Y and the Koszul complex is contractible; the localization
  unit is invertible in every degree, hence so is its indicated truncation.
- All f_i=0: W is empty; the Koszul complex has zero differential with O_Y as its
  degree-zero summand, so the hypothesis implies the required low cohomology vanishing.
- Arbitrarily negative a and unbounded E remain included; no cohomological bound was added.
- A=Z, f=2, E=O, a=0: Hom vanishes in degrees ≤0, but Z→Z[1/2] is not invertible in
  degree zero. The already-reviewed a-1 endpoint passes this test. The uncorrected
  printed 0GEK endpoint does not. This delivery does not reopen or modify that split.

Searches actually run using `batch2/msearch.py` (full log: sandbox searches.jsonl):

- LeanFinder, “Vanishing Hom from a Koszul complex below a implies that the canonical
  open localization unit is an isomorphism after truncation below a”: 8 results about
  truncations of complexes; no Koszul/open-localization theorem.
- LeanFinder, “Vanishing Hom from a Koszul complex in degrees at most a gives an
  isomorphism of the truncated derived open localization unit in degrees at most a
  minus one”: 8 results, including `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`;
  none is this assertion.
- Loogle, `koszulComplex, DerivedCategory`: 0 hits, unknown identifier koszulComplex.
- Grep, `[Kk]oszul.*(localiz|trunc)|[Tt]runc.*[Kk]oszul`: 0 Mathlib hits.
- LeanSearch, “Vanishing of Hom from a finite Koszul complex implies low degree
  isomorphism of the derived open restriction unit”: 8 generic homology/Hom-complex
  results, no match.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf` found the upstream
  `koszul_open_orthogonality`, which assumes vanishing for ALL shifts and proves the
  untruncated unit invertible. Its full signature/docstring was read: it is not this
  bounded-range statement. Other hits were Koszul restriction and Cech comparisons.
- Direct searches for the item id and `affine_koszul_low_localization` in both source
  trees and `dag/lean_names_upstream.json` found no declaration for this item.

Sources read: local Stacks perfect.tex, lemma-orthogonal-koszul-second-variant and
its preceding variant; all statement dependency declarations with docstrings; the
latest blueprint's direct-image stability unit. No new source error is asserted beyond
the reviewed numerical endpoint issue already documented on the node.

## Second reading by NF

This is an in-thread final consistency check; no second agent was started, as instructed.
The maintainer's independent delivery review remains the independent reading.
Re-read the node and final signature: A/r/f, the defining equality for W, the Zariski
carrier, arbitrary QCoh E, integer a, source shift -n with n≤a, canonical derived unit,
and truncation at a-1 all match clause for clause. The node text remains unchanged.
The first compiler run exposed inference of the distinct `Scheme.Modules` category
instance. The final signature fixes the adjunction's type to the shared
`SheafOfModules` carrier with typed `@id`; this changes no mathematical object.
The delivered signature has no auto-bound variables, local notation/instances,
helper choices, or additional mathematical assumptions. All definitions are reused;
the only new declaration is the named theorem with its proof postponed as required.

Validation: scompile.py compiled the module in sandbox and library modes without
errors or warnings. The prescribed deliver2.py --no-push passed server preflight and compilation
(OK dry run, commit d9313897b3b). The final push uses the same module and node packet.
