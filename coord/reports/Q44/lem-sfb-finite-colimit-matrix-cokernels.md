## Worker report

Item: lem-sfb-finite-colimit-matrix-cokernels. Module:
`Sheaf.CategoryTheory.FiniteColimitMatrixCokernels`.

The real-data helper `CategoryTheory.Functor.finiteColimitBiproductIso` constructs
E_r using H.mapIso of biproduct.isoCoproduct, PreservesCoproduct.iso, the inverse
biproduct.isoCoproduct in D, and biproduct.mapIso of the copies of e. It uses no
postponed theorem or arbitrary isomorphism choice. The single postponed theorem is
`CategoryTheory.Functor.finiteColimit_matrix_cokernels`, whose proof is exactly
`sorry`; its docstring contains all eight natural-language proof steps.

Hypothesis and clause correspondence:

- The two abelian categories are `{B : Type u₁} [Category.{v₁} B] [Abelian B]`
  and `{D : Type u₂} [Category.{v₂} D] [Abelian D]`. Object and morphism universes
  are explicitly bound independently. The abelian structure supplies preadditivity,
  zero objects, kernels, cokernels and finite biproducts.
- H is `(H : B ⥤ D) [PreservesFiniteColimits H]`. Mathlib's finite-colimit class
  means preservation for finite small indexing categories, and its higher-universe
  instance (Preserves/Finite.lean:207) also gives every finite shape in any universe.
  No infinite-colimit or exactness hypothesis is used.
- The fixed objects and comparison are `(X : B) (Y : D) (e : H.obj X ≅ Y)`.
- X^r and Y^r are Mathlib's chosen `⨁ fun _ : Fin r ↦ X` and the corresponding
  expression for Y. These are genuine biproducts with Mathlib's injections,
  projections, Kronecker relations and identity decomposition. Empty biproducts
  give rank zero. `attribute [local instance] Abelian.hasFiniteBiproducts` only
  activates the existing Mathlib theorem supplying this consequence of Abelian;
  it creates no definition or instance data and no hypothesis in either signature.
  The elaborated public signatures contain the existing Mathlib construction.
- Preservation of all zero morphisms is the first conjunct,
  `H.PreservesZeroMorphisms`; this is a conclusion, not an assumption.
- E_r is the helper described above, constructed for every `r : ℕ`. The next
  two conjuncts quantify over every `r : ℕ` and `j : Fin r`, stating respectively
  `H.map (biproduct.ι _ j) ≫ E_r.hom = e.hom ≫ biproduct.ι _ j` and
  `E_r.hom ≫ biproduct.π _ j = H.map (biproduct.π _ j) ≫ e.hom`.
  Lean's `≫` orders compositions left to right, reversing the printed source's
  composition notation. At r = 0 both equation families are empty.
- Ranks are arbitrary `(m n : ℕ)`. The entries are
  `(p : Fin n → Fin m → (X ⟶ X))` and the corresponding q over Y, with precisely
  the node's target-row, source-column order. The hypothesis is
  `∀ i j, H.map (p i j) ≫ e.hom = e.hom ≫ q i j`.
- The maps determined by those entries use `biproduct.matrix (fun j i ↦ p i j)`
  and its q analogue. Mathlib's matrix convention is source-column first, which
  is why these indices are reversed. `biproduct.matrix_components` and
  `biproduct.components_matrix` show that these are exactly the unique maps with
  the required entries; no replacement notion of a matrix is introduced.
- The square is the first conjunct under the entrywise hypothesis:
  `H.map (biproduct.matrix ...) ≫ E_n.hom = E_m.hom ≫ biproduct.matrix ...`.
- A source cokernel projection is any
  `cp : CokernelCofork (biproduct.matrix ...)` together with `IsColimit cp`.
  Similarly cq and `IsColimit cq` describe any target cokernel projection.
  A CokernelCofork is a cofork of the map and zero; its condition is p ≫ cp.π = 0,
  and IsColimit supplies unique factorization. This quantification includes all
  choices of cokernel objects and projections, not just Mathlib's chosen cokernel.
- The isomorphism is `∃ u : H.obj cp.pt ≅ cq.pt`. Its forward equation is
  `H.map cp.π ≫ u.hom = E_n.hom ≫ cq.π`. Its inverse is u.inv, with equation
  `cq.π ≫ u.inv = E_n.inv ≫ H.map cp.π`.
- The final universally quantified clause says every other isomorphism u' with
  the forward equation alone equals u. Thus uniqueness is not conditioned on
  imposing the inverse equation as an extra premise.
- There are no faithfulness, exactness, nonzero-object or positive-rank assumptions.
  The finite biproduct identities and uniqueness of the maps with prescribed
  entries are provided by the existing Mathlib definitions, not extra premises.

Dependencies read and used:

- def-sp-abelian: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`, class signature/docstring at line 112;
  the existing theorem `CategoryTheory.Abelian.hasFiniteBiproducts` at line 275.
- def-weil-pbc-category-colimit: `CategoryTheory.Limits.colimit`,
  `Mathlib.CategoryTheory.Limits.HasLimits`, together with `Cocone` and `IsColimit`.
  Read the full Cocone and IsColimit signatures/docstrings in Limits/Cones.lean:133
  and Limits/IsLimit.lean:62, and the chosen-limit/dual-colimit declaration and
  docstring in HasLimits.lean:179. The statement uses IsColimit directly so that
  arbitrary specified cokernel cocones are covered.
- Proof dependency lem-sfb-preserving-colimits-additive is the Mathlib leaf
  `CategoryTheory.rightExactFunctor_le_additiveFunctor` in
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`, imported without `public`.
  Read its signature and surrounding binders at lines 316–334: binary biproducts
  and zero objects follow from the abelian hypotheses.
- Other existing Mathlib interfaces read in full: `PreservesFiniteColimits`,
  `PreservesCoproduct.iso`, `biproduct.isoCoproduct`, `biproduct.mapIso`,
  `biproduct.matrix`, `biproduct.matrixEquiv`, `CokernelCofork`,
  `CokernelCofork.ofπ`, and `Functor.PreservesZeroMorphisms`.

Edge cases checked before writing: r = 0 uses the empty coproduct comparison;
m = 0 gives the sole map from zero and a cokernel isomorphic to the target;
n = 0 gives the sole map to zero and zero cokernels; m = n = 0 combines these.
All equation families with indices in Fin 0 are empty and all zero-rank matrices
are still defined by Mathlib. Zero X, zero Y, and the zero functor satisfy the
same universal-property argument. Tensoring abelian groups by ℤ/2 is a finite-
colimit-preserving example that is not left exact, confirming that exactness
must not be assumed. None of these cases is excluded by the Lean statement.

Searches made for an existing statement or notion:

- msearch.py leanfinder: “Finite colimit preserving functor between abelian
  categories conjugates rectangular matrices under biproduct comparisons and
  induces a unique cokernel isomorphism”. Eight hits: Mat_.liftUnique,
  Mat_.additiveObjIsoBiproduct_naturality variants, Functor.mapMatComp,
  biproduct.map_matrix, Mat_.lift, Mat_.ι_additiveObjIsoBiproduct_inv. These concern
  additive-envelope functors or individual matrix identities, not this statement.
- msearch.py leansearch: “A finite colimit preserving functor of abelian categories
  preserves matrices on finite direct sums and their cokernels”. Eight hits include
  preservesFiniteColimits_of_preservesCokernels, PreservesFiniteColimits.casesOn,
  Abelian.isColimitMapCoconeOfCokernelCoforkOfπ, and right-exact-functor definitions
  and equivalences. None gives the complete comparison/entry/cokernel equations.
- msearch.py loogle: `CategoryTheory.Limits.PreservesCokernel.iso,
  CategoryTheory.Limits.mapBiproduct`: zero hits, unknown identifier for the latter
  (the actual mapBiproduct API is in the Functor namespace).
- msearch.py grep, CategoryTheory: `mapBiproduct|biproduct.matrix|
  PreservesCokernel|rightExactFunctor_le_additiveFunctor`. Twenty-five hits include
  the matrix identities, Mat_ functor comparisons and the additivity leaf. Their
  interfaces are reused; no full statement match.
- rg in lean/WeilConjectures and lean/Sheaf:
  `matrix.*[Cc]okernel|finiteColimit.*[Mm]atrix|
  lem-sfb-finite-colimit-matrix-cokernels|mapBiproduct`. Existing applications in
  ScalarMatrixInverseImage, FiniteConstantLocalModel and related modules use
  particular coefficient functors; none states the general arbitrary-H result.
  Also checked the literal item id in upstream sources: no corresponding declaration.
- rg for `finiteColimitBiproductIso|finiteColimit_matrix_cokernels` in Mathlib,
  lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no collision.

Read the source blueprint proof paragraph “Constructible complexes” in
literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-proper-base-change-unbounded/sk-prop-proper-base-change-unbounded-pullback.proof.md.
This node is its categorical finite-presentation argument, not the unit statement.
No missing notion or dependency-interface repair was necessary. No statement
correction and no STATEMENT-DISPUTED flag.

Validation: scompile.py Q44 lem-sfb-finite-colimit-matrix-cokernels compiled both
its sandbox form (3.5 s) and actual module name (1.7 s) with exit code 0 and no
errors or warnings. Every variable and universe is explicit; autoImplicit is false.

## Second reading by Q44

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
