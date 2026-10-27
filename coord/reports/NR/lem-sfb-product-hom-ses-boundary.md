## Worker report

The module `Sheaf.Algebra.Homology.ProductHomSesBoundary` states
`CochainComplex.HomComplex.productHom_ses_boundary`. Its proof is `sorry`.
The auxiliary definitions `precompMap` and `homologyToDerived` have actual data,
use existing Mathlib constructions, and contain no postponed proof. There are
no new independent notions, dependency repairs, or changes to the informal node.
Only the node's `lean` field changes.

Hypothesis and clause correspondence:

- A locally small abelian category in a fixed Hom universe is
  `{𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]`. The category-object, original
  Hom, and derived-Hom universes `u`, `v`, `w` are independent and explicit.
- Its unbounded cochain derived category and localization are Mathlib's
  `[HasDerivedCategory.{w} 𝒜]`, `DerivedCategory 𝒜`, and `DerivedCategory.Q`.
- The sequence `0 → A → B → C → 0` is
  `(S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)`, with
  `A = S.X₁`, `B = S.X₂`, `C = S.X₃`, `i = S.f`, and `p = S.g`.
  Short exactness in the category of complexes is degreewise short exactness.
- K-injectivity is `[I.IsKInjective]`: the full Mathlib signature says every
  chain map from an acyclic complex has a homotopy to zero. Termwise
  injectivity is `[∀ r : ℤ, Injective (I.X r)]`. Enough injectives and
  boundedness are not assumed.
- The product Hom complex is exactly `CochainComplex.HomComplex X I`.
  Its degree-n cochains are all families over `Triplet n`, whose fields
  are `p`, `q`, and `p + n = q`; thus this is the product over every integer
  `p` of `Hom(X.X p, I.X (p+n))`. There is no finite-support condition.
  Mathlib's `δ n (n+1)` is `d_I f + (-1)^(n+1) f d_X`, exactly the
  node's `d_I f - (-1)^n f d_X`.
- `precompMap a I` is a concrete chain map. Its degree-n function is
  `(Cochain.ofHom a).comp z (zero_add n)`, hence its component at `(r,s)`
  is `a.f r ≫ z.v r s hrs`. The structure laws are existing theorems
  `Cochain.comp_zero`, `Cochain.comp_add`, and `δ_ofHom_comp`, supplied
  directly as proof terms. The maps for the conclusion are consequently
  exactly `p* = precompMap S.g I` and `i* = precompMap S.f I`.
- The existential `w₀` proves their composite is zero, and the existential
  `hH` is short exactness of precisely `ShortComplex.mk p* i* w₀`.
  These existential witnesses are proofs, not arbitrary maps or choices
  of data, and impose no additional hypothesis.
- `homologyToDerived X I j` is the canonical map on actual homology:
  apply `homologyAddEquiv X I j`, then `CohomologyClass.toHom`, then
  `DerivedCategory.Qh.map`, and compose the natural comparison isomorphisms
  `quotientCompQhIso` and `Q.commShiftIso`. No arbitrary equivalence or
  choice is used. The first conjunct states this canonical map is bijective
  for every `X` and `j`, rendering the node's stated identification of
  product-Hom cohomology with derived morphisms.
- The input `[f]` is
  `(homologyAddEquiv S.X₁ I 0).symm (CohomologyClass.mk (Cocycle.ofHom f))`.
  The cohomology connecting morphism is `hH.δ 0 1 (by decide)`.
- Its convention is lift-differentiate: Mathlib's
  `ShortComplex.ShortExact.δ_apply` in
  `Mathlib.Algebra.Homology.ConcreteCategory` takes a lift `x₂` of `x₃`
  and a vector `x₁` such that `S.f x₁ = d x₂`, and returns `[x₁]`.
  This specializes here to `g` extending `f` and `hp = Dg`. This was
  checked in the source, not inferred just from the connecting-map name.
- `b` is `DerivedCategory.triangleOfSESδ hS`. Its definition is the
  inverse of `Q.map (mappingCone.descShortComplex S)`, followed by
  `Q.map (mappingCone.triangle S.f).mor₃` and the shift comparison.
  The cone triangle uses the negative projection as its third arrow,
  so this is precisely `-Q(pr_A) Q(q)⁻¹`. The assertion for every
  `f : S.X₁ ⟶ I` is the displayed equality with
  `-(DerivedCategory.triangleOfSESδ hS ≫ (DerivedCategory.Q.map f)⟦1⟧')`.
  Lean's composition order renders `-Q(f)[1] ∘ b` exactly.

Dependency declarations used (full source signatures and docstrings read):

- `def-sp-abelian`: `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`, its recorded Mathlib match.
- `def-weil-abstract-derived-category`: `HasDerivedCategory`, `DerivedCategory`,
  `DerivedCategory.Q`, `Qh`, and `quotientCompQhIso` in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic` (publicly imported through
  `DerivedCategory.ShortExact`). The same latter module supplies
  `DerivedCategory.triangleOfSESδ` with the precise negative-projection convention.
- `def-sp-injective-resolutions`: `CategoryTheory.Injective` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`; this node only needs
  its injective-object clause, not a choice of injective resolution.
- `CochainComplex.IsKInjective` and its shift instance from
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`.
- `CochainComplex.HomComplex`, `Cochain.comp`, `Cochain.ofHom`,
  and `δ_ofHom_comp` from
  `Mathlib.Algebra.Homology.HomotopyCategory.HomComplex`.
- `homologyAddEquiv` and `CohomologyClass.toHom` from
  `Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology`.
- `CategoryTheory.ShortComplex.ShortExact.δ` from
  `Mathlib.Algebra.Homology.HomologySequence`.
- Proof dependencies are imported without `public`:
  `CochainComplex.IsKInjective.Qh_map_bijective` from
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
  (`lem-weil-pbc-kinjective-hom-derived`) and
  `CochainComplex.mappingCone.quasiIso_descShortComplex` from
  `Mathlib.Algebra.Homology.HomotopyCategory.ShortExact`
  (`lem-pc-cone-short-exact-quasi-iso`). The K-injective shift dependency
  is already supplied by the public KInjective import.

Source checks: read `literature/stacks-project/more-algebra.tex`, section
`section-hom-complexes`, including `equation-cohomology-hom-complex` (Tag 0A5X),
and `derived.tex` at the cone construction immediately preceding
`lemma-derived-canonical-delta-functor` and that lemma (Tag 0152).
The node's agent-written extension and explicit homotopy were checked clause
by clause; the six proof steps are carried into the theorem docstring.

Searches performed:

- `msearch.py ... leanfinder`: query "Hom complex short exact sequence cohomology
  connecting morphism signed derived boundary" returned eight hits, including
  `ShortComplex.ShortExact.δ_apply`, `δ_apply'`, and group cohomology boundaries.
  These provide general connecting-map calculations, not this signed comparison.
- `msearch.py ... leansearch`: query "Short exact sequence of product Hom
  complexes into an injective complex connecting homomorphism signed composition
  derived category" returned eight hits, including `δ`, `δ_apply`, `δ_eq'`,
  `ShortExact.extClass_hom`, and `Exact.comp_descToInjective_assoc`.
  None states this unbounded product-Hom comparison.
- `msearch.py ... loogle` with
  `CochainComplex.HomComplex, CategoryTheory.ShortComplex.ShortExact`
  succeeded with zero hits.
- `msearch.py ... grep` with
  `HomComplex.*([Ss]hortExact|boundary)|[Pp]recomp.*HomComplex`
  in `Algebra/Homology` succeeded with zero hits.
- Direct `rg` of Mathlib's HomComplex family found `Cocycle.precomp` and
  composition/differential lemmas, but no public precomposition chain map.
  Direct source and `lean/Sheaf` searches for `HomComplex`, `productHom`,
  `product_hom`, and precomposition combinations found sheaf Hom constructions,
  localized comparisons, and the private `complexPrecomp` specialized to
  single complexes in `WeilConjectures.CategoryTheory.InjectiveResolutionCohomologyPresheafData`.
  That private, specialized map cannot provide the needed general map here.
- Direct `rg` of the source library for `lem-sfb-product-hom-ses-boundary`
  found no existing attachment. Searches for `homologyToDerived`,
  `productHom_ses_boundary`, and the full target namespace in Mathlib,
  `WeilConjectures`, `lean/Sheaf`, and the upstream declaration index found
  no collision. An unrelated `precompMap` lies in a different namespace
  in `FilteredComplexDecalageTower`.

Edge cases checked mathematically: zero complex/zero category give zero groups
and zero boundaries; all integer degrees, including negative and zero, are
allowed. The index product is never a coproduct. Termwise splitting is absent:
for example an injective resolution of a nonsplit sequence can still be used.
The original category has no arbitrary-product or enough-injectives assumption.
Independent Hom and derived-localization universes are retained. The sign check
uses `d_{I[1]} = -d_I`, giving `dH + Hd = (-hp,f)` on the two cone summands.

The earlier worker's unchanged-item failure concerned the stage-1 split.
The current node has no Lean record and is queued at stage 2. The maintenance
handoff of 2026-10-22 in `coord/brief-stage2.md` explicitly authorizes this
Lean attachment while preserving the accepted split. No reopening is required.

## Second reading by NR

This is the author's second pass, not an independent review; the dispatcher
forbids starting another agent and the maintainer independently reviews delivery.
Reopened the node and the module and matched every hypothesis and clause above.
Checked the exact source signatures of the homotopy-to-derived comparison,
the SES connecting map, and its lift-differentiate formula. The two auxiliary
definitions use actual maps, and all existential witnesses in the main theorem
are proofs of zero composition/short exactness. There is no choice of unspecified
data. The short-exactness assumption on `S` does not assert a splitting.
The outer minus and the negative cone projection occur in separate places,
as the node requires. No mismatch in the informal statement was found.
The initial compiler warning was an unused binder name in `precompMap.comm'`;
that binder is now anonymous. Only the main theorem is postponed.
