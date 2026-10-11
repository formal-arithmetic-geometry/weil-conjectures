## Worker report

The new module `Sheaf.CategoryTheory.KInjectiveComputes` states
`CategoryTheory.Functor.kInjective_computes`, with `sorry` as its sole proof.
It is one theorem with six conjuncts spelling out the three numbered clauses of
`lem-sp-kinjective-computes`. No definition is duplicated, no dependency module
or new node is needed, and the node is changed only in its `lean` field.

Source inspected: the full blueprint lemma, including its proof and Status paragraph,
read over ssh from the server's literature/blueprint/master/blueprint/
sec-abelian-varieties/sk-prop-av-pqf-finite/lem-sp-kinjective-computes.md.
The local literature copy is absent. The node's four proof steps are all rendered
in the declaration docstring, naming the comparison principle, homotopy/cohomology,
enough-injectives, bounded-below injective, and shift dependencies. There is no
Cartan--Eilenberg dependency.

Hypotheses and conclusions, in order:

- The two categories are arbitrary `C : Type u₁`, `D : Type u₂`, with explicit
  `Category.{v₁}`, `Category.{v₂}`, `Abelian`, and `IsGrothendieckAbelian.{w₁}` /
  `IsGrothendieckAbelian.{w₂}` instances. The auxiliary smallness universes are
  independent; in particular taking w₁ = v₁ and w₂ = v₂ gives the ordinary notion.
- The functor v is `F : C ⥤ D`, with `[F.Additive]` and
  `[PreservesFiniteLimits F]`. In abelian categories this is exactly additive
  and kernel-preserving, by `Functor.preservesFiniteLimits_of_preservesKernels`.
- The complex K is quantified as `K : CochainComplex.Plus C`: its underlying
  integer-indexed complex is bounded below, with no fixed bound. Resolutions
  r and s are the recorded `CochainComplex.KInjectiveResolutionChoice K.obj`,
  so both their quasi-isomorphism and K-injectivity hypotheses are bundled.
- Clause (1), homotopy equivalence under K: the first conjunct gives maps u and v
  with `Nonempty (Homotopy (r.map ≫ u) s.map)` and its reverse, and homotopies
  `u ≫ v ~ 𝟙` and `v ≫ u ~ 𝟙`. Every other map satisfying the augmentation
  condition is homotopic to u (respectively v). Thus uniqueness means uniqueness
  of the homotopy class, not uniqueness of a homotopy witness.
- Clause (1), canonical isomorphism and well-defined RvK: the same conjunct
  supplies an isomorphism between the images under `Q`, the homotopy quotient,
  of the *recorded* `F.rightDerivedComplexWithResolution K r` and its s version.
  Its hom and inv are explicitly `Q.map (M.map u)` and `Q.map (M.map v)`,
  with M the termwise functor. The preceding uniqueness makes these independent
  of representatives. This is stronger evidence of canonicity than a bare
  `Nonempty` isomorphism with no prescribed maps.
- Clause (1), functoriality: the second conjunct applies to every family r of
  resolution choices. It gives a functor RF on bounded-below complexes and
  object identifications e with the bridge's values. For each morphism f it
  gives a lift u of `f.hom ≫ (r L).map`, unique up to homotopy, and the equality
  `RF.map f ≫ (e L).hom = (e K).hom ≫ Q.map (M.map u)`.
  RF's functor laws give identity and composition; the uniqueness in both
  conjuncts makes changing resolution choices compatible with these maps.
- Clause (2), bounded-below complexes of injectives: the third conjunct
  quantifies over any `I : CochainComplex.Plus C`, with
  `(∀ n : ℤ, Injective (I.obj.X n))`, and concludes `I.obj.IsKInjective`.
- Clause (2), an injective resolution resolves X[0]: the fourth conjunct uses
  the dependency's `I : InjectiveResolution X`. Extension along
  `ComplexShape.embeddingUpNat` places its ℕ-indexed complex in ℤ, with zero
  terms in negative degrees. It asserts that the extended augmentation is
  `QuasiIso` and the extended target is `CochainComplex.IsKInjective`.
  Its source is the zero-extension of `(CochainComplex.single₀ C).obj X`,
  precisely X placed in degree zero.
- Clause (2), agreement: the fifth conjunct bundles that same degree-zero
  complex as K₀ in Plus C. For every chosen K-injective resolution r and every
  `p : ℕ`, it asserts
  `Nonempty (F.rightDerivedCohomologyWithResolution K₀ r (p : ℤ) ≅
  (F.rightDerived p).obj X)`.
  Here p ranges over every index of the ordinary right derived functors,
  exactly as `def-sp-left-exact-additive` defines them for n ≥ 0. The
  complex-cohomology definition still accepts all integer indices.
- Clause (3): n ranges over all `ℤ`. The sixth conjunct says the shifted
  resolution exists, with complex `r.complex⟦n⟧` and augmentation HEq to the
  shifted r.map. HEq is needed because the target complex is carried as data
  in s and its equality to the shifted complex is another conjunct. For any
  chosen resolution of `K⟦n⟧`, the bridge value in the homotopy category is
  isomorphic to `(Q.obj (F.rightDerivedComplexWithResolution K r))⟦n⟧`.
  As clause (1) locates the canonical isomorphisms in the homotopy category,
  this is the meaning of clause (3)'s isomorphism for arbitrary choices;
  it does not assert that arbitrary homotopy equivalent complexes are
  isomorphic before quotienting.

Dependency declarations used and signatures/docstrings inspected:

- def-sp-kinjective-bridge: `Sheaf.CategoryTheory.KInjectiveBridge`,
  `CochainComplex.KInjectiveResolutionChoice`,
  `CategoryTheory.Functor.rightDerivedComplexWithResolution`, and
  `CategoryTheory.Functor.rightDerivedCohomologyWithResolution`.
  All are used directly. The Grothendieck resolution-choice declaration in
  that dependency was also read, but the theorem permits every choice.
- def-sp-left-exact-additive: Mathlib.CategoryTheory.Preadditive.AdditiveFunctor,
  `CategoryTheory.Functor.Additive`; Mathlib.CategoryTheory.Limits.Preserves.Finite,
  `CategoryTheory.Limits.PreservesFiniteLimits`; and
  Mathlib.CategoryTheory.Abelian.RightDerived, `CategoryTheory.Functor.rightDerived`.
  Also read `InjectiveResolution.isoRightDerivedObj`, including its direction
  and ℕ indexing, and the kernel/finite-limit equivalence recorded in the node.
- def-sp-grothendieck-abelian:
  Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic,
  `CategoryTheory.IsGrothendieckAbelian`, with its automatic colimits instance.
  The explicit EnoughInjectives import makes its enough-injectives instance
  available, hence rightDerived needs no additional hypothesis.
- def-sp-injective-resolutions: Mathlib.CategoryTheory.Preadditive.Injective.Resolution,
  `CategoryTheory.InjectiveResolution`, whose fields are cocomplex, degreewise
  injectivity, augmentation, and quasi-isomorphism. No specialized replacement.

Edge cases checked before writing: zero complex and zero object; p = 0 and positive
p; n = 0, positive and negative shifts; negative original lower bounds; arbitrary
unbounded K-injective targets of bounded-below K; and independently sized source
and target categories. No fixed lower bound, termwise injectivity of arbitrary
K-injective resolutions, or acyclicity of F is assumed. The natural-number
ordinary-derived index follows the dependency's stated domain. The shift result
correctly uses isomorphism in the homotopy category for arbitrary resolutions.
No statement dispute or correction is necessary.

Searches performed using /home/ubuntu/weil-launcher/msearch.py:

- LeanFinder: "K-injective resolutions compute right derived functors independent
  resolution homotopy equivalence commute shifts". Eight hits, all ordinary
  injective-resolution comparisons and naturality in RightDerived; none states
  this combined K-injective result or defines a replacement bridge.
- Loogle: "CochainComplex.IsKInjective, CategoryTheory.Functor.rightDerived".
  Service returned OK, zero hits.
- LeanSearch: "K injective resolutions right derived functor homotopy comparison".
  Service unavailable, Internal Server Error; no mathematical verdict from it.
- Mathlib grep via msearch: "rightDerived.*[Kk]Injective|[Kk]Injective.*rightDerived|
  isKInjective_of_injective", Algebra/Homology. Eight hits concern the existing
  bounded-below K-injectivity theorem and its applications; no combined match.
- rg of the same notions in the upstream WeilConjectures tree and lean/Sheaf:
  found the existing bridge, bounded-below existence, K-injectivity tools, and
  ordinary right-derived comparisons; none states this lemma.
- rg for the exact blueprint id in upstream WeilConjectures: no hit.
  `tools/lean_names_upstream.py show lem-sp-kinjective-computes` consulted both
  upstream name indexes. rg for the proposed full declaration's short name
  `kInjective_computes` in Mathlib, upstream, Sheaf, and the upstream-name index
  found no collision.

Validation: server scompile succeeded in 1.6 seconds, without errors or warnings,
after changing the extended-complex K-injectivity expression to the fully
qualified CochainComplex.IsKInjective. All universes and binders are explicit.

## Second reading by K1

I independently read the blueprint node and its source place (the full
`lem-sp-kinjective-computes.md`, node order 519) and matched each item with
`CategoryTheory.Functor.kInjective_computes` in
`lean/Sheaf/CategoryTheory/KInjectiveComputes.lean`.

- The source introduces a left exact additive functor between arbitrary
  Grothendieck abelian categories and a bounded-below cochain complex. Lean
  renders this as arbitrary `C : Type u₁`, `D : Type u₂` with independent
  category and Grothendieck universes, `[Abelian]`, `[IsGrothendieckAbelian]`,
  `(F : C ⥤ D)`, `[F.Additive]`, `[PreservesFiniteLimits F]`, and
  `K : CochainComplex.Plus C`. This has no extra geometric, finiteness,
  characteristic, or Noetherian hypothesis.
- Clause (1)'s two K-injective resolutions are exactly
  `CochainComplex.KInjectiveResolutionChoice K.obj`; its fields bundle the
  resolution maps, `QuasiIso`, and `CochainComplex.IsKInjective`. The first
  conjunct gives comparison maps in both directions, homotopies under `K`,
  homotopies to both identities, and uniqueness of each comparison map up to
  homotopy. The following existential gives the canonical quotient-category
  isomorphism, with hom and inverse explicitly `Q.map (M.map u)` and
  `Q.map (M.map v)`.
- The next conjunct renders functoriality: every family of resolution choices
  yields `RF`, object isomorphisms to the chosen quotient values, and for every
  `K L f` a lift unique up to homotopy satisfying the displayed naturality
  equation. Thus the source's functoriality and independence of choices are
  represented, rather than only asserted by a bare existence statement.
- Clause (2)'s bounded-below injective assertion is the third conjunct, with
  `I : CochainComplex.Plus C` and injectivity at every integer degree. The
  fourth conjunct takes `I : InjectiveResolution X`, extends its natural
  indexed complex and augmentation along `ComplexShape.embeddingUpNat`, and
  asserts both `QuasiIso` and the extended target's
  `CochainComplex.IsKInjective`. The fifth conjunct uses the corresponding
  degree-zero `K₀` and gives, for every choice `r` and every `p : ℕ`, the
  isomorphism between `rightDerivedCohomologyWithResolution K₀ r (p : ℤ)` and
  `(F.rightDerived p).obj X`. This is the ordinary right-derived indexing of
  the dependency declaration.
- Clause (3) is the sixth conjunct: `n : ℤ` is unrestricted, the shifted
  resolution exists with shifted complex and `HEq` of the augmentation, and
  every resolution of `K⟦n⟧` has the quotient-category isomorphism to the shift
  of the chosen result. Hence zero, positive, and negative shifts are included.

I checked edge cases explicitly: the zero object and zero complex, empty/zero
components, `p = 0`, arbitrary positive `p`, `n = 0`, positive and negative
`n`, complexes with any lower bound (including negative bounds), arbitrary
K-injective targets which are not termwise injective, and independently sized
universes. None is excluded by the binders. The source has no characteristic,
connectedness, or scheme assumptions, and Lean adds none.

The dependency declarations were opened and checked: `KInjectiveResolutionChoice`
and the two `rightDerived*WithResolution` definitions from
`Sheaf.CategoryTheory.KInjectiveBridge`, Mathlib's `Functor.rightDerived`,
`InjectiveResolution`, `IsGrothendieckAbelian`, and the finite-limit/left-exact
lemmas. The bridge is the project's general abelian-category notion; no
specialized module-sheaf notion was substituted. Searches used LeanFinder,
Loogle, LeanSearch (unavailable), Mathlib grep, upstream `WeilConjectures`
grep, project `lean/Sheaf` grep, and the upstream-name index. They found only
ordinary right-derived and K-injective comparison tools, not this combined
statement or a declaration named `kInjective_computes`.

No mismatch was found and no file or node statement was changed. The module
compiled remotely with `scompile.py` in 1.6 seconds, with no errors or warnings;
all variables and universes are explicit. The node copy's `lean.statement` is
verbatim the theorem signature.

## Reviewer fix (R-kic0945)

Clause (3) of the node asserts only $Rv(K[n])\cong(RvK)[n]$. The delivered sixth conjunct also asserted that the shifted resolution exists, with `s.complex = r.complex⟦n⟧` and an `HEq` of augmentations. That is a step of the proof, not part of the statement, so the reviewer removed it. The sixth conjunct is now the quotient-category isomorphism for every `K`, `r`, `n : ℤ` and resolution `s` of `K⟦n⟧`. Nothing else changed.
