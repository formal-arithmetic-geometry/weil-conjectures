## Worker report

The module states that a finite augmented resolution by acyclic objects computes every
right derived functor of a left exact additive functor. Its proof is `sorry`.

Statement correspondence:

- The abelian categories are `{C : Type u₁} [Category.{v₁} C] [Abelian C]` and
  `{D : Type u₂} [Category.{v₂} D] [Abelian D]`.
- Enough injectives in the source category is `[HasInjectiveResolutions C]`.
- The functor `v` is `(F : C ⥤ D)`, additive by `[F.Additive]` and left exact by
  `[Limits.PreservesFiniteLimits F]`, the Mathlib formulation for an additive functor
  between abelian categories that preserves kernels.
- The object `M` is `(M : C)`, and the finite upper degree is `(n : ℕ)`.
- The terms and differentials of `C⁰ → ⋯ → Cⁿ` are `(I : CochainComplex C ℕ)`;
  `(hfinite : ∀ i : ℕ, n < i → Limits.IsZero (I.X i))` makes its tail zero.
- The exact augmentation `0 → M → I⁰ → ⋯ → Iⁿ → 0` is the map
  `(ι : (CochainComplex.single₀ C).obj M ⟶ I) [QuasiIso ι]`. This requires
  cohomology to be `M` in degree zero and zero in positive degrees.
- Every displayed term is `F`-acyclic by
  `(hacyclic : ∀ i : ℕ, i ≤ n → F.rightAcyclic (I.X i))`. The imported
  `F.rightAcyclic` means `IsZero ((F.rightDerived (q + 1)).obj A)` for all `q : ℕ`.
- Every cohomological degree is `(q : ℕ)`; the conclusion is
  `Nonempty (((F.mapHomologicalComplex _).obj I).homology q ≅
  (F.rightDerived q).obj M)`. The existing `rightDerivedObjIsoOfResolution`
  supplies the comparison isomorphism after padding; the theorem records
  its existence in the orientation used by the node.

Dependency declarations read: `CategoryTheory.Abelian` in
`Mathlib.CategoryTheory.Abelian.Basic`; `CategoryTheory.Functor.Additive` in
`Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`,
`CategoryTheory.Limits.PreservesFiniteLimits` in
`Mathlib.CategoryTheory.Limits.Preserves.Finite`, and
`CategoryTheory.Functor.rightDerived` in `Mathlib.CategoryTheory.Abelian.RightDerived`;
`CategoryTheory.InjectiveResolution` in
`Mathlib.CategoryTheory.Preadditive.Injective.Resolution`. The theorem uses
`CategoryTheory.Functor.rightAcyclic` and the general comparison isomorphism
`CategoryTheory.Functor.rightDerivedObjIsoOfResolution`, both in
`WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`.

Edge cases: `n = 0` is admitted; `q = 0` and all `q > n` are admitted; zero
terms and zero objects satisfy the finite tail and acyclicity hypotheses.
The categories may be empty where Mathlib's abelian structure permits it.
Universes for objects and morphisms are explicitly independent.

Searches for an existing statement:

- `msearch leanfinder "finite exact resolution by F-acyclic objects computes right
  derived functor cohomology"`: the general `Functor.rightDerived` and
  `InjectiveResolution.isoRightDerivedObj`, no finite-resolution statement.
- `msearch loogle "Functor.rightDerived, HomologicalComplex.homology"`:
  zero hits (unknown identifier reported by the service).
- `msearch grep "acyclic.*resolution|resolution.*acyclic|rightDerived.*homology"
  CategoryTheory`: hits in `RightDerived.lean`, none for the finite criterion.
- `rg` in `WeilConjectures`: found the general acyclic-resolution criterion in
  `CategoryTheory/Abelian/RightDerived/Acyclic.lean`, but no finite specialization.
- `grep -rn "lem-pc-derived-acyclic-resolution"` in `WeilConjectures`:
  no hits.
- `rg` in the project's `lean/Sheaf`: no matching declaration.
- Stacks Tag 05TA read at https://stacks.math.columbia.edu/tag/05TA; the
  local `literature/stacks-project/derived-categories.tex` is absent here.

Server compile: clean, exit code 0.

## Second reading by E1

I read the node and the Lean declaration independently, item by item.

Node objects and hypotheses, with their Lean rendering and verdict:

- The source and target abelian categories are `C : Type u₁` and `D : Type u₂`,
  with independent category universes and `[Category] [Abelian]` instances. Lean
  has exactly these binders; no universe restriction or extra structure is added.
- Enough injectives is assumed only for the source, `[HasInjectiveResolutions C]`,
  matching the source proposition and the dependency declaration.
- The functor is `F : C ⥤ D`, with `[F.Additive]` and
  `[Limits.PreservesFiniteLimits F]`. This is the project's Mathlib encoding of
  additive left exactness; no stronger exactness or finiteness assumption occurs.
- The object and finite bound are `(M : C)` and `(n : ℕ)`, exactly as in the
  node, so `n = 0` is included.
- The augmented complex is `I : CochainComplex C ℕ` and
  `ι : (CochainComplex.single₀ C).obj M ⟶ I` with `[QuasiIso ι]`. This is the
  exact augmentation `0 → M → C⁰ → ⋯ → Cⁿ → 0`, expressed by the standard
  single-degree-zero complex and quasi-isomorphism; no exactness clause is
  omitted or strengthened.
- Finiteness of the displayed resolution is rendered by
  `hfinite : ∀ i, n < i → Limits.IsZero (I.X i)`. It permits all terms after
  `n` to be zero and does not constrain terms through `n`.
- Acyclicity of each displayed term is exactly
  `hacyclic : ∀ i, i ≤ n → F.rightAcyclic (I.X i)`. The imported notion is
  vanishing of every positive right-derived object, so the quantifier and
  degree convention agree with the node.
- For every `q : ℕ`, the conclusion is
  `Nonempty (((F.mapHomologicalComplex _).obj I).homology q ≅
  (F.rightDerived q).obj M)`, i.e. the finite complex's cohomology is
  isomorphic to the right derived functor in every degree, in the node's stated
  orientation. The existing comparison declaration exposes the canonical
  comparison as a witness of this isomorphism; `Nonempty` is the established
  project encoding used by that declaration.

Edge cases checked: `n = 0`, `q = 0`, `q > n`, zero terms and `M = 0`, and an
empty/degenerate abelian category are all admitted by the binders. The `ℕ`
index has no negative-degree exclusion beyond the source's bounded-below
convention, and the four universe parameters remain independent.

Searches were repeated with LeanFinder/Loogle-style queries for finite acyclic
resolutions and with `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf`.
Only the general `Functor.rightDerivedObjIsoOfResolution` and its
`nonempty_rightDerivedObjIso_homology_of_acyclic` wrapper were found; no finite
specialization exists. The dependency declarations were opened and match the
objects used here. The Stacks source place is Proposition 13.16.8, Tag 05TA.

No mismatch was found and no Lean change was needed. In particular, the finite
tail hypothesis, exact augmentation, acyclicity bound, quantifier order, and
comparison-isomorphism orientation all agree with the node. The worker module
compiled cleanly with `scompile.py` (no errors or warnings).
