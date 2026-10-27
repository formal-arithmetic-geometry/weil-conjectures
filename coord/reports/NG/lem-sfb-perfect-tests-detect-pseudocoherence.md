## Worker report

The module `Sheaf.AlgebraicGeometry.PerfectTestsDetectPseudoCoherence` states
`AlgebraicGeometry.isPseudoCoherent_of_perfect_tensor_tests`, with proof `sorry`.
No new definitions or other postponed theorems are introduced.

Clause-by-clause correspondence:

- A commutative ring R is `R : CommRingCat.{u}`; X and the specified structure map
  are `X : Scheme.{u}` and `p : X ⟶ Spec R`.
- Separatedness is `[IsSeparated p]`; flatness is `[Flat p]`.
- Finite presentation is `[LocallyOfFinitePresentation p] [QuasiCompact p]
  [QuasiSeparated p]`, exactly the convention of def-pc-morphism-conventions.
- `K : schemeDerivedCategory X` with `hK : schemeDerivedQCohProperty X K` renders
  K in D_QCoh(O_X), without assuming K bounded or perfect.
- `∀ E : schemeDerivedCategory X, Scheme.IsPerfect X E → ...` quantifies over
  every perfect object of the full derived category.
- `E ⊗ K` uses the global K-flat-derived `schemeDerivedTensorMonoidal` instance.
- `schemeDerivedGlobalSections X` is the recorded unbounded module-valued RΓ.
  Its composite with `(affineGlobalSectionsRestriction p).mapDerivedCategory`
  retains the R-action induced by `((Scheme.ΓSpecIso R).inv ≫ p.appTop).hom`.
  This is exactly the body of the existing `affineDerivedGlobalSections p`;
  spelling out the composite avoids its inherited universal localization binders
  and permits independent wX, wΓ and wR. It introduces no new functor or comparison.
- `DerivedCategory.IsPseudoCoherent` on that composite's value is the stated
  pseudo-coherence of derived sections as an R-module complex.
- `Scheme.IsPseudoCoherent X K` is exactly the absolute conclusion on X.
- No Noetherian, properness, cohomological boundedness or uniform test-bound
  hypothesis occurs. The HasDerivedCategory binders specify localizations for X,
  its open sites, its global section ring and R; all variables are explicit and
  `autoImplicit` is false.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: `AlgebraicGeometry.Flat`, whose docstring
  and `Flat.iff_flat_stalkMap` identify the stalkwise definition.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation: `LocallyOfFinitePresentation`;
  Morphisms.QuasiCompact and Morphisms.QuasiSeparated: `QuasiCompact`, `QuasiSeparated`;
  Morphisms.Separated: `IsSeparated`. The morphism convention node names these.
- WeilConjectures.AlgebraicGeometry.DerivedCategory: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`.
- WeilConjectures.AlgebraicGeometry.PerfectComplex: `Scheme.IsPerfect`.
- WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex: `Scheme.IsPseudoCoherent`.
- WeilConjectures.AlgebraicGeometry.DerivedTensorStructure:
  `schemeDerivedTensorMonoidal`.
- WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage:
  `schemeDerivedDirectImage` (imported as the node's direct-image dependency).
- WeilConjectures.RingTheory.RingPseudoCoherent: `DerivedCategory.IsPseudoCoherent`.
- WeilConjectures.AlgebraicGeometry.GlobalDerivedHom: `schemeDerivedGlobalSections`.
- WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap:
  `affineGlobalSectionsRestriction`, and the read definition `affineDerivedGlobalSections`.
  Added their two already landed owning nodes to stmt_deps, as allowed by brief §5.
  The affine module is imported directly from upstream: the recorded Sheaf module
  is now a compatibility public import of this exact module.

The four non-Mathlib proof prerequisites are not yet stated; they are recorded in
proof_deps and reproduced step by step in the theorem docstring, rather than fabricated.
The Mathlib proof leaves are available through the morphism imports. Read Stacks
more-morphisms.tex, `lemma-characterize-pseudo-coh-improved` (0GES), and
`lemma-check-relative-pseudo-coherence-on-charts` (09UU). The first gives relative
pseudo-coherence and the second, with identity immersion and flat ambient p,
gives the absolute conclusion. The accepted split and statement are preserved.

Edge cases checked: empty X (the local conclusion is vacuous); zero ring and its
empty spectrum (nothing excludes them); p the affine identity (testing the tensor
unit recovers pseudo-coherence of K); arbitrary non-Noetherian R; nonproper flat
finitely presented X; shifted perfect E with bounds depending on E. No independent
test universe can make the perfect-test quantifier vacuous: E and K share D(O_X).
The three localization morphism universes are independent.

Searches made:

- msearch.py leanfinder: "Perfect tensor tests detect pseudo coherence on a flat
  separated finitely presented scheme over any commutative ring": 8 hits, flatness
  and universally-open results, no matching criterion.
- msearch.py leansearch: the same query: 8 hits, flat module criteria, no match.
- msearch.py loogle: `"IsPseudoCoherent"`: 0 hits.
- msearch.py grep: `pseudoCoherent|PseudoCoherent|pseudo_coherent`: 0 Mathlib hits.
- rg in lean/WeilConjectures and lean/Sheaf for perfect tensor tests, pseudo-coherence
  and derived global sections found the existing predicates and scalar-section
  construction above, but no matching theorem. The upstream blueprint-id search
  for this item had no hits. The CompactObject example is now withdrawn; current
  upstream statement modules supplied the module/public-import/expose format.

Both the sandbox and library-name server checks passed for the delivered file,
with no errors or unexpected warnings. The module-mode type probe also confirmed
that affineDerivedGlobalSections inherits universal localization instances, which
is why its explicit existing composite is used in the statement.

## Second reading by NG

Reread the node and the final Lean declaration after compilation, matching each
binder and conclusion against the correspondence above. The final statement
retains separatedness, flatness, all three finite-presentation components,
quasi-coherence of K, every perfect E and pseudo-coherent R-valued sections. In
particular it concludes pseudo-coherence on X, rather than merely relative
pseudo-coherence or pseudo-coherence over Γ(X,O_X). No mathematical mismatch was
found. The only adjustment during drafting was expanding the existing affine
section composite to avoid unnecessary universal localization instances. This is
a worker self-check; the maintainer's independent review is still required, as
specified by the dispatcher brief. No other agent was started.
