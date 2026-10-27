## Worker report

Delivered `Sheaf.AlgebraicGeometry.PseudoCoherentTensorRelativeCriterion`, with the single
statement `AlgebraicGeometry.isPseudoCoherentRelativeTo_of_pseudoCoherent_tensor_tests`.
Its proof is exactly `by sorry`; no definition or additional theorem is introduced.
The statement was read against Stacks more-morphisms.tex, lines 20488–20495,
Tag 0CSL, `lemma-characterize-pseudo-coherent`; its proof was read through line 20546.
No statement correction or statement dispute is needed.

Clause-by-clause correspondence:

- A commutative ring: `(A : CommRingCat.{u})`. Bundling includes the zero ring.
- X a scheme over Spec A: `(X : Scheme.{u}) (f : X ⟶ Spec A)`.
- Separated: `[IsSeparated f]`, the Mathlib closed-diagonal predicate.
- Finite presentation: `[LocallyOfFinitePresentation f] [QuasiCompact f]
  [QuasiSeparated f]`, exactly the three-part convention in
  def-pc-morphism-conventions. The last factor also follows from separatedness;
  recording the convention does not impose another mathematical condition.
- K in D_QCoh(O_X): `(K : schemeDerivedCategory X)` and
  `(hK : schemeDerivedQCohProperty X K)`; the latter quantifies over every integer
  cohomology sheaf, requiring Mathlib `SheafOfModules.IsQuasicoherent`.
- Every pseudo-coherent E in D(O_X): `∀ E : schemeDerivedCategory X,
  Scheme.IsPseudoCoherent X E → ...`. E is not restricted to perfect or bounded
  complexes beyond what pseudo-coherence itself means. This uses the recorded
  scheme-local bounded-above finite-free definition.
- E tensor^L K: `E ⊗ K`, using the shared global `schemeDerivedTensorMonoidal`
  K-flat derived monoidal instance, with the order stated in the node.
- RΓ(X,-) in D(A): `(schemeDerivedGlobalSections X ⋙
  (affineGlobalSectionsRestriction f).mapDerivedCategory).obj (E ⊗ K)`.
  The first functor is the existing unbounded right derived Γ(X,-), valued in
  modules over Γ(X,O_X). The second is exact restriction along the canonical map
  A → Γ(X,O_X), namely `((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom`.
  This is verbatim the body of the existing `affineDerivedGlobalSections f`,
  expanded only to allow independent localization universes wΓ and wA. The
  existing `affineGlobalSectionsDerivedIso` verifies that this composite derives
  the underived sections functor with A-action. No arbitrary scalar action is used.
- Pseudo-coherent in D(A): `DerivedCategory.IsPseudoCoherent` of that object,
  requiring a bounded-above finite-free A-module complex representative.
- Conclusion: `Scheme.IsPseudoCoherentRelativeTo f K`, the recorded predicate
  quantifying over every integer m and allowing its affine covers and closed
  affine-space embeddings to depend on m. It is relative, rather than absolute,
  pseudo-coherence.
- No flatness, properness, Noetherianity, nonempty-source or boundedness
  hypothesis occurs. Universes u, w, wΓ, wA and all variables are explicitly
  bound; `set_option autoImplicit false` checks this.

The ambient family `[∀ Y : Scheme.{u}, HasDerivedCategory.{w}
(SheafOfModules.{u} (moduleRings Y.toRingedSpace))]` is exactly the size/localization
interface required by `Scheme.IsPseudoCoherentRelativeTo` on affine embeddings.
The over-open family for X supplies the recorded `Scheme.IsPseudoCoherent` test.
The two ModuleCat localization instances are infrastructure for the existing
sections functors. No equality of the ring-module localization universes is imposed.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Morphisms.Separated: `IsSeparated`.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation: `LocallyOfFinitePresentation`.
- Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact / QuasiSeparated: `QuasiCompact`,
  `QuasiSeparated` (available through the morphism imports).
- WeilConjectures.AlgebraicGeometry.DerivedCategory: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty` (their full definitions were read).
- WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage:
  `schemeDerivedDirectImage`, the recorded scheme specialization; imported publicly.
- WeilConjectures.AlgebraicGeometry.DerivedTensorStructure:
  `schemeDerivedTensorMonoidal`, with its global instance attribute.
- WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex:
  `Scheme.IsPseudoCoherent`, including its over-open localization family.
- WeilConjectures.RingTheory.RingPseudoCoherent: `DerivedCategory.IsPseudoCoherent`.
- Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex:
  `Scheme.IsPseudoCoherentRelativeTo` and `Scheme.IsMPseudoCoherentRelativeTo`.
- WeilConjectures.AlgebraicGeometry.GlobalDerivedHom: `schemeDerivedGlobalSections`.
- WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap:
  `affineGlobalSectionsRestriction`, `affineDerivedGlobalSections`, and
  `affineGlobalSectionsDerivedIso`. The recorded Sheaf module publicly reexports
  this upstream module; the upstream owning module is imported directly.

Added the already landed owning nodes `def-pc-global-derived-rhom` and
`def-pc-affine-global-hom-base-change-map` to stmt_deps as authorized by brief-stage2
§5. No new nodes or dependency repairs are required. All original node fields
apart from lean and this addition to stmt_deps are preserved.

The full six-step natural-language proof is in the theorem docstring. It retains
Chow neighbourhoods, geometry of both projections, quasi-coherence of F, the
pseudo-coherent G_d tests, the two projection formulas and finite-twist criterion,
and the flat-ambient argument followed by relative locality on X. The last step
uses F restricted to V (as corrected in the accepted proof), not the ill-typed
restriction to X × V appearing in the source display. Existing proof dependency
modules are imported with plain `import`. The recorded
Sheaf.AlgebraicGeometry.DerivedTensorPreservesQCoh is withdrawn; the actual adopted
WeilConjectures.AlgebraicGeometry.DerivedTensorPreservesQCoh is imported instead.
The six still-unstated sfb proof nodes have no module to import; they remain
named in the proof docstring and the unchanged proof_deps for later proof work.

Edge cases checked before writing:

- X empty: all relative neighbourhood requirements are vacuous; zero sections
  are pseudo-coherent. No point or nonempty-source witness is assumed.
- A the zero ring: Spec A is empty, so the statement still includes its unique
  possible source. No Nontrivial A binder is present.
- K zero and E zero: the tensor and derived sections are zero, compatible with
  both pseudo-coherent predicates and the relative conclusion.
- f the identity of Spec A: the tensor test includes E = O[0], so it detects
  pseudo-coherence of K over A; the relative conclusion is the expected one.
- Shifted, unbounded-below tests and K are allowed; no degree or uniform upper
  bound is introduced. The quantifier is over all pseudo-coherent tests.
- A non-Noetherian, f nonproper, or f nonflat is not excluded.

Searches actually run, using the prescribed msearch.py wrapper:

- LeanFinder: “A complex on a separated finitely presented scheme is relatively
  pseudo coherent if derived global sections of tensor products with all pseudo
  coherent complexes are pseudo coherent”: 8 hits, ordinary quasi-coherent
  presentation, Module sheaf abelian/category and limit declarations; no criterion.
- Loogle: `"IsPseudoCoherent"`: 0 hits.
- grep of Mathlib: `PseudoCoherent|pseudoCoherent|pseudo_coherent`: 0 hits.
- LeanSearch: “Relative pseudo coherence detected by derived global sections of
  tensor products with all pseudo coherent complexes”: 8 hits, ordinary
  SheafOfModules.IsQuasicoherent/presentation declarations; no criterion.
- Local rg over lean/WeilConjectures and lean/Sheaf for pseudo-coherent tensor /
  relative criterion patterns located the already landed sibling
  PerfectTestsDetectPseudoCoherence, which assumes flatness, tests perfect E,
  and concludes absolute pseudo-coherence. It is a different statement.
- `rg -n 'lem-sfb-pseudocoherent-tensor-relative-criterion'` in both source trees
  found only that sibling's proof docstring; no implementation of this item.
- `rg -n 'isPseudoCoherentRelativeTo_of_pseudoCoherent_tensor_tests'` in Mathlib,
  source, Sheaf, and dag/lean_names_upstream.json: no pre-existing declaration.
- Focused source search located `affineDerivedGlobalSections` and read its full
  definition, action map, and comparison; reused them instead of adding a notion.

Validation: scompile.py compiled the statement in module mode as sandbox and library
(2.3 s and 2.6 s), with no errors or unexpected warnings. The final module also
imports the adopted derived tensor quasi-coherence proof dependency. The prescribed
dry run and delivery perform the final fresh per-file compile and preflight.

## Second reading by NR

A final separate pass by this worker reopened the node and the complete module;
the dispatcher forbids starting another agent, and the maintainer supplies the
independent review after delivery. This pass checked A, X, f, all three finite
presentation factors and separatedness, hK, the unrestricted E quantifier,
the scheme pseudo-coherent premise, E ⊗ K in that order, the canonical A-action
on derived sections, ring pseudo-coherence, and the relative conclusion. Every
mathematical hypothesis and clause matches 0CSL and the node. No mathematical
mismatch or correction was found. The ring-localization universes remain independent.
The proof pass checked the local-to-global conclusion rather than claiming to
concatenate incompatible affine covers. The pass found the withdrawn proof-only
Sheaf tensor-quasi-coherence module; its actual adopted upstream module was added
to the plain imports. No definition or proof was added.
