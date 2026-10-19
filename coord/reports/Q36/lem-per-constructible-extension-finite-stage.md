## Worker report

The new module `Sheaf.DeligneLaumon.ConstructibleExtensionFiniteStage` states
`AlgebraicGeometry.Etale.exists_constructible_extension_finite_stage` with one `sorry`.
No definition, helper theorem, dependency record or mathematical statement is changed.
Only the item's `lean` field is added. Its signature is copied verbatim from the file.

Source checked directly: ILO, Travaux de Gabber, Expose XVII, printed page 306,
PDF page 312, proof of Lemma 7.4.4 (using `pdftotext -f 312 -l 312 -layout`).
The source asserts a short exact upper row and a commutative comparison to the given
row, with unchanged quotient and cocartesian left square. The present node isolates
that global extension-class assertion for a directed union. It does not assert
continuity of internal sheaf Ext. The module docstring carries all eight steps of
the node's replacement proof, including the monicity argument and the final
universal-property verification.

Hypotheses and conclusions, clause by clause:

- A scheme with a finite affine Noetherian cover is `(X : Scheme.{u}) [IsNoetherian X]`.
  Mathlib's `isNoetherian_iff_of_finite_affine_openCover` identifies this with the
  node's formulation. No separatedness or invertibility hypothesis is added.
- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The coefficient ring is
  `(R : Type (u + 1)) [CommRing R] [IsNoetherianRing R] [Algebra (ZMod ℓ) R]`.
  For prime ℓ, `ZMod ℓ` is the prime field. There is no finite-underlying-set,
  field, nontriviality or finite-type-algebra assumption on R.
- The category is `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)`.
  This is the existing constant-coefficient module-valued encoding used by both
  the constructibility dependency and the lifting proof dependency.
  `Scheme.etaleConstantModuleFunctor_isEquivalence` identifies it with modules over
  `(constantSheaf X.smallEtaleTopology RingCat).obj (RingCat.of R)`; the functor and
  its inverse retain the underlying abelian sheaf and linear maps. Thus this changes
  presentation, not the category of mathematical objects.
- The given sequence is `(S : ShortComplex ...) (hS : S.ShortExact)`, with
  `H = S.X₁`, `F = S.X₂`, `G = S.X₃`, injection `S.f` and projection `S.g`.
  `ShortComplex` includes the zero composite and `ShortExact` includes exactness,
  monicity of the first arrow and epicity of the second, encoding both zero endpoints.
- Constructibility is `[Scheme.IsConstructibleSheaf S.X₃]`. This existing declaration
  is explicitly exposed by the recorded dependency
  `def-weil-pbc-locally-constant-finite-type-modules` and imported publicly from
  `WeilConjectures.ConstructibleSheaf.Defs`. It means a finite stratification whose
  pullbacks by `Etale.upperStar` are finite locally constant. For ModuleCat, finite
  means finitely generated geometric stalks, not finite underlying sets. Its strata
  are constructible locally closed; the additional word constructible imposes no
  condition on Noetherian X, as `Stratification.ofNoetherianSpace` and
  `IsConstructibleSheaf.of_noetherianSpace` explain. This uses the dependency's
  recorded interface rather than a duplicate constructibility definition.
- The index is `(I : Type (u + 1)) [PartialOrder I] [Nonempty I] [IsDirectedOrder I]`.
  This is a small nonempty directed partially ordered set in the coefficient/site
  bound. The small etale site's object universe is u+1 and its Hom universe is u;
  they are not identified. No independent smaller index universe is used.
- The increasing family is `D : I ⥤ ...` with
  `ι : D ⟶ (Functor.const I).obj S.X₁` and `[∀ a : I, Mono (ι.app a)]`.
  The stage H_a is `D.obj a`, included into H by `ι.app a`. A monomorphism into H
  is a representative of a subobject of H. Naturality says
  `D.map (homOfLE hab) ≫ ι.app b = ι.app a`, exactly compatibility with inclusion
  when a ≤ b. Consequently transition maps are the unique inclusions of these
  subobjects; they are not arbitrary structure maps.
- The union/colimit condition is `hι : IsColimit (Cocone.mk S.X₁ ι)`.
  This asserts that H, with the actual inclusion maps, is a colimit. It is the
  under-inclusions isomorphism in the node, with no chosen colimit or isomorphism
  auxiliary to the statement.
- `∃ (a : I) (Fₐ : ...) (iₐ : D.obj a ⟶ Fₐ) (pₐ : Fₐ ⟶ S.X₃)
  (hz : iₐ ≫ pₐ = 0)` supplies the stage, middle object, arrows and complex relation.
  `(ShortComplex.mk iₐ pₐ hz).ShortExact` gives exactly the upper short exact row.
- `∃ φ : ShortComplex.mk iₐ pₐ hz ⟶ S` gives a morphism of the two sequences,
  including both commuting squares. `φ.τ₁ = ι.app a` fixes its left end to the
  actual inclusion, and `φ.τ₃ = 𝟙 S.X₃` fixes its right end to the identity.
- `Mono φ.τ₂` is the asserted monomorphism of middle terms.
- `IsPushout iₐ (ι.app a) φ.τ₂ S.f` is precisely the square with corners
  H_a, F_a, H, F. Its order follows Mathlib's definition: the two first arguments
  start at H_a, and the last two finish at F. It includes commutativity and the
  universal property for every target module sheaf: compatible maps out of F_a
  and H extend uniquely to F. This is not a chosen or unrelated pushout.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`; the category
  `Scheme.Etale` is in `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, a
  transparent alias for Mathlib `SheafOfModules`; the constant-coefficient encoding
  above uses its existing equivalence, with no copied category.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification` and its topological parent.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`, used
  inside the existing constructibility predicate.
- `Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules`:
  `SheafOfModules.IsLocallyConstantFiniteTypeModules` and its recorded etale module
  interface `Scheme.IsFiniteLocallyConstantSheaf` / `Scheme.IsConstructibleSheaf`.
  The generic equal-universe ringed-site definition is not misapplied to X.Etale.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, the finite-module notion
  underlying the existing ModuleCat finite-stalk predicate.
- `Mathlib.CategoryTheory.Limits.HasLimits` and its cone interfaces:
  `CategoryTheory.Limits.Cocone`, `IsColimit`, expressing the colimit condition.
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact` (the short-exact declaration
  recorded under `Mathlib.Algebra.Homology.ExactSequence`): `ShortComplex`,
  `ShortComplex.ShortExact` and its morphisms.
- `def-weil-size-convention` is a metatheoretic convention; explicit `universe u`,
  the site universes and the u+1 bounds implement it. There is no missing declaration.

The public constant-module equivalence is
`WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`,
`Scheme.etaleConstantModuleFunctor_isEquivalence`. Its current full source was
read using `scompile.py --source` because it is absent in the older checkout.
It occurs as justification of the coefficient encoding, not as a new hypothesis.
All eight proof dependencies are available through imports, including the
Mathlib short five lemma in the short-exact module. In particular the finite affine
lifting, Noetherian subobject, localized module adjunction, etale sum extension,
qcqs section-colimit and pushout-short-exact modules are imported for stage 3.
The current upstream subobject module was also read using `scompile.py --source`.

Edge cases checked before writing:

- Empty X is admitted. All sheaves then vanish; no nonempty-X hypothesis is imposed.
- G=0 is admitted: take any stage, F_a=H_a, the identity injection and zero quotient;
  the lower sequence identifies F with H. No constructibility is asked of H or F.
- H=0 and all stages zero are admitted; F_a can be the given F, with quotient G.
- A singleton directed set is admitted, and its inclusion into H is a colimit
  isomorphism, giving the original extension up to that isomorphism.
- No least stage is required. When the auxiliary finite sum in the proof is empty,
  `[Nonempty I]` supplies a stage. Empty I is explicitly excluded as in the node.
- The zero coefficient ring and infinite Noetherian F_ℓ-algebras are allowed.
  Rank or underlying-set finiteness is never substituted for finite generation.
- Nonsplit extensions are included; no splitting or constructibility of F_a is demanded.

Searches for an existing declaration:

- `msearch.py ... leanfinder` with "Every extension of a constructible etale sheaf
  by a directed union of subsheaves descends to an extension by one subsheaf and is
  its pushout": eight hits, concerning scheme gluing, directed open covers and
  sheaf gluing; no exact extension theorem.
- `msearch.py ... loogle` with
  `CategoryTheory.ShortComplex.ShortExact, CategoryTheory.IsPushout`: zero hits.
- `msearch.py ... grep` with
  `constructible.*extension|extension.*finite.stage` in `CategoryTheory`: zero hits.
- `msearch.py ... leansearch` with "A short exact sequence with constructible
  quotient and directed union as kernel is a pushout from a short exact sequence
  at a finite stage": eight hits, including general `IsPushout` and short-complex
  exactness interfaces. None supplies constructible finite-stage descent.
- `rg` for `constructible.*extension|extension.*finite.stage` in upstream
  `WeilConjectures/` and shared `lean/Sheaf/` found extension-closure, cohomology
  continuity and coefficient-descent statements, but not this assertion.
- The exact item-id search in the upstream tree found nothing. A declaration-name
  search for `constructible_extension_finite_stage` in both source trees and
  `dag/lean_names_upstream.json` found nothing.

Validation: final `scompile.py Q36 lem-per-constructible-extension-finite-stage <file>`
compiled the sandbox and module-path forms, each in about two seconds, without errors
or warnings. Both `autoImplicit` and `relaxedAutoImplicit` are explicitly false.
The sole theorem has exactly `by sorry` as its proof. No statement correction or
STATEMENT-DISPUTED issue was needed.

## Second reading by Q36

Author self-check, as required for this dispatcher-started direct delivery; the
maintainer supplies the independent review. I reopened the node and file and checked
all binders and all conclusion clauses against the list above. The chosen presentation
uses H=S.X₁ and G=S.X₃, so the endpoint equations are well typed without transports.
I checked the pushout argument order against Mathlib's square diagram, the inclusion
condition against `Cocone` naturality, and constructibility against the full upstream
signature and its Noetherian-space constructor. No finiteness assumption on R, extra
Noetherian condition on a stage, or constructibility condition on the middle terms is
present. The first compile exposed a private-import visibility issue for
`Scheme.IsConstructibleSheaf`; adding the direct public upstream definition import
fixed it without changing the signature. The final file also imports the recorded
Grothendieck-abelian proof module and compiles cleanly. No mathematical mismatch remains.
