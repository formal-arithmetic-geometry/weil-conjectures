## Worker report

This is an existing-declaration delivery. No Lean module is written and no proof or definition is duplicated. The two declarations in `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Derives` together give the node's existence statement and its criterion for every candidate. Their complete source, shared binders, module docstring and proofs were read, as were the Mathlib interfaces below. The base node already has a lead's attachment of precisely this pair, but its lean record lacks module, primary declaration, statement and existing fields; this delivery supplies a complete stage-2 record and preserves all other fields, including the existing audit.

The primary source signature, reproduced verbatim in lean.statement, is:

```lean
lemma hasLeftDerivedFunctor [Φ.IsLeftDerivabilityStructure] :
    F.HasLeftDerivedFunctor W₂
```

The second recorded signature is:

```lean
lemma isLeftDerivedFunctor_iff_isIso [Φ.IsLeftDerivabilityStructure] :
    LF.IsLeftDerivedFunctor α W₂ ↔ ∀ (X₁ : C₁), IsIso (α.app (Φ.functor.obj X₁))
```

Both include the earlier explicit argument `(h : Φ.Derives F)`; the second also includes `(α : L₂ ⋙ LF ⟶ F)` and `[L₂.IsLocalization W₂]`. Object and morphism universes are independently quantified as `u₁,u₂,u₃,u₄` and `v₁,v₂,v₃,v₄` in the upstream source.

Hypothesis and conclusion correspondence:

- Categories A, D, H, and the resolving category P: specialize `C₂ := A`, `D₂ := D`, `C₁ := P`, with `H` unchanged and their respective `Category` instances. This uses the recorded `CategoryTheory.Category` of def-nagata-category, from `Mathlib.CategoryTheory.Category.Basic`.
- The arrow class W containing identities: take `W₂ := W` and retain the node's `W.ContainsIdentities` assumption in the specialization. The general existing theorem needs no identities assumption, so it applies to this case without any additional hypothesis.
- The given localization L in the universal-property sense: `L₂ := L`, `[L₂.IsLocalization W₂]`. Read `Mathlib.CategoryTheory.Localization.Predicate`: its predicate says that the canonical induced functor from the localization model is an equivalence, hence is the usual localization universal property. No selected fraction calculus is imposed.
- Full inclusion i and the inverse-image arrows W_P: specialize `Φ := LocalizerMorphism.ofEq (F := i) rfl` with `W₁ := W.inverseImage i`. Its underlying functor is definitionally i. Restrict the general theorem to the node's full inclusion. Fullness is not an extra requirement of the existing theorem.
- The inclusion is a left derivability structure: `[Φ.IsLeftDerivabilityStructure]`. This is exactly the dependency record of def-sfb-left-derivability-structure in `Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic`. Its fields give left resolutions and Guitart exactness of the inverse comparison. The same dependency's `isLeftDerivabilityStructure_iff` and `Mathlib.CategoryTheory.GuitartExact.Basic`'s `TwoSquare.guitartExact_iff_final` identify its chosen-localization comma functor condition; these signatures and docstrings were read. Thus the dependency needs no replacement module.
- Functor F and inversion by F composed with i: `(F : C₂ ⥤ H)` and `h : Φ.Derives F`. `Derives` in `Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives` abbreviates `W₁.IsInvertedBy (Φ.functor ⋙ F)`, precisely inversion of every W_P arrow.
- Existence of LF and ε: `h.hasLeftDerivedFunctor` supplies `F.HasLeftDerivedFunctor W₂`. `Functor.hasLeftDerivedFunctor_iff` in `Mathlib.CategoryTheory.Functor.Derived.LeftDerived` transports existence from W.Q to the specified L. Its `F.totalLeftDerived L W` and `F.totalLeftDerivedCounit L W : L ⋙ F.totalLeftDerived L W ⟶ F` are the requested functor and natural transformation, with the provided `IsLeftDerivedFunctor` instance. These are already implemented Mathlib constructions, not arbitrary choices introduced by this delivery.
- For every V, the displayed bijection induced by ε: `IsLeftDerivedFunctor.isRightKanExtension` is exactly the right Kan extension property. In `Mathlib.CategoryTheory.Functor.KanExtension.Basic`, `Functor.homEquivOfIsRightKanExtension` is `(V ⟶ LF) ≃ (L ⋙ V ⟶ F)` with forward function `fun β ↦ Functor.whiskerLeft L β ≫ ε`. Its inverse is the universal lift, and the factorization and uniqueness statements are read directly in the source. Thus this is the specified map, with the correct direction, rather than an unrelated equivalence of sets.
- For every candidate T and η, universality iff invertibility on resolving objects: set `LF := T`, `α := η` in `h.isLeftDerivedFunctor_iff_isIso`. Its right side is `∀ P, IsIso (η.app (i.obj P))`; its left side is the same universal property just described.
- In particular ε is invertible on each iP: specialize that criterion to `F.totalLeftDerived L W` and its counit, which has the existing derived-functor instance. The same source module also states `Derives.isIso_of_isLeftDerivedFunctor` explicitly.

The source place was opened: current blueprint main-20261015, `sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`, paragraph saying tensor descends and is the two-variable left derived functor. This node isolates the unary categorical input used there. There is no statement correction and no new dependency.

Edge cases checked: the empty resolving category can satisfy left resolutions only when A is empty; the abstract existing theorems and the right Kan extension equivalence still apply, with the component criterion vacuous as it should be. For the identity inclusion, W containing identities supplies the identity derivability structure, and inversion is exactly inversion of W by F. No assumption of nonempty categories, zero objects, additivity, resolutions chosen functorially, or matched universe levels is introduced. Arbitrary T, η and V are retained; neither η nor ε is assumed invertible globally on A.

Searches performed:

- msearch.py leanfinder, query `A left derivability structure gives a left derived functor characterized by its counit being an isomorphism on resolving objects`: 8 hits, including Mathlib's `IsLeftDerivedFunctor`, `isLeftDerivedFunctor_iff_isIso_leftDerivedLift`, and the dual `LocalizerMorphism.Derives.isRightDerivedFunctor_iff_isIso`. They explain the general API but the exact left-handed pair is in the project supplement.
- msearch.py loogle, query `CategoryTheory.LocalizerMorphism.Derives.hasLeftDerivedFunctor, CategoryTheory.LocalizerMorphism.Derives.isLeftDerivedFunctor_iff_isIso`: 0 hits; unknown identifier for the first name in the Mathlib-only index.
- msearch.py grep, query `hasLeftDerivedFunctor|isLeftDerivedFunctor_iff_isIso`, subdirectory `CategoryTheory/Localization`: 0 hits in Mathlib.
- rg of the same names in upstream WeilConjectures finds the exact two declarations at DerivabilityStructure/Derives.lean:54 and :107, plus applications in DerivesTwo, DerivesThree, DerivesFour and the K-flat derived functor interface. Full upstream source and module docstring read.
- rg of the item id in upstream WeilConjectures finds no blueprint tag. This does not affect the signature match.
- rg in the project's lean/Sheaf finds applications and specialized K-flat criteria, not a separate general unary-calculus declaration. The general existing supplement is reused.

No new modules, no dependency modules, no new nodes, no statement disputes. Validation: the prescribed deliver2 existing-declaration probe checked both names successfully; server preflight passed. The dry run printed `OK (dry run): commit c40d52b745 passes the preflight and compiles; nothing pushed`. No Lean module is delivered, so no additional per-file compilation is required.

## Second reading by Q60

Independent maintainer second reading, 2026-10-17, of immutable delivery
06139a5e6ed4a4d3bbdbc08ebb03b5af4f5e7e10. This section is supplied by the
maintainer reviewer, who neither wrote nor previously second-read the delivery.
The original section was a placeholder, not a reading (H11); this complete
replacement report repairs that documentation fault. No node or Lean change is needed.

I read the immutable item node, both statement-dependency nodes, the worker report,
the full existing DerivabilityStructure.Derives module, its shared binders and
module documentation, and the exact supporting declarations below. I read the source
place in the read-only Q60 clone: literature/blueprint/main-20261015/blueprint/
sec-proetale-coefficients/sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md.
Its paragraph first asserts the left derivability structure of K-flat complexes,
then descent and the two-variable left derived functor. The node extracts the unary
categorical calculus supporting that paragraph; the paragraph does not itself spell
out the displayed bijection. The existing categorical theorems supply it.

Clause-by-clause reading:

- Categories A, D, H and P: C₂, D₂, H and C₁, respectively, with their Category
  instances. def-nagata-category records CategoryTheory.Category; I checked
  Category/Basic.lean:123 and :234 (identities, composition, identity laws and
  associativity), as well as Stacks categories.tex, definition-category.
- W and identities: W₂ is W. The upstream theorem works for arbitrary W₂; the
  node's identities assumption is harmless in the specialization. No extra
  closure, calculus of fractions or saturation assumption is required.
- The specified localization L: L₂ with [L₂.IsLocalization W₂]. Predicate.lean:52
  requires inversion and equivalence of the induced canonical localization lift,
  the localization universal property up to equivalence. The statement is not
  restricted to the constructed localization W₂.Q.
- Full inclusion i and W_P: take W₁ = W.inverseImage i and
  Φ = LocalizerMorphism.ofEq (F := i) rfl (LocalizerMorphism.lean:57).
  Its functor is i, and its map condition is precisely the inverse-image condition.
  Applying a theorem valid for all localizer morphisms to the given full inclusion
  adds no assumption and needs no private definition of the subcategory.
- Left derivability: use the recorded IsLeftDerivabilityStructure, not a substitute.
  Basic.lean:140-145 gives HasLeftResolutions and GuitartExact of the inverse
  comparison. Resolution.lean:67-72 and :88 give exactly arrows iP → X in W.
  Basic.lean:169-174 allows chosen localizations. For the inverse square, the
  costructured-arrow functor of GuitartExact/Basic.lean:69-75 has domain (i ↓ X)
  and target (E ↓ LX); :262-264 equates its finality with Guitart exactness.
  The StructuredArrowRightwards description at :96-115 gives exactly the
  factorization triples and their commuting arrows in the dependency node.
- F and inversion on P: h : Φ.Derives F is the abbreviation at Mathlib
  DerivabilityStructure/Derives.lean:57, W₁.IsInvertedBy (Φ.functor ⋙ F).
  Thus only restricted arrows must be inverted; F need not invert all W.
- Existence: the first recorded declaration, supplement Derives.lean:54-58,
  includes h and gives F.HasLeftDerivedFunctor W₂. Mathlib
  Functor/Derived/LeftDerived.lean's hasLeftDerivedFunctor_iff transports this to L.
  totalLeftDerived and totalLeftDerivedCounit construct LF and ε, and their
  IsLeftDerivedFunctor instance gives the required universal property.
- For every V: IsLeftDerivedFunctor is precisely IsRightKanExtension of ε.
  KanExtension/Basic.lean:109-114 defines homEquivOfIsRightKanExtension as
  (V ⟶ LF) ≃ (L ⋙ V ⟶ F), with forward map β ↦ whiskerLeft L β ≫ ε.
  Its inverse, factorization and uniqueness are the right Kan universal property.
  Hence the bijection has the required direction and is induced by ε itself.
- Every T and η: the second recorded declaration, supplement Derives.lean:107-109,
  retains h and [L₂.IsLocalization W₂], and quantifies arbitrary LF and α.
  Substituting T and η gives universality iff ∀ P, IsIso (η.app (i.obj P)).
  It does not assume universality or global invertibility of η in advance.
- In particular: apply this equivalence to totalLeftDerived and its counit using
  their existing derived-functor instance. This gives invertibility on each iP;
  the same module's isIso_of_isLeftDerivedFunctor also states this consequence.

Universes and edge cases: all four categories have independently declared object
and hom universes u₁,...,u₄ and v₁,...,v₄. No equality of universe levels, smallness,
nonemptiness, additive structure, zero object, finite resolution or functorial
resolution is imposed. If P is empty, left resolutions force A empty; localization
then forces D equivalent to empty, so the vacuous component criterion and universal
property agree. For the identity inclusion, W containing identities gives the
identity derivability structure (Basic.lean:185-195), and the inversion hypothesis
is exactly inversion of W by F. Arbitrary V, T and η remain quantified in all cases.

One-definition-per-notion: independent rg searches for right Kan extensions,
totalLeftDerived, and derived-functor criteria in Mathlib, the upstream supplement
and Q60 lean/Sheaf confirm this reuse. The existing left-handed pair is in the
supplement, while Mathlib has the general Kan API and the right-handed derivability
criterion; Sheaf has specialized derived-tensor statements. The worker records
LeanFinder, Loogle and grep searches. There is no duplicated definition, missing
helper or unusable statement-dependency interface requiring a repair.

Record and pilot gates: lean.statement was compared programmatically against the
upstream text from `lemma hasLeftDerivedFunctor` through the text before `:=`;
it is verbatim equal. Both names in lean.declarations exist at the recorded lines.
All their variables and universes are bound, including the explicitly included h.
There are no new modules, definitions, local proofs, new nodes or statement changes.
The upstream module docstring describes exactly existence and the criterion and
attributes its source to Joël Riou's localization work. It has no blueprint tag and
the individual upstream lemmas have no new project docstrings; these are reused
existing declarations, so the new-module source/blueprint/proof-docstring gates
create no new file obligation. There is no pro-etale site substitution: this item
is entirely abstract category theory. No §1(C) correction or citer audit is needed.

Compiler evidence: the worker reports a successful two-name existing-declaration
probe and dry run c40d52b745. There are zero delivered Lean files requiring separate
compilation. For independent reproduction I nevertheless invoked:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q60 lem-sfb-unary-left-derived-calculus /home/ubuntu/weil-src-slopmaster2/WeilConjectures/FromJoel/CategoryTheory/Localization/DerivabilityStructure/Derives.lean
```

The installed wrapper currently uses the server side overlay. It exited 0, with
sandbox Sheaf/Stage2/Sandbox0.lean [1.0 s] and library Sheaf/Stage2/Check.lean [1.1 s],
no errors or warnings, and the normal 60-second per-file limit. This recompiles the
existing source containing both exact declarations; it does not introduce a new
project statement. No global build, direct SSH invocation, live Lean edit or Git
mutation was performed.

Finding: H11, documentation only, repaired by replacing the placeholder section
with this actual independent reading. Mathematical statements, dependency records
and the existing-declaration binding are correct. Verdict: FIX for the complete
replacement report only.
