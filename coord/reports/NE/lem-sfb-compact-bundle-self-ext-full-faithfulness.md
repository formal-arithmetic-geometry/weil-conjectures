## Worker report

The module `Sheaf.AlgebraicGeometry.CompactBundleSelfExtFullFaithfulness` states
`AlgebraicGeometry.BundleEndomorphism.compact_bundle_self_ext_fullyFaithful`.
Its only proof is `sorry`. No definitions, helper theorems, or dependency repairs are needed.
Only `lean` changes in the item's JSON; the natural-language statement, split, and dependencies
are unchanged.

Source read: `literature/stacks-project/dga.tex`, Tag 09LZ,
`lemma-fully-faithful-in-compact-case`, statement and proof (lines 6121 onward).
The source's dg-endomorphism comparison specializes to ordinary End(E) when the bundle
has no self-Ext in nonzero degrees. As the node explicitly explains, only quasi-coherent
targets occur in its compactness argument; this is why the hypothesis uses D_QCoh.
The node's seven accepted proof steps are reproduced in the theorem's docstring,
including the regular-module calculation, the actual unit on B[n], preservation of
coproducts, and the shift-saturated telescope argument.

Hypotheses and clauses, in order:

* The commutative ring A is `(A : Type a) [CommRing A]`. The independent universe `a`
  is retained; it is not forced equal to the scheme universe.
* X is `(X : Scheme.{u})`. Its A-scheme structure is `(aX : A →+* Scalars X)`, precisely
  the structural-global-sections encoding used by the recorded adjunction dependency.
  It is equivalent to specifying X over Spec(A) in the appropriate common universe.
  No coefficient-linearity assertion is added to this node's conclusion.
* Quasi-compactness and quasi-separatedness are `[CompactSpace X] [QuasiSeparatedSpace X]`.
* The finite locally free sheaf is `(E : Modules X) [E.IsFiniteLocallyFree]`. This is the
  existing class with finite local generators on each covering member, so its rank can
  vary between opens and can be zero. `Modules X` is the dependency's exact abbreviation
  for the shared `SheafOfModules.{u} (moduleRings X.toRingedSpace)` carrier.
* E in degree zero is `single X E`, the dependency's abbreviation for the existing
  `DerivedCategory.singleFunctor (Modules X) 0` applied to E.
* B is the actual `End E`, whose multiplication is composition. Right B-modules are
  `ModuleCat.{u} (End E)ᵐᵒᵖ`. No commutativity or nontriviality is imposed on End(E).
* The two unbounded derived categories use independent localization morphism universes
  `[HasDerivedCategory.{w} (Modules X)]` and
  `[HasDerivedCategory.{wB} (ModuleCat.{u} (End E)ᵐᵒᵖ)]`. These are shared Mathlib
  localization interfaces, not boundedness or resolution hypotheses.
* The specified F_E is the binder `F` with source the latter derived category and target
  `schemeDerivedQCohCategory X`. The comparison `eps` and its
  `IsLeftDerivedFunctor` instance are exactly the first clause of the recorded
  `BundleEndomorphism.adjunctionStatement`: the ambient composite of F is the total
  left derived functor of the dependency's `tensor X E` on the homotopy category.
  Thus F is uniquely determined up to the derived comparison isomorphism; it is not an
  unconstrained functor. Quantifying over the chosen F and comparison states the result
  for the F_E provided by the dependency, without choosing data from a sorry theorem.
* The right adjoint is exactly the dependency's `qcHom X E`, namely the restriction of
  `(preadditiveCoyonedaObj E).rightDerivedFunctor`. This retains the actual right B-action
  by precomposition. The binder `adj : F ⊣ qcHom X E` supplies the tensor-Hom adjunction
  whose unit occurs in the conclusion. Full faithfulness makes the unit of every
  adjunction with this F and G invertible, so no normalization is lost by this binder.
* Compactness is `hcompact`: there is a proof `hE` that E[0] belongs to D_QCoh and
  `@IsCompactObject _ _ _ (derivedQCohDirectSums X) ⟨single X E, hE⟩` holds.
  The existential only packages that same E[0] into the full subcategory; it does not
  replace E or choose a different object. It uses the recorded u-indexed coproduct
  construction explicitly, with no local instance or hidden let in the statement.
* Vanishing is `hself : ∀ q : ℤ, q ≠ 0 → Subsingleton (single X E ⟶ (single X E)⟦q⟧)`.
  Since these Hom sets are additive groups, subsingleton is precisely the zero group.
  This is stated in the ambient D(O_X), exactly as the node requires, and includes
  both negative and positive integers.
* Full faithfulness is `F.Full ∧ F.Faithful`, and the natural isomorphism of the specified
  unit is `IsIso adj.unit`. This is the natural transformation itself, rather than an
  unrelated isomorphism between the two functors.
* There is no generator hypothesis on E or any restriction on the essential image of F.

Recorded statement dependencies opened and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
* `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`.
* `WeilConjectures.CategoryTheory.CompactObject`: `CategoryTheory.IsCompactObject`.
  The example `Sheaf.CategoryTheory.CompactObject` is withdrawn; the node correctly
  records this upstream declaration, which is the one imported here.
* `Sheaf.AlgebraicGeometry.BundleEndomorphismDerivedAdjunction`: read the entire module,
  including `Modules`, `Scalars`, `tensor`, `single`, `derivedHom`, `qcHom`,
  `adjunctionStatement`, and `tensor_derived_adjunction`. Its first existential witness
  supplies precisely F and eps as bound here, and its adjunction clause supplies adj.
  The item does not assert the dependency's extra A-linear/coefficient comparison clauses,
  so no irrelevant linear-category structure or derived A-module universe is required.

The statement also uses `WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSums`:
`AlgebraicGeometry.derivedQCohDirectSums` to make the compactness coproduct instance explicit.
The remaining recorded proof dependencies are imported without `public`:
`DerivedModuleDirectSums`, `DerivedModuleHomologyCoproduct`, `WeakTriangulatedGenerator`,
`ShiftSaturatedIsoLocus`, `CompactGeneratorsBuildObjects` under `WeilConjectures.CategoryTheory`,
and Mathlib's `DerivedCategory.KProjective`, `DerivedCategory.HomologySequence`, and
`DerivedCategory.FullyFaithful`. The last three give the recorded K-projective Hom,
cohomological isomorphism, and degree-zero fully faithful embedding leaves respectively.
No import cycle is introduced.

Edge cases checked before writing:

* E=0 is allowed (finite rank zero), so End(E) is the zero ring and the source derived
  category is zero. Full faithfulness and the unit assertion remain correct.
* The empty scheme is allowed; the same zero-category check applies.
* E=O_X on an affine scheme gives the familiar module/sheaf comparison, while E free
  of finite rank gives a possibly noncommutative matrix endomorphism ring; no [CommRing B]
  has slipped into the statement.
* A bundle supported on a proper clopen component can fail to generate all of D_QCoh;
  the conclusion still only asserts full faithfulness and the unit, without a counit iso.
* The self-Ext hypothesis omits q=0 and includes every positive and negative q.
* Empty and arbitrary u-small coproduct families are included in IsCompactObject.
  The categories have the same u-sized coefficient carriers and index universe, but
  their localization Hom universes w and wB stay independent.
* Complexes and derived categories are unbounded; there is no boundedness binder.

Searches actually run through msearch.py (group NE and this item):

* LeanFinder, `A compact vector bundle with no nonzero degree self extensions induces a
  fully faithful derived tensor functor from its endomorphism ring`: eight results,
  including `DerivedCategory.instFullSingleFunctor`, condensed module full faithfulness,
  and internally projective tensor conditions; none is this theorem.
* LeanSearch, `Compact vector bundle with vanishing nonzero self Ext induces fully faithful
  derived tensor`: eight results including Ext.mk₀, projective Ext vanishing, and condensed
  module embeddings; none is the compact self-Ext criterion.
* Loogle, `Adjunction, Full, IsIso`: zero results, with diagnostic unknown identifier
  `Adjunction`; this failed name lookup is not claimed as a successful exact-match search.
* Mathlib grep, `fully faithful|IsIso.*unit` in `CategoryTheory/Adjunction`: 25 results,
  including the general adjunction unit criterion in `Adjunction/FullyFaithful.lean`;
  none supplies the compact bundle/self-Ext argument.
* Local rg, `compact.*(fully|faithful)|self.ext|selfExt|tensor_derived_adjunction|adjunctionStatement`
  in `lean/WeilConjectures` and `lean/Sheaf`: finds the adjunction dependency and the parent
  `ProjectiveSpaceTiltingEquivalence`, plus unrelated self-Ext calculations. The parent
  only cites this item in its proof, and does not state this general theorem.
* Local rg of this item id in `lean/WeilConjectures`: no declaration.
* Local rg for `compact_bundle_self_ext_fullyFaithful` in Mathlib, both project source
  trees, and `dag/lean_names_upstream.json`: no existing declaration with that name.

Validation: the prescribed scompile.py compiled the module separately in sandbox mode and
under its final library module name, with no errors or warnings (4.2 s and 3.7 s respectively).
All variables and universes are explicit, `autoImplicit` is false, no local notation/instance
is introduced, and every Lean source line has at most 100 characters. The node's lean.statement
is extracted verbatim from the file. No node fault or STATEMENT-DISPUTED issue was found.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
