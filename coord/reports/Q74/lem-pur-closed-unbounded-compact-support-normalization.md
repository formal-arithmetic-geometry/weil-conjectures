## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedUnboundedCompactSupportNormalization` states
`AlgebraicGeometry.Etale.closed_unbounded_compactSupport_normalization`, with its proof
`sorry`. No definition, additional theorem, dependency repair, or statement correction is
introduced. Only the item's `lean` field changes. The declaration's docstring carries all
six proof steps, including the full, identity-on-objects passage from complexes to the
homotopy category in Step 3.

### Hypotheses and objects

- The fixed finite coefficient datum is `(P : PurityFiniteSetting.{u})`, using
  `Sheaf.Paper.PurityFiniteSetting`. Its `P.field` supplies k and its `P.Coefficient` is
  the recorded standard universe lift of the actual quotient O_E/(varpi_E^n). The prime,
  extension, and positive level are the fields of this existing setting, not new assumptions.
- The schemes are `{Z X : Scheme.{u}}`. Their `Over (Spec (CommRingCat.of P.field.k))`
  instances express that they are k-schemes. `IsSeparated` on each structure morphism
  expresses separatedness, and `LocallyOfFiniteType` together with `QuasiCompact` on each
  structure morphism expresses finite type.
- `(i : Z ⟶ X) [IsClosedImmersion i]` is the stated closed immersion. Its `IsOver` instance
  records that the morphism between these k-schemes is over k.
- Ordinary constant-coefficient module sheaves are always
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)`. Their ordinary unbounded
  derived category is the existing `DerivedCategoryModule P.Coefficient T`. This does not
  use the pro-etale site or the constructible subcategory bundled elsewhere in the conventions.
- `F0` is exactly `lowerStar (ModuleCat.{u + 1} P.Coefficient) i`, the recorded direct-image
  declaration, and `F` is its `mapDerivedCategory`. `Q` and `Qh` are the existing
  `DerivedCategory.Q` and `DerivedCategory.Qh` localizations. No arbitrary functor or map
  is supplied as a hypothesis.

### Conclusions, clause by clause

1. Exactness of F0 is the initial conjunction `PreservesFiniteLimits F0 ∧
   PreservesFiniteColimits F0`. Its additivity is the existing `lowerStar_additive` instance.
   The exactness needed to elaborate `mapDerivedCategory` comes from the published
   closed-immersion-to-finite instances and
   `Etale.preservesFiniteColimits_lowerStar_of_isFinite`; exactness remains an asserted
   conclusion, not a new assumption.
2. The descent is the existing, genuinely constructed `F0.mapDerivedCategory`. The witness
   `phi : Q ⋙ F ≅ F0.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q` has precisely the
   direction F Q_Z to Q_X C(F0) in the statement. Its equation
   `phi = F0.mapDerivedCategoryFactors` specifies the canonical normalization.
3. The identity-open compactification is `Compactification.ofIsProper i`; its definition
   has intermediate scheme Z, open arrow `𝟙 Z`, and proper arrow i. The witness `e` is a
   natural isomorphism from the existing unbounded
   `rightDerivedLowerShriekOfCompactification ... (Compactification.ofIsProper i)` to
   `F0.rightDerivedFunctor`. Its equation identifies it with whiskering
   `mapDerivedCategoryOpenImmersionLowerShriekId` by that right derived functor, followed
   by its left unitor. Thus the first arrow actually removes identity extension by zero.
   The upstream identity isomorphism is constructed by uniqueness of the extension-by-zero
   adjunction; it is the canonical identity identification of the defining presheaf and
   sheafification used in the node's proof.
4. `delta : F0.rightDerivedFunctor ≅ F0.mapDerivedCategory` is the second natural
   isomorphism. The clause quantified over every `K : CochainComplex ... ℤ` says that
   `F0.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient ...).obj K)` is invertible,
   without assuming K-injectivity. The equation
   `F0.rightDerivedFunctorUnit ≫ whiskerLeft Qh delta.hom =
   F0.mapDerivedCategoryFactorsh.inv` characterizes delta by the inverse of the actual
   total-derived comparison under the termwise localization normalization. This is an
   equation of natural transformations on the homotopy category, so includes all
   representatives and their morphisms. The source of the unit and the inverse of
   `mapDerivedCategoryFactorsh` are the same `C(F0)` followed by `Qh`.
5. For each integer m the conclusion is `Nonempty (F ⋙ homologyFunctor _ m ≅
   homologyFunctor _ m ⋙ F0)`. This is an isomorphism of functors on the entire unbounded
   derived category, and expresses exactly H^m(FV) isomorphic to F0(H^m(V)), naturally
   for every derived morphism. The full functor isomorphisms e and delta are stated in
   addition to this cohomological assertion.
6. For every unbounded V and all integers a,b the final conjunction is
   `V.IsGE a → (F.obj V).IsGE a` and `V.IsLE b → (F.obj V).IsLE b`.
   There is no boundedness, Tor, constructibility, smoothness, or nonemptiness hypothesis
   on V or the schemes.

### Dependency declarations read and used

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`,
  `WeilConjectures.PurityFiniteSetting`, `.Coefficient`, and `.coefficientCommRing`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` and `AlgebraicGeometry.IsSeparated`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`
  imports `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, which supplies
  `AlgebraicGeometry.Etale.DerivedCategoryModule`; homology is
  `DerivedCategory.homologyFunctor` and bounds are the existing `IsGE`/`IsLE` predicates.
- `def-weil-pbc-direct-image`:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`: its body is precisely sheaf pushforward along
  the etale base-change functor. The bounded-below derived declaration in that record
  is not used for the unbounded total derived direct image here.
- `def-amb-etale-compact-support`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`: its body is
  derived exact open extension by zero followed by unbounded total derived direct image.
- `def-weil-pbc-extension-by-zero`:
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`,
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`; its derived identity comparison is
  `AlgebraicGeometry.Etale.mapDerivedCategoryOpenImmersionLowerShriekId` from
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`.

All of these are available through public imports. Plain proof imports retain
`CategoryTheory.oriented_closed_base_localization` from
`Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization`,
`CategoryTheory.Functor.exactFunctor_derivedFunctor` from
`Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`, and
`CategoryTheory.exists_rightDerived_of_enough_isKInjective` from
`Sheaf.CategoryTheory.KInjectiveTotalDerived`. Generic factorization and homotopy
factorization are `CategoryTheory.Functor.mapDerivedCategoryFactors` and
`.mapDerivedCategoryFactorsh` (Mathlib exact-functor module); localization lift and
uniqueness are `CategoryTheory.Localization.lift`, `liftNatIso`, and `natTrans_ext`
(`Mathlib.CategoryTheory.Localization.Predicate`). Sheafification uses
`presheafToSheaf`, `toSheafify`, and `sheafificationAdjunction` from
`Mathlib.CategoryTheory.Sites.Sheafification`. Closed immersions are proper through
Mathlib's closed-to-finite-to-proper instances; finite-type Noetherian ascent is
`LocallyOfFiniteType.isLocallyNoetherian` together with
`QuasiCompact.compactSpace_of_compactSpace`, recorded by the corresponding proof node.
Cohomology commutation on complexes uses `CategoryTheory.Functor.homologyFunctorIso`
in `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.

### Sources and edge cases

Read the current blueprint `main-20261015`, sk-prop-a1 proof's first localization
triangle; Stacks sites-modules.tex `lemma-i-star-equivalence` (08M3),
etale-cohomology.tex `proposition-closed-immersion-pushforward` (04CA) and
`definition-extension-zero`/`equation-j-p-shriek` (03S3), derived.tex
`lemma-right-derived-exact-functor` (015F), and homology.tex `lemma-exact-functor` (010N).
They support the constant-module exactness, all-complex derived comparison, canonical
identity extension, and cohomological conclusions respectively.

Checked: i the identity gives the usual identity normalization; the empty closed
subscheme is allowed and gives zero sheaves; the zero complex satisfies all integer
bounds and its images have zero cohomology; genuinely unbounded V is included because
no bound is a binder, only conditional conclusions; negative m,a,b are included through
ℤ. There is no a≤b assumption, so the separate lower and upper claims also apply to
zero objects when the two bounds do not overlap. The coefficient level n=1 is allowed;
no divisibility of n by the ramification index is imposed. The site uses Scheme.{u}
and ModuleCat.{u+1} as in the published ordinary-etale interface. No independent
universe equality, exceptional-adjoint datum, or pro-etale comparison is required.

### Searches and validation

The sandbox search log contains the actual msearch results:

- leanfinder: "For a closed immersion exact etale direct image on unbounded derived
  categories equals compact support for the identity open compactification": eight
  hits, including Scheme.Modules restriction adjunctions, Ext.mapExactFunctor_hom,
  and DerivedCategory bounds on representatives. None states this normalized chain.
- loogle: `rightDerivedFunctorIsoMapDerivedCategory`: no indexed hit (unknown identifier).
  Direct source reading does find the generic upstream exact-functor isomorphism; it
  supplies no closed identity-compactification normalization with these clauses.
- grep: `rightDerivedFunctorIsoMapDerivedCategory|mapDerivedCategoryFactors` in
  Mathlib Algebra/Homology: ten hits in DerivedCategory/ExactFunctor and Ext/Map.
  The termwise descent and its comparison are reused here.
- rg in both `lean/WeilConjectures` and `lean/Sheaf`: closed/compact/normalization
  patterns; read the finite exactness module and LowerShriekComposition identity
  isomorphism. Neither states the combined theorem with its representative comparison,
  natural homology comparison and both bounds. Exact declaration-name search in
  Mathlib, upstream, Sheaf and dag/lean_names_upstream.json found no duplicate.
- The prescribed node-id grep in `lean/WeilConjectures` returned no match.

`scompile.py Q74 lem-pur-closed-unbounded-compact-support-normalization` with the module
path checked both sandbox and library module contexts cleanly (11.5 s and 8.7 s).
No warning or error was printed. Every universe and variable is bound explicitly and
`autoImplicit` is false. The sole proof is the required `sorry`.

No node fault or STATEMENT-DISPUTED issue was found.

## Second reading by Q74

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
