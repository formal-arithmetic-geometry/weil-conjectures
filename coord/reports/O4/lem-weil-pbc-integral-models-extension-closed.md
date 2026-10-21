## Worker report

Item: `lem-weil-pbc-integral-models-extension-closed`, O4, stage 2.
Module: `Sheaf.Paper.IntegralModelsExtensionClosed`.
Main declaration: `AlgebraicGeometry.ProEtale.integralModels_extension_closed`.
The node's statement, dependencies, and proof are unchanged. There are no new nodes or
repaired dependency records. The theorem has only `sorry` as its proof. The auxiliary
abbreviations specialize existing scalar extension on objects and arrows; the auxiliary
constant-scalar endomorphism has actual sectionwise linear maps and their restriction law.

Sources read: Bhatt--Scholze, *The pro-etale topology for schemes*, Lemma 6.8.13,
especially the final paragraph, and the adjacent Definition 6.8.10 and Proposition 6.8.11;
Stacks `derived.tex`, `lemma-ext-1`, Tag 06XV. The source's Ext localization argument is
used with the node's explicitly assumed surjectivity, rather than assuming an arbitrary
isomorphism of Ext groups. The example `CompactObject.lean` currently contains only its
withdrawal notice; its node record and the standing module conventions were also read.

Hypotheses and clauses, in node order:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite extension E/Q_l: `(E : Type u) [Field E] [Algebra ℚ_[l] E]`
  and `[FiniteDimensional ℚ_[l] E]`. No Type-0 restriction is imposed.
- A = O_E and its topology: `latticeCoefficientIntegers l E` is the existing subring of
  `WithAbs (Padic.coefficientExtensionAbsoluteValue l E)`, obtained by transporting the
  recorded `Padic.coefficientExtensionIntegers l E` along `WithAbs.equiv`.
  The ring's subspace topology is exactly the topology used in continuous constructibility.
- Uniformizer: the recorded chosen `Padic.coefficientExtensionUniformizer l E`, transported
  by `(WithAbs.equiv ...).symm` into the topology-bearing coefficient field. Its mth power
  is the scalar appearing in the Ext equation. This uses the choice already made by the
  coefficient-extension definition, without adding a uniformizer assumption.
- Scheme: `(X : Scheme.{u})`. Noetherian in the finite-affine-cover sense is
  `[IsNoetherian X]`; Mathlib's `isNoetherian_iff_of_finite_affine_openCover` identifies
  this with the node's stated meaning. This also supplies `NoetherianSpace X` needed by
  `IsContinuousConstructible`.
- Finite dimension: `_hdim : ∃ n : ℕ, topologicalKrullDim X ≤ n`, the finite bound on
  lengths of chains of irreducible closed subsets.
- Ell invertible on X: `_hl : IsUnit (l : Γ(X, ⊤))`. This is equivalent to being a unit
  in every local ring: inverses of the same global section glue uniquely.
- For all locally closed strata Y, continuous A and E coefficients are the existing
  `latticeCoefficientSheaf Y (latticeCoefficientIntegers l E)` and
  `latticeCoefficientSheaf Y (WithAbs ...)`, with underlying `latticeModuleRing`.
  Their section rings are lifted continuous-function rings and their restrictions are
  precomposition. Restriction to strata is already part of `IsContinuousConstructible`.
- Scalar extension S_X(M) = E_X tensor_{A_X} M is
  `integralModelScalarExtension X l E M`, a transparent abbreviation for the recorded
  `SheafOfModules.changeOfRings (integralLatticeCoefficientMap X l E) M`.
  Its arrow abbreviation is the recorded `SheafOfModules.changeOfRingsHom`, so the
  extension-class condition uses the actual inclusion of coefficient rings.
- P and Q: the two binders are `SheafOfModules.{u + 1}` over the existing integral
  `latticeModuleRing`; `_hP` and `_hQ` are precisely
  `IsContinuousConstructible X (latticeCoefficientIntegers l E) P/Q`. That definition
  uses finite locally closed stratifications, pro-etale covers, and finitely presented
  ordinary module local models. No freeness or torsion-freeness is assumed.
- Ext and surjectivity: `Abelian.Ext ... ... 1` is the dependency's ambient derived Ext.
  `[HasExt.{w} ...]` allows any small model of these groups; it is size infrastructure,
  always available in a sufficiently large universe by `HasExt.standard`, and imposes
  no mathematical restriction. The definition of the numerator condition is explained
  fully below. It is equivalent to the node's displayed surjectivity, not an extra
  geometric or exactness assumption.
- Arbitrary short exact rational sequence: `(F : SheafOfModules ... rationalRing)`,
  `(i : S(Q) ⟶ F)`, `(p : F ⟶ S(P))`, `(z : i ≫ p = 0)`, and
  `_h : (ShortComplex.mk i p z).ShortExact`. This includes the mono, epi, and middle
  exactness clauses, rather than imposing sectionwise surjectivity.
- Conclusion: `∃ N : SheafOfModules ... integralRing, IsContinuousConstructible ... N ∧`
  `Nonempty (integralModelScalarExtension X l E N ≅ F)`. There is no equation requiring
  the isomorphism to preserve the prescribed inclusion, and no claim that N is torsion-free.

Exact rendering of the localized-map hypothesis:

`_hsurj` quantifies over every rational class ξ and asks for m ≥ 0 (as `m : ℕ`) and an
integral short exact representative `Q --i--> B --p--> P`. The existential integral B
has NO constructibility condition. Its scalar-extended arrows are the actual
`integralModelScalarExtensionMap` arrows. Their short exactness and their canonical
`ShortExact.extClass` are recorded. The equation is

`hE.extClass = ξ.comp (Abelian.Ext.mk₀ (integralModelConstantScalar ... varpi^m)) (add_zero 1)`.

The right side is varpi^m ξ: `Ext.comp` with degree-zero postcomposition is the usual
coefficient action on the target, shifted to degree one. The scalar helper multiplies
sections by the constant function varpi^m, with its naturality proved by `M.val.map_smul`.

Why this is exactly surjectivity of the specified localized Ext map: every element of
`LocalizedModule.Away varpi (Ext¹(P,Q))` has a numerator α and denominator varpi^m
(`LocalizedModule.mk` and its induction principle, inspected in Mathlib). If the map is
surjective, choose α/varpi^m over ξ. Ext-one classification supplies an integral short
exact representative of α. Exactness of the existing scalar extension (continuous
coefficient localization and `scalarLocalization_sheaf_exact`) makes its actual
scalar-extended sequence short exact, and exact-functor compatibility makes its class
S(α). The fraction equation is equivalent to S(α) = varpi^m ξ because varpi is invertible
in E. These are precisely the witnesses in `_hsurj`. Conversely, take the class α of
its integral sequence. Exact-functor compatibility identifies `hE.extClass` with S(α),
so α/varpi^m maps to ξ. Neither direction uses constructibility of B. This spelling avoids
choosing a separate localized Ext-map implementation or adding linear/exactness binders
for an unspecified scalar-extension functor. The canonical tensor construction is fixed
on both objects and arrows throughout.

Dependency declarations used (full signatures and docstrings inspected):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public coefficient
  import: `Padic.coefficientExtensionIntegers`, `coefficientExtensionAbsoluteValue`,
  `coefficientExtensionUniformizer`, and `finite_coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, transparent
  over Mathlib `SheafOfModules`; its Mathlib abelian structure is retained.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, with its public tensor
  imports: `SheafOfModules.cochainModulesMonoidal`, the existing
  `SheafOfModules.changeOfRings` and `changeOfRingsHom` (sectionwise tensor, then sheafify).
- `Sheaf.Paper.ContinuousConstructibleModule`:
  `AlgebraicGeometry.ProEtale.IsContinuousConstructible`, whose existing coefficient
  imports give `latticeModuleRing`, `latticeCoefficientIntegers`, and
  `integralLatticeCoefficientMap`. No copy of constructibility or the coefficient ring
  has been introduced.
- `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic` (through ExtClass):
  `CategoryTheory.Abelian.Ext`, `Ext.comp`, `Ext.mk₀`; and ExtClass:
  `CategoryTheory.ShortComplex.ShortExact.extClass`.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule.Away`,
  `LocalizedModule.mk`, and `LocalizedModule.induction_on` explain the fraction-surjectivity
  expansion. Its module is publicly imported.
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`:
  `CategoryTheory.ShortComplex.ShortExact` (exact, mono, epi).

All recorded proof dependencies are imported for the future proof:
`Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`
(`Scheme.continuousCoefficientImmersionRestriction`),
`Sheaf.CategoryTheory.ScalarLocalizationSheafExact`
(`CategoryTheory.scalarLocalization_sheaf_exact`),
`Sheaf.CategoryTheory.ExtOneExtensionClassification`
(`CategoryTheory.ext_one_extension_classification`),
`Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
(`Scheme.integralStratifiedPerfectCharacterization`, `integralStratifiedPerfectClosure`),
and `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
(`DerivedCategory.triangleOfSESδ`, `triangleOfSES`, `triangleOfSES_distinguished`).
The localization-definition proof dependency is the public import already listed.

Edge cases checked before/following drafting:

- Empty X is allowed: no nonempty or positive-dimension binder is present; the unique
  continuous function on an empty object and the categorical exactness definitions work.
- Zero P or Q, zero F, and rank-zero local models are allowed. No positive-rank or
  nonzero-object hypotheses occur.
- `m = 0` is allowed and yields the identity scalar; α = 0 and split extensions are included.
- Torsion integral P and Q are allowed by finitely presented local models. Their
  rationalization may vanish; neither a lattice injection nor flatness of P/Q is assumed.
- No independent universe for test schemes or coefficient modules makes a hypothesis
  vacuous: X and E use u, site objects have universe u+1 and morphisms u, module carriers
  use u+1, and Ext uses the explicitly bound w.
- The integral B in the denominator hypothesis need not already be constructible; this
  essential point was checked against the node's proof steps 3 and 4.
- The prescribed rational inclusion is allowed to change by varpi^(-m); the conclusion
  only asks for an isomorphism of middle objects.

Searches run (actual tools and results):

1. `msearch.py ... leanfinder`, query "Surjectivity of localized Ext one scalar extension
   gives a constructible integral model for extensions of rationalized module sheaves":
   eight hits, including `IsLocalizedModule.mk'_surjective`,
   `IsLocalizedModule.map_surjective`, and ordinary finitely-presented module localization.
   None is this constructible sheaf statement.
2. `msearch.py ... loogle`, query `"Ext", "mapExactFunctor"`: eleven hits, including
   `Abelian.Ext.mapExactFunctor`, `mapExactFunctor_extClass`, and functoriality lemmas.
   These supply the classification-compatible map, not this integral-model theorem.
3. `msearch.py ... grep`, query
   `(constructible|integralModel).*(extension|Ext)|Ext.*integralModel` in CategoryTheory:
   zero hits.
4. `msearch.py ... leansearch`, query "An extension of rationalized constructible integral
   sheaves has an integral model when the scalar extension map on localized Ext one is
   surjective": eight hits, including an elliptic-curve integral model and ordinary
   scalar-extension/localization lemmas; none is a match.
5. `rg` of `lean/WeilConjectures` for the same constructible/integral-model/extension
   terms found constructible étale-sheaf closure and the condensed pro-etale framework,
   but no continuous `SheafOfModules` denominator criterion. Search for this node's id
   there gave no match.
6. `rg` of `lean/Sheaf` found continuous integral coefficients, integral-image triangulated
   closure and denominator results for derived internal modules. Their signatures use
   different categories/constructibility interfaces and do not state this node. Existing
   continuous constructibility and sheaf tensor declarations were therefore used directly.
7. Name checks in `dag/lean_names_upstream.json`, `lean/WeilConjectures`, `lean/Sheaf`,
   and `dag/nodes` found no declaration of any of the four full names introduced here.
   The similarly named `WeilConjectures.SixFunctors.integralModelConstantScalars` is a
   different coefficient ring map, not a module scalar endomorphism.

Compilation: the prescribed `scompile.py O4 lem-weil-pbc-integral-models-extension-closed`
compiled the final file successfully in sandbox and library-module modes (11.9 s and
38.0 s). No errors or warnings remained. The initial scalar helper needed the existing
commutative coefficient sheaf as the ring argument to `LinearMap.lsmul`, rather than its
RingCat reduct; this was repaired and recompiled. No live file or launcher tool was edited.
No statement fault or unresolved STATEMENT-DISPUTED finding remains.

## Second reading by O4

This is a separate reading pass by the same worker; the maintainer's independent review
follows delivery. I reopened the node and final module, and checked the hypotheses and
clauses in the correspondence above. In particular, P/Q are continuous-constructible
modules over the transported canonical valuation ring, the fraction hypothesis uses the
actual sheafified scalar-extension maps, the numerator B has no hidden constructibility
hypothesis, and the conclusion asserts only a middle-object isomorphism. The Ext class
postcomposition has degree 1+0=1 and targets S(Q), so it is the correct scalar action,
not an action on the quotient P or a degree-zero Hom assumption. The finite dimension
and invertibility hypotheses match the source-based characterization used in the proof.
The only implementation correction found was commutative ring inference in the scalar
helper, fixed before the clean compile; this did not change the mathematical signature.
The node signature record is extracted verbatim from the final theorem, all universes
are explicitly bound, and the data of every helper are fully constructed.
