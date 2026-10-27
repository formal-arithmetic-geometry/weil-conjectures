## Worker report

Item: `lem-tw-integral-comparison-descent`, group Q51, stage 2, 2026-10-22 UTC.

This is an existing-declaration delivery. Bind the node to
`WeilConjectures.ordinaryIntegralCompletionComparison_existsUnique` in
`Sheaf.Paper.OrdinaryCompletedIntegralPullback`, source lines 495–530. This is
exactly the declaration named by the node's source place. Its signature is copied
verbatim into `lean.statement`. No Lean module, definition, axiom, proof, or helper
node is added. Only this item's `lean` field changes.

The source module and its docstring were read locally and confirmed using
`scompile.py --source Sheaf.Paper.OrdinaryCompletedIntegralPullback`. Its public
availability and complete explicit type were checked on the server with a
module-mode scratch import and `#check @...`; that probe compiled cleanly in
both sandbox and library modes (8.8 s and 4.9 s). No global build was run.

### Hypotheses and objects

| Node's hypothesis or object | Existing Lean rendering |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]` in the enclosing explicit variable declaration. |
| Finite extension E/Q_ell | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. |
| Valuation ring and chosen uniformizer | The recorded `Padic.coefficientExtensionIntegers l E` and `Padic.coefficientExtensionUniformizer l E`, used by `Padic.coefficientExtensionRing`. They are the dependency's existing choices, not extra inputs. |
| Morphism f:X→Y | `{X Y : Scheme.{u}} (f : X ⟶ Y)` in the explicit variable declaration. |
| Ell invertible on X and Y | The existing proved theorem requires no invertibility hypothesis and applies to all scheme morphisms. Its conclusion specializes unchanged to the node's invertible-ell case, as permitted by STATE's “EXISTING RECORDS OF MORE GENERAL THEOREMS” ruling. No restriction on f, Noetherianity, dimension, separatedness, or base-field datum is introduced. |
| Small pro-etale sites | `Scheme.ProEt` and `Scheme.ProEt.topology`; the actual site has object universe u+1 and morphism universe u. No equality of these universes is imposed. |
| C_(W,n) for positive n | `integralCoefficientSheaf l E W k` uses exponent k+1. Thus k=0 is precisely n=1, not exponent zero. |
| B_W and its projections | `completedIntegralCoefficientSheafUnrestricted l E W = limit (integralCoefficientSheafSystem l E W)`; its projections are `limit.π ... (op k)`. These are completed ring sheaves, not discrete constant integral rings. |
| Canonical coefficient map c_f | `ordinaryIntegralDirectRingMap` is chosen from `ordinaryIntegralDirectRingMap_existsUnique`, with exactly the stated finite-projection equations. Its inverse-image adjoint is c_f. |
| Ordinary module pullback and adjunction | `ordinaryIntegralModulePull`, `ordinaryIntegralModulePush`, and `ordinaryIntegralModuleAdjunction`. Their fixed sheafified Kan-extension adjunction gives the ordinary tensor pullback; no arbitrary map or adjunction is supplied. |
| Unbounded module derived category and q_W | `DerivedCategory (integralTowerModules l E W)` and `DerivedCategory.Q`. No boundedness or constructibility condition appears. |
| P_f and its specified counit epsilon_Q | `ordinaryIntegralDerivedPull l E f` and `ordinaryIntegralPullComplexCounit l E f P.obj`. The latter is built from the actual `totalLeftDerivedCounit`, with the canonical cochain/homotopy localization comparisons. |
| Full category of good Q | `(integralOperationsGoodComplex l E Y).FullSubcategory`. Its predicate is the recorded independent-coefficient K-flatness together with flatness of every term. |
| Strict finite tower with quotient transitions | `integralOperationsPullbackTowerFunctor l E f`, built from `integralOperationsPullbackTransition`; its levels are the specified restricted finite pullbacks of coefficient reductions. |
| H_f(Q)=Cone(1-s)[-1] | `integralOperationsPullbackComplexFunctor l E f`, obtained by applying `integralOperationsRoosFunctor` to that strict tower. |
| Canonical representative comparison lambda_Q | `(integralDerivedPullbackComparison l E f).hom.app P`, with inverse `.inv.app P`. Its defining isomorphism comes from the normalized descent in `integralOperationsWellDefined`. |
| Prescribed chain map alpha_Q | `ordinaryIntegralCompletionChain l E f P.obj`. Its definition is `CochainComplex.mappingCocone.lift` of `ordinaryIntegralProductAugmentation ...` and the literal zero cochain `0`. The product augmentation uses the uniquely specified quotient-generator maps, not just any map with the same projected cohomology classes. |

The common input universe is the convention of the very source declaration named
by this node. All field and scheme sizes can be placed in such a common ambient
universe; the small site's unequal object and morphism universes are retained.
The coefficient and module universe in this specialization is u+1. No new
universe constraint is added to an independent-universe dependency interface.

### Every conclusion, including the resolution and roof formulas

Write O=`ordinaryIntegralDerivedPull l E f`, F=`integralDerivedPullback l E f`,
e=`integralDerivedPullbackComparison l E f`, c_Q=`ordinaryIntegralPullComplexCounit
l E f Q.obj`, and a_Q=`DerivedCategory.Q.map (ordinaryIntegralCompletionChain
l E f Q.obj)`. Composition below uses Lean's left-to-right `≫`.

1. **Existence and uniqueness of the natural transformation.** The existing
   signature is `∃! η : O ⟶ F, ∀ P : Good.FullSubcategory, ...`. Thus η is a
   natural transformation on the entire ambient derived category, not a family
   of arrows indexed only by resolutions. Uniqueness is of that transformation.
2. **Exact canonical counit normalization.** Its predicate is literally
   `η.app (DerivedCategory.Q.obj P.obj) ≫ e.hom.app P = c_P ≫ a_P`.
   This is the node's `lambda_Q ∘ eta = q(alpha_Q) ∘ epsilon_Q`, in Lean's
   composition order. Neither the counit nor e is replaceable by an unspecified
   comparison. Cancelling the isomorphism e yields
   `η_(qQ) = c_Q ≫ a_Q ≫ e.inv.app Q`.
3. **Every quasi-isomorphic resolution p:Q→A.** Put s=`DerivedCategory.Q.map p`.
   Localization makes s invertible, and O.map s is invertible since O is a
   functor. The naturality built into the term `η : O ⟶ F` says
   `O.map s ≫ η_(qA) = η_(qQ) ≫ F.map s`. Therefore its component is exactly
   `inv (O.map s) ≫ c_Q ≫ a_Q ≫ e.inv.app Q ≫ F.map s`.
   In the node's right-to-left composition order this is precisely its displayed
   formula, with every factor present in its specified order. This is a direct
   algebraic consequence of the existing signature; it adds no assumption on A.
4. **Agreement of all resolutions.** Each such expression equals the same
   `η.app (DerivedCategory.Q.obj A)`. For another resolution p':Q'→A the
   canonical comparison is `u = s ≫ inv (DerivedCategory.Q.map p')`.
   Naturality gives `O.map u ≫ η_(qQ') = η_(qQ) ≫ F.map u`. Substituting
   the normalized components proves exactly their compatibility under this
   comparison, including arbitrary good resolutions, not just chosen ones.
5. **Roofs and changes of representative.** For any roof Q←R→Q', let
   `h = inv (q(s)) ≫ q(v)`. Naturality of the same ambient transformation gives
   `O.map h ≫ η_(qQ') = η_(qQ) ≫ F.map h`. Inserting the normalized components
   gives the stated roof formula. Equality of represented derived arrows gives
   equality under O and F automatically. In particular the resolution/roof
   sentences do not require an extra theorem asserting new descent data:
   they are consequences of the natural-transformation type already bound here.
6. **Strict zero shifted coordinate.** `ordinaryIntegralCompletionChain` is the
   actual lift with second input `0`, read at source lines 360–370. The
   normalization refers to that chain map itself. It does not replace it by a
   lift specified only after projection to the unshifted product; this avoids
   the nonuniqueness of a morphism into a derived limit noted in Stacks 08TC.
7. **Scope of the assertion.** The signature neither requires constructibility
   of an input nor asserts constructibility of an output. It does not assert
   `IsIso (η.app K)`. The separate `ordinaryCompletedIntegralPullback` theorem
   later in the source is not rebound, not included in `lean.declarations`, and
   not used for this attachment.

Thus the explicit resolution and roof sentences are already entailed by, and
introduce no additional data beyond, the existing normalized natural
transformation statement. The main existence-uniqueness theorem has exactly the
node's counit-normalized conclusion. It is not a per-degree substitute for a
statement in the derived category.

### Dependency declarations read and used

All 15 statement-dependency nodes, their statements, and their recorded
interfaces were read. The source of each main declaration and its docstring
were opened, along with the constructions used by the normalized theorem.

| Dependency | Module and declarations |
| --- | --- |
| `def-weil-l-adic-coefficient-extension` | `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`, publicly importing `CoefficientExtension` with the integer ring, uniformizer, quotient rings and transitions. |
| `def-weil-scheme-morphism-properties` | A recorded convention with no declaration of its own; use Mathlib `Scheme` and its morphisms. |
| `def-weil-pbc-proetale-site` | `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and its topology. |
| `def-weil-completed-integral-coefficients` | `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: `WeilConjectures.integralConstantToCompletionOfUniverses`, reexporting the actual quotient sheaves, limit completion, projections and module categories from `CompletedIntegralCoefficients`. |
| `def-weil-proetale-inverse-image` | `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`, `proEtaleSheafDirectImage`, `proEtaleSheafAdjunction`. |
| `def-weil-sheaf-of-modules-category` | `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, an abbreviation for Mathlib `SheafOfModules`. |
| `def-pur-sheaf-tensor-product` | `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: `SheafOfModules.cochainModulesMonoidal`, the recorded sheafified localization tensor. |
| `def-weil-abstract-derived-category` | `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`, and the canonical cochain/homotopy comparison. |
| `def-sf-ordinary-integral-pullback-construction` | `Sheaf.Paper.OrdinaryCompletedIntegralPullback`: `WeilConjectures.ordinaryIntegralCompletionChain` and its recorded ring-map, module-adjunction and quotient-augmentation auxiliaries. |
| `def-pur-integral-derived-operations` | `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: `WeilConjectures.IntegralOnSlice.completedTensor`, publicly retaining `IntegralDerivedOperations` with `integralDerivedPullback` and `integralDerivedPullbackComparison`. This item uses that global pullback, not the sibling tensor or a slice replacement. |
| `def-weil-derived-limit` | `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`: `CategoryTheory.IsDerivedLimit`, `IsDerivedLimitTriangle`. The strict Roos cone is the prescribed representative, not an arbitrary choice of a triangle. |
| `lem-weil-pbc-ringed-topoi-derived-pullback` | `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`: `SheafOfModules.ringedTopoiDerivedPullbackIndependent`, its universal counit and resolving-class computation. The existing source specializes this via `ordinaryIntegralPull_hasLeftDerived`, `ordinaryIntegralDerivedPull`, `ordinaryIntegralPullCounit`, `ordinaryIntegralPullComplexCounit`. |
| `def-pc-flat-sheaf-modules` | `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`, exactness of right tensor. |
| `def-pc-kflat-complex` | `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: `CochainComplex.IsKFlatIndependentCoefficients`. |
| `lem-pur-integral-operations-well-defined` | `Sheaf.Paper.IntegralOperationsWellDefined`: `WeilConjectures.integralOperationsWellDefined`, `integralOperationsGoodComplex`, `integralOperationsGoodLocalization`, `integralOperationsPullbackOnGood`, and the actual strict-tower and Roos constructions. |

No recorded dependency requires repair. No private copy of a dependency notion
is supplied. Because this delivery attaches an existing declaration, it does not
alter that module's imports or its proof plan.

### Source and edge cases

Read Bhatt–Scholze Lemma 6.5.9(4) and Remark 6.8.15 from the local PDF using
`pdftotext` to stdout. They provide the completed/ordinary pullback context;
the node explicitly identifies the normalized descent as an agent extraction
at the existing Lean theorem, not as the constructibility result. Also read
Stacks 06YS (flat-term K-flat resolutions for every complex), 0G7D (factorization
through good complexes), 06YY (unbounded derived ringed pullback), and 08TC
(derived-limit triangle and the nonuniqueness of unspecified cone maps), and
Mathlib's localization natural-transformation API. None of these imposes a
Noetherian or boundedness condition on this resolving-class descent.

Checked: zero complex and empty scheme; identity morphism and identity
resolution; arbitrary unbounded A; arbitrary quasi-isomorphic good resolutions;
nonidentity roofs; the smallest positive quotient exponent; ell=2; and scheme
maps without geometric finiteness hypotheses. The source theorem has no
nonzero-object, boundedness, characteristic-away-from-2, or finiteness
restriction. Its arrow has the expected ordinary-to-completed direction even
for the identity morphism: no claim that completion is an isomorphism on every
ambient object is present. The fixed zero cochain is retained for the zero
complex as well as all other inputs. The universe convention preserves the
site's object/morphism distinction; no new independent-universe specialization
is attempted.

### Searches for an existing declaration

- `msearch.py ... leansearch "Natural transformations between derived functors are uniquely determined on K-flat resolutions"`: 8 hits, including `Functor.leftDerivedUnique`, `Functor.leftDerived_ext`, `Localization.natTrans_ext`; generic universal properties, not the specified integral comparison.
- `msearch.py ... leanfinder "A natural transformation from ordinary derived pullback to completed integral pullback is uniquely determined by its canonical counit on flat K-flat resolutions"`: 8 hits, including `Functor.leftDerivedUnique`, `Functor.mapDerivedCategoryFactorsh_hom_app`, `Functor.totalLeftDerivedCounit`; no exact Mathlib integral statement.
- `msearch.py ... loogle "CategoryTheory.Localization.liftNatTrans"`: 10 hits, the generic localization lift and its identities; it does not specify the ring map, quotient augmentation or zero shifted coordinate.
- `msearch.py ... grep "CompletionComparison|completionComparison|liftNatTrans" CategoryTheory`: 25 hits, mainly generic `Localization.liftNatTrans` and path-category variants; no exact integral comparison.
- `rg -n "ordinaryIntegralCompletionComparison_existsUnique|CompletionComparison|completionComparison" lean/WeilConjectures lean/Sheaf`: exact hit at `Sheaf/Paper/OrdinaryCompletedIntegralPullback.lean:504`; related completion comparisons concern different models. Read the complete theorem, docstring, proof, and underlying definitions. Its source place is exactly the one named by the item.
- `grep -rn "lem-tw-integral-comparison-descent" lean/WeilConjectures` and `rg -n -F "lem-tw-integral-comparison-descent" lean/WeilConjectures`: no hits.
- `rg -n "ordinaryIntegralCompletionComparison_existsUnique" dag/lean_names_upstream.json`: no indexed upstream hit; the declaration instead exists in the published Sheaf module above, as confirmed directly by the server.

No statement correction and no STATEMENT-DISPUTED issue. No new nodes or
dependency modules. The already published theorem is reused under the
one-definition-per-notion rule; this delivery makes no claim to have removed
any transitive sorry in that source.

## Second reading by Q51

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
