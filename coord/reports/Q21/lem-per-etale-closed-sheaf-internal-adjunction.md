## Worker report

Item: `lem-per-etale-closed-sheaf-internal-adjunction`. The delivery states
`AlgebraicGeometry.Etale.etale_closed_sheaf_internal_adjunction` in
`Sheaf.AlgebraicGeometry.EtaleClosedSheafInternalAdjunction`. Its only proof is `sorry`.
Three helper definitions assemble the two actual internal-Hom bifunctors and the
specified inverse comparison. All their data are existing functors and evaluation maps;
there is no choice of an unspecified isomorphism and no postponed data definition.
The original node changes only in `lean`.

Hypothesis-by-hypothesis and clause-by-clause reading:

| Node | Lean rendering |
| --- | --- |
| Arbitrary schemes X,Z,U | `{Z U X : Scheme.{u}}`; no Noetherian or finiteness assumption |
| Arbitrary commutative ring A | `(A : Type (u + 1)) [CommRing A]` |
| Closed immersion i | `(i : Z ⟶ X) [IsClosedImmersion i]` |
| Complementary open immersion j | `(j : U ⟶ X) [IsOpenImmersion j]` and `hij : Set.range i.base = (Set.range j.base)ᶜ` |
| Small etale sites | `X.smallEtaleTopology`, `Z.smallEtaleTopology` and the corresponding `upperStar`/`lowerStar` functors |
| Modules over the constant sheaf A_T | `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)`, the existing constant-coefficient encoding |
| P(F)=ker(F→j_*j^*F) with the actual unit | `kernel (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit`, a kernel in the functor category, hence pointwise with its induced maps |
| i!_0F=i^*P(F) | The composite of this kernel functor with `upperStar (ModuleCat.{u + 1} A) i`, written inline |
| i_* exact | `PreservesFiniteLimits (lowerStar ... i)` and `PreservesFiniteColimits (lowerStar ... i)`; these additive functors act between abelian sheaf categories |
| i_* left adjoint to the specified i!_0 | The existential `a : lowerStar ... i ⊣ kernel ... ⋙ upperStar ... i` |
| Actual support inclusion | The displayed equation `unit_i.app (P.obj F) ≫ a.counit.app F = (kernel.ι unit_j).app F` for every F fixes c_F as q_F^{-1} followed by the kernel inclusion |
| Preservation of injectives | `∀ I, Injective I → Injective ((kernel ... ⋙ upperStar ... i).obj I)` |
| Hom(i_*G,F) | `etaleClosedSheafHomSource A i`, using `Functor.uncurry.obj MonoidalClosed.internalHom` |
| i_*Hom(G,i!_0F) | `etaleClosedSheafHomTarget A i j`, using the same ordinary internal Hom on Z and then `lowerStar ... i` |
| Natural isomorphism for every G,F | `∃ e : etaleClosedSheafHomSource A i ≅ etaleClosedSheafHomTarget A i j`; the domain is the product of the opposite G-category and the F-category |
| Inverse induced by support inclusion | `e.inv.app (op G,F) = etaleClosedSheafHomComparison A i j a G F` for every G,F |
| Slice support-adjunction formula | The comparison curries the lax tensor map of i_*, pushed-forward evaluation, then c_F. On V this sends the local map k to i_V*k followed by c_F restricted to V, precisely the required inverse formula. This fixes the entire slice bijection, not just its global sections. |
| Further etale restriction and maps of F,G | Each component is a sheaf morphism and e is a natural isomorphism of the two bifunctors, so both compatibilities are included |
| A-actions, including local scalar sections | Components are morphisms of ModuleCat-valued sheaves. Local sections of the constant ring sheaf are locally constant scalars, so this is exactly linearity over A_X, not just additivity |
| No finiteness on coefficients/sheaves | No finite ring, finite presentation, constructibility, boundedness, or finite Tor assumption appears |

The object, morphism and coefficient sizes are the ordinary upstream SixFunctors convention:
X has universe u, its etale site has objects in u+1 and morphisms in u, and module
values lie in u+1. The statement does not equate the two site universes. Any ring
of a smaller universe is represented by its usual lift to the coefficient universe;
no restriction on cardinality relative to a fixed external coefficient universe is asserted.

Why the ordinary tensor-Hom object is the recorded sheaf Hom: the imported
`SheafOfModules.homObj` is module maps on each slice, as its full source/docstring says.
For constant coefficients the equivalent ModuleCat-valued encoding has the same
slice module maps. The existing `monoidalClosed_sheaf_of_essentiallySmall` is Day
reflection of the enriched presheaf Hom, not a derived Hom and not pointwise Hom
of the section modules. Its adjunction is tensor-Hom for the sheafified ordinary
tensor. A map from a sheaf tensor product is exactly a compatible family of
bilinear maps on sections. Restricting to V and evaluating at the generator of
the free rank-one A-module identifies sections of this internal Hom with maps
between the restricted module sheaves. The evaluation map sends (g,k) to k(g).
Consequently the formula chosen for `etaleClosedSheafHomComparison`, after the
lax direct-image tensor map and the support counit, sends k to c_F i_*k on every
slice, as required by the node. No new internal Hom, coefficient module category,
or support-kernel functor is defined. In particular the published downstream
`perEtaleSupportKernel` and `perEtaleClosedSupport` definitions are not copied or
imported, which avoids an import back into that consumer.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `Scheme.smallEtaleTopology`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent alias of the existing ringed-site module category. The statement uses
  the equivalent constant-coefficient ModuleCat-valued encoding already used by
  its recorded inverse/direct image functors; it does not redefine the category.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`,
  `Etale.lowerStar`, and `Etale.upperStarLowerStarAdjunction` with their full
  constant-coefficient signatures and actual units.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`: `SheafOfModules.homObj`;
  see the preceding comparison of its slice definition with ordinary tensor-Hom.

The modules of the recorded proof dependencies are imported as non-public imports:
`EtaleSupportedKernelAdjunction`, `EtaleClosedImmersionEssentialImage`,
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`,
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`,
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, and Mathlib's
`ModuleCat.Sheaf.PushforwardContinuous`. The remaining geometric Mathlib proof
inputs (etale composition/cancellation, finite-limit base change, closed-immersion
base change) are already supplied by these imports. The docstring contains all
seven DAG proof steps, including the normalized slice comparison b_V and both
inverse formulas. No stage-3 proof is supplied.

Edge cases checked before writing and on rereading:

- Z empty and U=X: the support kernel and the closed Hom sheaves are zero;
  Hom from the zero pushed-forward sheaf is the zero module sheaf.
- Z=X and U empty: the support kernel is the identity up to its canonical iso;
  the normalized counit and internal-Hom comparison give the identity formula.
- X empty: all module sheaves and all displayed arrows are unique; no nonempty
  index, point, or covering is assumed.
- Zero ring A and zero G or F: the formulas use unital module structures and
  evaluation and apply unchanged; no Nontrivial hypothesis occurs.
- Nonreduced closed immersions: etale support depends on the underlying closed
  subset, while i itself is the original scheme morphism. No reducedness assumption.
- Arbitrary infinite A and non-finitely generated G,F: tensor-Hom and the support
  factorization require no finite presentation. No finite-product argument is used.

Searches (the wrapper's exact results are in `searches.jsonl` in the task sandbox):

- msearch leanfinder, `closed immersion etale sheaves modules internal Hom right
  adjoint sections with support`: eight hits for general scheme-module restriction,
  pushforward and ideal adjunctions, none for this closed etale internal formula.
- msearch loogle, `SheafOfModules.homObj, SheafOfModules.pushforward`: no hits;
  Loogle reports unknown identifier `SheafOfModules.homObj` (it is project-side).
- msearch leansearch, `closed immersion module sheaves sections with support
  internal Hom adjunction`: eight hits for ordinary open restriction adjunctions
  and the definition of a closed immersion; no exact statement.
- msearch grep, `supportedKernel|closed.*Adjunction|support.*[Aa]dj|homObj` in
  `Algebra/Category/ModuleCat`: no Mathlib hit.
- rg of the item id and `supportedKernel|closed.*Adjunction|support.*[Aa]dj`
  in the read-only upstream WeilConjectures source: pro-etale support and ordinary
  tensor-Hom adjunctions only. No exact etale closed sheaf theorem.
- rg in `lean/Sheaf` for supported kernels, closed internal adjunction and ordinary
  Hom: the abelian support adjunction is narrower, the ringed/pro-etale support
  lemmas are on another site, and `EtaleInternalHomLocalization` is the derived
  consumer. Its actual kernel expressions are reused inline, without copying its
  definitions or importing its theorem.
- Read the ordinary internal Hom, presheaf internal Hom, sheaf monoidal construction,
  `GrothendieckAbelian.Monoidal.TensorColimits`, and the direct-image lax tensor
  construction to check that ordinary enriched/sheaf Hom is being used.
- Source checked locally: `literature/stacks-project/etale-cohomology.tex`,
  Section 09XP and lemma `lemma-sections-with-support-acyclic` (09XQ), including
  its displayed support Hom adjunction and exactness/injectivity argument.

Validation: prescribed `scompile.py Q21 lem-per-etale-closed-sheaf-internal-adjunction
<file>` compiled both sandbox and named library module cleanly, 2.9 seconds each.
An initial missing coefficient-instance import was corrected to the existing
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`; no added hypothesis was
needed. All lines are at most 100 characters, every variable/universe is bound,
and the only postponed declaration is the named theorem matching this DAG node.
No statement dispute, correction, new node or dependency-record repair is needed.

## Second reading by Q21

I reopened the original JSON and the compiling module for a separate rereading;
the dispatcher forbids starting another agent, so this is a worker self-check,
not a claim of independent review. Independent review belongs to the maintainer.

The binders preserve the arbitrary scheme and commutative ring, both immersions,
and the complement equality. The functor uses the actual adjunction unit and
actual kernel, in the original module categories. The two finite-preservation
clauses state exactness, the existential adjunction uses the same support functor,
and the injectivity clause uses `Injective` in that module category, never
injectivity after forgetting scalars. Both internal-Hom variables are unrestricted
and the natural isomorphism is on their product category with G opposite.
I checked the direction: e goes from Hom(i_*G,F) to i_*Hom(G,H(F)); e.inv is the
counit-induced map. The helper uses i_* of evaluation following its lax tensor
map and then the normalized support counit, so this is the node's prescribed
inverse on every slice. Sheaf-morphism and natural-isomorphism types include
restriction, both variable maps, and scalars. The clause table above covers every
sentence of the original statement. No mismatch or statement change was found.
