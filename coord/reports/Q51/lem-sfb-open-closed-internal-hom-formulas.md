## Worker report

The delivery states `AlgebraicGeometry.ProEtale.CondensedRing.openClosedInternalHomFormulas`
in `Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom`. All proofs remain `sorry`;
all helper definitions contain real constructions. The source statement is unchanged.
The source was checked in Bhatt--Scholze, Lemma 6.7.13 (the proof's internal-adjunction
calculation), and in Stacks `sites-cohomology.tex`, lemma-restriction-RHom-to-U (08JB).
The excellence and constructibility hypotheses of Bhatt--Scholze's preservation result
are not hypotheses of this separate formal internal-adjunction calculation.

Hypotheses and clauses, matched individually:

- The arbitrary commutative condensed ring is `Λ : Sheaf (coherentTopology Profinite.{u})
  Ab.{u+1}` with `[MonObj Λ] [IsCommMonObj Λ]`. This is the generic ring-object encoding;
  it is not restricted to continuous functions from a chosen topological ring. The
  condensed-ring dependency's current primary declaration constructs a special example;
  its generic notion is already supplied by its ring-object statement and the recorded
  pulled-back coefficient framework, so no private condensed-ring definition is made.
- `Z U X : Scheme.{u}` and `i : Z ⟶ X`, `j : U ⟶ X` are arbitrary scheme data.
  `[IsClosedImmersion i]`, `[IsOpenImmersion j]`, `[QuasiCompact j]` render precisely the
  immersion and quasi-compactness hypotheses. `hij : Set.range i.base = (Set.range j.base)ᶜ`
  says exactly that their images are complementary. There is no qcqs hypothesis on X.
- `supportModules Λ T` unfolds to `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u+1})
  (condensedRingObj Λ T)`. The coefficient is the actual pulled-back ring, not Λ evaluated
  at the point; sectionwise modules and internal module objects agree through their
  action axioms and the balanced coequalizer. `DerivedCategory` is the ordinary
  unbounded localization, with the existing relative derived tensor and `derivedHom`.
- `supportPullback` is the existing inverse-coefficient transport. The real natural
  isomorphism `supportPullbackIsoUpperStar` identifies it with the dependency's exact
  extension-of-scalars `upperStar`. Consequently using it in the formula does not
  replace the coefficient-compatible inverse image. The open adjunction is transported
  by this very isomorphism; the closed inverse/direct adjunction is the recorded
  `supportPullbackAdjunction` derived termwise.
- The open family `o L N` has source `derivedHom Λ X (j!L) N`, where j! is exactly
  `(openImmersionLowerShriek Λ j).mapDerivedCategory`, and target the total
  `(lowerStar Λ j).rightDerivedFunctor` of `derivedHom Λ U L (j^*N)`.
- The closed family `c P N` has source `derivedHom Λ X (i_*P) N`, and target exact
  `(lowerStar Λ i).mapDerivedCategory` of `derivedHom Λ Z P (Ri!N)`. Here `Ri!` is precisely
  `(closedSupport Λ i j).rightDerivedFunctor`, and `closedSupport` is the dependency's
  actual `supportKernel Λ j ⋙ supportPullback Λ i`. The kernel is formed from the actual
  open unit; this is i^* ker(N → j_*j^*N), not an arbitrary right adjoint.
- The last two quantified equations express simultaneous naturality for arbitrary
  `a : L' ⟶ L` (respectively `P' ⟶ P`) and `b : N ⟶ N'`. The opposite maps in the first
  input and ordinary maps in the second give exactly contravariance/covariance.
- The second and third conjuncts identify the isomorphism homs with `openSupportHomMap`
  and `closedSupportHomMap`. These real definitions apply tensor-Hom evaluation,
  projection, and the actual four adjunction transposes. Thus the normalization is
  part of the signature, not only its docstring. The auxiliary closed projection
  isomorphism `p` has hom fixed in the first conjunct to the explicit unit-induced map
  `closedSupportProjection`. The closed comparison correctly uses the unit
  id → i_*i^*, the pullback tensor map and the counit i^*i_* → id, then its inverse in
  the Hom construction. No counit i_*i^* → id is invented.
- There is no boundedness, completion, constructibility, finite Tor amplitude, or
  invertibility condition on L,P,N. Internal Hom remains an object of the sheaf-valued
  derived category; the theorem is not merely a global Hom-group bijection.
- Site objects remain in `Type (u+1)` and morphisms/modules in the framework's `u`/`u+1`
  levels. No site object/morphism universe equality is imposed. The convention node is
  metatheoretic and its recorded Lean interface explicitly requires no new definition.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`: the generic sheaf/ring-object setting and
  the recorded `Profinite.isCommMonObj_continuousCoefficientRingObj` example (read, not substituted
  for arbitrary Λ).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, `condensedPullbackHom`, its isomorphism instance and commutative
  ring-object structure. `coefficientRing` is `mapMon` of pullback from the point.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`: `derivedHom`,
  `derivedTensorHomAdjunction`, and `derivedTensorHomAdjunction₂`; these are internal
  Homs for the existing K-flat relative tensor, with localization's actual lax tensor map.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`: `upperStar`,
  `lowerStar`, their coefficient actions, exact inverse image and their adjunction.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `openImmersionLowerShriek`, its forgetful equality and exactness; the definition is
  scalar restriction along alpha followed by linear extension by zero.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek`:
  `derivedOpenImmersionLowerShriekUpperStarAdjunction` was read; the delivered exact
  adjunction is obtained from `openImmersionLowerShriekUpperStarAdjunction` by canonical
  coefficient transport and the exact-left/right-derived adjunction API.
- `Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction`: `supportModules`,
  `supportPullback`, `closedSupport`, `closedSupportDerivedAdjunction`,
  `closedSupportOpenDerivedAdjunction`, and `supportPullbackAdjunction`. These use the
  canonical coefficient map and kernel/unit/counit normalizations.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded total
  right-derived interface. The support dependency already identifies it uniquely and
  unit-compatibly with the upstream `rightDerivedFunctor` used in the statement;
  the latter has canonical K-injective representative comparisons.
- Mathlib `Scheme`, `Scheme.Hom`, `IsClosedImmersion`, `IsOpenImmersion`, `QuasiCompact`,
  `Scheme.ProEt`, its topology, and `DerivedCategory`. Their defining signatures and
  docstrings were checked in the supplied source tree. Finite type of either immersion
  is not added: only quasi-compactness of j is used from that multi-notion dependency.

All available proof-dependency modules are imported without `public`, unless already
exported by a statement dependency. The imports preserve the node's full eleven-step
proof plan (module-object/section-module comparison, localization, canonical projections,
coproducts, totalization, K-flat preservation, descent, derived adjunctions, the two
three-variable Hom calculations and their representing maps). Nodes with no recorded
module contribute no invented import. The theorem docstring contains all eleven steps.

Edge cases checked before writing: empty Z, empty U, a surjective closed immersion
including a nilpotent thickening, zero coefficient ring, zero input objects, degree-zero
complexes, and arbitrary unbounded complexes. For empty Z the closed sides vanish; for
empty U the open sides vanish. Nilpotent thickening is compatible with pro-etale
invariance and the given support construction. Zero modules and zero coefficients make
the evaluation identities maps between zero objects. No assumption excludes these cases.

Searches (actual results are retained in sandbox searches.jsonl):

- LeanFinder: “Derived internal sheaf Hom from open extension by zero and closed direct
  image with sections with closed support” returned eight section/restriction results,
  including `TopCat.Sheaf.restrictHomEquivHom` and scheme section maps; no derived formula.
- Loogle: `CategoryTheory.ihom.adjunction, CategoryTheory.MonoidalClosed.internalHom`
  returned `MonoidalClosed.internalHomAdjunction₂_adj`; no immersion formula.
- Mathlib grep: `internalHom|projectionFormula` in CategoryTheory/Monoidal returned 15
  generic internal-Hom declarations; no condensed open/closed identity.
- Project/source rg: the item id, `closedSupport.*[Hh]om`, `openImmersion.*[Hh]om` found
  the existing global support Hom-complex theorem and finite-coefficient open material,
  but neither of these two condensed internal sheaf-valued unbounded isomorphisms.
  `ClosedSupportHom` is an étale finite-ring/global-Hom interface and is not this theorem.
- The additional helper searches and absence of a condensed comparison node are detailed
  below. No declaration with the new exported names exists in Mathlib or the source.

Validation: every delivered file is checked separately in dependency order by the
prescribed `scompile.py` wrapper; dry-run preflight and final delivery use `deliver2.py`.
There is no statement correction or disputed mathematical clause.

## New nodes

`def-sfb-condensed-pullback-tensor-comparison` supplies the missing canonical comparison
on the actual condensed module categories. Its ordinary isomorphism is uniquely fixed by
the balanced-tensor coequalizer equation. Its derived isomorphism is uniquely fixed by
naturality and a square on every pair of complexes, with the unique chain map prescribed on each
total-tensor summand. `SupportComplexTensorNormalization` records those summand equations;
`existsUnique_supportComplexTensorComparison` specifies its unique chain map and
`supportComplexTensorComparison` constructs it from that uniqueness. The localization
square is written once as `SupportTensorDescentSquare`, with explicit tensor objects
and maps, and instantiated with the actual localization maps and exact-functor factorization. This supplies both representative and ordinary normalization; no
arbitrary isomorphism or extra tensor-comparison hypothesis is used. Choices are from
uniqueness theorems specifying the complete comparison, as the contract allows.
The source is Stacks 03EL, 06YL, 06YS and 0G7D, implementing steps 3--7 of the item's proof.
The node also exports the existing alpha scalar-transport isomorphism and real small-
colimit/complex-tensor instances.

DAG rg and `blueprint_refs.py search 'condensed pullback tensor'` found no definition node
of this condensed comparison (the latter returned zero blueprint nodes). General ringed-
site comparison nodes use `SheafOfModules` and have no directly usable Mod-object map;
the finite-coefficient counterparts concern different coefficient categories. Mathlib
LeanSearch for “The canonical derived pullback tensor comparison for module objects over
a commutative condensed ring” returned eight generic pullback/free-module interfaces.
LeanFinder for “A canonical pullback relative tensor comparison for condensed module
objects characterized by balanced tensor generators and total complexes” returned eight
LightCondensed projectivity/tensor results. Mathlib grep `leftDerivedTensorComparison|tensorObjπ`
in CategoryTheory returned zero hits. Source/project rg confirmed that only the general
exact strong-monoidal functor comparison exists upstream; it presupposes a module-object
monoidal pullback structure absent here. The new comparison uses existing relative-tensor
coequalizers and localization maps, rather than copying a coefficient ring, module
category, derived tensor, internal Hom, or derived inverse/direct-image construction.

## Second reading by Q51

This second reading is the writing worker’s self-check; independent review belongs to
the maintainer under the current dispatcher brief.

I reread the saved item, its current dependency records, both modules, and the new node.
The item changes only `lean` and adds the comparison definition to `stmt_deps`.
The two internal-Hom families use the same arbitrary commutative condensed coefficient,
the complementary immersions and precisely the stated quasi-compactness hypothesis.
The explicit map equations retain evaluation/adjunction normalization and simultaneous
naturality. No boundedness or coefficient restriction was introduced.

The resumed dry run first rejected two unregistered diagnostic modules. They are retained
as text under `scratchpad/`, outside the delivery. The subsequent compile exposed a timeout
in the derived comparison normalization. The repair passes the actual localization tensor
maps as explicit arguments to `SupportTensorDescentSquare` and names the candidate family
once as `SupportDerivedTensorComparisonFamily`. These change how the identical square and
family are expressed; the ordinary balanced-generator equation, every total-complex
summand equation, and the localization equation remain present. All choices still come
from uniqueness assertions. I also added the previously unlisted
`SupportComplexTensorEquations` to the helper declaration inventory and updated the
condensed-ring import to the module in its current dependency record, and included the
now-recorded proof dependency `Sheaf.Paper.ModuleObjects`.

This is the writing worker's self-check. The maintainer performs the independent review;
no independent reader was started, as required by this dispatcher's brief.

The full packet compile also found that the saved open/closed Hom-map definitions used
the inverse direction of their outer adjunction bijections. I changed these two outer
transposes to the forward `homEquiv`: restriction-Hom to pushforward-Hom for the open map,
and closed-inverse-image-Hom to closed-direct-image-Hom for the closed map. The inner
tensor-Hom and support transposes, and both stated target isomorphisms, are unchanged.


The final performance repair uses the existing upstream `derivedTensor` functor explicitly
for all tensor objects and maps. Cochain tensor objects are the existing
`HomologicalComplex.tensorObj`; no additional monoidal data instance is exported.
Only colimit/tensor-existence propositions are supplied as shortcut instances. The two
exact adjunctions are obtained with `mapDerivedCategoryRightDerivedAdjunction` and the
canonical `rightDerivedFunctorIsoMapDerivedCategory` of the exact right adjoint. The
open underived adjunction is first transported along `supportPullbackIsoUpperStar`.
This gives the same units/counits without invoking the general K-flat left-derived API.
The formulas, canonical maps and all hypotheses remain unchanged.


Final production validation: the delivery wrapper compiled both files, including their
library-path copies, without errors or warnings other than the expected `sorry` warnings.
The first complete preflight required the helper's recorded signature to start at the
`def` keyword (its `noncomputable` modifier is outside the recorded signature); corrected.
The declaration inventories were checked against both files, and the item differs from
the repository only in `lean` and the added comparison `stmt_deps` entry.


Repair retry, 2026-10-18: I first read this retained packet and ran the required
`deliver2.py --no-push`. Its local preliminary helper check timed out, but its automatic
confirmation against the current server sources passed, and the wrapper printed
`OK (dry run): commit ade26dd1ce passes the preflight and compiles`. As instructed, I retained
the saved tensor-comparison performance repair rather than restarting it.

The final self-check found one dependency-record update since the saved report:
`sk-def-sfb-condensed-ring` now records `Sheaf.Topology.ProfiniteCondensedRing` and
`Profinite.CondensedRing`. I read its full definition: it abbreviates `Mon` on the same
abelian sheaf category already used here and publicly reexports the continuous-coefficient
module. I updated the item's public import to that recorded module. The arbitrary
commutative ring binders, both derived internal-Hom formulas, all normalization equations
and all universe levels are unchanged. The saved node differs from the current repository
only in `lean` and the added tensor-comparison statement dependency; no repair note is
present for the item. This is the writing worker's self-check, not an independent review.
