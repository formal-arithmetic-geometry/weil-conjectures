## Worker report

The item is stated in `Sheaf.Paper.IntegralConstructibleCompactness` as
`AlgebraicGeometry.ProEtale.integralConstructibleCompactness`. Its proof is `sorry`.
The real, Prop-valued definition `IntegralConstructibleCompactnessAssertions` packages
exactly the three clauses of this node; it does not assert them and introduces no
replacement mathematical object. It is listed in `lean.declarations` alongside the theorem.
The original natural statement and dependency list of the item are unchanged.

Hypotheses and conventions:

| Natural hypothesis or object | Lean rendering |
| --- | --- |
| ell is prime | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| field of positive characteristic different from ell | `(k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)` |
| separated finite-type k-scheme | `X : Scheme.{u}`, `X.Over (Spec (.of k))`, and `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` of its structure morphism |
| fixed algebraic closure and finite subextension E | the existing fixed `PadicAlgCl ℓ` and `E : PadicAlgCl.FiniteIntermediateField ℓ`; this is the actual finite intermediate field, not an arbitrary ring |
| condensed ring of integers | `Profinite.padicIntegersRingObj ℓ E`, the abelian ring object underlying `Profinite.padicIntegersCondensedRing ℓ E` |
| coefficient ring R_X and left module sheaves | `condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X` and the existing `CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1})` over that object |
| ordinary unbounded derived category | `DerivedCategory` of that exact internal-module category; no completion, no finite-Tor restriction, no boundedness on general objects |
| Cons and Dbc | recorded `IsConstantModelConstructible` and `constantModelBoundedConstructible`, passed as H and B to the assertion definition |
| choose nonnegative d_C satisfying sk-lem-int-ext(2) | `(d : ConstantModelConstructible ... X → ℕ)` and `hd`, requiring `Subsingleton` of the ambient degree-q derived Hom for every constructible C,N and integer q greater than d C |
| fixed small universe | assertion index universe v specializes to u+1, the module Hom and derived Hom universe; all filtered diagrams and coproduct index sets use it |
| canonical truncations and cohomological shift | `DerivedCategory.TStructure.t.truncLE`, `.truncGE`, and `shiftFunctor _ m`, with H^q(K[m]) = H^(q+m)(K) |

The chosen-bound hypothesis `hd` is the explicit rendering of the node's instruction
to choose bounds satisfying the Ext lemma, not an additional restriction on an arbitrary
object K. The recorded Ext dependency states existence of integer bounds in its own finite-field
setting; taking a maximum with zero gives natural-number bounds there. The assigned
node expressly fixes such a family of bounds, and hd records exactly that premise.

Every conclusion is present in the assertion definition:

1. `Ind H.FullSubcategory` is Mathlib's category of small filtered colimits of
   representables, exactly the equivalent model expressly permitted by the node.
   It allows the locally small full constructible category as input; its presentations
   have small filtered indices, so choosing a small skeleton does not change the notion.
   The existential Phi is characterized by
   `Nonempty (Ind.yoneda ⋙ Φ ≅ H.ι)` and `PreservesFilteredColimits.{v} Φ`.
   Every ind-object is the small filtered colimit of its representables, so this
   characterizes Phi on objects AND arrows as the realization of the diagram by its
   ambient colimit, up to the unique isomorphism respecting its structural maps.
   These are characterization data for the specified realization, not an arbitrary
   functor in place of it. `PreservesFiniteLimits Φ` and `PreservesFiniteColimits Φ`
   are exactness (Mathlib `exactFunctor_iff`). Existence of finite limits and colimits
   in Ind is included in the conclusion, so preservation is not vacuous. `Φ.Full`
   and `Φ.Faithful` give full faithfulness. `Φ.essImage = H.ind.{v}` identifies the
   full replete image with exactly the ambient small filtered colimits of constructibles.
   Extension closure is the implication on `S : ShortComplex A` with `S.ShortExact`
   and first/third objects in H.ind. Kernel/cokernel closure is asserted for every
   ambient arrow f between objects in H.ind. The final conjunct in (1) is vanishing
   of the degree-q ambient derived Hom from C[0] to N[0][q], for N in H.ind and q>d C.
   `Subsingleton` means this abelian group is zero, including negative-degree notation.
2. Dic is expanded everywhere as `∀ n : ℤ, H.ind ((DerivedCategory.homologyFunctor A n).obj K)`.
   For every small family in Dic the sum clause supplies a colimit cofan c and
   requires c.pt to have all cohomology in H.ind. Any other coproduct is canonically
   isomorphic to this one, and H.ind is replete. The truncation clause requires
   membership in H.ind of every cohomology of BOTH tau_le(m) K and tau_ge(m) K,
   for all integers m,n. The containment clause takes `localizingClosure B K` and
   concludes every cohomology is in H.ind. The finite-window clause asserts `IsIso`
   for the actual additive Hom maps induced by shifted `truncLEι m` and
   `truncGEπ (m - (d C : ℤ))` evaluated on tau_le(m) K. The first arrow goes from
   Hom(C,tau_le(m)K[m]) to Hom(C,K[m]); the second goes to
   Hom(C,tau_ge(m-d_C)tau_le(m)K[m]). Invert the first and compose with the second.
   Both arrows are evaluations of natural transformations followed by functors;
   their inverses are natural once invertible. Thus this records the natural
   canonical zigzag isomorphism, rather than a bare equivalence of endpoint groups.
3. The last conjunct supplies `hc : HasCoproducts.{v} (localizingClosure B).FullSubcategory`
   and, for each object C there with B C.obj, the recorded `IsCompactObject` using hc.
   Every B-object belongs to its localizing closure by the definition and the recorded
   minimality theorem. The full-subcategory Hom groups are the ordinary ambient ones;
   the sums are the same ordinary sums because the localizing closure is sum closed.
   Unfolding `IsCompactObject` gives precisely the canonical direct-sum Hom map in the
   node, for every small family, with no bound and no completeness condition.

The exact-functor existence, small coproduct existence, and filtered-colimit preservation
above express the specified realization/sum objects and the meaning of exactness; they
add no geometric assumption or extra independent mathematical conclusion.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and its setting
  documentation. The theorem uses its explicit standing field/scheme binders, rather
  than adding a finite-field datum or assuming a chosen compactification unnecessarily.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicIntegersCondensedRing`, `Profinite.padicIntegersRingObj`; the dependency
  `def-sfb-padic-integers-condensed-ring` is closed upstream, despite having no lean record.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `coefficientRing_X`, `condensedRingObj`, preservation of commutativity.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, and `Mod.Hom`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `Q`; singleFunctor and homologyFunctor from its standard derived-category API.
- `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`: the recorded Ext is the shrunk
  degree-zero-to-shifted-single Hom; the statement uses this underlying integer-graded
  derived Hom directly, as the node's Ext convention and `sk-lem-int-ext` do.
- `Sheaf.Paper.CondensedConstantConstructibility`: `ConstantModelConstructible`,
  `IsConstantModelConstructible`, `constantModelBoundedConstructible`.
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`: public standard truncation API;
  directly `DerivedCategory.TStructure.t.truncLE`, `.truncGE`, `.truncLEι`, `.truncGEπ`
  from `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT` and `TruncLTGE`.
- `def-weil-size-convention` is the recorded metatheoretic convention; it is rendered
  by explicit universe variables, not by an invented Lean object.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cofan`, `IsColimit`, colimit APIs.
- `Mathlib.CategoryTheory.Limits.Indization.Category`: `Ind`, `Ind.yoneda`,
  `Ind.presentation`, `Ind.colimitPresentationCompYoneda`, and the recorded filtered
  colimit creation/existence instances. Also the recorded Ind arrow-presentation lemma.
- `Mathlib.CategoryTheory.ObjectProperty.Ind`: `ObjectProperty.ind`, the same ambient
  IndCons interface already used by the landed proper-unbounded and compactness statements.
- `Sheaf.Paper.IntegralConstructibleExt`: `integralConstructibleExt`, read with its existing finite-field setting (see scope note below).
- `Sheaf.Paper.LocalizingClosureExistence`: `localizingClosure_exists`, using the actual
  `CategoryTheory.localizingClosure` intersection from `Sheaf.Paper.LocalizingClosure`.
- `Sheaf.CategoryTheory.CompactObject`: `CategoryTheory.IsCompactObject`.

Proof-only imports follow the recorded proof-dependency modules: the internal-module
section-sheaf equivalence, the universe-correct ring-sheaf Grothendieck theorem,
Yoneda/derived Ext comparison, pushout short exact sequence, Grothendieck termwise
coproducts, pro-etale products and left completeness, and compact objects being thick.
`sk-lem-int-integral-heart` has no recorded Lean module on the base, so no invented
proof-dependency import is used. Remaining proof leaves are standard Mathlib imported
through these modules. The main theorem docstring follows all fifteen proof steps,
including the explicit unbounded-tail Milnor argument and its transition degrees.

Edge cases checked before drafting and again against the final signatures:

- Empty X and zero constructible C: ordinary full subcategories and zero Hom groups,
  without nonemptiness of X or C.
- Empty coproduct index type: no `Nonempty I`; the colimit cofan and IsCompactObject
  include the zero coproduct.
- Filtered indices are nonempty through Mathlib IsFiltered, as required for Ind.
- d_C=0: the window is [m,m], and hd requires only positive Ext vanishing.
- Negative m: all truncation indices and shifts are integers, with the specified signs.
- N already constructible: its constant filtered presentation lies in H.ind.
- Families with no common lower or upper bound: no bound occurs in the sum or
  compactness clauses. Common lower bounds occur only in the Ext dependency's
  continuity conclusion, where the source requires them.
- General positive-characteristic fields are included, without finite cardinality,
  algebraic closedness, perfection, or equality of site object/morphism universes.

Searches for an existing exact statement (2026-10-18):

- `msearch.py ... leanfinder`: "Integral constructible pro-etale complexes are compact in
  the localizing category and Ind constructible realization is exact fully faithful".
  Eight hits concern unrelated fully faithful condensed functors and etale forgetful
  functors; none state these three conclusions.
- `msearch.py ... leansearch`: "constructible integral sheaves Ind category realization
  exact fully faithful compact in localizing closure". Eight hits include the Ind
  presheaf inclusion and generic essential-image limit closure, not this realization
  in module sheaves or its compactness/window assertions.
- `msearch.py ... loogle`: `CategoryTheory.Ind, CategoryTheory.ObjectProperty.ind,
  CategoryTheory.IsCompactObject`. No match; the hosted index does not know the
  project's IsCompactObject declaration.
- `msearch.py ... grep`: `IntegralConstructibleCompact|integralConstructible_compact|
  integralConstructibleCompact|Ind.*realization`, restricted to CategoryTheory.
  Four matches are unrelated private inductiveStepRealization definitions.
- Local rg of the upstream WeilConjectures and side Sheaf source for compactness,
  IndCons, indConstructible, constantModelBoundedConstructible, the proposed names
  and the exact blueprint id. No exact statement exists. Nearby
  `ConstructibleCompactnessBounded` concerns rational coefficients and a common finite
  interval; `IntegralConstructibleBoundedBelowCompactness` assumes bounded-below families.
  `ProperUnboundedCoproducts` concerns proper direct image, not compact source objects.
  None can replace this node. Existing ObjectProperty.ind and localizingClosure are reused.

Validation: scompile.py compiled the delivered module, including its named-library
imports, with no errors or warnings. Every variable and universe
is explicit (`set_option autoImplicit false`); every line is at most 100 characters.
No new independent node, no item statement correction, and no unresolved statement dispute.

## Dependency scope note

The existing `sk-lem-int-ext` declaration uses a `FiniteFieldDatum`. Reading that node's
OWN statement dependencies shows that this is intentional: `sk-def-sf-setting` fixes
a global finite-field datum with k an algebraic closure of a finite field. Thus that
record is usable for its own node and is not changed under section 1(B).
The assigned item's natural statement instead explicitly cites the more general
`sk-def-sfb-dc-setting` AND instructs one to choose nonnegative bounds satisfying
sk-lem-int-ext(2). Its Lean signature retains that general field and renders the chosen
bounds as d,hd; it neither asserts existence of such bounds over every field nor
silently imposes a finite-field datum. The recorded proof's use of the whole Ext
continuity theorem over this general base therefore needs scope review in stage 3.
This is a proof-input scope gap, not an excuse to strengthen the theorem's field
hypothesis or to restate the Ext dependency with hypotheses different from its node.
No dependency module is delivered. The previous experimental broadening was removed
before delivery after reading sk-def-sf-setting. Only the item's own node and module
and this report are delivered.

## Second reading by Q29

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
