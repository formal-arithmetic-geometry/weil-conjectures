## Worker report

Item: `lem-exc-proetale-closed-exact`. Existing statement attachment, with no delivered Lean
module and no change to the natural-language statement, dependencies, or proof plan.

The declaration is
`AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_isCompl` in
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion` (source line 178).
Its public import `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` supplies
`AlgebraicGeometry.ProEtale.preservesFiniteLimits_lowerStar` (line 204). Both declarations
are recorded in `lean.declarations`. The former gives right exactness and the latter gives
left exactness of precisely the same functor. Mathlib's `CategoryTheory.exactFunctor_iff`
identifies their conjunction with exactness as defined by `def-galois-exact-functor`.
This records the whole conclusion; it does not equate finite-colimit preservation alone
with the definition of an exact functor.

The theorem is already explicitly labelled with this blueprint id. Its coefficient ring
is arbitrary, so its specialization to finite rings proves exactly the stated case.
The existing theorem's greater coefficient generality needs neither a statement correction
nor a second theorem. A temporary finite-ring `exactFunctor` formulation compiled cleanly,
but it is not delivered: the existing theorem plus the public left-exactness instance
supply this interface already. No new category, coefficient map, or functor is defined.

This is only a stage-2 attachment. In the archived checkout the existing proof passes through
`isIso_upperStarLowerStarAdjunction_counit`, which contains `sorry`; neither compilation
nor this attachment claims proof closure. The second reading found that the current server
source has since repaired that counit, with the same exactness signature. The DAG's seven-step covering-lift proof is
retained verbatim for stage 3. In particular, the existing source's counit-based argument
is not substituted into the DAG proof.

### Hypotheses and conclusion, clause by clause

The source's surrounding variables, checked in its full declaration signature, are
`{R : Type (u + 1)} [Ring R] {Z U X : Scheme.{u}}`, followed by the morphisms and instances
below. All universes are those of the published interface; no equality between object
and morphism universes is imposed.

| Node text | Existing Lean rendering |
| --- | --- |
| A scheme morphism `i : Z → X` | `{Z U X : Scheme.{u}} (i : Z ⟶ X)` |
| A closed immersion | `[IsClosedImmersion i]` |
| Its complementary open immersion | `(j : U ⟶ X) [IsOpenImmersion j]` together with `hij : IsCompl (Set.range i.base) (Set.range j.base)` |
| The open immersion is quasi-compact | `[QuasiCompact j]`, a relative condition on this actual open immersion |
| A finite constant coefficient ring | Specialize `{R : Type (u + 1)} [Ring R]` to `[Finite R]`; no commutativity or nontriviality is needed |
| All pro-etale module sheaves | `Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R)` and the corresponding category on `X`; no finiteness condition is put on the module values |
| Direct image `i_*` | `ProEtale.lowerStar (ModuleCat.{u + 1} R) i`, written `(i)_*[ModuleCat.{u + 1} R]` in the source |
| Exactness | The primary theorem gives `PreservesFiniteColimits`; the listed general instance gives `PreservesFiniteLimits`; `exactFunctor_iff` is their conjunction |

`lowerStar` is not an arbitrary map or replacement for the module direct image. Its full
source docstring and definition were read: it is precomposition with the opposite of
`MorphismProperty.Over.pullback @WeaklyEtale ⊤ i`. Its sections are
`G(W ×_X Z → Z)`, and its morphisms are the same sectionwise linear maps after
precomposition. Thus its scalar action is the prescribed constant `R`-action.
A module-valued sheaf is the fixed-scalar presentation of modules over the constant ring
sheaf: constant scalars act by the given module structures, their locally constant
extensions are obtained by gluing, and sheafification gives the action of the constant
ring sheaf. This uses the whole module category, not constructible modules or finite
stalks. The recorded operations module publicly exposes this existing fixed-scalar
interface as well as its intrinsic coefficient realization.

### Recorded statement dependencies read and reused

| Dependency | Recorded module and declaration used |
| --- | --- |
| `def-pc-scheme` | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom` |
| `def-weil-closed-immersion` | `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion` |
| `def-weil-open-immersion` | `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion` |
| `def-weil-finite-type-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, with `Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`; only quasi-compactness is used, no locally-finite-type binder is added |
| `def-weil-pbc-proetale-site` | `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `Scheme.proEtaleDerivedCategory`; its definition uses exactly `Scheme.ProEt.topology`, on the same small weakly-etale site |
| `def-weil-sheaf-of-modules-category` | `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the abbreviation for Mathlib `SheafOfModules`; fixed constant coefficients use the existing equivalent `ModuleCat`-valued sheaf presentation |
| `def-weil-pbc-proetale-operations` | `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`: `Scheme.sfIntrinsicDerivedPullback` and its publicly reexported operations; the theorem uses the already existing `ProEtale.lowerStar` in `UpperLowerStar.Defs` |
| `def-galois-exact-functor` | Mathlib match `Mathlib.CategoryTheory.Limits.Preserves.Finite` and `Limits.ExactFunctor`: `PreservesFiniteLimits`, `PreservesFiniteColimits`, `CategoryTheory.exactFunctor_iff` |

Every statement dependency has a recorded declaration or Mathlib match. No dependency node
is restated, and no dependency record is changed. The delivered attachment introduces no
module whose proof imports must be assembled. Source declarations and docstrings were
read in both source checkouts where applicable; the pro-etale framework documentation
`coord/pefw-upstream-framework.md` was also read.

### Sources and edge cases

Read the node's statement and all seven proof steps, the current blueprint statement and
proof under `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/`, and Stacks
`proetale.tex`, `lemma-closed-immersion-complement-retrocompact-exact` (Tag 09BM).
The latter says that a closed immersion with retrocompact open complement has exact
direct image. For an open immersion, retrocompactness of its image is exactly the
quasi-compactness of the immersion. Tag 09BK supplies the covering-extension geometry.
The node's external Tag 09A9 is the surrounding section; its split proof already gives
the precise Tag 09BM. No correction to the node is necessary.

Checked edge cases: the zero ring is allowed by `Ring R` (there is no `Nontrivial R`);
noncommutative finite rings are allowed by `Ring`, not restricted to `CommRing`. Infinite
module values are allowed in `ModuleCat`. The empty scheme, empty closed part, and empty
open complement are not excluded. When `Z` is empty, direct image is the zero module
sheaf; when the complement is empty, the theorem also covers nonreduced closed
thickenings. There is no assumption that `X` or `U` is globally quasi-compact, Noetherian,
separated, reduced, or of finite type. `IsCompl` requires exactly disjoint ranges with
union all of `X`, including these empty cases. No characteristic is excluded. The site
object universe remains `u+1`, its morphism universe `u`, and module values lie in `u+1`.

### Searches

All searches used the prescribed `msearch.py Q07 lem-exc-proetale-closed-exact` wrapper
where applicable; its raw results are in the sandbox `searches.jsonl`.

- LeanFinder: "Direct image along a closed immersion with quasi compact complement is
  exact on all pro etale module sheaves over a finite constant ring". Eight Mathlib hits,
  including `Profinite.NobelingProof.succ_exact`, scheme module pushforward faithfulness,
  and unrelated exactness facts; no pro-etale exactness theorem.
- Loogle: `CategoryTheory.Limits.PreservesFiniteLimits,
  CategoryTheory.Limits.PreservesFiniteColimits`. Twelve general exact-functor hits,
  including `CategoryTheory.exactFunctor_iff`, `ExactFunctor.of`, and
  `Functor.exact_tfae`; no geometric specialization.
- LeanSearch: "A closed immersion with quasi compact open complement has exact direct
  image on all proetale module sheaves". Eight closed-immersion geometry hits;
  no direct-image exactness theorem.
- Mathlib grep: `[Cc]losed.*[Ee]xact|preservesFiniteColimits_lowerStar_of_isCompl`.
  Twenty-five broad-text matches, none giving this pro-etale theorem.
- `rg` in the upstream project and `lean/Sheaf` for closed exactness, `lowerStar`,
  and `preservesFiniteColimits_lowerStar_of_isCompl`; literal node-id search in upstream.
  Found the exact blueprint-labelled theorem in
  `WeilConjectures/SixFunctors/ProEtale/UpperLowerStar/ClosedImmersion.lean`, its
  public left-exactness instance, and downstream uses in localization and adic modules.
  `lean/Sheaf` has more specialized ambient closed-support statements with additional
  hypotheses; none is needed. The upstream name-index search yielded no additional
  exactness declaration. The new finite-ring `exactFunctor` name had no prior occurrence;
  the draft was discarded in favor of this existing interface.

No `STATEMENT-DISPUTED` issue, new node, dependency module, or statement correction.

### Validation

The finite-ring draft compiled cleanly through `scompile.py`; it is scratch work only.
The existing-declaration probe and the required `deliver2.py --no-push` dry run check the
actual delivered attachment. The second reader supplies the independent reading and
performs delivery; this worker does not write their section or push.


## Second reading by Q07

I independently opened the node, all eight statement-dependency records, their defining
signatures, the existing theorem and its surrounding section variables, the framework
note, and the blueprint statement and proof. I also read Stacks `proetale.tex`, section
`section-closed-immersion`, especially `lemma-closed-immersion-affines` (09BK) and
`lemma-closed-immersion-complement-retrocompact-exact` (09BM). The tag table confirms
09A9 is the surrounding section. It has no ambient Noetherian, separated, characteristic,
finite-type, or global quasi-compactness assumption. The source theorem assumes exactly
a closed immersion and a retrocompact complementary open.

The statement inventory, matched to the actual Lean signatures, is:

| Object, hypothesis, or conclusion | Lean rendering and independent verdict |
| --- | --- |
| Schemes Z and X, arbitrary | `{Z U X : Scheme.{u}}`; exact, using Mathlib's locally ringed space with local affine charts. The extra U names the complementary open already present in the node. |
| A morphism i from Z to X | `(i : Z ⟶ X)`; exact, with the recorded `Scheme.Hom`. |
| i is a closed immersion | `[IsClosedImmersion i]`; exact: closed embedding and surjective stalk maps, equivalent to the recorded sheaf-surjection definition. |
| The complementary open immersion j | `(j : U ⟶ X) [IsOpenImmersion j]` and `hij : IsCompl (Set.range i.base) (Set.range j.base)`; exact. IsCompl says the two ranges are disjoint and exhaust X; this names any representative of the complementary open subscheme. |
| That immersion is quasi-compact | `[QuasiCompact j]`; exact. On compact open subsets of X this says their inverse images are compact, precisely retrocompactness of the open image. It does not require U or X globally quasi-compact. |
| Finite constant coefficient ring A | Specialize `{R : Type (u + 1)} [Ring R]` to `[Finite R]`. The existing declaration proves the same assertion for arbitrary rings, hence includes every finite-ring instance without changing the node. In particular it specializes to commutative finite rings in the recorded ringed-site interface. |
| All module sheaves on Z and X | `Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} R)` and its X counterpart; exact fixed-scalar presentation. There is no finite-stalk, constructibility, local constancy, or cohomological boundedness condition. |
| The specified direct image i_* | `ProEtale.lowerStar (ModuleCat.{u + 1} R) i`; exact. The definition is precomposition by the opposite weakly-etale base-change functor, so sections are `G(W ×_X Z)` and the same R-linear maps. This is the canonical direct image, not a free functor parameter. |
| i_* is exact | The primary `preservesFiniteColimits_lowerStar_of_isCompl` together with the recorded `preservesFiniteLimits_lowerStar` gives both required clauses for this same functor. `exactFunctor_iff` is definitionally their conjunction. Verified by compiling a consumer with precisely the finite-ring hypotheses, not by treating right exactness alone as exactness. |

The quantifier order is ring, schemes, immersion i, complementary immersion j, and the
complement equation, followed by preservation on the entire module-sheaf category.
No sheaf or sequence is fixed before these choices. All these variables are explicitly
bound in the compiled consumer under `set_option autoImplicit false`.

For dependency identity, I opened `Scheme`, `IsClosedImmersion`, `IsOpenImmersion`,
`QuasiCompact`, `PreservesFiniteLimits`, `PreservesFiniteColimits`, and `exactFunctor_iff`
in Mathlib. I opened `ringedSiteModules`, `proEtaleDerivedCategory`, and
`sfIntrinsicDerivedPullback` in their recorded Sheaf modules and followed the operations
module's public imports to the finite-coefficient and intrinsic realization interfaces.
The small site in both presentations is literally `Scheme.ProEt.topology`. The intrinsic
module category is Mathlib `SheafOfModules` for the sheafified constant ring, and the
published `sfIntrinsicModuleEquivalence` realizes exactly fixed-scalar module sheaves
(with the canonical ULift for small coefficients). Extending constant scalar actions
locally and gluing gives this equivalence; precomposition direct image retains those
same actions. Thus this existing fixed-scalar theorem has the node's objects, rather
than an unrelated notion suggested by a similar name. No new dependency module or
new definition node is needed, so H12/H13 introduce no additional obligations.

Edge cases checked independently: the zero ring and zero module sheaf are admitted
(no Nontrivial binder); arbitrary, including infinite, module values are admitted;
empty X, empty Z, and empty U are admitted by IsCompl. For empty Z the empty covering
forces zero sections, so direct image is the zero module sheaf. Empty U allows a
surjective closed thickening, not only an identity or reduced scheme. Finite limits and
colimits include the empty diagram, hence the zero object case is covered. There is no
integer n or characteristic restriction. For schemes in universe u the small site has
object universe u+1 and Hom universe u; coefficient modules have universe u+1. No
new equality of these universes is assumed. Finite coefficients from the smaller
universe are included by the existing ULift realization, and u is arbitrary.

Independent searches used different terms from the worker: LeanFinder for restriction
by base change along a closed embedding preserving epimorphisms with retrocompact open
complement (eight hits, none this geometric theorem); Loogle for finite-colimit and
finite-limit preservation (twelve generic hits, including exactFunctor_iff); Mathlib
grep for retrocompactness, closed direct images, and exact lowerStar (five geometry
hits, none this statement). Each search used `msearch.py` and is in `searches.jsonl`.
Independent `rg` searches in both project source trees and `lean/Sheaf` for retrocompact,
closed pushforward, pro-etale exactness, and finite-colimit lowerStar found the recorded
upstream theorem and its downstream applications. The Sheaf closed-pushforward results
are topological or quasi-coherent specializations. No second definition is warranted.

There is no H3 mismatch and no statement correction. I retained the existing attachment,
its literal source signature, the two-declaration list, and all node dependencies and
seven proof steps. Those steps remain sectionwise kernels and biproducts, the local
surjectivity criterion, affine/basis localization, base change of quasi-compactness,
finite refinement, covering extension with specified closed reductions and empty-fibre
lifts, and the kernel/cokernel exactness conclusion. No replacement theorem, definition,
or proof is delivered. H5/H6 and new-file H8/H9 therefore add nothing; the existing
source explicitly identifies this blueprint theorem and the node retains the full
proof for stage 3.

One reporting mismatch was repaired: the worker's claim that the counit still contains
sorry describes the archived source, not the current server source. I obtained the
current module with `scompile.py --source`, read its repaired counit and the unchanged
exactness declaration, and clarified `lean.note` and the report. This does not claim
transitive proof closure. Source line 178 in the worker report is an archived location.

Validation: `scompile.py Q07 lem-exc-proetale-closed-exact
scratchpad/ExistingChecks.lean` passed both sandbox and library checks without warnings.
It prints the fully bound signatures and checks the exactFunctor consumer with Finite R;
left exactness is synthesized and right exactness is supplied by the attached theorem.
The scratch examples are not delivered. There are no delivered Lean files to compile.
The required delivery dry run and final delivery follow this reading.
