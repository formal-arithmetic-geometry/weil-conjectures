## Worker report

The module `Sheaf.EtaleCohomology.SepClosedFieldVanishing` states the complete node as one
conjunction, with one `sorry` theorem and no new definitions. The node statement is unchanged.

Hypotheses and clauses:
- The field L is `(L : Type u) [Field L]`; separable closedness is `[IsSepClosed L]`.
  Every occurrence of X is the explicit scheme `Spec (.of L)`.
- Every small étale object is quantified as `V : (Spec (.of L)).Etale`.
  Its disjoint-union decomposition is the existence of an arbitrary `I : Type u` and
  injections `ι : I → (Spec (.of L) ⟶ V.left)` whose cofan is colimiting.
  `Nonempty (IsColimit (Cofan.mk V.left ι))` states the coproduct universal property in
  schemes. The equations `ι i ≫ V.hom = 𝟙 (Spec (.of L))` make it a decomposition over X,
  rather than only an abstract isomorphism of schemes. Coproducts of schemes are disjoint
  unions, so this is exactly the first clause. No finiteness or nonemptiness is imposed.
- An arbitrary abelian sheaf is
  `F : Sheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1}`.
  Positive degree is `(q : ℤ), 0 < q → ...`; the first vanishing is `IsZero` of the value
  of `Etale.cohomology ... q` on `(DerivedCategory.singleFunctor _ 0).obj F`.
- The final clause quantifies every scheme `(Y : Scheme.{u})` and every morphism
  `(f : Spec (.of L) ⟶ Y)` with no geometric property imposed on either.
  It applies `DerivedCategory.Plus.homologyFunctor ... q` to the bounded-below right derived
  functor of `Etale.lowerStar ... f`, evaluated on `DerivedCategory.Plus.singleFunctor _ 0`
  of the same arbitrary F. Its `IsZero` is precisely `R^q f_* F = 0` for `q > 0`.
  There is no coefficient restriction to constant or torsion sheaves.

Dependency declarations read and used:
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`. Its separable-polynomial splitting
  definition is the standard equivalent form of no nontrivial finite separable extensions.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, and
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Scheme.Etale` (étale objects over X).
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`, specialized to that topology
  and `AddCommGrpCat.{u + 1}`, exactly the recorded abelian sheaf encoding.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.cohomology`, defined as `rightDerivedGlobalSections` followed by
  homology. The declaration's docstring explicitly identifies its value on a degree-zero
  sheaf with the node's cohomology.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, the recorded direct image defined by base-change
  precomposition. For its derived functor the module uses the generic existing
  `CategoryTheory.Functor.rightDerivedFunctorPlus`, exactly as upstream
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar` does. The name
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` in the dependency record exists in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence` (lines 77–80).
  Its body is exactly `(g)_*[A].rightDerivedFunctorPlus`, so the delivered expression
  unfolds that recorded definition and introduces no replacement notion.

Proof imports follow all already stated proof dependencies: the project fibre-decomposition
module, Mathlib EpiMono, GlobalSections, Sheafification, Limits.MorphismProperty, and
ShortComplex.PreservesHomology. The six-step docstring follows the DAG's repaired proof,
including the local lift argument, exactness of both functors, and the K-injective argument.

Edge cases checked: the empty étale object allows `I = Empty` and the initial cofan;
infinite coproducts allow arbitrary small index sets (the points of V are in `Type u`);
no quasi-compactness is assumed. The zero sheaf is included. Degree zero and negative
degrees are excluded only by the required strict positivity. Separably closed imperfect
fields in positive characteristic are included: there is no algebraic-closedness or
characteristic assumption. An arbitrary target and morphism, including non-finite-type
ones, are allowed. The scheme universe matches the field universe; the sheaf coefficients
use the recorded `u + 1` convention. No automatic implicit variables or local notation.

Searches:
- `msearch.py ... leansearch "Every etale scheme over a separably closed field is a disjoint
  union of copies of its spectrum and higher direct images vanish"`: service unavailable,
  Internal Server Error.
- `msearch.py ... leanfinder "Higher etale cohomology and higher direct images from the
  spectrum of a separably closed field vanish"`: eight hits concerning formally étale
  algebras and cotangent cohomology; none states this result.
- `msearch.py ... loogle "AlgebraicGeometry.Etale, IsSepClosed"`: four hits, including
  `Scheme.exists_fac_of_etale_of_isSepClosed` and point-small-étale-fibre facts; no full match.
- `msearch.py ... grep "etale.*disjoint|cohomology.*isSepClosed|IsSepClosed"
  AlgebraicGeometry/Sites`: seven hits for geometric points and lifting, no full match.
- `rg` in Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf` for `IsSepClosed`,
  `rightDerivedLowerStarPlus`, `etale.*disjoint`, the proposed theorem name, and the item id.
  Upstream has `Scheme.subsingleton_H_of_isSepClosed` in
  `WeilConjectures/AlgebraicGeometry/Sites/FiniteSupport.lean`, read in full: this states only
  the cohomology clause using `Sheaf.H`, not the decomposition or higher direct images.
  There is no existing declaration of the complete conjunction. No upstream occurrence of
  `lem-kun-0ezp` was found. Existing project generic fibre-decomposition is reused as a proof
  import rather than copied. No new notion or new node is needed.

Source read: the full blueprint lemma and the local Stacks source for Tag 0EZP. The latter
states constant-coefficient vanishing for a more general integral normal scheme. The node's
field specialization with arbitrary coefficients is justified by its independent six-step
exactness proof, not by attributing that stronger coefficient assertion to the Stacks tag.
No statement correction or dispute is needed.

Validation: server `scompile.py NX lem-kun-0ezp` compiled the delivered file cleanly in
1.6 seconds, nice 19, two threads, 60-second per-file limit. No local compilation was run.

## Second reading by NX

I independently read the complete node, its six proof steps, the blueprint source,
Stacks `morphisms.tex` lemma-etale-over-field (02GL), and
`etale-cohomology.tex` lemma-Rf-star-zero-normal-with-alg-closed-function-field
(0EZP), including the surrounding argument. 02GL assumes only a field and an
étale morphism, with no quasi-compactness. 0EZP assumes an integral normal source
with separably closed function field and states vanishing for constant abelian
coefficients. The node deliberately specializes the geometry to a field and
proves arbitrary-coefficient vanishing by its separate exactness argument; the
Lean follows that node and does not extend the general 0EZP assertion.

Object, hypothesis, and conclusion checklist (all pass):

1. A field L: `(L : Type u) [Field L]`. Separably closed:
   `[IsSepClosed L]`, the recorded dependency declaration, whose splitting of
   separable polynomials is equivalent to absence of nontrivial finite separable
   extensions. No perfectness, algebraic closedness, or characteristic is assumed.
2. X is exactly Spec L: every occurrence is `Spec (.of L)`; X is not an
   independent scheme with an unspecified structure map.
3. Every small étale object V: `∀ V : (Spec (.of L)).Etale`. I opened Mathlib's
   `Scheme.Etale` definition (`MorphismProperty.Over @Etale ⊤ X`) and
   `smallEtaleTopology` (jointly surjective étale coverings), matching the
   dependency node, not its finite or affine subsite.
4. V is a disjoint union of copies of X: `∃ (I : Type u) (ι : I → (X ⟶ V.left))`
   with `Nonempty (IsColimit (Cofan.mk V.left ι))` is the scheme coproduct universal
   property. The equations `∀ i, ι i ≫ V.hom = 𝟙 X` put the components over X.
   A coproduct in schemes is a disjoint union, so no separate injectivity or
   disjointness hypothesis is missing. The universal property and these equations
   also give the coproduct in schemes over X.
5. Every abelian sheaf F: `Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`,
   exactly the dependency's encoding. I read the Sheaf structure and the five
   statement dependency nodes and their recorded signatures.
6. Every positive degree: `(q : ℤ), 0 < q → ...`. The cohomology conclusion is
   `IsZero ((cohomology ... q).obj ((DerivedCategory.singleFunctor _ 0).obj F))`.
   I opened `Etale.cohomology` and `rightDerivedGlobalSections` in LowerShriek:
   these are RΓ followed by degree-q homology, applied here to F in degree zero.
   Thus the node's group is zero, not merely a selected class or a constant sheaf.
7. Every scheme Y and morphism f: `(Y : Scheme.{u}) (f : X ⟶ Y)`, without
   additional geometric hypotheses. Every F and every positive q are quantified
   again, which is logically identical to the node's use of the same arbitrary F.
8. Higher direct images vanish: `IsZero` of `DerivedCategory.Plus.homologyFunctor`
   applied to `(lowerStar ... f).rightDerivedFunctorPlus` on
   `DerivedCategory.Plus.singleFunctor _ 0`. I read `lowerStar` in Defs: it is
   base-change precomposition on the small étale sites, including its section
   formula. I also read Derived.UpperLowerStar's identification of derived
   pushforward with this generic rightDerivedFunctorPlus. I also checked
   `Derived.UpperLowerStarCoherence`: its recorded `rightDerivedLowerStarPlus`
   (lines 77–80) has exactly `(g)_*[A].rightDerivedFunctorPlus` as its body.
   The delivered expression therefore uses that same derived direct image by unfolding.

Edge cases: Empty V permits an empty I and the initial cofan; no `Nonempty` or
`Finite` instance is imposed on I (the `Nonempty` wraps a colimit proof only).
Infinite discrete V is included: its points are small in the scheme universe u.
The zero sheaf is included. q = 0 and negative q are correctly outside the
assertion, with no claim that H⁰ vanishes. Imperfect separably closed fields and
all characteristics are included. X itself is nonempty because L is a field;
there is no meaningful empty-field case lost. Y may be empty, in which case the
morphism binder has no inhabitants, as in the natural statement. The universe u
is arbitrary; schemes share their ambient universe, and coefficients use the
recorded u+1 convention. There is no hidden finite-type or Noetherian restriction.

Independent searches used different phrases: LeanFinder query "Etale schemes
over a separably closed field are coproducts of spectra and direct image is
exact" returned eight algebraic étaleness results, including
`Algebra.Etale.iff_exists_algEquiv_prod`, which concerns finite affine algebra
presentations and is not this theorem. Loogle query
`IsSepClosed, CategoryTheory.Limits.IsColimit` returned no hits. I searched
Mathlib Sites, project `lean/Sheaf`, and upstream WeilConjectures with
`coproduct`, `coprod`, `IsColimit`, `rightDerivedFunctorPlus`, `vanishing`,
`IsSepClosed`, and `separably closed`. I opened PointCohomology's covering-section
and projective-constant-sheaf declarations, and FiniteSupport's
`Scheme.subsingleton_H_of_isSepClosed`: the latter gives only positive Sheaf.H
vanishing, not the coproduct and higher-direct-image clauses. None supplies the
complete node. Existing notions are reused; no new definition nodes or dependency
modules occur in this delivery, so H12/H13 do not require any additions.

No mismatch was found and no Lean or node change was needed. The module and
statement docstrings cite the source and blueprint id, and the six numbered proof
steps follow all six DAG steps. There is exactly one named theorem, whose entire
proof is `sorry`, and no definitions or local notation. All lines meet 100 columns,
all variables/universes are bound, and `lean.statement` is a verbatim substring of
the file's signature. No statement correction or citer review is needed.

I independently compiled the sole delivered file with
`scompile.py NX lem-kun-0ezp lean/Sheaf/EtaleCohomology/SepClosedFieldVanishing.lean`:
clean server result, 1.5 seconds, nice 19, two threads, 60-second per-file limit.
