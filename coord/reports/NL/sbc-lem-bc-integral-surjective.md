## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralSurjectiveTargetBaseChange` states
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_integralSurjective_target`.
The proof is `sorry`; no definitions or additional nodes are introduced.
Source read: Stacks `etale-cohomology.tex`, lemma-base-change-q-integral-top (Tag 0F04),
and the blueprint node in sec-smooth-base-change/sk-lem-universal-datum.

Clause-by-clause rendering:

- `X S : Scheme.{u}` and `f : X ⟶ S` are the given morphism.
- `n : ℕ`, `_hn : 0 < n`, `_hinv : IsUnit (n : Γ(S, ⊤))` render the positive integer
  invertible on S inherited from sbc-def-base-change-property.
- `q : ℕ`, `_hq : 1 ≤ q` give the specified positive cohomological degree.
- `_hprev : UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f ((q : ℤ) - 1)`
  says the SINGLE previous-degree property holds universally. It is not the cumulative
  condition and does not assume the degree-q property.
- `a : S' ⟶ S`, `b : X' ⟶ X`, `f' : X' ⟶ S'` and `_sq₀ : IsPullback b f' f a`
  render the left Cartesian square, with every base change allowed.
- `g : T ⟶ S'`, `e : Y ⟶ T`, `h : Y ⟶ X'`, and `sq : IsPullback e h g f'`
  render the middle Cartesian square. `[QuasiCompact g] [QuasiSeparated g]` are
  exactly the two restrictions on g; none is imposed on a or its composite with g.
- `π : T' ⟶ T`, `π' : Y' ⟶ Y`, `e' : Y' ⟶ T'`, and
  `sqπ : IsPullback e' π' π e` render the right Cartesian square.
  `[IsIntegralHom π] [Surjective π]` mean integral and surjective on underlying points.
- The composite square is `sqπ.paste_vert sq`, whose upper map is `π' ≫ h` and
  lower map is `π ≫ g`. Thus h' and g' have precisely the displayed composite values;
  they are not arbitrary replacement morphisms.
- `F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))`
  is an abelian sheaf annihilated by n, using the dependency's coefficient convention.
  A module structure over Z/n is uniquely determined by its underlying n-killed
  abelian group, so this encoding neither strengthens nor weakens the sheaf condition.
- `((π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))].obj F)` is F' = π⁻¹F,
  using the existing exact constant-coefficient inverse image.
- `_hF : IsIso (baseChangeHomologyMap ... (sqπ.paste_vert sq) (q : ℤ) ...)`
  is precisely invertibility of the displayed composite-square map at F'.
- The conclusion `IsIso (baseChangeHomologyMap ... sq (q : ℤ) F)` is invertibility
  of the middle-square map at F. These are the recorded bounded-below presentations
  of the degreewise maps, not arbitrary arrows or unrelated object isomorphisms.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.CumulativeUniversalBaseChangeProperty`: its documentation
  explicitly records fixed-degree `AlgebraicGeometry.Etale.UniversalBaseChangeProperty`
  from `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`, specialized to ULift ZMod.
  The cumulative predicate itself is deliberately not substituted for the single degree.
- `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMap`; the node's record explicitly identifies
  `Etale.baseChangeHomologyMap` in SmoothBaseChange.Defs as its existing bounded-below
  degreewise presentation. Read the full definitions and signatures of both maps and
  the fixed-degree/universal predicates. No private exchange is defined.
- `Mathlib.AlgebraicGeometry.Morphisms.Integral`: `AlgebraicGeometry.IsIntegralHom`,
  the affine-local integral definition (the integral clause of def-weil-finite-integral-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`,
  exactly surjectivity of the underlying point function.

The already recorded non-Mathlib proof-dependency modules are imported without `public`:
InverseImageStalkGerm, EtaleInverseImageModulesExact, Integral.BaseChange,
ExactFunctorDerivedFunctor, RingedToposDerivedPushforwardComposition, ExchangeIdentityPasting.
UpperLowerStar.Defs is already publicly imported by the statement dependencies.
Unrecorded proof prerequisites (not statement prerequisites) are not invented or imported.
The docstring includes all seven proof steps and their canonical-map compatibility arguments.

Edge cases checked: q=1 uses degree zero, not natural-number underflow; q=0 is excluded
by the source. n=1 gives the zero coefficient category and is allowed; n=0 is excluded
by the inherited coefficient domain. Empty schemes and zero sheaves are allowed, including
an empty integral surjective cover only when its target is empty. There is no finite,
Noetherian, separated, nonempty, characteristic, or qcqs condition on h, π, a or f.
All schemes lie in the same arbitrary universe u; the coefficients and module values
use the dependency's u+1 size convention. All variables and universes are explicitly bound.

Searches performed:

- msearch LeanFinder: "Integral surjective change of target detects whether etale higher
  direct image base change is an isomorphism"; eight hits, only etale permanence and
  standard-etale algebra results, none this statement.
- msearch Loogle: "IsIntegralHom, Surjective, IsIso"; zero hits, unknown identifier
  IsIntegralHom reported by that search service.
- msearch LeanSearch: "Integral surjective morphism detects etale cohomology base change
  isomorphism"; service unavailable (Internal Server Error); no negative verdict inferred.
- msearch grep: `integral.*base.change|base.change.*integral` in Mathlib AlgebraicGeometry;
  zero hits.
- rg of the source repository, including the exact blueprint id, found
  `Etale.isIso_baseChangeHomologyMap_of_isIntegralHom_of_surjective` in
  SmoothBaseChange/IntegralBaseChange.lean. Its complete signature/docstring were read.
  It is a more general ring-valued, fixed-base theorem assuming only BaseChangeProperty
  for p, without the displayed original f/base-change square, positivity or invertibility
  of n. Thus it is useful future proof material but is not the exact node statement.
- rg of lean/Sheaf found no such statement. The proposed full declaration name was
  also searched in Mathlib, the source project, lean/Sheaf, and dag/lean_names_upstream.json;
  there is no collision.

No statement correction, new node, dependency-interface repair, or statement dispute.

## Second reading by NL

I independently read the node, its four statement-dependency nodes and their recorded
interfaces, the delivered module, Stacks etale-cohomology.tex
`lemma-base-change-q-integral-top` (0F04), and its preceding
`remark-base-change-holds` and critical-degree injectivity proof. The source uses a
cumulative universal BC convention; this node deliberately asks only for the single
universal degree q-1, which is exactly what the displayed injectivity argument uses.
The positive invertible coefficient domain comes from the node's explicitly cited
sbc-def-base-change-property. No source-wide smoothness or finiteness assumption is hidden.

Object, hypothesis and conclusion checklist (all verdicts: matches):

1. A morphism of schemes f:X→S: `{X S : Scheme.{u}} (f : X ⟶ S)`.
2. A positive integer n invertible on S: `(n : ℕ) (_hn : 0 < n)` and
   `(_hinv : IsUnit (n : Γ(S, ⊤)))`. This is precisely the inherited domain.
3. A degree q≥1: `(q : ℕ) (_hq : 1 ≤ q)`.
4. Universal BC in the single degree q-1:
   `_hprev : UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f ((q : ℤ) - 1)`.
   I opened SmoothBaseChange/Defs.lean: this quantifies over every base change and
   then the qcqs horizontal squares and all coefficient sheaves in that one degree.
   It is not the cumulative predicate defined in the imported dependency module.
5. The left square, including all its objects and arrows: schemes X',S', arrows
   `a : S' ⟶ S`, `b : X' ⟶ X`, `f' : X' ⟶ S'`, and
   `_sq₀ : IsPullback b f' f a`. This is the dependency predicate's orientation.
6. The middle square: schemes Y,T, arrows `g : T ⟶ S'`, `e : Y ⟶ T`,
   `h : Y ⟶ X'`, and `sq : IsPullback e h g f'`. The only restrictions on g
   are exactly `[QuasiCompact g] [QuasiSeparated g]`.
7. The right square: schemes Y',T', arrows `π : T' ⟶ T`, `π' : Y' ⟶ Y`,
   `e' : Y' ⟶ T'`, and `sqπ : IsPullback e' π' π e`.
   `[IsIntegralHom π] [Surjective π]` use the recorded Mathlib classes. I opened
   Integral.lean and UnderlyingMap.lean: these mean affine-local integral ring maps
   and surjectivity on underlying points, respectively, with no finiteness restriction.
8. The composite square and specified h',g': `sqπ.paste_vert sq` has upper arrow
   `π' ≫ h` and lower arrow `π ≫ g`, and the remaining arrows e',f'. Thus no extra
   independent arrows or equality hypotheses have replaced the stated composites.
9. An abelian sheaf F on T annihilated by n:
   `F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))`.
   This is the dependency's coefficient convention: an n-killed abelian group has
   its unique Z/n-module structure; lifting the ring changes only its size encoding.
10. F'=π⁻¹F: `((π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))].obj F)`.
    I opened UpperLowerStar/Defs.lean: this is the canonical sheaf inverse image,
    constructed by Kan extension and sheafification, not an arbitrary pullback functor.
11. The hypothesis that the composite-square degree-q map at F' is invertible:
    `_hF : IsIso (baseChangeHomologyMap ... (sqπ.paste_vert sq) (q : ℤ) ...)`.
12. The conclusion that the middle-square degree-q map at F is invertible:
    `IsIso (baseChangeHomologyMap ... sq (q : ℤ) F)`.
    I opened the definitions of baseChangeHomologyMap, its source/target functors and
    transformation, and DerivedUnbounded.derivedBaseChangeMap. The former is the
    already recorded bounded-below presentation, homology of the canonical exchange
    at F[0]; it does not assert just an isomorphism between unrelated objects.

Edge cases: q=1 invokes degree zero since subtraction takes place in ℤ; q=0 is
excluded by the node. n=1, the zero sheaf, and empty schemes remain allowed; n=0 is
excluded by the cited coefficient convention. Surjectivity imposes no nonemptiness
when T is empty. No restrictions on characteristic beyond invertibility of n are
added. No index family occurs. The arbitrary common scheme universe u and coefficient
and value universe u+1 agree with the recorded dependency interfaces; there is no
additional universe equality, smallness instance, Noetherian hypothesis, or qcqs
assumption on a, h, f or π. All binders and universe names are explicit.

Independent searches, using wording different from the first reader:

- msearch LeanFinder: "Surjective integral covering descends invertibility of the
  critical etale cohomology exchange morphism" returned eight standard/formally
  etale ring and morphism results, none this statement.
- msearch Loogle: `"baseChangeHomologyMap"` returned zero hits.
- msearch LeanSearch: "Descent of higher etale base change isomorphisms along an
  integral surjective covering" was unavailable (Internal Server Error); this is
  not treated as evidence of absence.
- Independent rg in Mathlib/AlgebraicGeometry, upstream WeilConjectures and lean/Sheaf
  for `integralSurjective`, `integral_surjective`, `isIso_baseChangeHomologyMap`, and
  base-change/detection combinations found the upstream IntegralBaseChange theorem.
  I read its complete signature and docstring. It assumes fixed-base BC for p,
  arbitrary coefficient ring and integer degree, and a second Cartesian square over
  π≫g. It does not state the node's universal hypothesis on the original f, its
  displayed initial base change, or its coefficient domain. It is future proof
  material, not an exact existing statement under this brief's criterion.
  Other hits concern smooth maps, integral change of source, or localization.

No mismatches found; no Lean or node changes were necessary. There are no new nodes
or dependency modules to audit, no corrected statement or citer audit to check, no
new definitions, and no proved declarations. The single sorry is the named theorem;
its docstring carries the source, blueprint id and all seven node proof steps.
The recorded Lean signature was checked mechanically to equal the file verbatim,
and every line is at most 100 characters. The delivered module compiled cleanly
with the required server-side scompile.py (3.6 seconds for the library file).
The second reading adds this audit only.
