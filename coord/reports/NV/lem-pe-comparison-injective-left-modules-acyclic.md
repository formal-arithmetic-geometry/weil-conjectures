## Worker report

Delivery inventory reconstructed during the second reading: the dispatched sandbox contained only
its launcher markers, including `.check`; no worker report, node copy, or Lean module was present.
There is consequently no earlier worker prose to preserve or attribute. The binding below is based
on an independent reading of the unchanged DAG statement, its source, dependency declarations, and
the existing upstream theorem. No new statement module is needed or delivered.

The item uses the existing declaration
`AlgebraicGeometry.ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective`, in
`WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`. Its ambient parameters are
`(A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]`.
Specialize `A` to `ModuleCat.{u + 1} Λ`, for `(Λ : Type (u + 1)) [Ring Λ]`.
Import `Mathlib.Algebra.Category.ModuleCat.AB` to supply the standard Grothendieck instance.
The exact specialization and its positive-degree expansion compiled through `scompile.py` with
no errors or warnings. The theorem's current server source was also read with
`scompile.py --source WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`.
The checked upstream source already contains the generic theorem, so H4 requires reusing it.
The item receives only a `lean` record, with `existing: true`; every other node field is unchanged.

The specialization is:

```lean
(X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
(I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I] :
(comparisonLowerStar (ModuleCat.{u + 1} Λ) X).rightAcyclic
  ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj I)
```

The `lean.statement` field records the generic source signature verbatim, including its ambient
`A`, rather than pretending the specialization is a separately declared theorem.

Source places read: `proetale.tex` Tags 099U (`lemma-affine-vanishing`), 099V
(`lemma-relative-comparison`), and 099W (`lemma-compare-cohomology`), and
`sites-cohomology.tex` Tags 03FD (`lemma-cohomology-modules-abelian-agree`) and 03F3
(`lemma-cohomology-of-open`). 099V assumes only that X is a scheme; its affine objects are a proof
basis, not an affineness hypothesis on X. The arbitrary-left-module extension is part of this DAG
node and its generic source-library theorem, rather than a claim that 099V itself is stated with
noncommutative coefficients. The node's proof passes through underlying abelian cohomology using
03FD, and never assumes that forgetting module scalars preserves injectivity.

Dependency declarations read:

- `def-pc-scheme`: Mathlib's `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-pbc-etale-site`: `Scheme.Etale`, `Scheme.smallEtaleTopology`.
- `def-weil-pbc-proetale-site`: the recorded `ProEtaleDerivedCategory` module and the underlying
  Mathlib `Scheme.ProEt`, `Scheme.ProEt.topology`. Its derived abbreviation requires commutative
  coefficients and is not used as the arbitrary-ring coefficient category. The site itself has no
  such restriction; this delivery uses the site's existing definition, not another derived category.
- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules` is transparently
  `SheafOfModules`. This node explicitly also permits the equivalent fixed-scalar formulation,
  `Sheaf J (ModuleCat Λ)`, used by the existing comparison theorem.
- `def-weil-pbc-constant-sheaf`: `CategoryTheory.constantSheaf`, sheafification of the constant
  presheaf. No new constant ring, new scalar action, or chosen ring map is constructed here.
- `def-weil-pbc-site-comparison-morphism`: `Scheme.proEtaleSiteComparison` is the canonical
  set-valued continuous-functor adjunction for `Scheme.toProEt`. Its module wrapper
  `proEtaleSiteComparisonModules` carries `[Finite Λ]`, so that wrapper must not be used here.
  The upstream `comparisonUpperStar`, `comparisonLowerStar`, `comparisonAdjunction` from
  `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs` use the same inclusion and constructed
  pullback for arbitrary Grothendieck coefficients, and supply the needed arbitrary-ring interface.
- `def-sp-left-exact-additive`: a Mathlib leaf, with `Functor.Additive`,
  `PreservesFiniteLimits`, `Functor.rightDerived`, and `InjectiveResolution.isoRightDerivedObj`.
  The last identifies its value with the homology of any injective resolution after applying F.
- `def-sp-injective-resolutions`: `CategoryTheory.Injective`, `InjectiveResolution`.

No new nodes or dependency modules. No statement correction or target change.

## Second reading by NV

I read the whole item and its eight statement dependencies, the source statements and proof
paragraphs listed above, the upstream generic declaration and its ambient binders, and the
actual definitions of both comparison functors. This is the following object-by-object and
clause-by-clause list of the natural statement, with the rendering and verdict for each item.

1. **Any scheme X.** Rendered by `(X : Scheme.{u})`. Verdict: exact. There is no `IsAffine`,
   quasi-compactness, quasi-separatedness, connectedness, nonemptiness, or base-field instance.
2. **Any discrete associative unital coefficient ring Λ, possibly noncommutative.** Rendered by
   `Λ : Type (u + 1)` and `[Ring Λ]` in the specialization. `ModuleCat` uses left modules.
   Verdict: exact. No `CommRing`, `Finite`, torsion, or characteristic binder is required.
   Discreteness is implicit in the absence of a topological coefficient structure.
3. **The small etale and pro-etale sites in the larger size convention.** Rendered by
   `X.smallEtaleTopology` on `X.Etale` and `Scheme.ProEt.topology X` on `X.ProEt`.
   Verdict: exact. Objects lie in universe u+1 and arrows in u; coefficient module carriers
   and their Hom types are in u+1. The site's morphism universe has not been forced to equal
   its object universe. The existing Grothendieck/sheafification interfaces supply the
   required size handling, without an extra smallness assumption on X in the specialization.
4. **Left Λ-module sheaves, equivalently modules over the sheafified constant ring.** Rendered
   using the statement's first formulation, `Sheaf J (ModuleCat.{u + 1} Λ)`.
   Verdict: exact. A section is a left Λ-module, restriction is Λ-linear, and the sheaf condition
   is the usual underlying sheaf condition. This is not a structure-sheaf module category or a
   right-module category. The equivalent intrinsic constant-ring encoding is not substituted
   by an arbitrary ring sheaf, and no commutative intrinsic encoding is imposed.
5. **The specified comparison morphism and inverse image.** Rendered by
   `comparisonUpperStar (ModuleCat.{u + 1} Λ) X`. Its definition is the canonical left Kan
   extension and sheafification along `toProEt X`. Verdict: exact. Since the set inverse image
   is left exact and a left adjoint, its lift to the operations of the algebraic theory of
   left Λ-modules is the module-valued inverse image. This agrees with applying it to addition,
   zero, negation and each scalar operation. Neither an arbitrary left adjoint nor an arbitrary
   canonical-looking map is introduced.
6. **Direct image is restriction to the etale subsite with scalar action.** Rendered by
   `comparisonLowerStar (ModuleCat.{u + 1} Λ) X`. Its definition is
   `(toProEt X).sheafPushforwardContinuous`, so evaluation at an etale object is exactly
   evaluation on the same object regarded as pro-etale, with the same module structure.
   Verdict: exact; no unrelated scheme direct-image functor is used.
7. **Every injective etale left-module sheaf I.** Rendered by
   `(I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I]`.
   Verdict: exact. Injectivity is in this module-sheaf category, not in abelian sheaves.
   The standard `IsGrothendieckAbelian` instance for `ModuleCat` uses only `[Ring Λ]`;
   enough injectives on both sheaf categories synthesizes without additional hypotheses.
8. **Right derived direct image computed with module injective resolutions.** Rendered by
   `Functor.rightDerived` inside `rightAcyclic`. I opened its Mathlib definition and
   `InjectiveResolution.isoRightDerivedObj`: it is precisely H^n of the direct image of
   a module injective resolution. Verdict: exact; no abelian-derived substitute is asserted.
9. **Every positive integer q, with zero cohomology sheaf.** `rightAcyclic` is defined as
   `∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj M)`. Every positive integer is uniquely
   n+1, so this is exactly the stated positive degrees. The argument M is the actual
   comparison inverse image of I. Verdict: exact, with quantifier order X, Λ, I, degree;
   no degree-zero conclusion or other clause has been added.
10. **No affineness, quasi-compactness, torsion or finite-ring hypotheses.** The specialization
    has none of these, and all ambient coefficient-category instances infer from `[Ring Λ]`.
    Verdict: exact, with no hidden assumption from a similarly named finite-ring wrapper.

Edge cases checked: X can be the empty scheme; I can be the zero sheaf; the zero ring is allowed
because `[Ring Λ]` has no `Nontrivial` requirement. Fields in every characteristic, infinite rings,
and noncommutative matrix rings are included. There is no covering index binder that could exclude
an empty index set. Degree zero is deliberately absent (it need not vanish); n=0 in `rightAcyclic`
means degree one, the first required case. The universally quantified scheme universe is arbitrary;
coefficient and sheaf sizes follow the explicitly larger coefficient universe of the node.
No hidden derived-category universe or `HasDerivedCategory` binder is introduced.

Independent searches (executed through `msearch.py`, recorded in `searches.jsonl`):

- LeanSearch: “The etale to proetale comparison inverse image carries injective sheaves of left
  modules over any associative ring to direct image acyclic objects” — 8 hits, including enough
  injectives for arbitrary-ring modules and module sheaf pullback/sheafification; no comparison
  acyclicity theorem in Mathlib.
- Loogle: `"rightDerived", "injective"` — 12 hits, including
  `Functor.isZero_rightDerived_obj_injective_succ` and `InjectiveResolution.isoRightDerivedObj`.
  The first is vanishing on injectives, not on their comparison inverse images, so is not a match.
- LeanFinder: “Higher direct image acyclicity of the pro etale pullback of an injective etale
  module sheaf” — 8 hits concerning local injectivity, generic derived vanishing, and K-injectivity;
  no comparison theorem in Mathlib.
- msearch grep: `acyclic|higher.*direct.*image|derived.*injective` in
  `Mathlib/CategoryTheory/Abelian` — 10 hits, including the same right-derived-functor API.
- Direct rg with other wording: `acyclic.*comparison|comparison.*acyclic|pull.*injective|injective.*pull`
  in upstream ProEtale comparison sources and project comparison modules. This found the generic
  upstream theorem, as well as project abelian, commutative-ring and finite-ring interfaces. Those
  special interfaces do not suffice for arbitrary noncommutative coefficients. The generic theorem
  does: its full ambient signature was read, and the ModuleCat specialization actually compiled.
- `dag/lean_names_upstream.json` was searched for the exact declaration; there was no hit there.
  The item's own `lean_audit.slopmaster2` already names it, and its source declaration was opened.
  The checked live source retains the same signature (the theorem now has a proof in that source).

Mismatches and repairs: no mathematical mismatch in the node. The missing handoff artifacts were
replaced by this report and the node binding. A preliminary fresh theorem draft would duplicate the
existing generic statement, so it was removed from `lean/`; no such theorem enters the delivery.
The existing binding uses the verbatim generic signature and explicitly records its ring-module
specialization in `lean.note`. No hollow definition, postponed theorem, new node, dependency module,
or theorem proof is delivered, and no source checkout is edited.

For completeness, the node's five-step arbitrary-module proof was checked as follows. First, the
constant-ring module categories are Grothendieck and have enough injectives. Second, for each etale
W, localization and the comparison inverse-image square identify the underlying abelian sheaf of
the restricted module inverse image with the comparison inverse image of I_ab restricted to W.
Third, module injectivity kills derived evaluation of I; 03FD and 03F3 identify this with the
positive cohomology of I_ab on W_et, without asserting abelian injectivity. Fourth, 099W transfers
this vanishing to W_proet, and 03FD transfers it back to module-derived evaluation of nu^* I.
Fifth, any pro-etale module injective resolution evaluates to an exact complex in positive degrees
at every etale W. Restricting that complex is precisely nu_*; sectionwise kernels and sheafified
cokernels imply zero positive homology sheaves. This is exactly the conclusion of the existing
specialized `rightAcyclic` theorem. No correction or citer audit is necessary.

Validation: `scompile.py NV lem-pe-comparison-injective-left-modules-acyclic
scratchpad/ExistingSpecialization.lean` passed, testing the exact theorem specialization and its
positive-degree expansion, and synthesizing the Grothendieck coefficient instance and enough
injectives on both sites. The delivery wrapper additionally compiles an `@`-signature check of
the recorded existing declaration. Scratch checks are outside `lean/` and are not delivered.
