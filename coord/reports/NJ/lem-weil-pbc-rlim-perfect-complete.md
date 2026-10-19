## Worker report

The module `Sheaf.RingTheory.RlimPerfectComplete` states
`DerivedCategory.rlim_perfect_complete`, with its only theorem proof `sorry`.
The five definitions construct exact restriction functors, their canonical composition
isomorphism, the restricted transition maps, and the projection-induced reduction maps.
All data are constructed; none is postponed. Every helper belongs to the item and is
listed in `lean.declarations`, with source/blueprint docstrings.

Source checked: `literature/stacks-project/more-algebra.tex`,
`lemma-Rlim-perfect-gives-complete`, Tag 09AW (around line 28447).
The source assumes an arbitrary complete commutative ring, perfect first term, and
transition-induced derived reduction isomorphisms, exactly as the DAG node does.
No statement correction or additional definition node is needed.

Hypothesis and conclusion correspondence:

- A commutative ring and ideal: `{A : Type u} [CommRing A] (I : Ideal A)`.
- Bijectivity of the completion map: `[IsAdicComplete I A]`, the companion notion in
  the recorded `def-weil-pbc-adic-completion` declaration. For the regular module A,
  Mathlib's ideal-adic module quotients are the ring quotients in the node.
- `K_n in D(A/I^n)`, positive indices: `K n` lies in
  `DerivedCategory (ModuleCat (A ⧸ I ^ (n+1)))`, indexed by all naturals.
  Thus Lean level zero is the node's level one. The derived-category instance binders
  only specify realizations of the localizations, as the recorded perfectness API requires.
- A transition in `D(A/I^(n+1))`: `t n` goes from `K (n+1)` to the exact restriction
  of `K n` along `Ideal.Quotient.factorPowSucc I (n+1)`. This retains linearity over
  the larger quotient, rather than assuming only A-linearity.
- Derived scalar extension: `L n` with `adj n` is its universal characterization as
  the left adjoint to exact restriction along `A -> A/I^(n+1)`; `B n` and `badj n`
  similarly present scalar extension between consecutive quotients. These are choices
  of universally specified functors and adjunctions, not extra flatness, finiteness,
  resolution, or coefficient hypotheses. Derived tensor with a quotient has exactly
  this adjunction. Any two such realizations are uniquely isomorphic compatibly with
  their adjunctions. In particular no unconstrained comparison map or arbitrary
  `Nonempty` choice replaces the canonical construction.
- Transition-induced reduction isomorphisms: `hbase` says that the adjoint transpose
  of each given transition `t n` is an isomorphism. This is the specific map induced
  by the transition, rather than mere existence of an unrelated isomorphism.
- Perfect first term: `hperfect : IsPerfect (K 0)`, using the recorded upstream
  bounded finite-projective model definition without any private replacement.
- `C = R lim K_n` after restriction to A: the product instance and `p`, `δ`, `hlim`
  specify its Roos triangle via the recorded `IsDerivedLimitTriangle` definition.
  The theorem applies to every such triangle; it does not select a cone or impose
  any extra vanishing or boundedness on the input tower.
- Perfectness of the limit: `IsPerfect C`.
- Derived I-completeness: `IsDerivedComplete I C`, precisely the recorded vanishing
  condition for all constant multiplication towers, not ordinary adic completeness.
- Canonical reductions: `adicLimitReduction` is defined by transposing
  `p ≫ Pi.π _ n` through `adj n`. The third conjunct asserts these actual maps are
  isomorphisms for every positive level, including the first.
- Compatibility: the final equality compares their adjoint images in D(A) with the
  restricted given transition. The unit/comparison composite is the adjoint image of
  the reduction map. Applying the inverse hom-equivalence at the lower level gives
  precisely equality of the two reduction routes in D(A/I^(n+1)). Iteration gives
  the equality for every pair of levels. Thus restriction of scalars is not assumed
  faithful on derived morphisms.

Dependency declarations read and used:

- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, `IsAdicComplete`.
  Read their complete definitions and docstrings in the pinned Mathlib source.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; read their localization signatures and docstrings.
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`: `SheafOfModules.derivedChangeOfRings`;
  imported as the specified derived change-of-rings input. The module-ring case is
  presented by its equivalent derived tensor/restriction adjunction universal property.
- `WeilConjectures.CategoryTheory.DerivedCategory.Perfect`:
  `DerivedCategory.IsPerfect`; read its full bounded finite-projective definition.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimitTriangle`, `CategoryTheory.IsDerivedLimit`.
  The local recorded module was absent, so its full source was read using
  `scompile.py --source WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`.
  It specifies exactly the Roos-triangle property. The recorded module is imported.
- `Sheaf.RingTheory.DerivedCompleteModuleComplex`:
  `DerivedCategory.IsDerivedComplete`; read the full definition and docstring.

Additional existing APIs used, without duplication: Mathlib's
`Ideal.Quotient.factorPowSucc`, `Ideal.Quotient.factor_comp_mk`,
`ModuleCat.restrictScalars`, `ModuleCat.restrictScalarsComp'`, and exact restriction
instances; upstream `Functor.mapDerivedCategoryNatIso` and
`Functor.mapDerivedCategoryCompIso`. The composition isomorphism is induced by the
identity-on-elements underived isomorphism, not an arbitrary natural isomorphism.
The available proof dependencies `Sheaf.RingTheory.RingPseudoCoherent` and
`Sheaf.Algebra.Homology.KFlatTelescopeClosure` are proof-only imports. The other
proof ingredients have no recorded declaration yet and are documented in the
six-step theorem docstring, without treating them as statement prerequisites.

Edge cases checked: zero ring; zero ideal (constant quotient system); unit ideal
(completeness then forces the zero ring); zero tower; first level n=1; arbitrary
non-finitely-generated ideals; arbitrary non-Noetherian complete rings. All are
included. The only index shift is n -> n+1, so no zeroth quotient is inadvertently
used as the perfectness assumption. Product and Roos-triangle parameters specify
the derived limit already named in the node, rather than choosing a different limit.
No regularity, Noetherian, ideal-finiteness, flatness of the quotient map, or uniform
cohomology bound is assumed.

Searches for existing declarations (2026-10-15):

- `msearch.py ... leanfinder`: “Compatible derived reductions over powers of an ideal
  of a complete ring have a perfect derived inverse limit”: eight hits concerning
  Henselian rings, formal smoothness, BDeRhamPlus, untilts, and ordinary completion;
  none concerns perfect derived inverse-limit reconstruction.
- `msearch.py ... loogle`: `DerivedCategory.IsPerfect, IsAdicComplete`: zero hits;
  Loogle reports the project-specific first identifier unknown.
- `msearch.py ... grep`: `IsPerfect.*[Ll]imit|[Ll]imit.*IsPerfect`: zero hits.
- `msearch.py ... leansearch`: “Perfect inverse limit reconstruction over an adically
  complete ring”: service unavailable (Internal Server Error), recorded as unavailable.
- `rg` over pinned upstream `WeilConjectures` and project `lean/Sheaf` for the item ID
  and the perfect/limit pattern: no existing statement. Searches for the proposed
  helper and theorem names in those trees and `dag/lean_names_upstream.json` found
  no existing declarations. Searches for scalar-extension and restriction APIs found
  the existing change-of-rings, mixed tensor, exact derived-functor and restriction
  composition APIs used above; no reconstruction theorem.

Validation: the delivered module compiled cleanly with `scompile.py NJ
lem-weil-pbc-rlim-perfect-complete <file>`, nice 19, two threads, 60 seconds per file.
The server reports 1.8 seconds for the module. No local compiler or library build ran.
No statement dispute or node fault was found.


## Second reading by NJ

I independently read the node, its six proof steps, Tag 09AW
(`more-algebra.tex`, `lemma-Rlim-perfect-gives-complete`), and the full sandbox
module. The source introduces a ring and ideal, a tower over its positive-power
quotients, completeness, perfectness at level one, and transition-induced derived
reduction isomorphisms. The surrounding section does not assume Noetherianity,
finite generation of the ideal, or a uniform bound on the supplied tower. The
chapter is commutative algebra and uses unbounded derived categories. The node
adds explicit compatibility of the canonical reductions; this follows from the
projection construction and is rendered below. Verdict: the Lean says exactly
what the node says. No statement correction is necessary.

Object, hypothesis, and conclusion checklist (H3):

- Commutative ring A and arbitrary ideal I: `{A : Type u} [CommRing A]
  (I : Ideal A)`. Match; neither domain nor nonzero-ring hypotheses appear.
- Bijective completion map: `[IsAdicComplete I A]`. I read the Mathlib
  `IsHausdorff`, `IsPrecomplete`, and `IsAdicComplete` definitions and
  `AdicCompletion.of_bijective_iff`. With M = A the submodules are exactly
  the ideals I^n; this is the recorded companion notion of
  `def-weil-pbc-adic-completion`, not a stronger topological completeness.
- Positive-level derived objects: `K n : DerivedCategory
  (ModuleCat.{u} (A ⧸ I ^ (n + 1)))`. Lean n = 0 means paper n = 1,
  and every positive paper index occurs once. The `HasDerivedCategory`
  instances specify the localizations used by the recorded `IsPerfect` API.
- Transitions over the larger quotient: `t n : K (n + 1) ⟶
  (adicStepRestriction I n).obj (K n)`. This is a morphism in the larger
  quotient's derived category, not merely in D(A). I checked
  `factorPowSucc`, restriction exactness, and the composition isomorphism;
  `adicTowerTransition` uses that same t and canonical identification.
- Derived base change: `L`, `adj`, `B`, `badj` specify left adjoints to
  the exact restriction functors for the two kinds of quotient ring map.
  This is the universal characterization of derived tensor, and does not
  impose flatness or choose unrelated comparison maps. Uniqueness of a
  left adjoint with its adjunction identifies every such realization with
  derived scalar extension and identifies its transposed maps. The recorded
  sheaf change-of-rings theorem was opened: it supplies the K-flat derived
  construction; it is not itself a module restriction or a faithful functor.
- Transition-induced isomorphisms: `hbase` asserts `IsIso` of the inverse
  hom-equivalence applied to t. Thus the map is exactly the transition's
  derived reduction, rather than an arbitrary isomorphism of the two objects.
- Perfect first term: `hperfect : IsPerfect (K 0)`. I opened upstream
  `DerivedCategory.IsPerfect`: its witnesses are a complex P, integers a,b,
  strict bounds, projectivity and module finiteness in every degree, and an
  isomorphism to `Q.obj P`. This is the recorded bounded finite-projective
  notion for every commutative ring.
- Specified derived limit: `C`, `p`, `δ`, the product instance, and `hlim`.
  I read the recorded upstream `IsDerivedLimitTriangle` via
  `scompile.py --source` and the local side module as well. Its condition
  is precisely that `C → product → product → C[1]`, with middle map 1-s,
  is distinguished. Product existence is part of this recorded notion;
  no alternative cone, chain-level limit, or boundedness is assumed.
- Perfectness and completeness conclusions: `IsPerfect C ∧
  IsDerivedComplete I C`. I opened `DerivedCompleteModuleComplex.lean`:
  the latter quantifies over f in I and every derived limit of the constant
  multiplication-by-f tower and requires `IsZero`; it is derived completeness,
  not the ordinary completion condition on cohomology modules.
- Canonical reductions: `∀ n, IsIso (adicLimitReduction ... n)`.
  Its definition is the inverse adjunction hom-equivalence of
  `p ≫ Pi.π _ n`, so the conclusion refers to the actual limit projections.
- Compatibility: the last equality is `η_high ≫ U_high(q_high) ≫ t_A =
  η_low ≫ U_low(q_low)`, with `t_A = adicTowerTransition ... n`.
  The two sides are the adjoint images of the two reduction routes from
  `L_low.obj C` to `K n`, using the canonical composite-adjunction
  identification `L_low ≅ L_high ⋙ B n`. The lower adjunction's
  hom-equivalence is bijective, so this equality is equivalent to equality
  of those routes over the lower quotient. This does not rely on restriction
  of derived morphisms being faithful. Consecutive equalities iterate to
  all pairs of positive levels. Match; no compatibility clause is omitted.

Edge cases: the index is the required nonempty positive tower, not a variable
index set, so an empty index set is inapplicable. There is no level A/I^0;
`K 0` is exactly K_1. Zero tower and zero ring are included. I = 0 is the
constant quotient tower. I = top is included, with ordinary completeness
forcing A to be zero. No characteristic restriction, nonempty geometric
object, Noetherian hypothesis, finite ideal-generation hypothesis, or
finite amplitude hypothesis on the tower occurs. Empty schemes are not
objects of this algebraic statement. Universe u is arbitrary; rings and
modules can be placed in any larger common universe, and the same-universe
perfectness signature is the recorded upstream interface, not an equality
between site-object and site-morphism universes. All variables and the one
universe are explicitly bound.

Independent H4 searches, with different vocabulary from the worker:

- LeanFinder: “Algebraization of compatible perfect complexes over the
  infinitesimal thickenings of an adic ring”. Eight hits, concerning formal
  smoothness, lifts, completion, and BDeRhamPlus; none is this theorem.
- Loogle: `"IsAdicComplete", "IsIso"`. No hits.
- Mathlib grep via msearch: `algebri[sz].*perfect|perfect.*(Roos|reconstruct)|
  [Rr]lim.*perfect`. No hits.
- Independent rg over upstream WeilConjectures, project lean/Sheaf, and
  dag/lean_names_upstream.json with algebraization, reconstruction, Roos,
  rlim/perfect, and helper-name patterns. The only conceptual hit was the
  docstring of `isPerfect_compactlySupportedGlobalSections_integral` in
  PointPerfect.lean. I opened it: its conclusion is perfectness of compactly
  supported cohomology under Noetherian-domain, principal-ideal, finite-residue,
  and scheme hypotheses. It is not the arbitrary-ring reconstruction theorem.
  No helper or theorem name collision was found. All five helpers construct
  the item-specific maps from existing restriction and adjunction APIs.

H5/H6/H8/H9 review: the five definitions have real data; the sole theorem
body is `sorry`. The source and blueprint appear in every declaration's
docstring, and the main theorem carries all six proof steps, including the
finite-free complement construction, square-zero reconstruction, uniform
residue-field bound, pointwise criterion, torsion completeness, and transition
compatibility. No local notation, private definitions, local instances, hidden
let/show statement binders, or unbound parameters occur. The node's
`lean.statement` was mechanically compared with the exact file signature
and is verbatim equal. There are no new nodes or dependency modules to audit.

Mismatches and changes: none found. The Lean and node were retained unchanged;
this independent second-reading section and search records were added.
Validation uses only the required server scompile and deliver2 checks, with
nice 19, two threads, and 60 seconds per file; no local compiler or build.
