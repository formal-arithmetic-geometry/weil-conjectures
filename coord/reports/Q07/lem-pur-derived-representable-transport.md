## Worker report

The module `Sheaf.CategoryTheory.Abelian.DerivedRepresentableTransport` states
`lem-pur-derived-representable-transport` in four named theorems. All four proofs
are exactly `by sorry`; each declaration has this node's blueprint tag and its
complete corresponding proof in the docstring. The node changes only in `lean`.
No statement correction, new node, or dependency repair was needed.

The remaining declarations are actual constructions of the canonical maps and
identifications named in this node. They belong to this node's notion and are
listed in `lean.declarations`, following the human's helper-declaration rule.
There is no arbitrary natural transformation standing in for the comparison.

Hypotheses and objects:

| Node text | Lean |
| --- | --- |
| Abelian A and B with enough injectives | `A : Type u₁`, `B : Type u₂`, `[Category.{v} A]`, `[Category.{v} B]`, `[Abelian A]`, `[Abelian B]`, `[EnoughInjectives A]`, `[EnoughInjectives B]` in the explicit section-variable declaration. |
| Fixed compatible Hom universes | A and B have the common Hom universe `v`, so both represented functors take values in `AddCommGrpCat.{v}`. Their object universes `u₁`, `u₂` remain independent. `[HasDerivedCategory.{w₁} A]`, `[HasDerivedCategory.{w₂} B]`, `[HasDerivedCategory.{wAb} AddCommGrpCat.{v}]` retain independent derived-Hom universes. The composition theorem adds independent `u₃`, `w₃` for C. |
| Additive exact L | `(L : A ⥤ B)`, `[L.Additive]`, `[PreservesFiniteLimits L]`, `[PreservesFiniteColimits L]`. |
| P, P', and the specified isomorphism | `(P : A) (P' : B) (d : L.obj P ≅ P')`. |
| Additive left exact S and S' valued in Ab | Functors to `AddCommGrpCat.{v}`, with `.Additive` and `PreservesFiniteLimits` instances. Finite-limit preservation is the recorded encoding of additive left exactness. |
| The additive representing isomorphisms | `θ : preadditiveCoyoneda.obj (op P) ≅ S` and `θ'` for P'. Their components are isomorphisms in abelian groups, hence additive. |
| Natural transformation lambda | `tau : S ⟶ L ⋙ S'`. |
| Its representing square for every M and f | `h : ∀ (M : A) (f : P ⟶ M), θ'.hom.app (L.obj M) (d.inv ≫ L.map f) = tau.app M (θ.hom.app M f)`. Lean's composition order reverses the written order of the paper's usual function-composition notation. |
| Exact termwise DL with termwise shifts | The published `L.mapDerivedCategoryPlus`, `L.mapDerivedCategory`, `.commShiftIso`, `.mapDerivedCategorySingleFunctor`, and `.mapDerivedCategoryPlusFactorsh`; no alternative derived functor or shift structure. |
| Canonical b | `representableTransportComparison L S S' tau` is `rightDerivedDesc` applied to `representableTransportUnit`. The latter is the termwise `tau`, the canonical termwise-composition identification, the target derived unit, and the inverse exact factorization. |
| The specified chi and chi' | `representedTransportHomEquiv` first applies cohomology to `rightDerivedFunctorPlusNatIso θ.symm`, then applies `representableTransportRoof`. The latter chooses exactly the family in `exists_rhom_hom_derived_roof`; its normalization on every injective resolution determines this family. No unrelated isomorphism is supplied as a hypothesis. |

Clauses of the conclusion:

1. `derived_representable_transport` starts with the factorization equation for
   b, followed by uniqueness among natural transformations satisfying that same
   equation. This is precisely the source-unit factorization in the node.
2. Its third conjunct quantifies over every bounded-below F, I, J and every
   chosen resolution `e : F ⟶ I`, `e' : L.mapCochainComplexPlus.obj F ⟶ J`.
   `[QuasiIso e.hom]`, `[QuasiIso e'.hom]`, `_hi`, `_hj` are precisely the
   quasi-isomorphism and degreewise-injectivity conditions. Boundedness is part
   of `CochainComplex.Plus`, not an extra uniform bound or a nonnegative-degree
   restriction. There is no injectivity assumption on LI.
3. That conjunct produces a chain map t with
   `Nonempty (Homotopy (L(e) ≫ t) e'.hom)` and asserts that every other such t'
   is homotopic to t. Thus the comparison is unique up to homotopy.
4. `representableTransportChainMap` is exactly the complex map S(I) -> S'(LI)
   -> S'(J). The next equality says its localized image computes b, using
   `representableTransportModel S e` and `representableTransportModel S' e'`.
   The final `S'.rightDerivedFunctorPlus.map (representableTransportExactIso L F).inv`
   identifies Q(LF) with DL(QF). These are the canonical identifications implicit
   in the node, not additional choices.
5. The final part of that conjunct quantifies over each integer a and each
   cocycle `f : P ⟶ I.obj.X a`. It asserts that `d.inv ≫ L.map f ≫ t.f a` is
   closed and that the termwise model evaluated on `θ(f)` equals its image
   through `θ'`. This gives exactly the stated cocycle formula and hence its
   cohomology class.
6. The fourth conjunct quantifies over every X in D+(A), every integer a and
   every alpha in H^a(RS(X)). It states `chi'(H^a(b)(alpha)) = DL(chi(alpha)) d⁻¹`.
   `representableTransportHom` writes out the degree-zero isomorphism d⁻¹,
   the single-functor comparison, the exact derived action, and its shift
   comparison. This includes every QF asked for by the node.
7. `derived_representable_transport_independence` asserts that a boundary has
   zero localized single-complex map, and that homotopic t induce equal
   localized model maps. Combined with the formula for every e and e' and
   uniqueness up to homotopy, this makes the model independent of all three
   choices e, e', t and of the cocycle representative. The theorem gives the
   boundary and homotopy assertions directly, rather than assuming them.
8. `derived_representable_transport_comp` introduces C, L₂, P'', d₂, S'', θ''
   and tau₂ with the analogous exactness, left exactness, and square hypothesis.
   Its first conjunct verifies the total representing square using
   `L₂.mapIso d ≪≫ d₂` and `tau ≫ whiskerLeft L tau₂ ≫ associator.inv`.
   Its second conjunct identifies the comparison of L₂L with the composite of
   comparisons under `mapDerivedCategoryPlusCompIso`. Its third conjunct is the
   Hom formula obtained by applying the two exact derived Hom actions in order,
   with the canonical `mapDerivedCategoryCompIso` on the total formula's target.
9. `derived_representable_transport_coherence` treats an isomorphism
   `zeta : L ≅ T` of exact functors (in particular, of any two composites).
   `hd : zeta.hom.app P ≫ dT.hom = d.hom` and
   `htau : tau ≫ whiskerRight zeta.hom S' = tauT` express exactly agreement of
   the underived data under it. Both representing squares are included.
   Its first conjunct identifies the derived comparisons through
   `mapDerivedCategoryPlusNatIso zeta`. Its second identifies the displayed Hom
   formulas through `mapDerivedCategoryNatIso zeta` and the degree-a shift.
10. No theorem assumes `L.PreservesInjectiveObjects`, `T.PreservesInjectiveObjects`,
    or `L₂.PreservesInjectiveObjects`.

`representableTransportResolutionInverse` uses the inverse of the raw localized
quasi-isomorphism and the canonical quotient comparisons, then the fully faithful
Plus inclusion's `preimage`. This is a construction of Q(e)⁻¹ without assuming an
additional invertibility hypothesis on Plus.Q. No deferred theorem is needed to
define it. The roof equivalence is chosen from a theorem characterizing its
values on all injective resolutions; it does not choose an unspecified object
from an unstructured existence statement. All definitions have real data.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`.
- `def-sp-enough-injectives`: `CategoryTheory.EnoughInjectives`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-weil-pbc-bounded-derived-subcategories`: `DerivedCategory.Plus`,
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure`, together with the
  published Plus.Q and Plus.Qh from `Mathlib.Algebra.Homology.DerivedCategory.Plus`.
- `def-sp-left-exact-additive`: `Functor.Additive`, `PreservesFiniteLimits`,
  `Functor.preservesFiniteLimits_of_preservesKernels`, and the recorded
  `Functor.rightDerived` signature. Here complexes require the total
  `rightDerivedFunctorPlus`, not the object-only natural-number `rightDerived`.
- `lem-weil-pbc-right-derived-plus-injective`: its `mathlib_match` is the usable
  record. `Functor.rightDerivedFunctorPlus`, `.rightDerivedFunctorPlusUnit`
  from `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`, and
  `rightDerivedDesc` from `Mathlib.CategoryTheory.Functor.Derived.RightDerived`
  construct the canonical b. The unit's injective-computation instance was read
  in `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`.
- `lem-sc-p1-rhom-hom-derived-roof`: `Functor.exists_rhom_hom_derived_roof`,
  `Sheaf.CategoryTheory.Abelian.RHomDerivedRoof`; its full signature and
  resolution-uniform normalization are used by the roof helper.
- Proof dependencies: `Functor.mapDerivedCategoryFactors` and its termwise
  shift-compatible exact functor from `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`;
  `CochainComplex.isKInjective_of_injective` from
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`;
  `CochainComplex.IsKInjective.Qh_map_bijective` and `.quasiIso_iff` from
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`;
  `DerivedCategory.Plus.Qh_map_bijective_of_isKInjective` from
  `Mathlib.Algebra.Homology.DerivedCategory.Plus`;
  `DerivedCategory.Plus.exists_injective_nonempty_iso` from
  `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`.
  These are already in the public dependency closure; no proof import is omitted
  for a cycle.
- Additional published canonical interfaces used directly:
  `rightDerivedFunctorPlusNatIso` from
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp`;
  the exact Plus restriction, composition and natural-isomorphism comparisons
  from `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`;
  `preadditiveCoyoneda` from Mathlib's preadditive Yoneda files.

Sources read: Stacks `derived.tex`, the full lemmas
`lemma-injective-acyclic` (05TH), `lemma-enough-injectives-right-derived` (05TI),
`lemma-right-derived-exact-functor` (015F), and the injective-resolution statement
(013K); the blueprint main-20261015 `thm-pur-affine-line-orientation` statement
and proof, including the final etale-origin transport sentence. The node's
representability/coherence refinements are agent calculations, as its source
record explicitly says, not claims that those Stacks tags state them verbatim.
No repair-note file exists for this item in the read repository.

Edge cases checked mathematically: L = identity with identity d and tau gives
identity transport; zero P or P' gives zero represented cohomology and zero Hom;
zero complexes and zero functors are included; a = 0 is the ordinary represented
map; negative and odd a remain allowed, using the published signed shift and
`Cocycle.fromSingleMk` conventions. Identity and associatively identified exact
composites are covered by the composition and coherence theorems. Arbitrary
lower bounds and independent derived-Hom universes remain allowed. No nonempty
index set, unbounded injective-resolution existence, Grothendieck hypothesis,
or preservation of injectives was introduced.

Searches (2026-10-21):

- `msearch.py ... leanfinder` query: "Exact functor transports represented left
  exact functors and their bounded below right derived comparison via injective
  resolutions and derived Hom". Eight results, including
  `Ext.mapExactFunctor`, `Ext.mapExactFunctor_hom`, `mapDerivedCategoryFactors`,
  `mapDerivedCategoryFactorsh`, and
  `LocalizerMorphism.rightDerivedFunctorComparison`. None states all the
  represented comparison, injective-model formula, roof normalization and
  composition/coherence clauses.
- `msearch.py ... loogle` query:
  `CategoryTheory.Functor.rightDerivedDesc, CategoryTheory.Functor.mapDerivedCategoryFactors`.
  Zero hits for the combined query. The actual declarations were read locally
  and are used; the zero result does not mean these declarations are absent.
- `msearch.py ... grep` query `rightDerivedFunctorPlus|rightDerivedNatTrans`,
  under `Algebra/Homology/DerivedCategory`: five hits in
  `RightDerivedFunctorPlus.lean`, providing the functor and unit, not the full
  node statement.
- `msearch.py ... leansearch` query: "Right derived comparison of representable
  additive left exact functors across an exact functor computed by maps between
  bounded below injective resolutions". Eight hits: object rightDerived,
  injectiveResolutions, rightDerived_map_eq, NatTrans.rightDerived,
  isoRightDerivedObj_hom_naturality_assoc, rightDerived_app_eq,
  isoRightDerivedObj, rightDerivedDesc. The last is used as a construction;
  none is the full statement.
- `rg -n` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id found
  no declaration. Searches for `rightDerived.*[Cc]omparison`,
  `representable.*[Tt]ransport` and the candidate declaration names found related
  derived-comparison APIs, but no existing full-node statement. The final
  candidate-name search also included `dag/lean_names_upstream.json` and found
  no collision. The existing RHomRoof modules were opened and reused.

Validation: prescribed `scompile.py Q07 lem-pur-derived-representable-transport`
compiled the module separately under both the sandbox and final library module
names, with no errors or warnings. There are four intended theorem sorries,
all named and all covered by this DAG node. No definitions contain sorry.
The final delivery dry run and push are performed after this report.

## Second reading by Q07

No independent worker was started: the dispatcher's brief forbids other agents
and assigns independent review to the maintainer after delivery. This section
records no claim of an independent review. My final self-check matched all
hypotheses and all clauses above against the node and checked the canonical
single, localization, shift, composition and natural-isomorphism orientations.
