## Worker report

The module `Sheaf.Algebra.Homology.LocallyFreeDerivedHom` states
`CategoryTheory.locallyFree_derivedHom`, with its sole postponed proof `sorry`.
All helper definitions have real data. There are no new DAG nodes or dependency repairs.

The signature uses the equivalent uniform degree-zero formulation on ALL bounded-below
complexes, including every shift. In detail, apply `e P hP` to `K[n]`. Localization
commutes with shift, so its left side is `Hom_D(P[0],QK[n])`. The tensor functor is
additive and termwise, so its value on `K[n]` is canonically `(P∨ ⊗ K)[n]`, including
the differential sign. Zeroth hypercohomology of that shifted object is precisely
`H^n(RΓ(P∨ ⊗ K))`. Thus no degree, negative degree, or shift is excluded.

Hypothesis and clause correspondence:

- The small ringed site is `C : Type u`, `[SmallCategory C]`,
  `J : GrothendieckTopology C`, `R : Sheaf J CommRingCat.{u}`. The common universe
  is the node's small-skeleton convention, not a restriction to schemes or to a
  site with a final object. The source Tag 08JJ uses commutative module tensors.
- Module sheaves use the recorded `CategoryTheory.ringedSiteModules` abbreviation,
  which is exactly Mathlib `SheafOfModules`. The only localization parameter is
  `[HasDerivedCategory.{w} ...]`, with the Hom universe `w` independent of `u`.
- `P.IsFiniteLocallyFree` is the upstream general-site class. Its local generator
  data are locally free and finite, and the finite ranks vary between covering
  objects. It is not the constant-rank class, a global finite-free hypothesis,
  or a hypothesis of finite presentation on sections.
- `locallyFreeDualTensor` is `tensorLeft (homObj P (unit R))` with the recorded
  monoidal tensor. Thus the dual is the recorded sheaf Hom and the tensor is the
  sheafification tensor, not a sectionwise tensor mistakenly treated as a sheaf.
- `K : CochainComplex ... ℤ`, `hK : CochainComplex.plus _ K` encode an arbitrary
  bounded-below complex with no specified common lower bound.
- `DerivedCategory.singleFunctor _ 0` is `P[0]`; `DerivedCategory.Q` is localization.
  The output `≃+` is an isomorphism of additive abelian groups, with the Hom group
  on the left and the cohomology group on the right.
- The right side uses the shared `ringedSiteZerothHypercohomology`, not a new
  definition of cohomology. For a bounded-below tensor complex this agrees with
  computation by a bounded-below injective resolution. The proof docstring
  explains the intervening bounded-below K-injective model and its comparison
  with a degreewise injective model; it does not claim the tensor of an
  injective is necessarily injective, or that sections are exact.
- The first conjunct is the naturality square for `p : P' → P` and `f : K → L`.
  The tensor chain map `t` is constrained in EVERY degree to be exactly
  `homObjMap p id ⊗ f.f i` by `locallyFreeDualTensorMap`. It is not an arbitrary
  comparison map or extra assumption about the objects: the canonical termwise
  tensor map always has these components. Inverting quasi-isomorphisms gives
  the same square for derived morphisms (or use maps between K-injective models).
- The second conjunct fixes the equivalence on every global tensor cycle in a
  bounded-below K-injective target. `iCycles` includes the cycle in the degree-zero
  term; `locallyFreeEvaluate` contracts it using the actual tensor-Hom evaluation;
  `singleObjXSelf` identifies the degree-zero source with P. If `f` is the chain
  map with that contraction as its degree-zero component, `e(Qf)` is exactly the
  cycle class (`homologyπ`) followed by the ordinary-to-derived cohomology map.
  Every such evaluation cycle gives this chain map; maps to K-injectives are
  represented by these cycles. Together with naturality, this fixes the entire
  family, rather than merely asserting unrelated abstract isomorphisms.
- Shift compatibility is encoded by that SAME normalization on all shifted
  complexes: applying it to `I[n]` evaluates a cycle `P → I^n`, with the shifted
  differential `(-1)^n d`. Replacing K by K[m] therefore evaluates the same cycle
  in degree n+m as applying the original formula in degree n+m. This is exactly
  the node's shift compatibility, not an independent choice of isomorphism per n.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  (also checked against the current server source using `scompile.py --source`).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`; the derived single functor is the
  shared Mathlib construction.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, `homObjMap`; full signatures and docstrings read.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`: its public upstream
  `SheafOfModules.monoidalCategory`, whose tensor is sheafification of the
  presheaf tensor, and its tensor/sheafification comparison.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomology`:
  `CategoryTheory.ringedSiteZerothHypercohomology`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree`; general-site varying-rank class read.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree` and its public
  `MonoidalClosed`: tensor additivity, `SheafOfModules.tensorHomEquiv`.
- The stated proof dependencies are imported without `public`, including KFlat,
  HomComplex, KInjectiveHomComplex, LocalizedModuleAdjunctionExact,
  BoundedBelowInjectiveResolution, FiniteFreeInternalHomExact, the Mathlib local
  bijectivity criterion, K-injective localization comparison and shift theorem.

Edge cases checked before finalizing the statement: rank zero, varying ranks,
zero complex, empty underlying category, a topology allowing empty coverings,
negative lower bound, n=0, n negative, arbitrary further shifts. Neither a terminal
site object nor exactness of global sections nor a uniform rank is assumed.

Searches for an existing statement:

- `msearch.py ... leanfinder "Derived Hom from a locally finite free module sheaf
  on a ringed site equals cohomology of derived global sections of its dual tensor
  a complex"`: 8 hits, for ordinary sheaf cohomology, the sheaf-module abelian
  instance, sheafification equivalences and unit sections; none states the formula.
- `msearch.py ... loogle "SheafOfModules.homObj, DerivedCategory"`: 0 hits;
  unknown identifier `SheafOfModules.homObj` in that search service.
- `msearch.py ... grep "locally.*free.*derived|derived.*locally.*free|homObj.*Derived|homObj.*rightDerived"`:
  0 hits.
- `rg` of the upstream project for this exact node id: no occurrence.
- `rg` of upstream and project Lean for locally-free/derived-Hom/ringed-site-Hom
  patterns: found InternalHomFree, Bidual, RhomGlobalSections, the scheme-only
  FiniteLocallyFreeDerivedHom, GlobalHomShiftedHypercohomology and related modules;
  none is the locally finite free, bounded-below, arbitrary-ringed-site formula.
- DAG searches found the existing zeroth hypercohomology, Hom complex, scheme-only
  finite-locally-free definitions, and bounded-free RHom model. They were inspected
  to avoid duplicating notions; the bounded-free model assumes global direct
  summands and is neither this local-freeness statement nor a missing definition.

The source `literature/stacks-project/sites-cohomology.tex`,
`lemma-dual-perfect-complex` (Tag 08JJ), was read including its evaluation map and
finite-free calculation. No statement dispute or source correction is needed.

## Second reading by NC

I independently read the node, its six proof steps, the complete delivered module,
Stacks `sites-cohomology.tex`, Tag 08JJ (`lemma-dual-perfect-complex`, including the
finite-free evaluation calculation), and the declarations behind its dependency records.
The source introduces an arbitrary ringed site and a perfect derived object; its final
formula specialized to P[0] gives precisely this node. Its tensors and internal Hom use
commutative coefficients. No scheme, final object, Noetherian hypothesis, or hypothesis
on characteristic is assumed in this specialization.

Object/hypothesis/conclusion checklist (each verdict is pass):

- Small ringed site: `{C : Type u} [SmallCategory C]`, `J : GrothendieckTopology C`,
  `R : Sheaf J CommRingCat.{u}`. The common bound implements the small-skeleton size
  convention. Raising u accommodates an initially larger coefficient or site universe;
  there is no equality imposed on independently supplied universe parameters.
- Module sheaves: `ringedSiteModules.{u} ((sheafCompose J
  (forget₂ CommRingCat RingCat)).obj R)` is the recorded transparent abbreviation of
  Mathlib `SheafOfModules`. I read RingedSiteModules, not merely its name.
- Derived category and Q: the recorded Mathlib `DerivedCategory`, `Q`, and
  `singleFunctor _ 0` are localization at quasi-isomorphisms and P[0].
  `[HasDerivedCategory.{w} ...]` leaves the localization Hom universe independent.
- Local finite freeness: `P.IsFiniteLocallyFree` is the upstream class whose field is
  local generators data with `IsLocallyFreeData` and `IsFiniteType`. The former makes
  the local free presentation an isomorphism, the latter makes each generator index
  finite. I also read `LocalGeneratorsData.coversTop`: this is local on every object,
  and neither a globally fixed rank nor a terminal site object is required.
- Dual and tensor: `locallyFreeDualTensor` uses the recorded `homObj P (unit _)`
  and `tensorLeft`. I read InternalHom's `homObj` and `homObjMap` and Monoidal's
  `monoidalCategory` and `tensorObjIsoSheafification`: these are slice-linear sheaf
  Hom and sheafified tensor, exactly the dependency notions, not sectionwise tensor.
- Bounded-below K: `K : CochainComplex ... ℤ` and `CochainComplex.plus _ K`.
  Mathlib defines plus as existence of an arbitrary integer lower bound.
- Group isomorphism: `e P hP K hK` is an `AddEquiv` from derived Hom to the recorded
  `ringedSiteZerothHypercohomology` of the termwise dual tensor. I read the latter's
  actual definition: `Hom(unit,-).rightDerivedFunctor` followed by degree-zero
  homology. Thus it is RΓ, not ordinary global sections or degree-zero sheaf homology.
- Every n and shifts: apply the one family e to K[n]. The Mathlib plus property is
  stable under every integer shift (read its instance in CochainComplexPlus).
  The additive termwise tensor commutes with the signed shift differential, so
  H⁰ RΓ(P∨ ⊗ K[n]) identifies with Hⁿ RΓ(P∨ ⊗ K). This is an equivalent uniform
  degree-zero presentation of the integer-quantified formula, not a restriction to n=0.
- Naturality in P and K: the first conjunct precomposes by `singleFunctor.map p`
  and postcomposes by `Q.map f`. Its `t` is constrained in every degree to
  `homObjMap p id ⊗ f.f i`. This is the canonical tensor map, which exists because
  these components commute with the differentials; t is not arbitrary extra data
  on which the result depends. Exactness of dual tensor for locally finite free P
  makes its action invert quasi-isomorphisms, extending this square to derived maps.
- Canonical evaluation normalization: the second conjunct uses actual tensor-Hom
  evaluation (`tensorHomEquiv.symm id`, whose signature I opened), and the explicit
  ordinary-to-derived cohomology map `locallyFreeSectionsComparison`.
  On bounded-below K-injective K, every derived map from P[0] is represented by a
  cycle P → K⁰. Local finite freeness identifies these with global tensor cycles z.
  The stated normalization therefore fixes e on every input. Naturality along a
  bounded-below injective resolution fixes e for every other K. Applying this same
  normalization to shifted K-injectives forces shift compatibility; independent
  unrelated isomorphisms for different degrees cannot satisfy these conditions.
- The bounded-below injective computation is respected: tensor with the dual is
  exact and carries the chosen injective resolution to a bounded-below K-injective
  Hom complex. Resolving that again degreewise injectively gives a homotopy-equivalent
  model; applying sections preserves that homotopy. The docstring explicitly gives
  this comparison rather than assuming sections exact or tensor-injectives injective.

Edge cases: rank zero and independently varying finite ranks are included by the
class's finite index types; the empty site and empty coverings are not excluded.
The zero module/complex, negative bounds, n=0, negative n, and arbitrary iterated
shifts all satisfy the same typing and normalization. There is no field,
characteristic, nonzero-ring, nonempty-site, or uniform-bound assumption.

Independent H4 searches, using different wording from the author:

- LeanFinder: “Morphisms from a dualizable locally free sheaf to a derived complex
  computed by global sections of the dual tensor”: eight hits, including
  `SheafOfModules.unitHomEquiv`, `freeHomEquiv`, and `CategoryTheory.Sheaf.H`.
  These give ordinary sections/free Hom or nonnegative sheaf cohomology, not this
  evaluation-normalized derived formula.
- Loogle: `"SheafOfModules", "cohomology"`: zero hits.
- `rg` in Mathlib's sheaf-module sources, upstream WeilConjectures, project Sheaf,
  and the upstream declaration index for dual/Hom and finite-locally-free patterns.
  I opened InternalHomFree, the signatures of FiniteLocallyFreeDerivedHom and
  GlobalHomShiftedHypercohomology, and RhomGlobalSections. The first two derived
  results concern schemes; RhomGlobalSections concerns derived internal Hom and
  does not identify it with termwise dual tensor. None replaces this statement.
  Existing tensor, sheaf Hom, and hypercohomology notions are reused.

There are no new nodes, dependency modules, or statement_change to audit. All helpers
have concrete data; the sole postponed theorem is the item itself, with a source and
proof docstring following the node's local evaluation, exactness, resolution,
cohomology, and naturality steps. All helper declarations carry the item's blueprint
and source. I found no mathematical or signature mismatch and changed no Lean or node
content; this independent reading is the only addition. No unbound variables, private
notions, file-local notation, local instances, or proofs of auxiliary theorems occur.

Validation: `scompile.py NC lem-weil-pbc-ringed-site-locally-free-derived-hom
lean/Sheaf/Algebra/Homology/LocallyFreeDerivedHom.lean` completed cleanly on the
server (29.2 seconds for the item; nice 19, two threads, 60-second per-file limit).
The stored `lean.statement` matches the theorem signature after whitespace
normalization, and `lean.declarations` lists every helper and the main theorem.
