## Worker report

The module `Sheaf.CategoryTheory.ExactFunctorTowerFiltrationSplicing` states
`CategoryTheory.exactFunctorTowerFiltrationSplicing`, with one postponed theorem
and no new definition. The node's natural-language statement is unchanged.
The source was read in `literature/blueprint/latest/blueprint/sec-deligne-laumon-general/sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`,
final paragraphs on the open–closed exact sequence and splicing from the last
nonempty closed member. The expanded six-step DAG proof is included in the
statement docstring. All files are compiled only with the prescribed scompile wrapper.

Hypothesis and conclusion correspondence:

- `t : ℕ`, `A : Fin (t+1) → Type u`, and the families of `Category.{v}` and
  `Abelian` instances are the finite family of abelian categories. Object and
  morphism universes are independent. A finite family of categories can be
  placed in common object and morphism universes; no smallness is required.
- `T a : A a.succ ⥤ A a.castSucc` is the functor from the next stage to the
  preceding stage. `hadd`, `hlim`, `hcol` mean additive and exact (preserving
  finite limits and finite colimits), exactly the recorded dependency interfaces.
- `H`, `K`, `u`, and `π` are the objects and arrows displayed in the node.
  `hHt` says the last object is zero. `huπ`, `hu`, and `hπ` specify the zero
  composite and the kernel/cokernel universal properties, without choosing a
  section or assuming a split sequence. No additional mono/epi hypothesis is used.
- `n`, `Ks`, `hKzero`, `hKtop`, and `hKmono` are precisely the prescribed finite
  increasing filtrations in the kernels, including endpoints. Steps are Mathlib
  `Subobject`s (monomorphisms modulo isomorphism), not arbitrary objects or maps.
  `cokernel (Subobject.ofLE ... (hKmono a s))` is the original quotient `Q`.
- `P`, `hPinv`, `hPT`, `v`, and `hQ` are the optional isomorphism-invariant real
  labelled classes, their preservation by each functor, the original labels,
  and membership of the original quotients. Taking all classes to be universal
  supplies the unlabelled assertion with no extra restriction on the tower.
- The existential `N` is the output length. `hN` is exactly the sum over all
  stages from `a` through `t-1`; stages before `a` contribute zero. Thus at the
  terminal stage the sum is empty.
- `F`, `hFzero`, `hFtop`, and `hFmono` are simultaneous increasing filtrations
  of the `H a`, from bottom to top at length `N a`. A natural-indexed monotone
  extension is used to avoid casts on every index; after reaching top it is
  necessarily constant. Restricting to `0,...,N a` gives exactly the finite
  filtration. Conversely every finite filtration extends this way.
- `V` represents the composites `T_{a,c}`. Its equations `hVid` and `hVstep`
  normalize the diagonal to the identity and specify each composite by the
  next composite followed by `T a`. These equations force the prescribed
  functor, so no arbitrary functor replaces the composite.
- `hFkernel` specifies every step in the first block as the image of the original
  kernel subobject under `u`. `hFpullback` specifies every step of the second
  block as the inverse image of the exact functor's transported subobject.
  Transport is `imageSubobject (T.map L.arrow)`; exactness makes this arrow
  monic, so this is exactly the subobject `T L`. The inverse image is Mathlib's
  actual `Subobject.pullback`.
- Taking the second-block index to be zero and the first-block index to be
  `n a`, and using `hFzero`, `hKtop`, and `hFkernel`, gives exactly the stated
  junction `π⁻¹(0) = u(K)`; it is not assumed separately.
- `hQFkernel` identifies each first-block quotient with the original `Q`.
  `hQFtail` gives the displayed quotient isomorphism for successive inverse
  images, to `T a` applied to the next stage's actual successive quotient.
- The final universal conclusion gives the full ordered quotient assertion,
  not just the one-step recursion: for every `a ≤ c`, and original quotient
  `s : Fin (n c)`, the output position `r` is the sum of the lengths of stages
  `a,...,c-1` plus `s.val`. Its quotient is isomorphic to `V a c` applied to
  `Q c s`, and belongs to `P a (v c s)`. Zero-based `s` denotes the original
  quotient numbered `s+1`. These positions enumerate the output quotients in
  precisely the order in the node. Membership retains the exact input label,
  so every real common upper bound is retained as well.

Dependency declarations used and read:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`; the normal-mono/normal-epi formulation
  supplies the kernel/cokernel definition in the node.
- `def-galois-exact-functor`: `CategoryTheory.Limits.PreservesFiniteLimits` and
  `PreservesFiniteColimits`, `Mathlib.CategoryTheory.Limits.Preserves.Finite`.
  Their conjunction is exactly `CategoryTheory.exactFunctor` as read in
  `Mathlib.CategoryTheory.Limits.ExactFunctor`.
- `def-weil-pbc-additive-functor`: `CategoryTheory.Functor.Additive`,
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`.
- The proof-only imports are `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
  (`Functor.preservesHomologyOfExact`), `Mathlib.CategoryTheory.Abelian.Refinements`
  (`epi_iff_surjective_up_to_refinements`,
  `ShortComplex.exact_iff_exact_up_to_refinements`,
  `Limits.CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements`),
  `Mathlib.Algebra.Homology.ShortComplex.Exact` (`ShortComplex.Exact.gIsCokernel`),
  and `WeilConjectures.ConstructibleSheaf.Devissage`
  (`Subobject.cokernelOfLEMkIso`). Their relevant signatures were read. Thus all
  recorded proof dependencies have their modules imported; none closes a cycle.

Edge cases checked before finalizing: `t=0` leaves just the zero terminal object
with `N=0`, no functors, no kernel data, and no quotient indices. A zero kernel
filtration has bottom equal to top, so forces the kernel to be zero, exactly as
in the node. If all lengths vanish, all output sums vanish and bottom equals top
at every stage. Repeated subobjects give zero quotients and are allowed. Either
block at a splice may be empty, including the zero second block at the last
stage. The nonsplit sequence ℤ/2 → ℤ/4 → ℤ/2 is not excluded. No strictness,
nonzero object, section, choice of a splitting, or smallness hypothesis occurs.

Searches (msearch.py, group Q43 and this item):

- LeanFinder: “Finite tower of exact functors between abelian categories splice
  prescribed filtrations by inverse images with ordered quotient factors”. Eight
  hits, including `Functor.exact_tfae`, Grothendieck transfinite monomorphism
  constructions and exact sequences; none states this finite tower assertion.
- Loogle: “Subobject.map, Subobject.pullback, Subobject.ofLE”. Zero hits (the remote
  Loogle index did not recognize `Subobject.map`). Direct local source reading
  found all three Mathlib subobject operations; no private replacement is used.
- Mathlib grep: “filtration|Filtration|ofSequence” in `CategoryTheory`. Seven
  results, constructors for a single sequence and their importers; no tower
  splicing theorem. Read the sequence and composable-arrows APIs as well.
- LeanSearch: “finite filtration abelian category exact functors inverse image
  splice ordered successive quotients”. Eight hits for exact functors and image
  comparisons, including `Functor.exact_tfae`; no full tower-splicing result.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id, tower
  filtrations, filtration splicing and the proposed declaration name found no
  declaration stating this theorem. The existing `DecreasingFiltration` API
  describes integer-indexed decreasing filtrations; the present theorem uses
  Mathlib subobjects directly and introduces no second definition of filtration.
  The upstream name index also has no `exactFunctorTowerFiltrationSplicing`.

No new nodes, dependency repairs, node faults, statement correction or
STATEMENT-DISPUTED flag. Validation: clean scompile of the sandbox and library
module, with autoImplicit disabled. The only postponed proof is
`CategoryTheory.exactFunctorTowerFiltrationSplicing`.

## Second reading by Q43

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
