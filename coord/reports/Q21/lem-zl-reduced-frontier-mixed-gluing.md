## Worker report

Item: lem-zl-reduced-frontier-mixed-gluing. Module:
`Sheaf.Paper.ReducedFrontierMixedGluing`. Main declaration:
`WeilConjectures.zlReducedFrontierMixedGluing`.

I read the item's full statement and seven proof steps, all eight statement-dependency
nodes and their recorded interfaces, and the current blueprint source
`literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`,
particularly its last three paragraphs. The statement is unchanged. No statement dispute,
new DAG node, dependency re-recording or dependency module is needed. The structures in
this module are clause packages for this node, not replacements for existing mathematical
notions. Only the main theorem has a postponed proof. Every other declaration has real data.

Hypotheses, in the same order as the node:

- The prime power, base finite field and chosen algebraic closure are the existing
  `D : FiniteFieldDatum.{u}`. The coefficient assumptions are `l : ℕ`, `[Fact l.Prime]`,
  `hl : l ≠ D.p`, `Ω : Type v`, `[Field Ω]`, `[Algebra (Padic l) Ω]` and
  `[IsAlgClosure (Padic l) Ω]`. The embedding in this statement is exactly the specified
  isomorphism `iota : Ω ≃+* ℂ`, passed as a ring homomorphism to the recorded predicates.
  Scheme and coefficient universes `u` and `v` are independent and explicitly declared.
- The ambient separated finite-type k₀-scheme is the section variable
  `X : Over (Spec (.of D.k₀))`, with `LocallyOfFiniteType X.hom`,
  `QuasiCompact X.hom` and `IsSeparated X.hom`. The sheaf is exactly
  `F : sfCommonStageWeilSheaf D l hl X Ω`, the recorded common-stage constructible
  Weil heart, not a discrete coefficient sheaf or a derived category of Weil sheaves.
- `C : ZlReducedFrontier D X` packages the GIVEN chain, not an existence hypothesis
  about an unspecified stratification. `C.length` is t; `C.closed : Fin (t+1) → Over …`
  supplies Z₀ through Zₜ. `C.reduced` asserts reducedness of every term.
- `C.ambient a` is its closed inclusion into X. `C.reduction` identifies Z₀ with
  `X.left.nilradical.subscheme`; `C.reduction_over` identifies its actual map with
  `X.left.nilradical.subschemeι`. Thus the reduction is the existing nilradical
  reduction, with no replacement notion or arbitrary closed surjection. An isomorphic
  presentation of this subscheme is permitted, rather than requiring equality of types.
- `C.finish : IsEmpty (C.closed (Fin.last t)).left` says Zₜ is empty.
  `C.inclusion a : Zₐ₊₁ ⟶ Zₐ` is a closed immersion, and `C.ambient_next` says these
  are the inclusions over X. No strictness of the chain is imposed.
- `C.difference a` and `C.openInclusion a` give Uₐ as an open subscheme of Zₐ;
  `C.complement` is precisely the equality of its range with the complement of Zₐ₊₁.
- `C.count a` and `Fin (C.count a)` encode an arbitrary finite component set.
  `C.piece a b`, `C.pieceInclusion a b`, `piece_open`, `piece_closed`, `cover`, and
  `disjoint` give its finite clopen disjoint decomposition. Neither smoothness,
  affineness, connectedness nor nonemptiness of a component is added. Using Fin loses
  no finite set: an enumeration transports the scheme family and all its arrows.
- Every arrow is a morphism in `Over (Spec (.of D.k₀))`, so all inclusions and the
  decomposition are over the same k₀. The finite-type/quasi-compact/separated
  structures bundled on the closed terms, differences and components are inherited
  from their closed/open immersions into the ambient finite-type separated scheme.
  They impose no extra geometric condition: finite type over a field is Noetherian,
  every open is quasi-compact, and restrictions of the structure morphism are separated.
- The hypothesis `mixed` says, for EACH a,b, `∃ w : ℝ,
  SfIsMixedOfWeightsAtMost … (C.piece a b) iota ((zlWeilPull …
  (C.pieceInclusion a b ≫ C.openInclusion a ≫ C.ambient a.castSucc)).obj F) w`.
  This is a finite mixed Weil filtration of the actual restriction. Existentially
  allowing an upper bound is equivalent to an unbounded finite mixed filtration:
  a finite list of real quotient weights has a common bound, including the empty list.

Conclusions, clause by clause:

- The first conjunct `∃ w, SfIsMixedOfWeightsAtMost … X iota F w` gives a finite
  mixed filtration of F in the recorded abelian Weil heart. The predicate itself
  permits non-strict monomorphisms and a filtration of length zero.
- The next conjunct quantifies over every `w : ℝ`: if EVERY component restriction
  satisfies that same bound, then `SfIsMixedOfWeightsAtMost … X iota F w`.
  Thus no fixed bound is imposed in advance, and every prescribed common bound is retained.
- The component-extension conjunct is `ZlFrontierFiltrationPreservation …
  (zlOpenWeilShriek … (C.pieceInclusion a b))`, for every a,b. This is extension
  from a clopen component into Uₐ; the subsequent extension from Uₐ into Zₐ is
  separately included. These are the actual open-heart left adjoints of the recorded
  restriction functors, identified with compact support by `extensionByZero_punctual`.
- `ZlFrontierFiltrationPreservation.filtration` quantifies over the actual list G,
  monomorphisms φ and real weight list. Its conclusion uses `T.obj (G 0)`,
  `T.map (φ s)` and `cokernel (T.map (φ s))`: thus it is the IMAGE filtration,
  not merely existence of some mixed output. It asserts that its start remains zero,
  its arrows remain monic and the new quotients have precisely `weights s`.
  The terminal object is literally T applied to the old terminal object; an endpoint
  identification with the original sheaf transports by `T.mapIso`.
- The `additive`, `finiteLimits`, `finiteColimits` fields state exactness of the
  heart functor. The `mixed` field states preservation of each real mixed upper bound.
  These clauses apply to each component extension, each stratum open extension,
  each chain closed image and the reduction closed image.
- The existential `images a : ZlFrontierClosedImage … (C.inclusion a)` is a presentation
  of the actual iₐ*. Its `carrier` equation identifies the WHOLE functor, on objects
  AND maps after the full-subcategory inclusion, with `sfModelWeilDerivedPush`.
  Its `adjunction` is the restriction/direct-image adjunction, and its
  `unit_normalization` identifies its unit with the recorded derived unit. This
  data specifies the canonical operation rather than an arbitrary map or an
  unnormalized natural isomorphism. No functor is defined by a choice from this theorem.
- For each a, put Fₐ = `(zlWeilPull … (C.ambient a.castSucc)).obj F`.
  `ZlFrontierLocalization … (C.openInclusion a) (C.inclusion a) (images a) Fₐ`
  is exactly short exactness of the ACTUAL open counit followed by the ACTUAL closed
  unit. `∃ h` only supplies the proof that their composite is zero; it chooses no
  arrow. `ShortComplex.ShortExact` includes monicity, exactness in the middle, and
  epicity. Its last term is iₐ*iₐ*Fₐ; inverse-image composition and
  `C.ambient_next` identify iₐ*Fₐ with Fₐ₊₁, the notation in the node's display.
  Its first term is jₐ!jₐ*Fₐ. Every arrow lies in the Weil heart, so equivariance
  is part of its type, not a forgotten assertion.
- `reduction : ZlFrontierClosedImage … (C.ambient 0)` has the same recorded carrier
  and normalized unit; `IsIso (reduction.adjunction.unit.app F)` is the actual
  reduction-unit Weil isomorphism in the heart, F → r*r*F. An inverse is therefore
  an equivariant heart map too. The reduction_over equation ensures this r really
  is the canonical reduction map under the displayed presentation of Z₀.
- There is no reality hypothesis anywhere.

Dependency declarations used:

- `def-weil-punctual-weights`: `Sheaf.Paper.AdicPunctualWeights`,
  `WeilConjectures.SfIsMixedOfWeightsAtMost`, `SfIsPunctuallyPureOfWeight`
  (and its underlying `SfPunctualEigenvalue`). Read the full predicate signatures.
- `def-weil-weil-sheaf-complex`: `Sheaf.Paper.SfWeilSheafComplex`,
  `WeilConjectures.sfCommonStageWeilSheaf`, with the existing fixed-pair category
  and heart predicate; the complete source and docstrings were read.
- `def-weil-pbc-scheme-reduction`: `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`,
  `AlgebraicGeometry.Scheme.nilradical`, `Scheme.IdealSheafData.subscheme` and
  `Scheme.IdealSheafData.subschemeι` (subscheme source lines 454 and 472).
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion` (line 38).
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion` (line 45).
- `def-weil-integral-rational-qbar-compact-support`:
  `Sheaf.Paper.QcqsCompactSupportRealization`, `sfQcqsCompactSupportRealization`,
  reexporting the original finite-integral/rational/common-stage constructions.
  The normalized heart realization used is `Sheaf.Paper.ExtensionByZeroPunctual`,
  `WeilConjectures.zlOpenWeilShriek`, `zlOpenWeilPull_isRightAdjoint`,
  `extensionByZero_punctual`. I read their full signatures and normalization clauses.
- `def-weil-derived-direct-image`: `Sheaf.Paper.SfDerivedDirectImage`,
  `WeilConjectures.SfIntegralDirectImage` (specified Roos triangle);
  its common-stage Weil realization is `Sheaf.Paper.SfCommonStageDirectImage`,
  `sfModelWeilDerivedPush`, `sfModelWeilDerivedAdjunction`, with the canonical
  forgetful comparison `sfModelWeilDerivedPush_forget`. These were read, including
  the adjunction and unit/counit normalization.
- `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom`,
  `commonStageDerivedPullback` (and its rational/integral restrictions).
  `Sheaf.Paper.WeilIndSheafCategory.zlWeilPull` is its canonical Weil-heart lift;
  that module also supplies the existing abelian-heart instance. No new pullback,
  purity, mixedness, abelian structure, or compact-support functor is defined here.
- Every stated proof-dependency module is imported without `public` unless also a
  statement dependency. The Mathlib leaf modules for finite type, separatedness,
  quasi-compactness, finite closed immersions and Noetherianity are also imported.
  Some proof records use the older upstream WeilSheaf encoding (notably the finite
  purity and mixed-stability lemmas); they remain proof-plan imports. The present
  signature uses the recorded common-stage heart throughout and assumes no
  identification with that older encoding. A future proof must supply any necessary
  transport or prove the corresponding clause in the common-stage heart.

Edge cases checked before and after writing:

- Empty X and t=0: `Fin 0` has no stages; `finish` forces Z₀ empty and its reduction
  comparison forces X empty. The mixed hypothesis is vacuous, and every w is allowed;
  the zero sheaf has the empty filtration in the existing predicate.
- Empty component set at a stage: `count a = 0` makes `cover` force Uₐ empty.
  It does not make a nonempty stratum's mixedness hypothesis disappear.
- Empty individual components and repeated closed terms are allowed.
- Zero F has a length-zero mixed filtration; the preservation package explicitly
  includes m=0 with no quotient conditions. Non-strict monomorphisms are permitted.
- A one-component layer, a chain of length one, arbitrary different real component
  weights, negative weights and a common bound w all match the two induction arguments.
- Nonreduced X is unrestricted: only the chain terms are reduced; `reduction` and
  `reduction_over` retain the nilpotent reduction and its actual unit.
- No restriction on p except primality in the finite-field datum, nor on l except
  primality and l ≠ p; no equality of the scheme and coefficient universes is added.

Searches actually run:

1. `msearch.py … leanfinder` query: "Mixed constructible Weil filtrations glue across
   a finite chain of reduced closed subschemes with clopen components".
   Result: 8 hits, consisting of ideal-sheaf gluing morphisms and ideal/module
   filtration lemmas (`Scheme.IdealSheafData.glueDataObjHom_comp`,
   `range_glueDataObjι_ι`, `Ideal.Filtration.Stable.*`, `IsModuleFiltration.mk_int`).
   No match for the Weil-heart statement.
2. `msearch.py … loogle` query:
   "CategoryTheory.ShortComplex.ShortExact, CategoryTheory.Functor".
   Result: 12 hits. `ShortComplex.ShortExact.map` and `.map_of_exact` and exact-functor
   criteria are useful general infrastructure, but none states the present gluing result.
3. `msearch.py … grep` query: `WeilSheaf|mixed.*filtration|frontier.*gluing`.
   Result: 0 Mathlib hits.
4. `rg`/id search in `lean/WeilConjectures`, `lean/Sheaf`, and
   `dag/lean_names_upstream.json`: no item-id tag or proposed declaration-name collision.
   Concept search found `WeilSheaf.IsMixedOfWeightsAtMost.of_openClosed` in
   `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` (lines 360--378), read in full.
   This is a single-pair statement in the older upstream category, without the current
   common-stage heart, entire finite chain, actual sequence, quotient-weight and
   reduction-unit clauses. It is not an exact existing declaration of this node.
   Search of `lean/Sheaf/Paper` and `lean/Sheaf/DeligneLaumon` found the existing weight
   predicates, stability and extension-by-zero modules, which are reused.

Validation: the prescribed `scompile.py Q21 lem-zl-reduced-frontier-mixed-gluing …`
compiled the module both as sandbox and at its library module path with no errors or
warnings. No global build, direct git operation, or shared-library edit was performed.
The independent maintainer review is performed after delivery; I have not represented
my own rereading as an independent second reading.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
