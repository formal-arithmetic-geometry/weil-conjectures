## Worker report

Existing declarations only; no new Lean module or postponed proof is delivered.
The node is exactly the pair `AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`
and `AlgebraicGeometry.Etale.mono_cokernelMap`, in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.CriticalMap`
(lines 82–85 and 156–163 of the read-only slopmaster2 source).
Their complete signatures and docstrings were read, together with their common
section binders. The existing partial attachment in the node is completed with
all mandatory stage-2 metadata; all other node fields are preserved.

The source is Stacks Tag 0F03, `lemma-base-change-q-injective`, clauses (1) and
(2), read in `literature/stacks-project/etale-cohomology.tex:16869`.
The node expressly uses the fixed-base arbitrary-ring specialization stated in
the upstream CriticalMap source. The long-exact-sequence proof only uses the
preceding single-degree property: embed F in an injective I, compare the two
long exact sequences for F → I → I/F, use the preceding-degree isomorphisms
and positive-degree vanishing for I to obtain injectivity. For cokernel
monotonicity embed G in an injective I and factor the injective map from the
cokernel for F into the higher direct image for I through the cokernel for G.
The existing theorems already prove these claims; no duplicate is introduced.

Hypothesis and clause correspondence:

- The commutative ring is the common binder `(Λ : Type (u + 1)) [CommRing Λ]`.
  This is the existing six-functor coefficient-size convention; u is arbitrary.
- The schemes and arrows are `{X S T Y : Scheme.{u}}`, `{p : X ⟶ S}`,
  `{g : T ⟶ S}`, `{e : Y ⟶ T}`, `{h : Y ⟶ X}`. There is no geometric
  restriction on p, X or S.
- The degree and its lower bound are `(q : ℤ) (hq : 1 ≤ q)` in both declarations.
- Fixed-base BC(p, Λ, q−1) is exactly
  `(hprev : Etale.BaseChangeProperty Λ p (q - 1))`. Expanding that definition
  quantifies over qcqs g, its Cartesian squares and coefficient sheaves, at
  this fixed p and this single degree. It is not UniversalBaseChangeProperty.
- The two properties on g are `[QuasiCompact g] [QuasiSeparated g]`.
  The finite-type dependency contributes its quasi-compact notion only;
  locally finite type is not a hypothesis of either theorem.
- The Cartesian projections are `(sq : IsPullback e h g p)`: top e, left h,
  right g, bottom p. Any chosen fiber-product identification from the recorded
  ChosenCartesianSquare gives precisely this pullback property. Conversely a
  pullback square has its unique projection-compatible isomorphism with the
  chosen fiber product. Thus arbitrary chosen Y and the literal X ×_S T are
  both covered; no arbitrary comparison map is substituted.
- M is `(F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))` in clause (1).
  The dependency's record explicitly permits this module-valued encoding.
- The canonical b_M is `Etale.baseChangeHomologyMap Λ sq q F` from sk-def-bc.
  Its definition is the component of `baseChangeHomologyNatTrans`, namely
  degree-q homology of the derived unit/exchange/counit base-change morphism
  evaluated on F[0]. Source and target are `baseChangeSourceFunctor` and
  `baseChangeTargetFunctor`: H^q(p^* Rg_* F[0]) and H^q(Rh_* e^* F[0]).
  Exactness of inverse image identifies these with the stated classical
  p⁻¹ R^q g_* F and R^q h_* e⁻¹ F; this is also the precise map stipulated
  in sk-def-bc, not a newly chosen arrow.
- Clause (1) is `Mono (Etale.baseChangeHomologyMap Λ sq q F)` for every F.
- Clause (2) has `{F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}`,
  `(α : F ⟶ G) [Mono α]`. Its conclusion is `Mono (cokernel.map ...)`, with
  maps on source and target given by the corresponding functors applied to α,
  and commutativity supplied by `baseChangeHomologyMap_naturality Λ sq q α`.
  This is exactly the naturality-induced map Coker(b_F) → Coker(b_G).
- Mono and cokernel are those of the abelian category of module-valued sheaves.
  Neither declaration has a universal BC, annihilator, torsion, invertibility,
  smoothness or injectivity hypothesis on the coefficients F or G.

Dependency declarations read and used by the existing statements:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- sk-def-bc: `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`,
  `AlgebraicGeometry.Etale.BaseChangeProperty`, `baseChangeHomologyMap`,
  `baseChangeSourceFunctor`, `baseChangeTargetFunctor`, and
  `baseChangeHomologyMap_naturality` (all latter names in AlgebraicGeometry.Etale).
- def-weil-finite-type-morphism: the record's quasi-compact declaration
  `AlgebraicGeometry.QuasiCompact` from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`; the record's
  `LocallyOfFiniteType` signature was also read but is not imposed.
- def-weil-quasi-separated-morphism: Mathlib match `AlgebraicGeometry.QuasiSeparated`
  in `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- def-weil-pbc-cartesian-square: `AlgebraicGeometry.ChosenCartesianSquare`
  in `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`; its projection-compatible
  `isoPullback`, `hom_fst`, `hom_snd` give the IsPullback notion used upstream.
  An existing theorem does not require a new wrapper importing that structure.
- def-weil-pbc-etale-sheaves: record in
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves`; the relevant declaration is
  Mathlib's `CategoryTheory.Sheaf`, specialized to ModuleCat as explicitly
  authorized in lean.note. The unrelated local-constancy, torsion and
  constructibility predicates from that record are not hypotheses here.
- def-weil-pbc-direct-image and def-weil-pbc-inverse-image:
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`
  in `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, used by the canonical
  base-change construction. The direct-image record's additional
  `rightDerivedLowerStarPlus` name is now located in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence` rather than
  the recorded Defs module (confirmed by reading current `scompile.py --source`
  Defs and the local Coherence source). This metadata drift does not obstruct
  either existing theorem: SmoothBaseChange.Defs uses generic `R+(lowerStar)`
  from `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.
- def-sp-abelian: Mathlib match `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`; Mono and `Limits.cokernel.map` are the
  standard category-theoretic constructions, with cokernel.map read in
  `Mathlib.CategoryTheory.Limits.Shapes.Kernels`.

Edge cases checked against the signatures and the source proof: q=1 uses
exactly degree 0 BC; q≤0 is deliberately excluded by the stated bound, not by a
hidden natural-number convention. The zero ring and zero sheaf are admitted,
and their vanishing maps/cokernels are monomorphisms as expected. Empty schemes
and identity base changes are admitted. F=G and α=identity give the identity
map of cokernels; F=0 gives a zero source cokernel. Noninvertible coefficients
such as integral coefficients are not excluded. No additional universe equality
is imposed; schemes have size u and module coefficients size u+1 as in sk-def-bc.
No statement correction, new definition, or dependency module is needed.

Searches performed:

- msearch.py leanfinder, query: "The critical degree etale base change map is a
  monomorphism and its cokernel is monotone under monomorphisms if base change
  holds in the preceding degree". Eight hits, all general homology-sequence
  monomorphism results; no étale theorem matching both clauses.
- msearch.py loogle, query:
  `CategoryTheory.Limits.cokernel.map, CategoryTheory.Mono`. One result:
  `CategoryTheory.Abelian.mono_cokernel_map_of_isPullback`; a general abelian
  categorical fact, not this fixed-base étale statement.
- msearch.py grep, query:
  `mono_baseChangeHomologyMap|mono_cokernelMap|BaseChangeProperty`. No Mathlib hits.
- rg in the source's SmoothBaseChange/Injectivity directory for
  `mono_baseChangeHomologyMap|mono_cokernelMap|baseChangeHomologyMap` found the
  two exact theorems in CriticalMap.lean, with their complete proofs, plus
  their uses and the separate universal theorem. The latter is not substituted
  for the fixed-base theorems.
- grep -rn `lem-sbc-fixed-base-critical-map` in upstream WeilConjectures: no hit;
  the exact statements are documented under the older sk-prop-injectivity id.
- rg `mono_baseChangeHomologyMap|mono_cokernelMap|fixed.base.critical` in
  the shared `lean/Sheaf`: no hit. No side-project duplicate is needed.

Common binders, verbatim from CriticalMap.lean:

```lean
variable (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} {p : X ⟶ S}
  {T Y : Scheme.{u}} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
```

Existing signatures, verbatim (the first is lean.statement):

```lean
theorem Etale.mono_baseChangeHomologyMap (q : ℤ) (hq : 1 ≤ q)
    (hprev : Etale.BaseChangeProperty Λ p (q - 1)) [QuasiCompact g] [QuasiSeparated g]
    (sq : IsPullback e h g p) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Mono (Etale.baseChangeHomologyMap Λ sq q F)
```

```lean
theorem Etale.mono_cokernelMap (q : ℤ) (hq : 1 ≤ q)
    (hprev : Etale.BaseChangeProperty Λ p (q - 1)) [QuasiCompact g] [QuasiSeparated g]
    (sq : IsPullback e h g p) {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (α : F ⟶ G) [Mono α] :
    Mono (cokernel.map (Etale.baseChangeHomologyMap Λ sq q F)
      (Etale.baseChangeHomologyMap Λ sq q G) ((Etale.baseChangeSourceFunctor Λ p g q).map α)
      ((Etale.baseChangeTargetFunctor Λ e h q).map α)
      (Etale.baseChangeHomologyMap_naturality Λ sq q α))
```

Validation: the scratchpad ExistingChecks.lean was compiled with the prescribed
`scompile.py Q06 lem-sbc-fixed-base-critical-map` wrapper. Both sandbox and
library checks passed without warnings. The elaborated signatures match the
clause correspondence above. `#print axioms` on each theorem reports exactly
`propext`, `Classical.choice`, and `Quot.sound`; neither reaches sorryAx.
Only the lean field differs in the item node. No delivered Lean modules.

## Second reading by Q06

I reread the item node, its source place, and every declaration named by its
statement dependencies. The node's objects and clauses, in order, are:

1. A commutative ring `Λ`, schemes `X,S,T,Y : Scheme.{u}`, and morphisms
   `p : X ⟶ S`, `g : T ⟶ S`, `e : Y ⟶ T`, `h : Y ⟶ X`.
2. An integer `q` with `1 ≤ q`, and the fixed-base, single-degree hypothesis
   `BC(p,Λ,q-1)`.
3. Quasi-compactness and quasi-separatedness of `g`, and a Cartesian square
   with `e` and `h` as the projections (`Y = X ×_S T` in the source
   presentation).
4. For every sheaf `M` of `Λ`-modules on `T_et`, the canonical degree-q map
   `b_M : p⁻¹ R^q g_* M ⟶ R^q h_* e⁻¹ M` is mono.
5. For every mono `u : M ⟶ N`, naturality induces a mono
   `Coker(b_M) ⟶ Coker(b_N)` in the abelian category of module sheaves.
   The node explicitly imposes no universal-BC, annihilator, invertibility,
   smoothness, or injectivity assumption.

The common source binders in `CriticalMap.lean` are exactly
`(Λ : Type (u + 1)) [CommRing Λ]`, `{X S T Y : Scheme.{u}}`, and the four
displayed morphisms. The first clause is rendered verbatim by
`Etale.mono_baseChangeHomologyMap`: `(q : ℤ) (hq : 1 ≤ q)`,
`hprev : Etale.BaseChangeProperty Λ p (q - 1)`, typeclass hypotheses
`[QuasiCompact g] [QuasiSeparated g]`, `sq : IsPullback e h g p`, and
`F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, concluding
`Mono (Etale.baseChangeHomologyMap Λ sq q F)`. The second clause is rendered
verbatim by `Etale.mono_cokernelMap` with implicit `F G` in the same sheaf
category, `(α : F ⟶ G) [Mono α]`, and the conclusion
`Mono (cokernel.map ... (baseChangeHomologyMap_naturality Λ sq q α))`.
Thus the map is the canonical map from `sk-def-bc`, and `cokernel.map` is the
actual naturality-induced cokernel map; no arbitrary comparison map appears.
`IsPullback` expresses precisely the universal Cartesian-square condition, so
the theorem covers the chosen fibre-product presentation in the node (and any
isomorphic chosen pullback), without adding a hypothesis.

I checked the dependency declarations: `Scheme`/`Scheme.Hom` are Mathlib's
scheme category; `BaseChangeProperty` and `baseChangeHomologyMap` are the
recorded declarations in `SmoothBaseChange.Defs`; `QuasiCompact` and
`QuasiSeparated` are the recorded Mathlib classes; the chosen-square node
supplies the projection-compatible pullback notion; module-valued etale sheaves
use the explicitly recorded `ModuleCat.{u+1} Λ` encoding; and `lowerStar`/
`upperStar` are the recorded direct/inverse-image constructions. The abelian
category, `Mono`, and `Limits.cokernel.map` are the standard Mathlib notions.
No dependency interface is missing or unusable, so no dependency module was
added.

Edge cases remain covered: `q = 1` asks exactly for degree-zero BC; negative
and zero `q` are excluded only by `1 ≤ q`; `Λ = 0`, zero sheaves, empty
schemes, empty `T`, identity squares, `F = G`, and identity `α` all fit the
signatures. The universe convention is the source convention (`Scheme.{u}`
and `ModuleCat.{u+1} Λ`), with no forced universe equality or characteristic,
finite-type, smoothness, or separatedness assumption.

For the independent existence check I ran LeanFinder, Loogle, and Mathlib grep
searches for the critical map, cokernel map, and base-change property, and
searched the source and shared `lean/Sheaf` tree by declaration name. The only
matching declarations are the two proof-complete theorems in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.CriticalMap`;
the Loogle hit is only the general abelian `mono_cokernel_map_of_isPullback`.
No second definition or statement module is needed. The node's existing
attachment is therefore complete after filling all metadata (module,
declarations, statement, branch, and audit fields); no mismatch was found and
no Lean file was changed.

The prescribed compile was rerun with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q06
lem-sbc-fixed-base-critical-map scratchpad/ExistingChecks.lean`. Both sandbox
and library checks passed with no warnings; both declarations report only
`propext`, `Classical.choice`, and `Quot.sound`.
