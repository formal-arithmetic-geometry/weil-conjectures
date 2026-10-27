## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSaturationQuasiAffinePullback` states
`AlgebraicGeometry.AlgebraicSpace.etale_saturation_quasi_affine_pullback` with one
`sorry`, and no auxiliary declarations or new definitions. The node's natural-language
statement, statement dependencies and proof are unchanged. Source read: Stacks
`spaces-morphisms.tex`, Tag 03XW, lemma-neighbourhood-scheme, the complete statement
and proof, especially the third and fourth proof paragraphs (lines 10469–10585).

The chosen presentations in the signature introduce only the objects that the node
says to form. They carry universal properties, rather than arbitrary comparison maps.
For each canonical fibre product they can be supplied by its projections. Universality
makes the assertion independent of that presentation.

The base-change and Z conclusions precede the universal conditional quantification
over H and its quasi-compact scheme representative. Thus they do not require the
induction hypothesis about H. The final conclusion applies to every H satisfying
that hypothesis.

Hypothesis-by-hypothesis correspondence:

| Node data or hypothesis | Lean rendering |
| --- | --- |
| Scheme S and affine S-schemes T,T' | `{S : Scheme.{u}}`, `T T' : Over S`, `[IsAffine T.left]`, `[IsAffine T'.left]` |
| Étale S-map a:T'→T | `a : T' ⟶ T`, `[Etale a.left]` |
| Algebraic space X over S and its map f:X→T | `X : AlgebraicSpace S`, `f : X.obj.obj ⟶ yoneda.obj T` |
| Every representable étale scheme chart has locally quasi-finite composite | `hqf`, for all `U : Over S` and `v : yoneda.obj U ⟶ X.obj.obj` with `IsEtale v`; the composite scheme map is `yoneda.preimage (v ≫ f)` |
| f is separated, with closed diagonal on every scheme test | `hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) (Limits.pullback.diagonal f)` |
| X'=X×_T T', with its two projections | `X'`, `r`, `t`, and `hX' : IsPullback r t f (yoneda.map a)` |
| V' is an open subspace of X' represented by a scheme | `V : OpenSubspace X'`, `Vscheme : Over S`, `eV : yoneda.obj Vscheme ≅ V.val.toFunctor` |
| V'→T' is quasi-affine | `hV : IsQuasiAffineHom (yoneda.preimage (eV.hom ≫ V.val.ι ≫ t)).left` |
| W is the open point image of V'→X | `W : OpenSubspace X` and `hW : pointImage W.val.ι = pointImage (V.val.ι ≫ r)` |
| T''=T'×_T T', with π₀,π₁ | `Limits.pullback a a`, `Limits.pullback.fst a a`, `Limits.pullback.snd a a`, all in `Over S` |
| Tstar is its open and closed diagonal complement | `Tstar : Over S`, `i : Tstar ⟶ Limits.pullback a a`, the open- and closed-immersion instances on `i.left`, and `hi` identifying its range with the complement of the diagonal range |
| Tstar is affine and b=π₁ restricted to it is étale | `[IsAffine Tstar.left]`, `hb : Etale (i ≫ Limits.pullback.snd a a).left` |
| Xstar=X×_T Tstar and the two maps to X' | `Xstar`, `d₀`, `d₁`, `s`, with `hstar`, `hd₁r`, `hd₁t` as explained below |
| Z=p₀⁻¹(V')∩Xstar | `(V.val.preimage d₀)` |
| H is the open image of Z→X' via p₁ | `H : OpenSubspace X'` and `hH` equating its point image to `pointImage ((V.val.preimage d₀).ι ≫ d₁)` |
| H is represented by a quasi-compact scheme | `Hscheme`, `eH : yoneda.obj Hscheme ≅ H.val.toFunctor`, `hHqc : CompactSpace Hscheme.left` |

The presentation `hstar : IsPullback d₀ s t (yoneda.map (i ≫ π₀))` first
identifies Xstar with X'×_(T',π₀)Tstar. Pasting with `hX'` identifies it with
X×_T Tstar. Since π₀a=π₁a on the scheme pullback, its map `d₁` to X'
is uniquely characterized by the two equations `hd₁r`, `hd₁t`. Thus it is the
restriction of p₁:X''→X', and `d₀` is the restriction of p₀. The intermediate
X'' is eliminated by this universal-property presentation; no extra hypothesis
on X, X', or Xstar is introduced. In particular neither `d₀` nor `d₁` is an
unconstrained map, and the relation is the actual base-change relation.

Conclusion clause-by-clause correspondence:

| Node conclusion | Lean rendering |
| --- | --- |
| X'→T' is chartwise locally quasi-finite | First conjunct, universally quantifying `U`, `v`, `IsEtale v` and using `Scheme.Hom.IsLocallyQuasiFinite` on the Yoneda composite to T' |
| X'→T' is separated | Second conjunct, representable closed-immersion property of `Limits.pullback.diagonal t` |
| Xstar=X'×_(T',b)Tstar using π₁ | Third conjunct `IsPullback d₁ s t (yoneda.map (i ≫ π₁))` |
| Z is open in Xstar | Fourth conjunct, `IsRepresentableWith` open immersions for `(V.val.preimage d₀).ι` |
| Z is represented by Tstar×_(T',π₀)V' | The existential `eZ`, from the Yoneda presheaf of `Limits.pullback (yoneda.preimage (eV.hom ≫ V.val.ι ≫ t)) (i ≫ π₀)` to the preimage subfunctor; swapping the written order of the two factors is canonical |
| This is the specified identification over Tstar and V' | The two equations on `eZ.hom`, one after projection to V' and one after projection to Tstar |
| Z→Tstar is quasi-affine | `IsQuasiAffineHom` of this scheme pullback's second projection, using π₀ |
| P=W×_X X' | `∃ P : OpenSubspace X'`, with `P.val = W.val.preimage r` |
| P=V'∪H as open subspaces | `IsLUB ({V, H} : Set (OpenSubspace X')) P` in the recorded inclusion order |
| P=W×_T T' | `∃ k : P.val.toFunctor ⟶ W.val.toFunctor`, the equation `k ≫ W.val.ι = P.val.ι ≫ r`, and the pullback square `IsPullback k (P.val.ι ≫ t) (W.val.ι ≫ f) (yoneda.map a)` |
| P is represented by a quasi-compact scheme | `Pscheme`, `eP : yoneda.obj Pscheme ≅ P.val.toFunctor`, `CompactSpace Pscheme.left` |
| P→T' is quasi-affine | `IsQuasiAffineHom (yoneda.preimage (eP.hom ≫ P.val.ι ≫ t)).left` |

The least-upper-bound formulation is necessary: the lattice join of bare subfunctors
is pointwise disjunction, which need not be a sheaf. For example, a map from a
disconnected scheme to V'∪H can meet V' on one component and H on another. Such a
map belongs to the open union but need not belong to either subfunctor on the whole
test scheme. `OpenSubspace` has the recorded inclusion order, and `IsLUB` expresses
exactly the open-subspace union without introducing a new definition or assuming a
lattice instance. `CompactSpace` means every open cover has a finite subcover and
requires no Hausdorff or nonempty hypothesis.

Dependency declarations used and read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `AlgebraicSpace.IsEtale`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`, including the Stacks local
  finite-type condition, rather than bare Mathlib `LocallyQuasiFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`; its universal property is
  expressed by `CategoryTheory.IsPullback` on the chosen space presentations.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`:
  `AlgebraicGeometry.IsQuasiAffineHom` (affine-open preimages quasi-affine).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage`:
  `AlgebraicGeometry.AlgebraicSpace.etale_open_image` and
  `openSubspace_points_orderIso`; the statement uses their existing `pointImage`
  (from `AlgebraicSpacePointTopology`) and `OpenSubspace`
  (from `AlgebraicSpaceOpenSubspace`), not fresh notions of points or opens.

Plain proof imports supply the recorded modules for
`lem-a1-space-separated-lqf-permanence`, `lem-trf-quasi-affine-base-change`,
`lem-pc-zariski-coverings-are-fppf`, `lem-pc-schemes-criterion`,
`lem-weil-pbc-affine-scheme-qcqs`, `lem-weil-pbc-qcqs-morphism-permanence`,
`lem-weil-pbc-lqf-locally-finite-type` and
`lemma-nagata-quasi-affine-morphism-of-quasi-finite`. The latter uses the already
publicly imported `QuasiAffine` module. Statement dependencies that also occur in
the proof stay public. The one unstated proof-only dependency
`lem-a1-space-open-factor-scheme-tests` has no recorded Lean module, so no import
can be added for it yet; this is not a missing notion in the present signature.
There is no import cycle and no dependency module is redefined.

Edge cases checked before drafting and again against the signature: V'=empty
makes W and H empty, with empty P; Tstar=empty (in particular a=identity) makes
Z and H empty and P=V'; empty T' or T is allowed; a need not be surjective;
X, V', W and H need not be connected. Two disjoint copies T'=T⊔T give the
crossed off-diagonal images, consistent with the two projection formulas. There
are no Noetherian, finite-presentation or quasi-compactness hypotheses on X, and
no nonempty hypotheses. All scheme, field-point and chart universes are the
existing common `u` of the algebraic-space interface; there is no smaller
independently quantified chart universe. `set_option autoImplicit false` binds
all variables explicitly.

Searches performed on 2026-10-24:

- `msearch.py ... leanfinder "The saturated pullback of an open scheme under an affine etale map is the union of the original open and the off diagonal image and is quasi affine"`: OK, eight hits; scheme diagonal/local affine-property lemmas and `Scheme.isPullback_toSpecΓ_toSpecΓ`, no algebraic-space saturation theorem.
- `msearch.py ... loogle '"IsQuasiAffineHom", "pullback"'`: OK, zero hits.
- `msearch.py ... grep 'saturat|AlgebraicSpace' AlgebraicGeometry`: OK, zero hits.
- `msearch.py ... leansearch "An etale base change saturation of a quasi affine open in an algebraic space is a quasi compact quasi affine scheme when its off diagonal image is a quasi compact scheme"`: OK, eight hits; quasi-compact base change, quasi-separated diagonals, and absolute quasi-affine scheme results, no matching theorem.
- `rg` of the project's `lean/WeilConjectures` and `lean/Sheaf` for the item id and proposed declaration name: no existing declaration. Searches for `etale.*saturat|saturat.*pullback|saturation_quasi` found the different scheme descent-saturation cover theorem, not this statement.
- Broader `rg` for `OpenSubspace`, `pointImage`, chartwise local quasi-finiteness,
  quasi-affineness, and saturation located the recorded space/open/point APIs,
  `SpaceSeparatedLqfPermanence`, and `EtaleQuasiAffineImageScheme`. Read their
  signatures and docstrings: none states this induction-step lemma. The parent
  image theorem is not substituted for its stronger explicit induction checks.

Initial validation: `scompile.py Q22 lem-a1-etale-saturation-quasi-affine-pullback
lean/Sheaf/AlgebraicGeometry/EtaleSaturationQuasiAffinePullback.lean` passed both
sandbox and library module modes (7.0 s and 4.8 s), with no errors or unexpected
warnings. There are no node faults or STATEMENT-DISPUTED concerns.

Final audit adjustment: moved H and its hypotheses into the final universally quantified
conclusion, preserving the unconditional base-change and Z clauses before them.

The final signature passed `scompile.py` in sandbox mode (8.4 s) and library
module mode (8.6 s), with no errors or unexpected warnings.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
