## Worker report

The module `Sheaf.Paper.PurityFrameIndependence` states independence of the concrete frame class, using the recorded `WeilConjectures.PurityFiniteSetting.frameClass` from `Sheaf.Paper.PurityFrameClass`. The sole new postponed theorem is `WeilConjectures.PurityFiniteSetting.frameClass_independent`. Its docstring contains all seven steps of the node's repaired proof. Nothing is proved in this stage.

`frameClassOnPullback` is a helper belonging to this equality statement, not a second construction of the frame class. It composes the existing `frameClass` with the degree-zero map of the inverse of `frameClosedCoefficientIso`, applied to `F.isPullback.isoPullback`. Its result lives in the fixed group with support immersion `pullback.snd i F.e`. This is the canonical support identification: the zero subscheme presentation and the chosen scheme-theoretic pullback are uniquely isomorphic over U. All data are explicit compositions and existing canonical isomorphisms; the helper contains no sorry and no arbitrary choice of class, support identification, change-of-generators matrix, or twist trivialization.

Hypothesis-by-hypothesis and clause-by-clause reading:

- “In the situation of def-pur-frame-class”: `P : PurityFiniteSetting.{u}` retains the finite-field/coefficient setting and positive level, including arbitrary ramification indices. The schemes `B V Z : Scheme.{u}` and `b : B ⟶ Spec (.of P.field.k)` specify the base k-scheme. The composition `v ≫ b` makes V a k-scheme, and `i ≫ v ≫ b` makes Z one.
- The smooth relative family is `v : V ⟶ B` with `[SmoothOfRelativeDimension P.level v]`. This follows the existing node's reuse of n as both coefficient level and relative dimension exactly; it adds no finite-type or separatedness hypothesis on B or V over k.
- The closed subfamily is `i : Z ⟶ V` with `[IsClosedImmersion i]` and `[Smooth (i ≫ v)]`.
- Pure codimension is exactly `c : ℕ` and `hcodim : ∀ z : Z, ringKrullDim (V.presheaf.stalk (i z)) = ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞)`, copied from the recorded frame-class interface. No regular-immersion hypothesis or finite local dimension is substituted.
- A common étale neighbourhood is arbitrary `U : Scheme.{u}`, `e : U ⟶ V`, `[Etale e]`. In particular e is not assumed an open immersion or surjective.
- Two ordered frames are arbitrary `f g : Fin c → Γ(U, ⊤)`. The maps `tf`, `tg` and pullback squares `hf`, `hg` are precisely the generating-ideal condition of the existing `Scheme.Hom.EtaleFrame`: both zero subschemes equal `Z ×_V U` scheme-theoretically. These are not equality merely of reduced supports; no equality of ranges or generator order is assumed. Each structure literal passed to `frameClassOnPullback` is this existing frame structure with the corresponding tuple.
- “the class cl(f) of def-pur-frame-class”: both sides of the equality are the already defined `P.frameClass b v i c hcodim F`, precomposed solely with the canonical support identification. The degree is `2 * (c : ℤ)` and the coefficient is `P.frameTwist U c`, with the existing `cupSingle` and `cupSupportedHom`.
- “depends only on the ideal of Z, i.e. only on the pair, not on the frame”: `frameClass_independent` equates these two elements in the identical group supported on `pullback.snd i e`. All functions and both presentations are universally quantified. Thus this includes every pair of generating frames of that ideal.
- Frames on different neighbourhoods are compared on their common étale fibre product, as specified in proof step 1 of the node. Apply this universally quantified statement with U that fibre product, e its map to V, and f,g the restrictions of the two tuples. Their pullback squares are obtained by pullback pasting. The equality is of the concrete classes of the restricted tuples; the naturality in `lem-pur-supported-cup-functoriality` identifies them with the restrictions of the original classes. There is no untyped assertion of equality of elements on different ambient schemes. Naturality is part of the construction's compatibility, rather than a hypothesis imposing extra conditions on frames.

Dependency declarations read and used:

- Statement dependency `def-pur-frame-class`: `Sheaf.Paper.PurityFrameClass`, `WeilConjectures.PurityFiniteSetting.frameClass`, `frameClosedCoefficientIso`; also the public `cupSingle`, `cupSupportedHom`, and `frameTwist` interfaces. I read the complete recorded definition and helper constructions. The original frame definition is `AlgebraicGeometry.Scheme.Hom.EtaleFrame` in `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion`, including its full `isPullback` field and docstring.
- Canonical pullback comparison: `CategoryTheory.IsPullback.isoPullback` and `isoPullback_hom_snd` in Mathlib's `CategoryTheory/Limits/Shapes/Pullback/IsPullback/Defs.lean`. These identify the supports over U, and the existing frame-class coefficient comparison transports their pushforwards of constants.
- Stated proof dependencies imported non-publicly: `Mathlib.AlgebraicGeometry.Sites.Etale` (`Scheme.smallEtaleTopology` and `Scheme.Etale`); `Sheaf.RingTheory.LocalGeneratingTuples` (`Module.exists_elementary_generating_tuple_change`); `Sheaf.AlgebraicGeometry.SupportLongExact` (`AlgebraicGeometry.exists_support_longExact`); `Sheaf.Paper.SupportedAffineLineHomotopy` (`WeilConjectures.PurityFiniteSetting.supportedAffineLineHomotopy`).
- `lem-pur-relative-support-bottom-descent` and `lem-pur-supported-cup-functoriality` currently have no recorded Lean declarations. They are proof dependencies only, not missing notions needed to state this theorem. They are named in the proof docstring; no import is invented. No dependency interface repair or extra definition node is needed.

Edge cases checked before writing:

- c=0 is retained: the empty tuple cuts out the zero ideal and both classes are the supported unit of `frameEmptyClass`. Transport uses the canonical isomorphism and never divides by c.
- Empty U, Z, or V is not excluded. Pullback squares and support comparisons still make sense; when Z is empty the supported group is zero. For c=0 and empty Z a nonempty U would simply not admit the stated pullback square.
- c=1 includes unit multiples of the equation. No invertible matrix is assumed or chosen; the proof uses the exact sequence to kill the extra unit's boundary.
- Arbitrary permutations have even cohomological sign, and the rank-one twist symmetry preserves the product. Shears interpolate over A¹_U without asserting that it is étale over V.
- Non-reduced ideals are compared scheme-theoretically, and a frame's map e may be a genuine étale neighbourhood rather than an open embedding.
- Arbitrary positive coefficient level, including levels not divisible by the ramification index, uses the recorded concrete frame class. No extra divisibility condition is introduced.
- A common universe u is the existing scheme/setting universe; the pro-étale object/morphism size convention and coefficient lift are unchanged. All universe and term binders are explicit, with `set_option autoImplicit false`.

Searches for an existing statement (2026-10-18):

- `msearch.py Q64 lem-pur-frame-independence leanfinder "the cohomology class of a frame obtained from supported Kummer boundaries is independent of its generating functions"`: 8 group-cohomology/Hilbert-90/low-degree coboundary hits; none is supported étale/pro-étale frame independence.
- `msearch.py ... loogle "AlgebraicGeometry.Etale.frameClass"`: 0 hits, unknown identifier (the project-specific declaration is outside this Mathlib search service).
- `msearch.py ... grep "frameClass|frame_independ|frameIndepend"`: 0 Mathlib hits.
- `msearch.py ... leansearch "The class in cohomology with supports defined by Kummer boundaries of generators of a smooth closed subscheme is independent of the generators."`: 8 ideal-sheaf-support, Hom-complex cohomology-class and cotangent-restriction hits; none states the item.
- `rg -n 'frameClass|FrameClass|frame_independ|frameIndepend'` in `lean/Sheaf` and the upstream `WeilConjectures` source: finds the recorded concrete frameClass and the upstream abstract frameClass and fundamental-class theorem. The upstream `existsUnique_fundamentalClass` uses abstract `HasKummerClass`/normalization data, regularity of Z and smoothness over a perfect field; it neither identifies the concrete finite-level class nor covers these relative hypotheses. It is not an exact existing attachment.
- Search of upstream for `lem-pur-frame-independence`: no match. Search for `frameClassOnPullback|frameClass_independent` in Mathlib, upstream and `lean/Sheaf`: no existing names.

No statement correction, new nodes, dependency modules, or disputed statement. The item's only changed field is `lean`. The current main-20261015 statement and the DAG's repaired proof were read; the original blueprint proof's Smith-normal-form and constant-sheaf arguments are not reused.

Validation: `scompile.py Q64 lem-pur-frame-independence <module>` passed with exit code 0 and no warnings: sandbox check 17.9 s, module check 18.5 s. Both checks used the prescribed server wrapper and retained the 60-second per-file limit. `deliver2.py Q64 lem-pur-frame-independence --no-push` then printed `OK (dry run): commit cbdd92b64e passes the preflight and compiles; nothing pushed`. The packet contains precisely the module, the lean-only node update and this report.

## Second reading by Q64

The delivered section was a placeholder ("No second reading by a worker"), which delivery-errors H11 does not accept. This independent clause-by-clause reading was done by the maintainer's reviewer (NT-cc, run 2, 2026-10-18) with the node, def-pur-frame-class, `Sheaf.Paper.PurityFrameClass`, `Scheme.Hom.EtaleFrame` (WeilConjectures/EtaleCohomology/Purity/Smooth/RegularImmersion.lean:108) and the delivered module open. Nothing in the module or the node record was changed.

Node statement as a list, with its Lean and the verdict:

1. "In the situation of def-pur-frame-class": `P : PurityFiniteSetting.{u}`, `B V Z : Scheme.{u}`, `b : B ⟶ Spec k`, `v : V ⟶ B` with `[SmoothOfRelativeDimension P.level v]`, `i : Z ⟶ V` with `[IsClosedImmersion i]`, `[Smooth (i ≫ v)]`, `c : ℕ`, `hcodim` (pointwise Krull codimension). These are binder for binder the hypotheses of the recorded `frameClass` signature; nothing is added (no finite type, separatedness, regularity, Noetherian or universe restriction). Correct.
2. A frame (e : U → V étale, f_1..f_c ∈ Γ(U,O) generating the ideal of Z ×_V U): `U`, `e`, `[Etale e]`, `f g : Fin c → Γ(U, ⊤)`, `tf`/`tg` and `hf`/`hg : IsPullback _ (U.zeroLocusSubschemeι (Set.range _)) i e`, exactly the fields of `EtaleFrame`; the structure literals are that structure. The ideal condition is scheme-theoretic (pullback square), not equality of reduced supports. Correct.
3. "the class cl(f) of def-pur-frame-class": `frameClassOnPullback` = `(cupSingle P U).map (frameClosedCoefficientIso ... F.isPullback.isoPullback isoPullback_hom_snd).inv ≫ P.frameClass b v i c hcodim F`. It is the recorded class, precomposed with the canonical coefficient iso induced by the unique iso of the frame's zero subscheme with the chosen `pullback i e` over U (argument order and the equation `isoPullback.hom ≫ pullback.snd = zeroLocusSubschemeι` checked). Not a second construction, no choice, real data. Correct.
4. "depends only on the ideal of Z, i.e. only on the pair, not on the frame": `frameClass_independent` equates the two transported classes, in literally the same group `cupSupportedHom P (pullback.snd i e) (frameTwist U c) (2c)`, for all pairs of frames on the same (U, e). Frames on different neighbourhoods are compared on the étale fibre product, which is exactly how proof step 1 of the node defines the meaning; their classes live in different groups, so this is the faithful typed rendering. Correct, not weaker.

Edge cases: c = 0 (both zero subschemes are U, classes are `frameEmptyClass`, equality nontrivial-typed and true); empty U/Z/V allowed; c = 1 unit multiples; arbitrary order/repetition of generators (no assumption on ranges); non-reduced Z_U; e not an open immersion; level not divisible by ramification index. Universes: one `u`, inherited from `frameClass`; all variables bound, `autoImplicit false`.

Searches: `rg 'frameClass|frame_independ|frameClassOnPullback'` over lean/Sheaf and WeilConjectures: only the recorded concrete `frameClass` and the upstream abstract `frameClass`/`existsUnique_fundamentalClass` (abstract HasKummerClass data, different hypotheses, not an attachment). No duplicate notion.

Dependencies: only stmt_dep def-pur-frame-class (recorded, used). Proof-dep imports (`LocalGeneratingTuples`, `SupportLongExact`, `SupportedAffineLineHomotopy`) are recorded modules of the cited proof deps; lem-pur-relative-support-bottom-descent and lem-pur-supported-cup-functoriality have no Lean record and are only named in the docstring, which is acceptable for proof deps.

Docstrings carry the source place and `(blueprint: lem-pur-frame-independence)`; the theorem docstring gives all seven proof steps. Only `sorry` in the theorem; the helper is sorry-free.

Compile: `nt_compile.py --json` with the delivered module: rc 0, no error or warning output, 17.6 s / 19.0 s (two runs).
