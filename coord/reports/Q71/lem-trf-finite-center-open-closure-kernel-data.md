## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteCenterOpenClosureKernelData` states
`AlgebraicGeometry.finiteCenterOpen_closure_kernel_data`. The theorem's whole proof is
`sorry`; nothing is proved. Its docstring carries all eight DAG proof steps with their
named dependencies. The only auxiliary declaration is the transparent abbreviation
`finiteCenterOpen f I = f ⁻¹ᵁ I.support.compl`, giving the actual canonical open already
introduced by this node. It introduces no independent notion, map, or chosen data.
No new node, dependency repair, or statement correction is needed. Only the item's
`lean` field changes.

Sources read: Stacks Project `morphisms.tex:849–884`, Tag 01R8,
`lemma-quasi-compact-scheme-theoretic-image`, and `properties.tex:3720–3752`, Tag 01PH,
`lemma-quasi-coherent-finite-type-ideals`. The latter proof's converse applies on every
affine open without requiring the ambient scheme to be qcqs. The full item statement,
eight proof steps, and all nine statement-dependency records were read before writing.

Hypotheses and objects:

- `X Y : Scheme.{u}` and `f : Y ⟶ X` are arbitrary schemes and their morphism. The universe
  is explicit; neither a field nor Noetherian, qc, qs, reduced, or nonempty hypotheses occur.
- `I : X.IdealSheafData` is exactly a quasi-coherent ideal sheaf; its associated module is
  the existing `I.toModules`. `[I.toModules.IsFiniteType]` is the node's finite-type condition.
  Quasi-coherence is inherent in the ideal-sheaf data, not an extra assumption.
- `I.support.compl` is `U = X ∖ V(I)`. `finiteCenterOpen f I` is its preimage open in `Y`.
  Its canonical open scheme represents `Y ×_X U`; its inclusion `.ι` is `j`. Thus the use
  of the preimage model changes no object or hypothesis of the fibre-product statement.
- `j.image`, `j.imageι`, `j.toImage` are exactly `S`, `i`, `h` from the recorded image
  construction. The conclusion identifies `j.ker` with the raw sheaf kernel on EVERY open,
  rather than silently substituting its quasi-coherent interior for that raw kernel.

Conclusions, in their Lean order:

1. `QuasiCompact (finiteCenterOpen f I).ι` states that `j` is quasi-compact.
2. `j.ker.toModules.IsQuasicoherent`, together with
   `∀ V : Y.Opens, j.ker.idealOfOpens V = RingHom.ker (j.app V).hom`, states that the
   actual sheaf kernel `J` is quasi-coherent, including on nonaffine opens.
3. For each `V : Y.affineOpens`, an isomorphism
   `CommRingCat.of (Γ(Y,V) ⧸ j.ker.ideal V) ≅ Γ(j.image, j.imageι ⁻¹ᵁ V)` intertwines
   the quotient projection with `j.imageι.app V`. This is precisely the quotient-sheaf
   identification `i_* O_S = O_Y/J`: affine opens are a basis, and compatibility of the
   isomorphisms with the quotient maps forces compatibility with restriction. No
   surjectivity on sections of arbitrary opens is asserted. In particular, this is an
   isomorphism of rings with the specified quotient map, not merely of underlying modules.
4. `IsIso (pullback.snd j.imageι j)` is the canonical projection
   `S ×_Y Ω → Ω`, expressing the scheme-theoretic equality over the open.
5. `IsOpenImmersion j.toImage`, `QuasiCompact j.toImage`, `QuasiSeparated j.toImage`, and
   `IsIso (pullback.diagonal j.toImage)` match all assertions about `h` and its diagonal.
6. `∀ V : j.image.Opens, Function.Injective (j.toImage.app V)` is injectivity of its
   structure-sheaf map. `IsSchemeTheoreticallyDominant j.toImage` says `SIm(h)=S`.
7. The universally quantified `R`, `s : R ⟶ Y`, and `[IsClosedImmersion s]` range over
   every closed immersion in the node. The supplied `hR : Ω → R` satisfies
   `IsPullback hR (𝟙 Ω) s j`, exactly the specified identification `R ×_Y Ω = Ω`.
   This determines the induced inclusion, rather than allowing an arbitrary map or
   adding an open-immersion assumption. `IsSchemeTheoreticallyDominant hR` is precisely
   the hypothesis `SIm(hR)=R`. It imposes no raw-kernel condition in advance.
8. Under these assumptions, `QuasiCompact hR` and `∀ V, Function.Injective (hR.app V)`
   give the first two conclusions. `s.ker = j.ker` identifies the ideal of `R` with `J`.
   The isomorphism `e : R ≅ j.image` with `e.hom ≫ j.imageι = s` explicitly gives equality
   as closed subschemes over `Y` (not an equality of underlying sets).
9. For every `P`, closed `k : Y ⟶ P`, and EVERY open `V : P.Opens`, the final two equalities
   identify `(s ≫ k).ker.idealOfOpens V` both with `RingHom.ker ((j ≫ k).app V).hom` and
   with `Ideal.comap (k.app V).hom (j.ker.idealOfOpens (k ⁻¹ᵁ V))`. These are the ambient
   kernel and the inverse image of `k_* J` under the canonical structure map.

Dependency declarations used (including the actual signatures/docstrings read):

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`, lines 35–47 and 70–79.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`,
  `Scheme.Modules.IsQuasiCoherentFiniteType` (the full module was read); its publicly
  exposed `SheafOfModules.IsFiniteType` is the actual predicate used. Its definition in
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/Generators.lean:140–145` and
  `IsQuasicoherent` in `Quasicoherent.lean:249–253` were read. There is no copy of either.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `.snd`, `.diagonal`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, lines 95–130 and the
  scheme pullback API. `IsPullback` records the specified fibre-product square for `R`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion:34–39`.
- `def-nagata-scheme-theoretic-image`: `Scheme.Hom.image`, `.imageι`, `.toImage`,
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme:659–715`; these are used without
  redefinition. `.subschemeObjIso` and `.subschemeι_app` at 535–559 were also read
  to fix precisely the compatible quotient-ring formulation.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact:37–45`; the recorded
  `LocallyOfFiniteType` signature in `Morphisms/FiniteType.lean:43–48` was also read.
  Only the quasi-compactness notion of this multi-notion node is needed here.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:41–46`, and its lift / isomorphism
  API at 202–235. Closed immersions are not replaced by arbitrary monomorphisms.
- `def-sbc-closed-immersion-ideal-sheaf`: `Scheme.Hom.ker`,
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic:689–703` (definition and qc identification).
  The full existing bridge `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`
  was read and imported for `.toModules` and `.idealOfOpens`, especially lines 89–137.
- `def-weil-quasi-separated-morphism`: `AlgebraicGeometry.QuasiSeparated`,
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated:47–55`.
- For density, `IsSchemeTheoreticallyDominant` in
  `Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant:36–42` is precisely
  `.ker = ⊥`; `.app_injective` in that module was read as well.

Proof dependencies' recorded Lean/Mathlib matches were inspected. Their supplying modules
are imported directly or through the public statement imports: the affine finite-type
criterion, prime-spectrum basic opens, qc and open base change, image kernel/quotient API,
closed-subscheme base-change ideal image, equal-ideal closed-immersion comparison,
open-immersion monomorphism, and image-factor injectivity. Proof-only imports are ordinary
`import`s. All definitions used by the statement are publicly exposed.

Edge cases checked mathematically:

- `I = 0`: `U` and `Ω` are empty; `J = O_Y`, `S` is empty, and the quotient is the zero
  ring. Density for `hR` forces `R` empty. No nonempty assumption excludes this case.
- `I = O_X`: `Ω = Y`, `J = 0`, `S = Y`. The pullback hypothesis then forces `s` to be an
  isomorphism, and the ambient formula becomes the ideal of `k`.
- Empty `X`, `Y`, or `P` cause no excluded cases. Finite generation includes zero generators.
- Noetherianity, quasi-compactness and quasi-separatedness of `X` and `Y` are absent;
  finite type of the ideal ensures retrocompactness affine-locally even on non-qcqs schemes.
- Nonreduced examples retain nilpotent ideal information: equality of `.ker` and the
  structure-sheaf injectivity conditions cannot be replaced by topological density.
- The sheaf quotient is checked only on the affine basis with the actual quotient maps;
  the arbitrary-open formulas concern kernels and injectivity, where sections do commute
  with these assertions. No erroneous global-sections quotient assertion is made.

Searches actually run through the prescribed wrapper:

- `leanfinder`: “A finite type quasi coherent ideal complement open immersion has quasi
  compact scheme theoretic closure kernel ideal and ambient closed immersion kernel”.
  Eight hits: subscheme-inclusion qc, kernel restriction, support kernel, `Hom.ker_apply`,
  `.subscheme`, affine-cover kernel, qc immersion factorization, `ker_toSpecΓ`. These are
  components, none the full node statement.
- `loogle`: `AlgebraicGeometry.Scheme.Hom.ker, AlgebraicGeometry.Scheme.Hom.toImage`.
  One hit, `Scheme.Hom.toImage_app`, supplies the affine quotient-lift formula, not this
  combined finite-centre/open-closure/ambient-recognition assertion.
- `grep`: `toImage|ker_apply|IsSchemeTheoreticallyDominant` in `AlgebraicGeometry/IdealSheaf`.
  Twelve hits in Basic, Functorial, Subscheme; none states the entire node.
- `leansearch`: “quasi compact open immersion kernel sheaf scheme theoretic image”.
  Eight hits: `IsImmersion.instIsOpenImmersionToImageOfQuasiCompact`, `ker_toSpecΓ`,
  `Hom.ker`, cover kernel, `QuasiCompact.mk`, `.ker_apply`, `instQuasiCompactToImage`,
  and `ker_ideal_of_isPullback_of_isOpenImmersion`. All were component matches.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `finiteCenter`, `finite_center`, `openClosure`, `open_closure`, and the node id found
  no existing statement of this node. Broader ideal/kernel searches located the existing
  IdealSheaf.Module bridge and were used to avoid redefining it. The helper name
  `finiteCenterOpen` also has no collision in the source trees or declaration registry.

Validation: `scompile.py Q71 lem-trf-finite-center-open-closure-kernel-data <module>`
compiled both the sandbox probe and the actual library module cleanly (48.2 s and 4.1 s).
There were no errors or warnings. Universes and all variables are explicitly bound;
`set_option autoImplicit false` is in the module. All Lean lines are at most 100 characters.

## Second reading by Q71

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
