## Worker report

Module: `Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupEmbeddingExtension`.
Declaration: `AlgebraicGeometry.AlgebraicSpace.exists_blowup_embedding_extension`.
This is a stage-2 statement only: its sole theorem has proof `by sorry`; there are
no new definitions or helper theorems.

The source is Stacks, `spaces-more-morphisms.tex`, Tag 088R,
`lemma-blowup-to-find-embedding`, read in full, specialized as the node requests
to a scheme base B. The seven-step proof docstring records the node's full route,
including the extra common boundary blowup that makes the density argument valid
without assuming U dense in X. Tags 085Q, 085R, 085T and 085Z specify the blowup
construction and its properties.

Hypothesis-by-hypothesis correspondence:

- The ambient scheme is `{S : Scheme.{u}}`. Every scheme, coefficient carrier and
  algebraic space uses the same arbitrary universe `u`; site object universes
  remain those of the recorded algebraic-space definition. `autoImplicit` is false.
- The scheme B over S is `B : Over S`; its quasi-compactness and quasi-separatedness
  are `[CompactSpace B.left]` and `[QuasiSeparatedSpace B.left]`.
- `X U : AlgebraicSpace S`, `f : X ⟶ schemeSpace B`, `hfs : MapIsSeparated f` and
  `hfft : MapIsFiniteType f` express the separated finite-type morphism to B.
- The open subspace is an arbitrary open immersion `j : U ⟶ X` with
  `hj : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom`.
  Presenting a subspace by its open immersion retains precisely its data up to
  isomorphism, without a second definition of open subspace.
- `hUqc` asks for a quasi-compact scheme with representable etale surjective map
  to U. This is the existing atlas formulation of quasi-compactness used in
  `exists_common_admissible_blowups`, not a quasi-compactness assumption on X.
- `n : ℕ` includes n = 0. The coordinate type is `ULift.{u} (Fin (n + 1))`, since
  ProjectiveSpace indexes homogeneous coordinates; the lift keeps the prescribed
  universe without changing the finite coordinate set.
- `a` is a map from the actual sheaf of U to the Yoneda sheaf of projective space
  over B, endowed with its composite map to S. `ha` tests `IsImmersion` on every
  scheme base change. Mathlib's immersion is a closed immersion followed by an
  open immersion (`IsImmersion.isImmersion_iff_exists`).
- `haB` is exactly the assertion that a is over B: its projection to B equals j f.

Clause-by-clause correspondence of the conclusion:

- `Z : Over S` is a scheme over S and `i : Z ⟶ ...` maps it into projective space.
  `IsClosedImmersion i.left` is its closed-immersion property.
- `u₀` is the map U to Z, represented by a natural transformation; its
  `IsRepresentableWith ... IsOpenImmersion` condition makes it an open immersion.
  `u₀ ≫ yoneda.map i = a` is exactly i u = a. Keeping U as an algebraic space here
  avoids assuming as an input the scheme representability which a implies.
- `I : QuasiCoherentIdeal X` is an ideal subobject of the small-etale structure
  module, with the existing quasi-coherence predicate. `(I.val : X.Modules).IsFiniteType`
  asserts local finite generation.
- `J : Z.left.IdealSheafData` is a Zariski quasi-coherent ideal sheaf on the scheme Z;
  `J.toModules.IsFiniteType` is exactly local finite generation of its module.
- The condition on all `T : X.EtaleSite` factoring through j says their ideal of
  sections is top, hence I restricted to U is the full structure sheaf. This is
  the sectionwise definition used by `IdealIsUnitAbove` and by the common-blowup node.
- The condition on every `h : T ⟶ Z` factoring through `u₀` is `J.comap h.left = ⊤`.
  This is u^*J = O_U, expressed without inventing a Zariski module category on the
  algebraic-space source U. Every such test scheme lies over U, and after the open
  immersion identifies U with an open subscheme, these are exactly its scheme tests.
- `D : BlowupPresentation I` is the descended Rees-Proj blowup: the recorded
  structure requires its pullback on every affine etale chart to be the ordinary
  scheme blowup. This is not an arbitrary proper modification.
- `V : Over S` and `e : schemeSpace V ≅ D.space` assert the blowup is a scheme.
  Its q is concretely the composite `e.hom ≫ D.projection`.
- Z-prime is precisely `J.blowup`; b is precisely `J.blowupMap`, not an arbitrary
  scheme equipped with a morphism to Z. `v : V ⟶ Over.mk (J.blowupMap ≫ Z.hom)`
  is the indicated scheme map, and `IsOpenImmersion v.left` is its open-immersion clause.
- `IsRepresentable (e.hom.hom.hom ≫ D.projection.hom.hom)` and
  `MapIsProper (e.hom ≫ D.projection)` state representability and properness of q.
- The equality with `yoneda.map (v ≫ ... b ... i ... projection)` is precisely
  commutativity over B. Every map is already over S.
- `IsPullback s (𝟙 U.obj.obj) q j.hom.hom` asserts the ENTIRE inverse image of U is
  U, with s the inverse identification followed by inclusion. It implies q s = j
  and that this restriction of q is an isomorphism; it is stronger than an arbitrary
  section but exactly the isomorphism-over-U clause of the node.
- `s ≫ yoneda.map (v ≫ Over.homMk J.blowupMap) = u₀` is b v s = u. No separate
  open-immersion assumption on s is needed: it follows by base changing j in the
  displayed square.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsRepresentable`, `IsEtale`, `IsSurjective`, the small etale module category.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsSeparated`,
  `MapIsFiniteType`, `MapIsProper`, with their full chart and point-topology definitions.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace` and its
  `CanonicallyOver` structure (projection to B). This also supplies the already-stated
  projective-space properness proof dependency.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `IsImmersion`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` uses the existing
  `SheafOfModules.IsQuasicoherent`, also used by `QuasiCoherentIdeal` (no duplicate QCoh).
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`;
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`: `toModules`;
  `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`: `comap`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: exposes
  `SheafOfModules.IsFiniteType` from `pqf-def-coherent`; its conjunction
  `IsQuasiCoherentFiniteType` is not substituted for the required ideal predicates.
- The metatheoretic `def-weil-size-convention` is rendered by explicit universe `u`;
  its record intentionally has no Lean declaration or module.
- The three additional stmt_deps are ALREADY LANDED definition nodes:
  `def-trf-scheme-algebraic-space` supplies `schemeSpace` in
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`;
  `def-sfb-space-quasi-coherent-ideal` supplies `QuasiCoherentIdeal`;
  `def-sfb-space-blowup-presentation` supplies `BlowupPresentation`, `blowupChartIdeal`,
  `IdealIsUnitAbove`. Their source declarations and docstrings were read in full.
  These additions only expose the existing notions explicitly requested by the item.

All proof dependencies with recorded modules are imported. The common admissible
blowups, finite-type boundary ideal, composition of admissible blowups and
ideal/closed-subspace correspondence modules are private proof imports. The image
and immersion/image modules are imported as well. The other proof dependencies
have no recorded Lean module, so no such import can yet be supplied.

Edge cases checked before writing: U empty (the unit ideal restriction conditions
are vacuous and the zero-ideal blowup permits empty V and Z); U = X; n = 0 (one
homogeneous coordinate); B empty; nonreduced and non-Noetherian schemes; and U not
dense in X. There are no nonemptiness, density, reduction, Noetherian or positive-n
hypotheses. The proof docstring's common boundary blowup addresses the nondense case.

Searches for an existing statement:

- `msearch.py ... leanfinder`: “An immersion of a quasi compact open in a separated
  finite type algebraic space into projective space extends after admissible blowups”.
  Eight hits: Proj affine charts/properness and the quasi-compact immersion/image
  factorization; none gives this extension by two admissible blowups.
- `msearch.py ... leansearch`: “Extending a prescribed immersion of an open algebraic
  space into projective space by admissible blowups”. Eight hits, all ordinary
  immersion definitions, inheritance and coborder factorization; no matching theorem.
- `msearch.py ... loogle`: `AlgebraicGeometry.IsImmersion, "blowup"`: zero hits.
- `msearch.py ... grep`: `blow.?up|[Aa]dmissible`, Mathlib AlgebraicGeometry: five
  unrelated admissible Weierstrass variable-change hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `embedding.extension|find.embedding|blowup.*embedding|Embedding.*Blowup|extends.*immersion`:
  only unrelated field embeddings, ideal-stalk extension, existing projective blowup
  charts and quasi-affine descent. Search for the exact item id in WeilConjectures
  has no hits. Searches for scheme representability, quasi-coherent ideals and blowup
  presentations found the existing nodes above; they are reused, never copied.

No STATEMENT-DISPUTED flag or statement correction is needed. No dependency is repaired
and no new node is introduced. Only `lean` and the three landed stmt_dep additions
change in the item copy. Compilation via the prescribed scompile.py succeeded for
both its sandbox and library module checks, with no diagnostics.

## Second reading by Q58

The original section was a self-audit by the delivering worker. This independent
reading was done by the maintainer's stage-2 reviewer. It replaces that section. It
checks the node's clauses against the Lean of
`AlgebraicGeometry.AlgebraicSpace.exists_blowup_embedding_extension`.

Objects and hypotheses:
- S is a scheme and B a qcqs scheme over S. In the Lean, `S : Scheme.{u}`,
  `B : Over S`, `[CompactSpace B.left]` and `[QuasiSeparatedSpace B.left]`. Exact.
- f : X → B is separated and of finite type. In the Lean, `f : X ⟶ schemeSpace B`
  (from def-trf-scheme-algebraic-space) with `MapIsSeparated` and `MapIsFiniteType`
  (from def-sfb-space-morphism-properties). Exact.
- U ⊆ X is a quasi-compact open subspace. In the Lean, `j` is open-immersion
  representable and `hUqc` gives a quasi-compact étale surjective scheme atlas. This
  is the same encoding as the cited lem-sfb-space-common-admissible-blowups. Exact.
- a : U → P^n_B is an immersion over B, for n ≥ 0. In the Lean, P^n_B is
  `ProjectiveSpace (ULift (Fin (n+1))) B.left`, with structure map pullback.fst
  (def-nagata-projective-space-base-change, n+1 homogeneous coordinates). `ha`
  requires `IsImmersion` on every scheme test. In Mathlib this is a closed immersion
  followed by an open immersion. `haB` is the condition that a lies over B. Exact,
  and n = 0 is allowed.

Conclusion:
- The scheme Z, the closed immersion i, the open immersion u and the equation iu = a
  are rendered by `Z`, `i`, `IsClosedImmersion i.left`, `u₀` (open-immersion
  representable) and `u₀ ≫ yoneda.map i = a`. Exact.
- I is a finite-type quasi-coherent ideal on the étale site of X with I|_U = O_U.
  The Lean uses `QuasiCoherentIdeal X` (def-sfb-space-quasi-coherent-ideal) and
  `IsFiniteType`. The unit condition requires the section ideal to be ⊤ on every
  étale chart over U. This matches IdealIsUnitAbove and the common-blowups node.
- J is a finite-type Zariski ideal on Z with u^*J = O_U. The Lean uses
  `Z.left.IdealSheafData` (quasi-coherent by construction) and
  `J.toModules.IsFiniteType`. The unit condition is `J.comap h.left = ⊤` for every
  scheme map h that factors through u₀. Taking T = U (U is a scheme because a is
  representable) gives u^*J = O_U; conversely, u^*J = O_U implies it for every such h.
  Equivalent.
- V = Bl_I X. In the Lean, `D : BlowupPresentation I` is the chartwise ordinary
  blowup (def-sfb-space-blowup-presentation), and `e : schemeSpace V ≅ D.space`
  makes V a scheme. Exact.
- Z' = Bl_J Z and b are `J.blowup` and `J.blowupMap` (def-nagata-global-blowup), not
  an arbitrary modification. v is an open immersion: `IsOpenImmersion v.left`. Exact.
- q is representable and proper: `IsRepresentable` and `MapIsProper` of
  `e.hom ≫ D.projection`.
- The commutative diagram over B is the equation q f = (v b i proj) as Yoneda maps.
  Exact.
- q^{-1}(U) → U is an isomorphism with s its inverse followed by inclusion. The Lean
  states `IsPullback s (𝟙 U) q j`. This is a cartesian square whose bottom map is the
  identity, which is exactly the clause.
- bvs = u is `s ≫ yoneda.map (v ≫ homMk J.blowupMap) = u₀`. Exact.
- The Lean adds no density, Noetherian, reducedness, nonemptiness or extra universe
  hypothesis. The quantifier order is the node's.

Edge cases:
- U = ∅: the unit conditions are vacuous, and I = J = 0 is allowed.
- U = X, n = 0, B = ∅, nonreduced or non-Noetherian X: no hypothesis excludes any of
  them.

Records:
- `lean.statement` matches the file verbatim.
- The three added stmt_deps are landed definition nodes that the statement uses:
  def-trf-scheme-algebraic-space, def-sfb-space-quasi-coherent-ideal and
  def-sfb-space-blowup-presentation.
- The live item is unchanged and has no lean record. No parallel declaration exists
  in live lean/Sheaf.
- The proof is `sorry` only, and the docstrings carry Tag 088R and the blueprint id.
- There is no new definition and no pro-étale content.

No mismatch was found in the Lean or the records.
